import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358

/-- The energy absorption step in the stationary-site moment estimate. -/
theorem midpoint_energy_absorption {A B R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A / 4 ≤ R ^ 2 * B / 8 + R / 2 * Real.sqrt (A * B)) :
    A ≤ 5 * R ^ 2 * B := by
  rw [Real.sqrt_mul hA] at h
  have hsa := Real.sq_sqrt hA
  have hsb : (R * Real.sqrt B) ^ 2 = R ^ 2 * B := by
    rw [mul_pow, Real.sq_sqrt hB]
  nlinarith [sq_nonneg (Real.sqrt A - 2 * (R * Real.sqrt B))]

/-- Uniform comparisons of nearby cell masses, in the normalization used in
    the finite-difference estimate. -/
theorem nearby_mass_square_bound {M α γ : ℝ}
    (hM : 0 < M) (hα : 0 ≤ α) (hαM : α ≤ 2 * M)
    (hγM : M / 2 ≤ γ) : α ^ 2 / M ≤ 8 * γ := by
  apply (div_le_iff₀ hM).2
  have hsq : α ^ 2 ≤ (2 * M) ^ 2 := (sq_le_sq₀ hα (by positivity)).2 hαM
  nlinarith

/-- The reciprocal comparison for nearby cell masses. -/
theorem nearby_mass_reciprocal_bound {M γ δ : ℝ}
    (hM : 0 < M) (hγM : M / 2 ≤ γ) :
    δ ^ 2 / γ ≤ 2 * (δ ^ 2 / M) := by
  have hγ : 0 < γ := by linarith
  apply (div_le_iff₀ hγ).2
  have hm : δ ^ 2 * M ≤ δ ^ 2 * (2 * γ) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg δ)
  calc
    δ ^ 2 ≤ (2 * δ ^ 2 * γ) / M := (le_div_iff₀ hM).2 (by nlinarith)
    _ = 2 * (δ ^ 2 / M) * γ := by ring

/-- A finite-difference moment estimate with a constant independent of the
    number of cells or the smallest cell mass. The geometric input is the
    midpoint energy estimate and the elementary bound on each moment change. -/
theorem stationary_moment_finite_difference
    {ι V : Type*} [Fintype ι] [SeminormedAddCommGroup V]
    (M α γ δ D : ι → ℝ) (Δ : ι → V) (R : ℝ)
    (hM : ∀ i, 0 < M i) (hα : ∀ i, 0 ≤ α i)
    (hαM : ∀ i, α i ≤ 2 * M i)
    (hγM : ∀ i, M i / 2 ≤ γ i)
    (hD : ∀ i, 0 ≤ D i) (hR : 0 ≤ R)
    (hΔ : ∀ i, ‖Δ i‖ ≤ R * |δ i| + α i * Real.sqrt (D i))
    (henergy : (∑ i, γ i * D i) ≤
      5 * R ^ 2 * (∑ i, δ i ^ 2 / γ i)) :
    (∑ i, ‖Δ i‖ ^ 2 / M i) ≤
      162 * R ^ 2 * (∑ i, δ i ^ 2 / M i) := by
  have hpoint (i : ι) : ‖Δ i‖ ^ 2 ≤
      2 * R ^ 2 * δ i ^ 2 + 2 * α i ^ 2 * D i := by
    have hsq := (sq_le_sq₀ (norm_nonneg (Δ i))
      (show 0 ≤ R * |δ i| + α i * Real.sqrt (D i) from
        add_nonneg (mul_nonneg hR (abs_nonneg _))
          (mul_nonneg (hα i) (Real.sqrt_nonneg _)))).2 (hΔ i)
    have ha : (R * |δ i|) ^ 2 = R ^ 2 * δ i ^ 2 := by
      rw [mul_pow, sq_abs]
    have hb : (α i * Real.sqrt (D i)) ^ 2 = α i ^ 2 * D i := by
      rw [mul_pow, Real.sq_sqrt (hD i)]
    nlinarith [sq_nonneg (R * |δ i| - α i * Real.sqrt (D i))]
  have hterm (i : ι) : ‖Δ i‖ ^ 2 / M i ≤
      2 * R ^ 2 * (δ i ^ 2 / M i) + 16 * (γ i * D i) := by
    have hmass := nearby_mass_square_bound (hM i) (hα i) (hαM i) (hγM i)
    have hmul := mul_le_mul_of_nonneg_right hmass (hD i)
    calc
      ‖Δ i‖ ^ 2 / M i ≤
          (2 * R ^ 2 * δ i ^ 2 + 2 * α i ^ 2 * D i) / M i :=
        div_le_div_of_nonneg_right (hpoint i) (hM i).le
      _ = 2 * R ^ 2 * (δ i ^ 2 / M i) +
          2 * (α i ^ 2 / M i * D i) := by ring
      _ ≤ 2 * R ^ 2 * (δ i ^ 2 / M i) + 16 * (γ i * D i) := by
        linarith
  have hrecip : (∑ i, δ i ^ 2 / γ i) ≤
      2 * (∑ i, δ i ^ 2 / M i) := by
    calc
      (∑ i, δ i ^ 2 / γ i) ≤ ∑ i, 2 * (δ i ^ 2 / M i) :=
        Finset.sum_le_sum fun i _ => nearby_mass_reciprocal_bound (hM i) (hγM i)
      _ = _ := by rw [Finset.mul_sum]
  have henergy' : (∑ i, γ i * D i) ≤
      10 * R ^ 2 * (∑ i, δ i ^ 2 / M i) := by
    have hm := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ 5 * R ^ 2 by positivity)
    nlinarith
  calc
    (∑ i, ‖Δ i‖ ^ 2 / M i) ≤
        ∑ i, (2 * R ^ 2 * (δ i ^ 2 / M i) + 16 * (γ i * D i)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * R ^ 2 * (∑ i, δ i ^ 2 / M i) + 16 * (∑ i, γ i * D i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 162 * R ^ 2 * (∑ i, δ i ^ 2 / M i) := by linarith

/-- Positive limiting cell masses give all nearby-mass comparisons
simultaneously, with no uniform lower bound on the finite configuration. -/
theorem eventually_nearby_mass_bounds
    {ι A : Type*} [Finite ι] {l : Filter A}
    (M : ι → ℝ) (α β : A → ι → ℝ)
    (hM : ∀ i, 0 < M i)
    (hα : ∀ i, Filter.Tendsto (fun a => α a i) l (nhds (M i)))
    (hβ : ∀ i, Filter.Tendsto (fun a => β a i) l (nhds (M i))) :
    ∀ᶠ a in l, ∀ i, 0 < α a i ∧ 0 < β a i ∧
      α a i ≤ 2 * M i ∧ M i / 2 ≤ Real.sqrt (α a i * β a i) := by
  apply Filter.eventually_all.mpr
  intro i
  have hγ : Filter.Tendsto (fun a => Real.sqrt (α a i * β a i)) l (nhds (M i)) := by
    simpa only [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos (hM i)] using
      ((hα i).mul (hβ i)).sqrt
  filter_upwards [(hα i).eventually_const_lt (hM i),
    (hβ i).eventually_const_lt (hM i),
    (hα i).eventually_lt_const (show M i < 2 * M i by linarith [hM i]),
    hγ.eventually_const_lt (show M i / 2 < M i by linarith [hM i])]
    with a ha hb haM hγM
  exact ⟨ha, hb, haM.le, hγM.le⟩

/-- The raw geometric moment inputs imply the uniform finite-difference
estimate eventually, using continuity of the actual two endpoint masses. -/
theorem eventually_stationary_moment_finite_difference
    {ι V A : Type*} [Fintype ι] [SeminormedAddCommGroup V] {l : Filter A}
    (M : ι → ℝ) (α β δ D : A → ι → ℝ) (Δ : A → ι → V) (R : ℝ)
    (hM : ∀ i, 0 < M i) (hR : 0 ≤ R)
    (hα : ∀ i, Filter.Tendsto (fun a => α a i) l (nhds (M i)))
    (hβ : ∀ i, Filter.Tendsto (fun a => β a i) l (nhds (M i)))
    (hD : ∀ᶠ a in l, ∀ i, 0 ≤ D a i)
    (hΔ : ∀ᶠ a in l, ∀ i,
      ‖Δ a i‖ ≤ R * |δ a i| + α a i * Real.sqrt (D a i))
    (henergy : ∀ᶠ a in l,
      (∑ i, Real.sqrt (α a i * β a i) * D a i) ≤
      5 * R ^ 2 * (∑ i, δ a i ^ 2 / Real.sqrt (α a i * β a i))) :
    ∀ᶠ a in l, (∑ i, ‖Δ a i‖ ^ 2 / M i) ≤
      162 * R ^ 2 * (∑ i, δ a i ^ 2 / M i) := by
  filter_upwards [eventually_nearby_mass_bounds M α β hM hα hβ,
    hD, hΔ, henergy] with a hm hd hdelta he
  exact stationary_moment_finite_difference M (α a)
    (fun i => Real.sqrt (α a i * β a i)) (δ a) (D a) (Δ a) R
    hM (fun i => (hm i).1.le) (fun i => (hm i).2.2.1)
    (fun i => (hm i).2.2.2) hd hR hdelta he

/-- Weighted squared norm energies scale quadratically. -/
theorem weighted_moment_energy_smul
    {ι V : Type*} [Fintype ι] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (M : ι → ℝ) (B : ι → V) (c : ℝ) :
    (∑ i, ‖c • B i‖ ^ 2 / M i) = c ^ 2 * (∑ i, ‖B i‖ ^ 2 / M i) := by
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_div_assoc]
  rw [Finset.mul_sum]

/-- The finite moment inequality passes to derivative limits. The arbitrary
    scale `c` is typically `(2*s)⁻¹`; stating the argument for any filter also
    permits one-sided finite differences and sequences. -/
theorem stationary_moment_limit
    {ι V A : Type*} [Fintype ι] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter A} [l.NeBot]
    (M : ι → ℝ) (B : A → ι → V) (m : A → ι → ℝ)
    (c : A → ℝ) (dB : ι → V) (dm : ι → ℝ) (C : ℝ)
    (hB : ∀ i, Filter.Tendsto (fun a => c a • B a i) l (nhds (dB i)))
    (hm : ∀ i, Filter.Tendsto (fun a => c a * m a i) l (nhds (dm i)))
    (hbound : ∀ᶠ a in l, (∑ i, ‖B a i‖ ^ 2 / M i) ≤
      C * (∑ i, m a i ^ 2 / M i)) :
    (∑ i, ‖dB i‖ ^ 2 / M i) ≤ C * (∑ i, dm i ^ 2 / M i) := by
  have hleft : Filter.Tendsto (fun a => ∑ i, ‖c a • B a i‖ ^ 2 / M i)
      l (nhds (∑ i, ‖dB i‖ ^ 2 / M i)) := by
    exact tendsto_finsetSum Finset.univ fun i _ => ((hB i).norm.pow 2).div_const (M i)
  have hright : Filter.Tendsto (fun a => C * (∑ i, (c a * m a i) ^ 2 / M i))
      l (nhds (C * (∑ i, dm i ^ 2 / M i))) := by
    exact Filter.Tendsto.const_mul C
      (tendsto_finsetSum Finset.univ fun i _ => ((hm i).pow 2).div_const (M i))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hbound] with a ha
  rw [weighted_moment_energy_smul]
  have hs : (∑ i, (c a * m a i) ^ 2 / M i) =
      c a ^ 2 * (∑ i, m a i ^ 2 / M i) := by
    simp_rw [mul_pow, mul_div_assoc]
    rw [Finset.mul_sum]
  rw [hs]
  have hh := mul_le_mul_of_nonneg_left ha (sq_nonneg (c a))
  nlinarith

/-- The stationary-site derivative estimate from continuous endpoint masses,
the geometric energy input, and genuine limits of the scaled differences. -/
theorem stationary_moment_limit_of_continuous_masses
    {ι V A : Type*} [Fintype ι] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter A} [l.NeBot]
    (M : ι → ℝ) (α β δ D : A → ι → ℝ) (Δ : A → ι → V) (R : ℝ)
    (c : A → ℝ) (dB : ι → V) (dm : ι → ℝ)
    (hM : ∀ i, 0 < M i) (hR : 0 ≤ R)
    (hα : ∀ i, Filter.Tendsto (fun a => α a i) l (nhds (M i)))
    (hβ : ∀ i, Filter.Tendsto (fun a => β a i) l (nhds (M i)))
    (hD : ∀ᶠ a in l, ∀ i, 0 ≤ D a i)
    (hΔ : ∀ᶠ a in l, ∀ i,
      ‖Δ a i‖ ≤ R * |δ a i| + α a i * Real.sqrt (D a i))
    (henergy : ∀ᶠ a in l,
      (∑ i, Real.sqrt (α a i * β a i) * D a i) ≤
      5 * R ^ 2 * (∑ i, δ a i ^ 2 / Real.sqrt (α a i * β a i)))
    (hB : ∀ i, Filter.Tendsto (fun a => c a • Δ a i) l (nhds (dB i)))
    (hm : ∀ i, Filter.Tendsto (fun a => c a * δ a i) l (nhds (dm i))) :
    (∑ i, ‖dB i‖ ^ 2 / M i) ≤
      162 * R ^ 2 * (∑ i, dm i ^ 2 / M i) := by
  exact stationary_moment_limit M Δ δ c dB dm (162 * R ^ 2) hB hm
    (eventually_stationary_moment_finite_difference M α β δ D Δ R
      hM hR hα hβ hD hΔ henergy)

end Problem358

end

noncomputable section

open scoped BigOperators Topology

namespace Problem358

/-- Quantitative arithmetic--geometric mean gap for two positive cell masses. -/
theorem mass_geometric_mean_gap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) / 2 - Real.sqrt (a * b) ≤
      (a - b) ^ 2 / (8 * Real.sqrt (a * b)) := by
  have hg : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hgsq := Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  apply (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt (a * b))).2
  nlinarith [sq_nonneg (a + b - 2 * Real.sqrt (a * b))]

/-- Weighted Cauchy--Schwarz in precisely the variables used by the cell argument. -/
theorem moment_weighted_cauchy {ι : Type*} [Fintype ι]
    {δ γ D : ι → ℝ} (hγ : ∀ i, 0 < γ i) (hD : ∀ i, 0 ≤ D i) :
    (∑ i, |δ i| * Real.sqrt (D i)) ≤
      Real.sqrt ((∑ i, γ i * D i) * (∑ i, δ i ^ 2 / γ i)) := by
  have hid : ∀ i, |δ i| * Real.sqrt (D i) =
      Real.sqrt (γ i * D i) * Real.sqrt (δ i ^ 2 / γ i) := by
    intro i
    rw [← Real.sqrt_mul (mul_nonneg (le_of_lt (hγ i)) (hD i))]
    have heq : γ i * D i * (δ i ^ 2 / γ i) = δ i ^ 2 * D i := by
      field_simp [ne_of_gt (hγ i)]
    rw [heq, Real.sqrt_mul (sq_nonneg (δ i)), Real.sqrt_sq_eq_abs]
  calc
    (∑ i, |δ i| * Real.sqrt (D i)) =
        ∑ i, Real.sqrt (γ i * D i) * Real.sqrt (δ i ^ 2 / γ i) := by
      exact Finset.sum_congr rfl (fun i _ => hid i)
    _ ≤ Real.sqrt (∑ i, γ i * D i) * Real.sqrt (∑ i, δ i ^ 2 / γ i) := by
      exact Real.sum_sqrt_mul_sqrt_le Finset.univ
        (fun i => mul_nonneg (le_of_lt (hγ i)) (hD i))
        (fun i => div_nonneg (sq_nonneg (δ i)) (le_of_lt (hγ i)))
    _ = _ := (Real.sqrt_mul
      (Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hγ i)) (hD i))) _).symm

/-- Symmetric moment differences converge to the negative derivative. -/
theorem tendsto_symmetric_moment_quotient {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {v : V} (hf : HasDerivAt f v 0) :
    Filter.Tendsto (fun s : ℝ => (2 * s)⁻¹ • (f (-s) - f s))
      (𝓝[>] 0) (𝓝 (-v)) := by
  have hn : HasDerivAt (fun s : ℝ => f (-s)) (-v) 0 := by
    have hf' : HasDerivAt f v (- (0 : ℝ)) := by simpa using hf
    simpa [Function.comp_def] using hf'.scomp 0 (hasDerivAt_neg 0)
  have hd := (hn.sub hf).const_smul (1 / 2 : ℝ)
  have ht := hd.tendsto_slope_zero_right
  have htarget : (1 / 2 : ℝ) • (-v - v) = -v := by module
  rw [htarget] at ht
  convert ht using 1
  ext s
  simp only [zero_add, Pi.smul_apply, Pi.sub_apply, neg_zero, sub_self, smul_zero, sub_zero,
    smul_smul]
  congr 1
  simp [mul_inv_rev]

/-- Passing a uniform symmetric finite-difference estimate to cell derivatives.
The geometric construction supplies `hfinite`; this lemma performs the limit step. -/
theorem moment_derivative_bound {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : ι → ℝ → V} {m : ι → ℝ → ℝ}
    {dB : ι → V} {dm M : ι → ℝ} {C : ℝ}
    (hB : ∀ i, HasDerivAt (B i) (dB i) 0)
    (hm : ∀ i, HasDerivAt (m i) (dm i) 0)
    (hfinite : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (∑ i, ‖B i (-s) - B i s‖ ^ 2 / M i) ≤
        C * ∑ i, (m i (-s) - m i s) ^ 2 / M i) :
    (∑ i, ‖dB i‖ ^ 2 / M i) ≤ C * ∑ i, dm i ^ 2 / M i := by
  have hl : Filter.Tendsto
      (fun s : ℝ => ∑ i, ‖(2 * s)⁻¹ • (B i (-s) - B i s)‖ ^ 2 / M i)
      (𝓝[>] 0) (𝓝 (∑ i, ‖dB i‖ ^ 2 / M i)) := by
    apply tendsto_finsetSum
    intro i _
    simpa using (((tendsto_symmetric_moment_quotient (hB i)).norm).pow 2).div_const (M i)
  have hr : Filter.Tendsto
      (fun s : ℝ => ∑ i, ‖(2 * s)⁻¹ • (m i (-s) - m i s)‖ ^ 2 / M i)
      (𝓝[>] 0) (𝓝 (∑ i, dm i ^ 2 / M i)) := by
    apply tendsto_finsetSum
    intro i _
    simpa [Real.norm_eq_abs, sq_abs] using
      (((tendsto_symmetric_moment_quotient (hm i)).norm).pow 2).div_const (M i)
  apply le_of_tendsto_of_tendsto hl (hr.const_mul C)
  filter_upwards [hfinite] with s hs
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg ((2 * s)⁻¹))
  simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_div_assoc, Finset.mul_sum, mul_assoc, mul_left_comm] using hh

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.MomentCouplingBounds

variable {A F : Type*} [MeasurableSpace A] {μ : Measure A}
  [IsProbabilityMeasure μ] [NormedAddCommGroup F]

/-- The elementary probability-space L1/L2 comparison for a norm. -/
theorem integral_norm_le_sqrt_integral_sq_norm {f : A → F} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  apply Real.le_sqrt_of_sq_le
  have h := ProbabilityTheory.variance_nonneg (fun x => ‖f x‖) μ
  rw [ProbabilityTheory.variance_eq_sub hf.norm] at h
  exact sub_nonneg.mp h

/-- A coupling's quadratic displacement bounds the displacement of its barycentres. -/
theorem norm_integral_sub_le_sqrt [NormedSpace ℝ F] {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) :
    ‖(∫ x, X x ∂μ) - ∫ x, Z x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) := by
  rw [← integral_sub (hX.integrable (by norm_num)) (hZ.integrable (by norm_num))]
  exact (norm_integral_le_integral_norm _).trans
    (integral_norm_le_sqrt_integral_sq_norm (hX.sub hZ))

/-- Squared norms are `2R`-Lipschitz on a ball of radius `R`. -/
theorem abs_sq_norm_sub_le {R : ℝ} {x z : F} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |‖x‖ ^ 2 - ‖z‖ ^ 2| ≤ 2 * R * ‖x - z‖ := by
  have hid : ‖x‖ ^ 2 - ‖z‖ ^ 2 = (‖x‖ - ‖z‖) * (‖x‖ + ‖z‖) := by ring
  rw [hid, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    |‖x‖ - ‖z‖| * (‖x‖ + ‖z‖) ≤ ‖x - z‖ * (‖x‖ + ‖z‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x z)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖x - z‖ * (2 * R) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := by ring

/-- The quadratic concave potential used in the midpoint argument has controlled
expectation difference under a bounded coupling. -/
theorem quadratic_potential_expectation_sub_le {R : ℝ} (hR : 0 ≤ R)
    {X Z : A → F} (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hXR : ∀ᵐ x ∂μ, ‖X x‖ ≤ R) (hZR : ∀ᵐ x ∂μ, ‖Z x‖ ≤ R) :
    |(∫ x, R ^ 2 - ‖X x‖ ^ 2 ∂μ) - (∫ x, R ^ 2 - ‖Z x‖ ^ 2 ∂μ)| ≤
      2 * R * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) := by
  have hXi : Integrable (fun x => R ^ 2 - ‖X x‖ ^ 2) μ :=
    (integrable_const _).sub (hX.integrable_norm_pow (by norm_num))
  have hZi : Integrable (fun x => R ^ 2 - ‖Z x‖ ^ 2) μ :=
    (integrable_const _).sub (hZ.integrable_norm_pow (by norm_num))
  have hXZ : Integrable (fun x => ‖X x - Z x‖) μ :=
    (hX.sub hZ).norm.integrable (by norm_num)
  rw [← integral_sub hXi hZi, ← Real.norm_eq_abs]
  calc
    ‖∫ x, (R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2) ∂μ‖ ≤
        ∫ x, ‖(R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, 2 * R * ‖X x - Z x‖ ∂μ := by
      apply integral_mono_ae (hXi.sub hZi).norm (hXZ.const_mul (2 * R))
      filter_upwards [hXR, hZR] with x hx hz
      rw [Real.norm_eq_abs]
      have h := abs_sq_norm_sub_le hx hz
      change |(R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2)| ≤ _
      have heq : (R ^ 2 - ‖X x‖ ^ 2) - (R ^ 2 - ‖Z x‖ ^ 2) =
          -(‖X x‖ ^ 2 - ‖Z x‖ ^ 2) := by ring
      rw [heq, abs_neg]
      exact h
    _ = 2 * R * ∫ x, ‖X x - Z x‖ ∂μ := integral_const_mul _ _
    _ ≤ 2 * R * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_norm_le_sqrt_integral_sq_norm (hX.sub hZ))
        (by positivity)

/-- The expectation of a bounded random vector lies in the same norm ball. -/
theorem norm_integral_le_of_ae_norm_le [NormedSpace ℝ F] {X : A → F} {R : ℝ}
    (hX : Integrable X μ) (hXR : ∀ᵐ x ∂μ, ‖X x‖ ≤ R) :
    ‖∫ x, X x ∂μ‖ ≤ R := by
  calc
    ‖∫ x, X x ∂μ‖ ≤ ∫ x, ‖X x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : A, R ∂μ := integral_mono_ae hX.norm (integrable_const _) hXR
    _ = R := by simp

/-- The unnormalized cell-moment difference estimate in the stationary-site proof. -/
theorem weighted_barycentre_sub_le [NormedSpace ℝ F] {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) {R α β : ℝ}
    (hα : 0 ≤ α) (hZR : ∀ᵐ x ∂μ, ‖Z x‖ ≤ R) :
    ‖α • (∫ x, X x ∂μ) - β • (∫ x, Z x ∂μ)‖ ≤
      R * |α - β| + α * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) := by
  have hZb := norm_integral_le_of_ae_norm_le (hZ.integrable (by norm_num)) hZR
  have heq : α • (∫ x, X x ∂μ) - β • (∫ x, Z x ∂μ) =
      (α - β) • (∫ x, Z x ∂μ) + α • ((∫ x, X x ∂μ) - ∫ x, Z x ∂μ) := by module
  rw [heq]
  calc
    ‖(α - β) • (∫ x, Z x ∂μ) + α • ((∫ x, X x ∂μ) - ∫ x, Z x ∂μ)‖ ≤
        ‖(α - β) • (∫ x, Z x ∂μ)‖ + ‖α • ((∫ x, X x ∂μ) - ∫ x, Z x ∂μ)‖ :=
      norm_add_le _ _
    _ = |α - β| * ‖∫ x, Z x ∂μ‖ +
        α * ‖(∫ x, X x ∂μ) - ∫ x, Z x ∂μ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ |α - β| * R + α * Real.sqrt (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) :=
      add_le_add (mul_le_mul_of_nonneg_left hZb (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_integral_sub_le_sqrt hX hZ) hα)
    _ = _ := by ring

end Problem358.MomentCouplingBounds

namespace Problem358.MidpointEnergy
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The concave quadratic used in the midpoint argument. -/
def quadraticPotential (R : ℝ) (x : F) : ℝ := R ^ 2 - ‖x‖ ^ 2

lemma quadraticPotential_midpoint (R : ℝ) (x z : F) :
    quadraticPotential R ((1 / 2 : ℝ) • (x + z)) =
      (quadraticPotential R x + quadraticPotential R z) / 2 + ‖x - z‖ ^ 2 / 4 := by
  unfold quadraticPotential
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    mul_pow, norm_add_sq_real, norm_sub_sq_real]
  ring

omit [InnerProductSpace ℝ F] in
lemma quadraticPotential_nonneg {R : ℝ} {x : F} (hx : ‖x‖ ≤ R) :
    0 ≤ quadraticPotential R x :=
  sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hx 2)

omit [InnerProductSpace ℝ F] in
lemma quadraticPotential_le (R : ℝ) (x : F) :
    quadraticPotential R x ≤ R ^ 2 := sub_le_self _ (sq_nonneg _)

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]

/-- The integrated parallelogram identity gives the exact midpoint energy gain. -/
theorem integral_quadraticPotential_midpoint (R : ℝ) {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ) :
    (∫ x, quadraticPotential R ((1 / 2 : ℝ) • (X x + Z x)) ∂μ) =
      ((∫ x, quadraticPotential R (X x) ∂μ) +
        (∫ x, quadraticPotential R (Z x) ∂μ)) / 2 +
      (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) / 4 := by
  have hXi : Integrable (fun x => quadraticPotential R (X x)) μ :=
    (integrable_const _).sub (hX.integrable_norm_pow (by norm_num))
  have hZi : Integrable (fun x => quadraticPotential R (Z x)) μ :=
    (integrable_const _).sub (hZ.integrable_norm_pow (by norm_num))
  have hDi : Integrable (fun x => ‖X x - Z x‖ ^ 2) μ :=
    (hX.sub hZ).integrable_norm_pow (by norm_num)
  simp_rw [quadraticPotential_midpoint]
  have hAi : Integrable (fun x =>
      (quadraticPotential R (X x) + quadraticPotential R (Z x)) / 2) μ :=
    (hXi.add hZi).div_const 2
  rw [integral_add hAi (hDi.div_const 4),
    integral_div, integral_add hXi hZi, integral_div]

variable [MeasurableSpace F] [BorelSpace F]

omit [InnerProductSpace ℝ F] in
/-- A bounded-support measure integrates the nonnegative quadratic potential. -/
theorem integrable_quadraticPotential_of_ae_bound {ρ : Measure F} [IsFiniteMeasure ρ]
    {R : ℝ} (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) : Integrable (quadraticPotential R) ρ := by
  apply (integrable_const (R ^ 2)).mono'
  · exact (show Continuous (quadraticPotential R) by unfold quadraticPotential; fun_prop).aestronglyMeasurable
  · filter_upwards [hρ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (quadraticPotential_nonneg hx)]
    exact quadraticPotential_le R x

/-- Cellwise measure domination gives the midpoint energy inequality.
The geometric existence of the dominated coupling is an explicit hypothesis. -/
theorem scaled_midpoint_energy_le {ρ : Measure F} [IsFiniteMeasure ρ]
    {R γ : ℝ} (hγ : 0 ≤ γ) {X Z : A → F}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 μ)
    (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (hdom : ENNReal.ofReal γ •
      Measure.map (fun x => (1 / 2 : ℝ) • (X x + Z x)) μ ≤ ρ) :
    γ * (((∫ x, quadraticPotential R (X x) ∂μ) +
      (∫ x, quadraticPotential R (Z x) ∂μ)) / 2 +
      (∫ x, ‖X x - Z x‖ ^ 2 ∂μ) / 4) ≤
      ∫ x, quadraticPotential R x ∂ρ := by
  have hmid : MemLp (fun x => (1 / 2 : ℝ) • (X x + Z x)) 2 μ :=
    (hX.add hZ).const_smul (1 / 2 : ℝ)
  have hnonneg : 0 ≤ᵐ[ρ] quadraticPotential R := by
    filter_upwards [hρ] with x hx
    exact quadraticPotential_nonneg hx
  have h := integral_mono_measure hdom hnonneg (integrable_quadraticPotential_of_ae_bound hρ)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hγ, smul_eq_mul,
    integral_map hmid.aemeasurable
      (show AEStronglyMeasurable (quadraticPotential R) _ from
        (show Continuous (quadraticPotential R) by unfold quadraticPotential; fun_prop).aestronglyMeasurable),
    integral_quadraticPotential_midpoint R hX hZ] at h
  exact h

end Problem358.MidpointEnergy

end

end OAI
