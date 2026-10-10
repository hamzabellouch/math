import OAI.Analysis.Brenier.Argmax
import OAI.Analysis.Brenier.MaxCalculus
import OAI.Analysis.Brenier.Potential

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem358

variable {ι : Type*} [Fintype ι]

/-- Positive weighted mean-zero coordinates bounded above are bounded below too. -/
theorem normalized_intercept_lower_bound
    (m c : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hmean : ∑ i, m i * c i = 0) {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ i, c i ≤ R) (i : ι) : -R / m i ≤ c i := by
  classical
  have hnonneg : ∀ j, 0 ≤ m j * (R - c j) :=
    fun j => mul_nonneg (hm j).le (sub_nonneg.mpr (hupper j))
  have htotal : (∑ j, m j * (R - c j)) = R := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hmean]
    ring
  have hi : m i * (R - c i) ≤ R := by
    have hs := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    simpa only [htotal] using hs
  apply (div_le_iff₀ (hm i)).mpr
  have hprod : 0 ≤ m i * R := mul_nonneg (hm i).le hR
  nlinarith

/-- A continuous objective whose coordinate lower bounds control its sublevel sets
attains a minimum on the positive weighted normalization hyperplane. This is the
coercivity step in the prescribed-cell-mass variational argument. -/
theorem exists_minimum_on_normalized_intercepts
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F) (B : ℝ)
    (hlower : ∀ c : ι → ℝ, (∑ i, m i * c i) = 0 → ∀ i, c i - B ≤ F c) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧
      ∀ d : ι → ℝ, (∑ i, m i * d i) = 0 → F c ≤ F d := by
  classical
  let S : Set (ι → ℝ) := {c | (∑ i, m i * c i) = 0 ∧ F c ≤ F 0}
  let R : ℝ := max 0 (F 0 + B)
  have hR : 0 ≤ R := le_max_left _ _
  have hupper : ∀ c ∈ S, ∀ i, c i ≤ R := by
    intro c hc i
    have hci := hlower c hc.1 i
    have hFB : F 0 + B ≤ R := le_max_right _ _
    linarith [hc.2]
  have hclosed : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_le hF continuous_const
  have hbox : S ⊆ Set.Icc (fun i => -R / m i) (fun _ => R) := by
    intro c hc
    exact ⟨fun i => normalized_intercept_lower_bound m c hm hsum hc.1 hR
      (hupper c hc) i, hupper c hc⟩
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hbox
  have hzero : (0 : ι → ℝ) ∈ S := by simp [S]
  obtain ⟨c, hc, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hF.continuousOn
  refine ⟨c, hc.1, ?_⟩
  intro d hd
  by_cases hle : F d ≤ F 0
  · exact hmin ⟨hd, hle⟩
  · exact hc.2.trans (le_of_not_ge hle)

/-- The mass-residual gradient vanishes if it annihilates the normalization
hyperplane and its unweighted coordinate sum is zero. -/
theorem normalized_stationary_gradient_eq_zero
    (m g : ι → ℝ) (hsum : ∑ i, m i = 1) (hgsum : ∑ i, g i = 0)
    (hstationary : ∀ q : ι → ℝ, (∑ i, m i * q i) = 0 →
      (∑ i, g i * q i) = 0) : g = 0 := by
  classical
  funext i
  let q : ι → ℝ := fun j => (if j = i then 1 else 0) - m i
  have hq : (∑ j, m j * q j) = 0 := by
    simp [q, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  have hg := hstationary q hq
  simpa [q, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hgsum] using hg

/-- First-order optimality on the weighted normalization hyperplane, in a
form directly applicable after differentiating the integral of a finite maximum. -/
theorem gradient_eq_zero_of_normalized_minimum
    (m g c : ι → ℝ) (hsum : ∑ i, m i = 1) (hgsum : ∑ i, g i = 0)
    (hc : ∑ i, m i * c i = 0) (F : (ι → ℝ) → ℝ)
    (hmin : ∀ d : ι → ℝ, (∑ i, m i * d i) = 0 → F c ≤ F d)
    (hderiv : ∀ q : ι → ℝ,
      HasDerivAt (fun t : ℝ => F (c + t • q)) (∑ i, g i * q i) 0) :
    g = 0 := by
  apply normalized_stationary_gradient_eq_zero m g hsum hgsum
  intro q hq
  have hline : ∀ t : ℝ, (∑ i, m i * (c + t • q) i) = 0 := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
    rw [Finset.sum_add_distrib, hc]
    simp_rw [← mul_assoc, mul_comm (m _) t, mul_assoc]
    rw [← Finset.mul_sum, hq]
    ring
  have hlocal : IsLocalMin (fun t : ℝ => F (c + t • q)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using hmin (c + t • q) (hline t)
  exact hlocal.hasDerivAt_eq_zero (hderiv q)

/-- Abstract prescribed-mass existence from a coercive potential objective and
its cell-mass directional derivative. Geometry is isolated in `hlower`, `hMsum`,
and `hderiv`; no existence or stationarity assumption is hidden in the conclusion. -/
theorem exists_prescribed_masses_of_variational_objective
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F) (B : ℝ)
    (hlower : ∀ c : ι → ℝ, (∑ i, m i * c i) = 0 → ∀ i, c i - B ≤ F c)
    (M : (ι → ℝ) → ι → ℝ) (hMsum : ∀ c, ∑ i, M c i = 1)
    (hderiv : ∀ c q : ι → ℝ,
      HasDerivAt (fun t : ℝ => F (c + t • q))
        (∑ i, (M c i - m i) * q i) 0) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧ M c = m := by
  classical
  obtain ⟨c, hc, hmin⟩ := exists_minimum_on_normalized_intercepts m hm hsum F hF B hlower
  refine ⟨c, hc, ?_⟩
  have hresidual : (fun i => M c i - m i) = 0 := by
    apply gradient_eq_zero_of_normalized_minimum m _ c hsum _ hc F hmin (hderiv c)
    rw [Finset.sum_sub_distrib, hMsum c, hsum]
    ring
  funext i
  have hi := congrFun hresidual i
  exact sub_eq_zero.mp hi

end Problem358

end

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [Fintype ι] in
/-- Every active affine branch has an intercept within twice the source-site product
radius of every other active branch. No lower bound on the cell masses is needed. -/
theorem abs_intercept_sub_le_of_active
    (y : ι → V) (c : ι → ℝ) {R L : ℝ} (hL : 0 ≤ L)
    (hy : ∀ i, ‖y i‖ ≤ L)
    (hactive : ∀ i, ∃ x : V, ‖x‖ ≤ R ∧
      ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i) :
    ∀ i j, |c i - c j| ≤ 2 * R * L := by
  have hupper : ∀ i j, c i - c j ≤ 2 * R * L := by
    intro i j
    obtain ⟨x, hx, hmax⟩ := hactive j
    have hb : ∀ k, |⟪x, y k⟫| ≤ R * L := by
      intro k
      exact (abs_real_inner_le_norm x (y k)).trans
        ((mul_le_mul_of_nonneg_left (hy k) (norm_nonneg x)).trans
          (mul_le_mul_of_nonneg_right hx hL))
    have hi := (abs_le.mp (hb i)).1
    have hj := (abs_le.mp (hb j)).2
    linarith [hmax i]
  intro i j
  exact abs_le.mpr ⟨by linarith [hupper j i], hupper i j⟩

/-- Weighted normalization turns a bound on pairwise intercept differences into a
bound on each intercept, without a reciprocal minimum-weight factor. -/
theorem abs_intercept_le_of_normalized
    (c m : ι → ℝ) {B : ℝ} (hm : ∀ i, 0 ≤ m i)
    (hsum : ∑ i, m i = 1) (hnormal : ∑ i, m i * c i = 0)
    (hspread : ∀ i j, |c i - c j| ≤ B) : ∀ i, |c i| ≤ B := by
  intro i
  have heq : ∑ j, m j * (c i - c j) = c i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hsum, one_mul, hnormal, sub_zero]
  calc
    |c i| = |∑ j, m j * (c i - c j)| := congrArg abs heq.symm
    _ ≤ ∑ j, |m j * (c i - c j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, m j * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hm j)]
      exact mul_le_mul_of_nonneg_left (hspread i j) (hm j)
    _ = B := by rw [← Finset.sum_mul, hsum, one_mul]

omit [Fintype ι] in
/-- Positive source mass in each maximizing cell gives the pointwise activity
needed for the uniform intercept bound, even when maximality is only almost everywhere. -/
theorem abs_intercept_sub_le_of_positive_cells
    [MeasurableSpace V] (ρ : Measure V) (y : ι → V) (c : ι → ℝ)
    (k : V → ι) {R L : ℝ} (hL : 0 ≤ L) (hy : ∀ i, ‖y i‖ ≤ L)
    (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (hmax : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hmass : ∀ i, 0 < ρ.real {x | k x = i}) :
    ∀ i j, |c i - c j| ≤ 2 * R * L := by
  apply abs_intercept_sub_le_of_active y c hL hy
  intro i
  by_contra hex
  have hne : ∀ᵐ x ∂ρ, k x ≠ i := by
    filter_upwards [hR, hmax] with x hx hmx
    intro hki
    exact hex ⟨x, hx, by simpa only [hki] using hmx⟩
  have hz : ρ {x | k x = i} = 0 := by
    simpa only [not_not] using ae_iff.mp hne
  have hi := hmass i
  simp only [Measure.real, hz, ENNReal.toReal_zero] at hi
  exact lt_irrefl _ hi

/-- A mass-normalized intercept solving the positive prescribed-cell problem lies
in a fixed compact box determined only by the source and site radii. -/
theorem abs_intercept_le_of_prescribed_cells
    [MeasurableSpace V] (ρ : Measure V) (y : ι → V) (c m : ι → ℝ)
    (k : V → ι) {R L : ℝ} (hL : 0 ≤ L) (hy : ∀ i, ‖y i‖ ≤ L)
    (hR : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (hmax : ∀ᵐ x ∂ρ, ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x))
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (hnormal : ∑ i, m i * c i = 0)
    (hmass : ∀ i, ρ.real {x | k x = i} = m i) :
    ∀ i, |c i| ≤ 2 * R * L := by
  apply abs_intercept_le_of_normalized c m (fun i => (hm i).le) hsum hnormal
  apply abs_intercept_sub_le_of_positive_cells ρ y c k hL hy hR hmax
  intro i
  rw [hmass i]
  exact hm i

end Problem358.MaxPotential

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
variable (ρ : Measure V) [IsProbabilityMeasure ρ]

/-- The finite-target variational objective as a function of affine intercepts. -/
def objective (y : ι → V) (m c : ι → ℝ) : ℝ :=
  (∫ x, potential y c x ∂ρ) - ∑ i, m i * c i

theorem continuous_objective (y : ι → V) (m : ι → ℝ) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) :
    Continuous (objective ρ y m) := by
  apply Continuous.sub
  · exact (lipschitzWith_integral_potential ρ y
      (fun c => integrable_potential ρ y c L hy hρ)).continuous
  · fun_prop

/-- The actual finite-potential objective attains its normalized minimum. -/
theorem exists_minimum_objective (y : ι → V) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧
      ∀ b : ι → ℝ, (∑ i, m i * b i) = 0 →
        objective ρ y m c ≤ objective ρ y m b := by
  apply exists_minimum_on_normalized_intercepts m hm hsum (objective ρ y m)
    (continuous_objective ρ y m L hy hρ) ((L : ℝ) * ∫ x, ‖x‖ ∂ρ)
  intro c hc i
  have hi := intercept_le_integral_potential ρ y c L hy hρ i
  simp only [objective, hc, sub_zero]
  linarith

/-- A cell-mass derivative formula suffices to solve the prescribed mass problem.
The only analytic input beyond integrability is the explicit directional derivative
of the integral of the maximum; normalization and minimization are proved here. -/
theorem exists_prescribed_masses (y : ι → V) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (M : (ι → ℝ) → ι → ℝ) (hMsum : ∀ c, ∑ i, M c i = 1)
    (hderiv : ∀ c q : ι → ℝ,
      HasDerivAt (fun t : ℝ => ∫ x, potential y (c + t • q) x ∂ρ)
        (∑ i, M c i * q i) 0) :
    ∃ c : ι → ℝ, (∑ i, m i * c i) = 0 ∧ M c = m := by
  refine exists_prescribed_masses_of_variational_objective m hm hsum
    (objective ρ y m) (continuous_objective ρ y m L hy hρ)
    ((L : ℝ) * ∫ x, ‖x‖ ∂ρ) ?_ M hMsum ?_
  · intro c hc i
    have hi := intercept_le_integral_potential ρ y c L hy hρ i
    simp only [objective, hc, sub_zero]
    linarith
  · intro c q
    have hlin : HasDerivAt (fun t : ℝ => ∑ i, m i * (c + t • q) i)
        (∑ i, m i * q i) 0 := by
      have heq : (fun t : ℝ => ∑ i, m i * (c + t • q) i) =
          (fun t => (∑ i, m i * c i) + t * ∑ i, m i * q i) := by
        funext t
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [heq]
      simpa only [zero_add, one_mul, Pi.add_apply, id_eq] using!
        (hasDerivAt_const 0 (∑ i, m i * c i)).add
          ((hasDerivAt_id 0).mul_const (∑ i, m i * q i))
    simpa only [objective, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using!
      (hderiv c q).sub hlin

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]

/-- A normalized potential minimizer has an explicit uniform coordinate upper bound. -/
theorem minimizer_upper_bound (ρ : Measure V) [IsProbabilityMeasure ρ]
    (y : ι → V) (c : ι → ℝ) (L : NNReal) (hy : ∀ i, ‖y i‖ ≤ L)
    (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (hmin : (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y 0 x ∂ρ) :
    ∀ i, c i ≤ 2 * (L : ℝ) * ∫ x, ‖x‖ ∂ρ := by
  have hzero : (∫ x, potential y 0 x ∂ρ) ≤ (L : ℝ) * ∫ x, ‖x‖ ∂ρ := by
    have hpoint : ∀ x : V, potential y 0 x ≤ (L : ℝ) * ‖x‖ := by
      intro x
      have hn := norm_potential_le y 0 L hy x
      have hle : potential y 0 x ≤ ‖potential y 0 x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (potential y 0 x)
      simpa only [norm_zero, add_zero] using hle.trans hn
    have hi := integral_mono (integrable_potential ρ y 0 L hy hρ)
      (hρ.const_mul (L : ℝ)) hpoint
    simpa only [integral_const_mul] using hi
  intro i
  have hc := intercept_le_integral_potential ρ y c L hy hρ i
  linarith

/-- The positive weighted normalization turns the preceding upper bound into a compact box. -/
theorem minimizer_mem_box (ρ : Measure V) [IsProbabilityMeasure ρ]
    (y : ι → V) (c m : ι → ℝ) (L : NNReal) (hy : ∀ i, ‖y i‖ ≤ L)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (hc : ∑ i, m i * c i = 0)
    (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (hmin : (∫ x, potential y c x ∂ρ) ≤ ∫ x, potential y 0 x ∂ρ) :
    c ∈ Set.Icc (fun i => -(2 * (L : ℝ) * ∫ x, ‖x‖ ∂ρ) / m i)
      (fun _ => 2 * (L : ℝ) * ∫ x, ‖x‖ ∂ρ) := by
  have hupper := minimizer_upper_bound ρ y c L hy hρ hmin
  refine ⟨?_, hupper⟩
  intro i
  apply normalized_intercept_lower_bound m c hm hsum hc _ hupper i
  positivity

end Problem358.MaxPotential

end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace Problem358.MaxPotential

variable {ι V : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (ρ : Measure V) [IsProbabilityMeasure ρ]

/-- Prescribed finite cell masses, with null affine ties as the only geometric input.
The maximizing selector is globally measurable, including on exceptional tie sets. -/
theorem exists_prescribed_cell_masses (y : ι → V) (m : ι → ℝ)
    (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) (L : NNReal)
    (hy : ∀ i, ‖y i‖ ≤ L) (hρ : Integrable (fun x : V => ‖x‖) ρ)
    (hties : ∀ c : ι → ℝ, ∀ᵐ x ∂ρ, ∀ i j, i ≠ j →
      ⟪x, y i⟫ + c i ≠ ⟪x, y j⟫ + c j) :
    ∃ (c : ι → ℝ) (k : V → ι),
      (∑ i, m i * c i) = 0 ∧ Measurable k ∧
      (∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) ∧
      (∀ i, ρ.real {x | k x = i} = m i) := by
  classical
  have hchoices : ∀ c : ι → ℝ, ∃ k : V → ι, Measurable k ∧
      ∀ x j, ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x) := by
    intro c
    obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax
      (fun i (x : V) => ⟪x, y i⟫ + c i)
      (fun i => ((continuous_id.inner continuous_const).add continuous_const).measurable)
    exact ⟨k, hk, hmax⟩
  choose k hk hmax using hchoices
  have hfib : ∀ c i, MeasurableSet {x | k c x = i} := by
    intro c i
    exact (hk c) (measurableSet_singleton i)
  let M : (ι → ℝ) → ι → ℝ := fun c i => ρ.real {x | k c x = i}
  have hMsum : ∀ c, ∑ i, M c i = 1 := by
    intro c
    have hint := FiniteMaxDerivative.integral_finite_selection (μ := ρ)
      (fun _ : ι => (1 : ℝ)) (k c) (hfib c)
    simpa [M] using hint.symm
  have hderiv : ∀ c q : ι → ℝ,
      HasDerivAt (fun t : ℝ => ∫ x, potential y (c + t • q) x ∂ρ)
        (∑ i, M c i * q i) 0 := by
    intro c q
    have hstrict : ∀ᵐ x ∂ρ, ∀ j, j ≠ k c x →
        ⟪x, y j⟫ + c j < ⟪x, y (k c x)⟫ + c (k c x) := by
      filter_upwards [hties c] with x hx
      intro j hj
      exact lt_of_le_of_ne (hmax c x j) (hx j (k c x) hj)
    have hq : Measurable q := Measurable.of_discrete
    have hi := FiniteMaxDerivative.hasDerivAt_integral_finiteMax
      (μ := ρ) (fun i (x : V) => ⟪x, y i⟫ + c i) q (k c)
      (fun i => ((continuous_id.inner continuous_const).add continuous_const).aestronglyMeasurable)
      (integrable_potential ρ y c L hy hρ) hstrict
      (hq.comp (hk c)).aestronglyMeasurable
    rw [FiniteMaxDerivative.integral_finite_selection q (k c) (hfib c)] at hi
    simpa only [potential, FiniteMaxDerivative.finiteMax, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, add_assoc, M] using! hi
  obtain ⟨c, hc, hMc⟩ := exists_prescribed_masses ρ y m hm hsum L hy hρ M hMsum hderiv
  exact ⟨c, k c, hc, hk c, hmax c, fun i => congrFun hMc i⟩

end Problem358.MaxPotential

end

end OAI
