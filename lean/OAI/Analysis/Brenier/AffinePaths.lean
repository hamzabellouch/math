import OAI.Analysis.Brenier.AffineCertificate
import OAI.Analysis.Brenier.Argmax
import OAI.Analysis.Brenier.PotentialTime

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace NNReal BigOperators

namespace Problem358

/-- Quantitative time stability for a genuine finite affine maximum with fixed cell
masses.  Null ties, time regularity, square integrability, and the fundamental theorem
are derived from the stated coefficient data rather than assumed for the potential. -/
theorem finite_affine_path_L2_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {a b w κ : ℝ} {R A B : ℝ≥0}
    (hab : a < b) (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hv : ∀ i, Measurable (v i)) (hr : ∀ i, Measurable (r i))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Icc a b → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Icc a b → HasDerivAt (c i) (r i q) q)
    (hvBound : ∀ i q, q ∈ Icc a b → ‖v i q‖ ≤ A)
    (hrBound : ∀ i q, q ∈ Icc a b → ‖r i q‖ ≤ B)
    (hinj : ∀ᵐ q ∂volume.restrict (Ioc a b), Function.Injective (fun i => y i q))
    (hactive : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K), ∀ j,
      ⟪p.2, y j p.1⟫_ℝ + c j p.1 ≤
        ⟪p.2, y (active p) p.1⟫_ℝ + c (active p) p.1)
    (hm : ∀ q ∈ Ioc a b, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hvEnergy : ∀ q ∈ Ioc a b, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioc a b, (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    Real.sqrt (∫ x,
      (FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫_ℝ + c i q) b -
        FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫_ℝ + c i q) a) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b - a) := by
  let f : ι → ℝ × E d → ℝ := fun i p => ⟪p.2, y i p.1⟫_ℝ + c i p.1
  let g : ι → ℝ × E d → ℝ := fun i p => ⟪p.2, v i p.1⟫_ℝ + r i p.1
  have hf (i : ι) : Measurable (f i) :=
    (measurable_snd.inner (hy i |>.comp measurable_fst)).add
      (hc i |>.comp measurable_fst)
  have hg (i : ι) : Measurable (g i) :=
    (measurable_snd.inner (hv i |>.comp measurable_fst)).add
      (hr i |>.comp measurable_fst)
  have hd (i : ι) (q : ℝ) (hq : q ∈ Icc a b) (x : E d) :
      HasDerivAt (fun t => f i (t, x)) (g i (q, x)) q := by
    convert ((hasDerivAt_const q x).inner ℝ (hdy i q hq)).add (hdc i q hq) using 1
    simp only [inner_zero_left, add_zero]
    rfl
  have hbound (i : ι) (q : ℝ) (hq : q ∈ Icc a b) (x : E d) (hx : ‖x‖ ≤ R) :
      ‖g i (q, x)‖ ≤ (R : ℝ) * A + B := by
    calc
      ‖g i (q, x)‖ ≤ ‖⟪x, v i q⟫_ℝ‖ + ‖r i q‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖v i q‖ + ‖r i q‖ := add_le_add (norm_inner_le_norm _ _) le_rfl
      _ ≤ (R : ℝ) * A + B := by
        gcongr
        · exact hvBound i q hq
        · exact hrBound i q hq
  have hLip : ∀ᵐ x ∂uniformMeasure K, ∀ i,
      LipschitzOnWith (R * A + B) (fun q => f i (q, x)) (Icc a b) := by
    filter_upwards [hxR] with x hx
    intro i
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun q hq => (hd i q hq x).hasDerivWithinAt)
    intro q hq
    change ‖g i (q, x)‖ ≤ (↑(R * A + B) : ℝ)
    simpa only [NNReal.coe_add, NNReal.coe_mul] using hbound i q hq x hx
  have htime : ∀ᵐ p : ℝ × E d ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      p.1 ∈ Ioc a b :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hspace : ∀ᵐ p : ℝ × E d ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      ‖p.2‖ ≤ R := Measure.quasiMeasurePreserving_snd.ae hxR
  have hderiv : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K), ∀ i,
      HasDerivAt (fun q => f i (q, p.2)) (g i p) p.1 := by
    filter_upwards [htime] with p hp
    exact fun i => hd i p.1 (Ioc_subset_Icc_self hp) p.2
  have hstrict : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K), ∀ j,
      j ≠ active p → f j p < f (active p) p :=
    ae_prod_strict_active_affine K (fun q x => active (q, x)) hy hc hinj hactive
  have hfullbound : ∀ᵐ p ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      ‖g (active p) p‖ ≤ (R : ℝ) * A + B := by
    filter_upwards [htime, hspace] with p hp hx
    exact hbound (active p) p.1 (Ioc_subset_Icc_self hp) p.2 hx
  have hspeed : ∀ᵐ q ∂volume.restrict (Ioc a b),
      (∫ x, g (active (q, x)) (q, x) ^ 2 ∂uniformMeasure K) ≤
        (Real.sqrt (2 * (1 + κ)) * R * w) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    have hsel : Measurable (fun x => active (q, x)) :=
      hactiveMeas.comp (measurable_const.prodMk measurable_id)
    have hh := PotentialSpeed.integral_affine_speed_sq_le_of_energy
      hsel (fun i => v i q) (fun i => r i q) m hxR (hm q hq)
      (hvEnergy q hq) (hrEnergy q hq)
    have hsquare : (Real.sqrt (2 * (1 + κ)) * R * w) ^ 2 =
        2 * (1 + κ) * (R : ℝ) ^ 2 * w ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsquare]
    exact hh
  exact FiniteMaxDerivative.finite_max_path_L2_bound f g active hab (by positivity)
    hf hg (fun i => hactiveMeas (measurableSet_singleton i)) hLip hderiv hstrict
    hfullbound hspeed

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators RealInnerProductSpace

namespace Problem358.FiniteAffine

variable {I F : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Uniform comparison of finite affine maxima, without any uniqueness of
active indices or separation of the sites. -/
theorem abs_potential_sub_le_coefficients (y z : I → F) (c b : I → ℝ)
    {R : ℝ} (hR : 0 ≤ R) {x : F} (hx : ‖x‖ ≤ R) :
    |potential y c x - potential z b x| ≤
      R * ∑ i, ‖y i - z i‖ + ∑ i, |c i - b i| := by
  classical
  let e := R * ∑ i, ‖y i - z i‖ + ∑ i, |c i - b i|
  have hscore (i : I) :
      |(⟪x, y i⟫ + c i) - (⟪x, z i⟫ + b i)| ≤ e := by
    have hy : ‖y i - z i‖ ≤ ∑ j, ‖y j - z j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (y j - z j)) (Finset.mem_univ i)
    have hc : |c i - b i| ≤ ∑ j, |c j - b j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c j - b j)) (Finset.mem_univ i)
    calc
      _ = |⟪x, y i - z i⟫ + (c i - b i)| := by
        congr 1
        rw [inner_sub_right]
        ring
      _ ≤ |⟪x, y i - z i⟫| + |c i - b i| := abs_add_le _ _
      _ ≤ R * (∑ j, ‖y j - z j‖) + ∑ j, |c j - b j| := by
        apply add_le_add _ hc
        exact (abs_real_inner_le_norm _ _).trans
          ((mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hy hR))
  have hr : potential y c x ≤ potential z b x + e := by
    apply potential_le_of_affine_le
    intro i
    have hi := affine_le_potential z b x i
    have hs := (abs_le.mp (hscore i)).2
    linarith
  have hl : potential z b x ≤ potential y c x + e := by
    apply potential_le_of_affine_le
    intro i
    have hi := affine_le_potential y c x i
    have hs := (abs_le.mp (hscore i)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable [MeasurableSpace F] (μ : Measure F) [IsFiniteMeasure μ]

/-- Coefficient convergence gives scalar L² convergence on every finite
bounded source.  Arbitrary filters are allowed, including both endpoint
filters; repeated limiting sites cause no issue. -/
theorem tendsto_integral_potential_sub_sq
    {A : Type*} {l : Filter A} {y : A → I → F} {c : A → I → ℝ}
    {z : I → F} {b : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (z i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (b i))) :
    Tendsto (fun t => ∫ x, (potential (y t) (c t) x - potential z b x) ^ 2 ∂μ)
      l (𝓝 0) := by
  classical
  let e : A → ℝ := fun t => R * ∑ i, ‖y t i - z i‖ + ∑ i, |c t i - b i|
  have hyl (i : I) : Tendsto (fun t => ‖y t i - z i‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hy i).sub (tendsto_const_nhds (x := z i))).norm
  have hcl (i : I) : Tendsto (fun t => |c t i - b i|) l (𝓝 0) := by
    simpa only [sub_self, abs_zero] using ((hc i).sub (tendsto_const_nhds (x := b i))).abs
  have hel : Tendsto e l (𝓝 0) := by
    simpa [e] using ((tendsto_finsetSum Finset.univ (fun i _ => hyl i)).const_mul R).add
      (tendsto_finsetSum Finset.univ (fun i _ => hcl i))
  have hbound (t : A) :
      (∫ x, (potential (y t) (c t) x - potential z b x) ^ 2 ∂μ) ≤
        μ.real Set.univ * e t ^ 2 := by
    have hb : ∀ᵐ x ∂μ,
        (potential (y t) (c t) x - potential z b x) ^ 2 ≤ e t ^ 2 := by
      filter_upwards [hx] with x hx
      have he := abs_potential_sub_le_coefficients (y t) z (c t) b hR hx
      have he0 : 0 ≤ e t := by dsimp [e]; positivity
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he0).mpr he
    have hi := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => sq_nonneg
        (potential (y t) (c t) x - potential z b x)) (integrable_const (e t ^ 2)) hb
    simpa only [integral_const, smul_eq_mul] using hi
  apply squeeze_zero (fun t => integral_nonneg fun x => sq_nonneg _) hbound
  simpa using (hel.pow 2).const_mul (μ.real Set.univ)

/-- Norm-form endpoint convergence of the finite affine potentials. -/
theorem tendsto_sqrt_integral_potential_sub_sq
    {A : Type*} {l : Filter A} {y : A → I → F} {c : A → I → ℝ}
    {z : I → F} {b : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (z i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (b i))) :
    Tendsto (fun t => Real.sqrt
      (∫ x, (potential (y t) (c t) x - potential z b x) ^ 2 ∂μ)) l (𝓝 0) := by
  simpa only [Real.sqrt_zero] using
    (tendsto_integral_potential_sub_sq μ hR hx hy hc).sqrt

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [IsFiniteMeasure μ] in
/-- The scalar square-root energy is the genuine L² metric. -/
theorem sqrt_integral_sub_sq_eq_dist {f g : F → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, (f x - g x) ^ 2 ∂μ) =
      dist (hf.toLp f) (hg.toLp g) := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (hf.sub hg).aestronglyMeasurable]
  simp [Real.sqrt_eq_rpow, Real.norm_eq_abs]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [IsFiniteMeasure μ] in
/-- L² convergence of both endpoints preserves their scalar L² distance. -/
theorem tendsto_sqrt_integral_pair_sub_sq
    {A : Type*} {l : Filter A} {u v : A → F → ℝ} {u₀ v₀ : F → ℝ}
    (hu : ∀ t, MemLp (u t) 2 μ) (hv : ∀ t, MemLp (v t) 2 μ)
    (hu₀ : MemLp u₀ 2 μ) (hv₀ : MemLp v₀ 2 μ)
    (hul : Tendsto (fun t => Real.sqrt (∫ x, (u t x - u₀ x) ^ 2 ∂μ)) l (𝓝 0))
    (hvl : Tendsto (fun t => Real.sqrt (∫ x, (v t x - v₀ x) ^ 2 ∂μ)) l (𝓝 0)) :
    Tendsto (fun t => Real.sqrt (∫ x, (u t x - v t x) ^ 2 ∂μ))
      l (𝓝 (Real.sqrt (∫ x, (u₀ x - v₀ x) ^ 2 ∂μ))) := by
  have huLp : Tendsto (fun t => (hu t).toLp (u t)) l (𝓝 (hu₀.toLp u₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← sqrt_integral_sub_sq_eq_dist] using hul
  have hvLp : Tendsto (fun t => (hv t).toLp (v t)) l (𝓝 (hv₀.toLp v₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [← sqrt_integral_sub_sq_eq_dist] using hvl
  simpa only [← sqrt_integral_sub_sq_eq_dist] using huLp.dist hvLp

variable [BorelSpace F]

/-- Finite affine potentials are in L² on every finite bounded source. -/
theorem memLp_potential_of_ae_norm_le (y : I → F) (c : I → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R) :
    MemLp (potential y c) 2 μ := by
  apply MemLp.of_bound (continuous_potential y c).aestronglyMeasurable
    (R * ∑ i, ‖y i‖ + ∑ i, |c i|)
  filter_upwards [hx] with x hx
  have h := abs_potential_sub_le_coefficients y (fun _ => 0) c (fun _ => 0) hR hx
  simpa [Real.norm_eq_abs, potential] using h

/-- Endpoint coefficients alone suffice for continuity of the distance
between two finite affine potentials. -/
theorem tendsto_sqrt_integral_potential_pair_sub_sq
    {A : Type*} {l : Filter A}
    {y z : A → I → F} {c b : A → I → ℝ}
    {y₀ z₀ : I → F} {c₀ b₀ : I → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hx : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (hy : ∀ i, Tendsto (fun t => y t i) l (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun t => c t i) l (𝓝 (c₀ i)))
    (hz : ∀ i, Tendsto (fun t => z t i) l (𝓝 (z₀ i)))
    (hb : ∀ i, Tendsto (fun t => b t i) l (𝓝 (b₀ i))) :
    Tendsto (fun t => Real.sqrt
      (∫ x, (potential (y t) (c t) x - potential (z t) (b t) x) ^ 2 ∂μ))
      l (𝓝 (Real.sqrt (∫ x, (potential y₀ c₀ x - potential z₀ b₀ x) ^ 2 ∂μ))) := by
  exact tendsto_sqrt_integral_pair_sub_sq μ
    (fun t => memLp_potential_of_ae_norm_le μ (y t) (c t) hR hx)
    (fun t => memLp_potential_of_ae_norm_le μ (z t) (b t) hR hx)
    (memLp_potential_of_ae_norm_le μ y₀ c₀ hR hx)
    (memLp_potential_of_ae_norm_le μ z₀ b₀ hR hx)
    (tendsto_sqrt_integral_potential_sub_sq μ hR hx hy hc)
    (tendsto_sqrt_integral_potential_sub_sq μ hR hx hz hb)

end Problem358.FiniteAffine

end

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace NNReal BigOperators

namespace Problem358

/-- Positive finite weights turn a uniform weighted square bound into a uniform
coordinate norm bound. The bound is used only for local time regularity; it does
not enter the final potential stability constant. -/
theorem exists_uniform_norm_bound_of_weighted_energy
    {ι P F : Type*} [Fintype ι] [NormedAddCommGroup F]
    (m : ι → ℝ) (f : ι → P → F) (S : Set P) {C : ℝ}
    (hm : ∀ i, 0 < m i)
    (henergy : ∀ q ∈ S, (∑ i, m i * ‖f i q‖ ^ 2) ≤ C) :
    ∃ A : ℝ≥0, ∀ i q, q ∈ S → ‖f i q‖ ≤ A := by
  classical
  let A : ℝ≥0 := ⟨∑ i, Real.sqrt (C / m i),
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _⟩
  refine ⟨A, ?_⟩
  intro i q hq
  have hi : m i * ‖f i q‖ ^ 2 ≤ C :=
    (Finset.single_le_sum (fun j _ => mul_nonneg (hm j).le (sq_nonneg ‖f j q‖))
      (Finset.mem_univ i)).trans (henergy q hq)
  have hs : ‖f i q‖ ^ 2 ≤ C / m i := by
    apply (le_div_iff₀ (hm i)).mpr
    simpa only [mul_comm] using hi
  calc
    ‖f i q‖ = Real.sqrt (‖f i q‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C / m i) := Real.sqrt_le_sqrt hs
    _ ≤ A := Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (C / m j))
      (Finset.mem_univ i)

/-- On a specified parameter set, pointwise prescribed-mass witnesses suffice for
one globally measurable affine maximizing selector. No separation or mass
condition is imposed outside that set. -/
theorem ParameterizedArgmax.exists_joint_measurable_affine_argmax_with_masses_on
    {P ι : Type*} [MeasurableSpace P] [MeasurableSpace ι]
    [Fintype ι] [Nonempty ι] {d : ℕ} (K : Set (E d)) (S : Set P)
    (y : P → ι → E d) (c m : P → ι → ℝ)
    (hy : ∀ i, Measurable (fun p => y p i))
    (hc : ∀ i, Measurable (fun p => c p i))
    (hinj : ∀ p ∈ S, Function.Injective (y p))
    (hex : ∀ p ∈ S, ∃ k : E d → ι,
      (∀ᵐ x ∂uniformMeasure K, ∀ i,
        ⟪x, y p i⟫_ℝ + c p i ≤ ⟪x, y p (k x)⟫_ℝ + c p (k x)) ∧
      ∀ i, (uniformMeasure K).real {x | k x = i} = m p i) :
    ∃ k : P × E d → ι, Measurable k ∧
      (∀ p x i, ⟪x, y p i⟫_ℝ + c p i ≤
        ⟪x, y p (k (p, x))⟫_ℝ + c p (k (p, x))) ∧
      ∀ p ∈ S, ∀ i, (uniformMeasure K).real {x | k (p, x) = i} = m p i := by
  have hf (i : ι) : Measurable (fun p : P × E d =>
      ⟪p.2, y p.1 i⟫_ℝ + c p.1 i) :=
    (measurable_snd.inner ((hy i).comp measurable_fst)).add
      ((hc i).comp measurable_fst)
  obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax _ hf
  refine ⟨k, hk, fun p x i => hmax (p, x) i, ?_⟩
  intro p hp i
  obtain ⟨l, hl, hmass⟩ := hex p hp
  have hsep : ∀ᵐ x ∂uniformMeasure K,
      Function.Injective (fun i => ⟪x, y p i⟫_ℝ + c p i) := by
    filter_upwards [uniform_ae_affine_tie_implies_slopes_eq K (y p) (c p)] with x hx
    intro i j hij
    exact hinj p hp (hx i j hij)
  have heq := ParameterizedArgmax.ae_eq_of_maximizers (uniformMeasure K)
    (fun i x => ⟪x, y p i⟫_ℝ + c p i) (fun x => k (p, x)) l hsep
    (Filter.Eventually.of_forall fun x => hmax (p, x)) hl
  have hsets : {x | k (p, x) = i} =ᵐ[uniformMeasure K] {x | l x = i} := by
    filter_upwards [heq] with x hx
    exact congrArg (fun z => z = i) hx
  exact (congrArg ENNReal.toReal (measure_congr hsets)).trans (hmass i)

/-- Interior finite-potential stability directly from positive fixed masses and
weighted energies. Joint selection and auxiliary coordinate derivative bounds
are consequences, not extra hypotheses. In particular, sites may collide outside
the integration interval. -/
theorem finite_affine_path_L2_bound_of_positive_cell_masses
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ) (m : ι → ℝ)
    {a b w κ : ℝ} {R : ℝ≥0}
    (hab : a < b) (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hm : ∀ i, 0 < m i)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Measurable (y i)) (hc : ∀ i, Measurable (c i))
    (hv : ∀ i, Measurable (v i)) (hr : ∀ i, Measurable (r i))
    (hdy : ∀ i q, q ∈ Icc a b → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Icc a b → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioc a b, Function.Injective (fun i => y i q))
    (hcell : ∀ q ∈ Ioc a b, ∃ k : E d → ι,
      (∀ᵐ x ∂uniformMeasure K, ∀ i,
        ⟪x, y i q⟫_ℝ + c i q ≤ ⟪x, y (k x) q⟫_ℝ + c (k x) q) ∧
      ∀ i, (uniformMeasure K).real {x | k x = i} = m i)
    (hvEnergy : ∀ q ∈ Icc a b, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Icc a b,
      (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    Real.sqrt (∫ x,
      (FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫_ℝ + c i q) b -
        FiniteMaxDerivative.maxValue (fun i q => ⟪x, y i q⟫_ℝ + c i q) a) ^ 2
      ∂uniformMeasure K) ≤ (Real.sqrt (2 * (1 + κ)) * R * w) * (b - a) := by
  obtain ⟨A, hA⟩ := exists_uniform_norm_bound_of_weighted_energy m v (Icc a b) hm hvEnergy
  obtain ⟨B, hB⟩ := exists_uniform_norm_bound_of_weighted_energy m r (Icc a b) hm
    (show ∀ q ∈ Icc a b, (∑ i, m i * ‖r i q‖ ^ 2) ≤
        κ * (R : ℝ) ^ 2 * w ^ 2 from by
      simpa only [Real.norm_eq_abs, sq_abs] using hrEnergy)
  obtain ⟨active, hmeas, hmax, hmass⟩ :=
    ParameterizedArgmax.exists_joint_measurable_affine_argmax_with_masses_on
      K (Ioc a b) (fun q i => y i q) (fun q i => c i q) (fun _ => m)
      hy hc hinj hcell
  apply finite_affine_path_L2_bound K y v c r active m hab hw hκ hxR
    hy hc hv hr hmeas hdy hdc hA hB
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact hinj q hq
  · exact Filter.Eventually.of_forall fun p j => hmax p.1 p.2 j
  · exact hmass
  · exact fun q hq => hvEnergy q (Ioc_subset_Icc_self hq)
  · exact fun q hq => hrEnergy q (Ioc_subset_Icc_self hq)

end Problem358

end

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators RealInnerProductSpace

namespace Problem358

/-- An interior time estimate for finite affine potentials passes to both
endpoints using only continuity of the coefficients.  Sites may collide at
 either endpoint. -/
theorem finite_affine_path_endpoint_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y : ι → ℝ → E d) (c : ι → ℝ → ℝ) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Continuous (c i))
    (hinterior : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      Real.sqrt (∫ x,
        (FiniteAffine.potential (fun i => y i b) (fun i => c i b) x -
         FiniteAffine.potential (fun i => y i a) (fun i => c i a) x) ^ 2
        ∂uniformMeasure K) ≤ L * (b - a)) :
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => y i 1) (fun i => c i 1) x -
       FiniteAffine.potential (fun i => y i 0) (fun i => c i 0) x) ^ 2
      ∂uniformMeasure K) ≤ L := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hot : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ht
  have hlim := FiniteAffine.tendsto_sqrt_integral_potential_pair_sub_sq
    (uniformMeasure K) hR hxR
    (fun i => (hy i).continuousAt.tendsto.comp hot)
    (fun i => (hc i).continuousAt.tendsto.comp hot)
    (fun i => (hy i).continuousAt.tendsto.comp ht)
    (fun i => (hc i).continuousAt.tendsto.comp ht)
  apply le_of_tendsto hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 / 2 :=
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 ht1
  have htpos : 0 < t := ht0
  exact (hinterior t (1 - t) htpos (by linarith) (by linarith)).trans
    (mul_le_of_le_one_right hL (by linarith))

/-- Squared form of the endpoint bound for use in gradient interpolation. -/
theorem finite_affine_path_endpoint_integral_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y : ι → ℝ → E d) (c : ι → ℝ → ℝ) {R L : ℝ}
    (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Continuous (c i))
    (hinterior : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      Real.sqrt (∫ x,
        (FiniteAffine.potential (fun i => y i b) (fun i => c i b) x -
         FiniteAffine.potential (fun i => y i a) (fun i => c i a) x) ^ 2
        ∂uniformMeasure K) ≤ L * (b - a)) :
    (∫ x,
      (FiniteAffine.potential (fun i => y i 1) (fun i => c i 1) x -
       FiniteAffine.potential (fun i => y i 0) (fun i => c i 0) x) ^ 2
      ∂uniformMeasure K) ≤ L ^ 2 :=
  (Real.sqrt_le_iff.mp
    (finite_affine_path_endpoint_bound K y c hR hL hxR hy hc hinterior)).2

/-- A finite C¹ fixed-mass path on the open time interval has the full
endpoint estimate. Derivatives need neither exist nor stay bounded near
endpoints; continuity of the endpoint coefficients is sufficient. -/
theorem finite_affine_C1_path_endpoint_L2_bound
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (K : Set (E d)) [IsFiniteMeasure (uniformMeasure K)]
    (y v : ι → ℝ → E d) (c r : ι → ℝ → ℝ)
    (active : ℝ × E d → ι) (m : ι → ℝ)
    {w κ : ℝ} {R : ℝ≥0} (hw : 0 ≤ w) (hκ : 0 ≤ κ)
    (hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hy : ∀ i, Continuous (y i)) (hc : ∀ i, Continuous (c i))
    (hv : ∀ i, ContinuousOn (v i) (Ioo 0 1))
    (hr : ∀ i, ContinuousOn (r i) (Ioo 0 1))
    (hactiveMeas : Measurable active)
    (hdy : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (y i) (v i q) q)
    (hdc : ∀ i q, q ∈ Ioo 0 1 → HasDerivAt (c i) (r i q) q)
    (hinj : ∀ q ∈ Ioo 0 1, Function.Injective (fun i => y i q))
    (hactive : ∀ q ∈ Ioo 0 1, ∀ x j,
      ⟪x, y j q⟫ + c j q ≤
        ⟪x, y (active (q, x)) q⟫ + c (active (q, x)) q)
    (hm : ∀ q ∈ Ioo 0 1, ∀ i,
      (uniformMeasure K).real {x | active (q, x) = i} = m i)
    (hvEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * ‖v i q‖ ^ 2) ≤ w ^ 2)
    (hrEnergy : ∀ q ∈ Ioo 0 1, (∑ i, m i * r i q ^ 2) ≤ κ * (R : ℝ) ^ 2 * w ^ 2) :
    Real.sqrt (∫ x,
      (FiniteAffine.potential (fun i => y i 1) (fun i => c i 1) x -
       FiniteAffine.potential (fun i => y i 0) (fun i => c i 0) x) ^ 2
      ∂uniformMeasure K) ≤ Real.sqrt (2 * (1 + κ)) * R * w := by
  classical
  let v' : ι → ℝ → E d := fun i => (Ioo 0 1).piecewise (v i) (fun _ => 0)
  let r' : ι → ℝ → ℝ := fun i => (Ioo 0 1).piecewise (r i) (fun _ => 0)
  have hv'Meas (i : ι) : Measurable (v' i) :=
    (hv i).measurable_piecewise continuousOn_const measurableSet_Ioo
  have hr'Meas (i : ι) : Measurable (r' i) :=
    (hr i).measurable_piecewise continuousOn_const measurableSet_Ioo
  have hv'eq (i : ι) {q : ℝ} (hq : q ∈ Ioo 0 1) : v' i q = v i q := by
    simp [v', hq]
  have hr'eq (i : ι) {q : ℝ} (hq : q ∈ Ioo 0 1) : r' i q = r i q := by
    simp [r', hq]
  apply finite_affine_path_endpoint_bound K y c (by positivity) (by positivity)
    hxR hy hc
  intro a b ha hab hb
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro q hq
    exact ⟨ha.trans_le hq.1, hq.2.trans_lt hb⟩
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_pi.mpr fun i => (hv i).mono hsub)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_pi.mpr fun i => (hr i).mono hsub)
  let An : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hvBound (i : ι) (q : ℝ) (hq : q ∈ Icc a b) : ‖v' i q‖ ≤ An := by
    rw [hv'eq i (hsub hq)]
    exact (norm_le_pi_norm (fun j => v j q) i).trans ((hA q hq).trans (le_max_left _ _))
  have hrBound (i : ι) (q : ℝ) (hq : q ∈ Icc a b) : ‖r' i q‖ ≤ Bn := by
    rw [hr'eq i (hsub hq)]
    exact (norm_le_pi_norm (fun j => r j q) i).trans ((hB q hq).trans (le_max_left _ _))
  have htime : ∀ᵐ q : ℝ ∂volume.restrict (Ioc a b), q ∈ Ioo 0 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact hsub (Ioc_subset_Icc_self hq)
  have hpair : ∀ᵐ p : ℝ × E d ∂(volume.restrict (Ioc a b)).prod (uniformMeasure K),
      p.1 ∈ Ioo 0 1 := Measure.quasiMeasurePreserving_fst.ae htime
  have hbound := finite_affine_path_L2_bound K y v' c r' active m
    hab hw hκ hxR (fun i => (hy i).measurable) (fun i => (hc i).measurable)
    hv'Meas hr'Meas hactiveMeas
    (fun i q hq => by rw [hv'eq i (hsub hq)]; exact hdy i q (hsub hq))
    (fun i q hq => by rw [hr'eq i (hsub hq)]; exact hdc i q (hsub hq))
    hvBound hrBound
    (htime.mono fun q hq => hinj q hq)
    (hpair.mono fun p hp => hactive p.1 hp p.2)
    (fun q hq => hm q (hsub (Ioc_subset_Icc_self hq)))
    (fun q hq => by
      simp only [hv'eq _ (hsub (Ioc_subset_Icc_self hq))]
      exact hvEnergy q (hsub (Ioc_subset_Icc_self hq)))
    (fun q hq => by
      simp only [hr'eq _ (hsub (Ioc_subset_Icc_self hq))]
      exact hrEnergy q (hsub (Ioc_subset_Icc_self hq)))
  exact hbound

end Problem358

end

end OAI
