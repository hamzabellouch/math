import OAI.Analysis.ProductSpaces.ScalarBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section WeightedMoments
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [Fintype ι]
variable {P : Measure Ω}

lemma weighted_sum_memLp_two [IsProbabilityMeasure P] (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) :
    MemLp (fun ω => ∑ i, a i ^ 2 * U i ω) 2 P := by
  exact memLp_finsetSum _ (fun i _ => (hU i).const_mul _)

variable [IsProbabilityMeasure P]

lemma weighted_sum_mean (a : ι → ℝ) (U : ι → Ω → ℝ) (hU : ∀ i, MemLp (U i) 2 P)
    (hm : ∀ i, ∫ ω, U i ω ∂P = 1) :
    (∫ ω, ∑ i, a i ^ 2 * U i ω ∂P) = ∑ i, a i ^ 2 := by
  rw [integral_finsetSum _ (fun i _ => ((hU i).integrable (by norm_num)).const_mul _)]
  simp_rw [integral_const_mul, hm, mul_one]

lemma weighted_sum_second_moment_le (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) (M : ℝ)
    (hm : ∀ i, (∫ ω, U i ω ^ 2 ∂P) ≤ M) :
    (∫ ω, (∑ i, a i ^ 2 * U i ω) ^ 2 ∂P) ≤ M * (∑ i, a i ^ 2) ^ 2 := by
  have hint : ∀ i, Integrable (fun ω => U i ω ^ 2) P :=
    fun i => (memLp_two_iff_integrable_sq (hU i).aestronglyMeasurable).mp (hU i)
  have hintV := (memLp_two_iff_integrable_sq (weighted_sum_memLp_two a U hU).aestronglyMeasurable).mp
    (weighted_sum_memLp_two a U hU)
  calc
    _ ≤ ∫ ω, (∑ i, a i ^ 2) * ∑ i, a i ^ 2 * U i ω ^ 2 ∂P := by
      apply integral_mono hintV
        ((integrable_finsetSum _ (fun i _ => (hint i).const_mul _)).const_mul _)
      intro ω
      have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun i => a i * U i ω)
      simpa only [mul_pow, ← mul_assoc, ← pow_two] using hc
    _ = (∑ i, a i ^ 2) * ∑ i, a i ^ 2 * ∫ ω, U i ω ^ 2 ∂P := by
      rw [integral_const_mul, integral_finsetSum]
      · simp_rw [integral_const_mul]
      · exact fun i _ => (hint i).const_mul _
    _ ≤ (∑ i, a i ^ 2) * ∑ i, a i ^ 2 * M := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i) (sq_nonneg _)
    _ = M * (∑ i, a i ^ 2) ^ 2 := by rw [← Finset.sum_mul]; ring

lemma weighted_sum_tail (a : ι → ℝ) (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 P) (hmeas : ∀ i, Measurable (U i))
    (hpos : ∀ i ω, 0 ≤ U i ω) (hm : ∀ i, ∫ ω, U i ω ∂P = 1)
    (M : ℝ) (hM : 0 < M) (hm2 : ∀ i, (∫ ω, U i ω ^ 2 ∂P) ≤ M)
    (ha : 0 < ∑ i, a i ^ 2) :
    1 / (4 * M) ≤ P.real {ω | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * U i ω} := by
  let S := ∑ i, a i ^ 2
  let V : Ω → ℝ := fun ω => ∑ i, a i ^ 2 * U i ω
  have hV := weighted_sum_memLp_two a U hU
  have hmV := weighted_sum_mean a U hU hm
  have htail := second_moment_tail_bound V hV (by fun_prop)
    (fun ω => Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hpos i ω)))
    (S / 2) S (by dsimp [S]; positivity) (by dsimp [S]; linarith) hmV.ge
  have hm2V := weighted_sum_second_moment_le a U hU M hm2
  have hnonneg : 0 ≤ P.real {ω | S / 2 ≤ V ω} := measureReal_nonneg
  have hx : (S / 2) ^ 2 ≤ M * S ^ 2 * P.real {ω | S / 2 ≤ V ω} := by
    have hh := mul_le_mul_of_nonneg_right hm2V hnonneg
    nlinarith [htail]
  rw [div_le_iff₀ (by positivity : 0 < 4 * M)]
  have hs : 0 < S ^ 2 := sq_pos_of_pos ha
  nlinarith

end WeightedMoments
section GaussianVector
variable {ι : Type uι} [Fintype ι]

def gaussianVector : Measure (ι → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
instance : IsProbabilityMeasure (gaussianVector (ι := ι)) := by unfold gaussianVector; infer_instance

lemma gaussian_eval_hasLaw (i : ι) : HasLaw (fun x : ι → ℝ => x i) (gaussianReal 0 1) gaussianVector :=
  (measurePreserving_eval (fun _ => gaussianReal 0 1) i).hasLaw

lemma gaussian_square_memLp : MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert h using 1
  funext x
  change (x ^ 2) ^ 2 = |x| ^ 4
  rw [← pow_mul]
  norm_num
  rw [← abs_pow, abs_of_nonneg (by positivity)]

lemma gaussian_quadratic_tail (a : ι → ℝ) (ha : 0 < ∑ i, a i ^ 2) :
    1 / 12 ≤ (gaussianVector (ι := ι)).real
      {x | (∑ i, a i ^ 2) / 2 ≤ ∑ i, a i ^ 2 * x i ^ 2} := by
  have hU : ∀ i : ι, MemLp (fun x : ι → ℝ => x i ^ 2) 2 gaussianVector := fun i =>
    gaussian_square_memLp.comp_measurePreserving
      (measurePreserving_eval (fun _ => gaussianReal 0 1) i)
  have hm : ∀ i : ι, (∫ x : ι → ℝ, x i ^ 2 ∂gaussianVector) = 1 := by
    intro i
    exact (gaussian_eval_hasLaw i).integral_comp (by fun_prop) |>.trans gaussian_integral_sq
  have hm2 : ∀ i : ι, (∫ x : ι → ℝ, (x i ^ 2) ^ 2 ∂gaussianVector) ≤ 3 := by
    intro i
    have he : (∫ x : ι → ℝ, (x i ^ 2) ^ 2 ∂gaussianVector) = 3 := by
      exact ((gaussian_eval_hasLaw i).integral_comp (f := fun x : ℝ => (x ^ 2) ^ 2)
        (by fun_prop)).trans (by simpa only [← pow_mul, Nat.reduceMul] using gaussian_integral_fourth)
    exact he.le
  have hh := weighted_sum_tail a (fun i (x : ι → ℝ) => x i ^ 2) hU
    (fun _ => by fun_prop) (fun _ _ => sq_nonneg _) hm 3 (by norm_num) hm2 ha
  norm_num at hh ⊢
  exact hh

end GaussianVector
end IndependentProducts

namespace IndependentProducts

def excess (t r z : ℝ) : ℝ := max (t * |z| - r) 0

lemma excess_nonneg (t r z : ℝ) : 0 ≤ excess t r z := le_max_right _ _

lemma excess_midpoint (t r u v : ℝ) (ht : 0 ≤ t) :
    excess t r ((u - v) / 2) ≤ (excess t r u + excess t r v) / 2 := by
  unfold excess
  rw [max_le_iff]
  constructor
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := abs_sub u v
    have hh' := mul_le_mul_of_nonneg_left hh ht
    have hu := le_max_left (t * |u| - r) 0
    have hv := le_max_left (t * |v| - r) 0
    linarith
  · positivity

lemma integrable_excess {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable X P) (t r : ℝ) :
    Integrable (fun ω => excess t r (X ω)) P :=
  ((hX.abs.const_mul t).sub (integrable_const r)).sup (integrable_const 0)

lemma integral_excess_independent_copy {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Integrable X P)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∫ z : Ω × Ω, excess t r ((X z.1 - X z.2) / 2) ∂P.prod P) ≤
      ∫ ω, excess t r (X ω) ∂P := by
  have hxf := hX.comp_fst P
  have hxs := hX.comp_snd P
  have h1 := integrable_excess ((hxf.sub hxs).div_const 2) t r
  have h2 := ((integrable_excess hxf t r).add (integrable_excess hxs t r)).div_const 2
  calc
    _ ≤ ∫ z : Ω × Ω, (excess t r (X z.1) + excess t r (X z.2)) / 2 ∂P.prod P :=
      integral_mono h1 h2 (fun z => excess_midpoint t r (X z.1) (X z.2) ht)
    _ = ∫ ω, excess t r (X ω) ∂P := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_add (integrable_excess hxf t r) (integrable_excess hxs t r),
        integral_fun_fst (fun ω => excess t r (X ω)), integral_fun_snd (fun ω => excess t r (X ω))]
      simp
      ring

lemma integral_excess_ge_tail {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P)
    (hXm : Measurable X) {t : ℝ} (ht : 0 ≤ t) (r k : ℝ) (hk : 0 ≤ k) :
    P.real {ω | k ≤ |X ω|} * excess t r k ≤ ∫ ω, excess t r (X ω) ∂P := by
  let A : Set Ω := {ω | k ≤ |X ω|}
  have hA : MeasurableSet A := measurableSet_le measurable_const hXm.abs
  calc
    _ = ∫ ω, A.indicator (fun _ => excess t r k) ω ∂P := by simp [integral_indicator hA, mul_comm, A]
    _ ≤ ∫ ω, excess t r (X ω) ∂P := by
      apply integral_mono ((integrable_const _).indicator hA) (integrable_excess hX t r)
      intro ω
      by_cases hω : ω ∈ A
      · simp only [Set.indicator_of_mem hω]
        apply max_le_max_right
        have hh : k ≤ |X ω| := hω
        exact sub_le_sub_right (by simpa [abs_of_nonneg hk] using mul_le_mul_of_nonneg_left hh ht) _
      · simp only [Set.indicator_of_notMem hω]
        exact excess_nonneg _ _ _

end IndependentProducts

namespace IndependentProducts

lemma gaussian_sqrt_scale (v : ℝ≥0) :
    HasLaw (fun x : ℝ => Real.sqrt (v : ℝ) * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul]
  apply congrArg₂ gaussianReal
  · ring
  · ext
    change (Real.sqrt (v : ℝ)) ^ 2 * 1 = (v : ℝ)
    rw [Real.sq_sqrt v.coe_nonneg, mul_one]

lemma gaussian_tail_variance_lower (v : ℝ≥0) (K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hv : s ^ 2 / 2 ≤ (v : ℝ)) :
    gaussianTail (Real.sqrt 2 * K) ≤ (gaussianReal 0 v).real {x | K * s ≤ |x|} := by
  rw [← (gaussian_sqrt_scale v).measureReal_eq (measurableSet_le measurable_const (by fun_prop))]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  change Real.sqrt 2 * K ≤ |x| at hx
  change K * s ≤ |Real.sqrt (v : ℝ) * x|
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsv := Real.sq_sqrt v.coe_nonneg
  have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hscale : s ≤ Real.sqrt (v : ℝ) * Real.sqrt 2 := by
    have hp : (Real.sqrt (v : ℝ) * Real.sqrt 2) ^ 2 = (v : ℝ) * 2 := by
      rw [mul_pow, hsv, htwo]
    apply (sq_le_sq₀ hs (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    nlinarith [hp]
  calc
    K * s ≤ K * (Real.sqrt (v : ℝ) * Real.sqrt 2) := mul_le_mul_of_nonneg_left hscale hK
    _ = Real.sqrt (v : ℝ) * (Real.sqrt 2 * K) := by ring
    _ ≤ Real.sqrt (v : ℝ) * |x| := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)

section GaussianFinite
variable {ι : Type uι} [Fintype ι]

lemma gaussian_weighted_hasLaw (a : ι → ℝ) :
    HasLaw (fun x : ι → ℝ => ∑ i, a i * x i)
      (gaussianReal 0 (NNReal.mk (∑ i, a i ^ 2) (Finset.sum_nonneg fun _ _ => sq_nonneg _))) gaussianVector := by
  classical
  refine ⟨(by fun_prop : Measurable (fun x : ι → ℝ => ∑ i, a i * x i)).aemeasurable, ?_⟩
  unfold gaussianVector
  rw [map_gaussian_weighted_sum]
  congr 1
  ext
  simp

lemma gaussian_weighted_excess (a : ι → ℝ) (K s t r : ℝ)
    (hK : 0 ≤ K) (hs : 0 ≤ s) (ht : 0 ≤ t) (hv : s ^ 2 / 2 ≤ ∑ i, a i ^ 2) :
    gaussianTail (Real.sqrt 2 * K) * excess t r (K * s) ≤
      ∫ x : ι → ℝ, excess t r (∑ i, a i * x i) ∂gaussianVector := by
  have hm : Measurable (fun x : ι → ℝ => ∑ i, a i * x i) := by fun_prop
  have hint : Integrable (fun x : ι → ℝ => ∑ i, a i * x i) gaussianVector :=
    (gaussian_weighted_hasLaw a).hasGaussianLaw.integrable
  have htail : gaussianTail (Real.sqrt 2 * K) ≤
      gaussianVector.real {x : ι → ℝ | K * s ≤ |∑ i, a i * x i|} := by
    rw [(gaussian_weighted_hasLaw a).measureReal_eq (p := fun z : ℝ => K * s ≤ |z|)
      (measurableSet_le measurable_const (by fun_prop))]
    exact gaussian_tail_variance_lower _ K s hK hs hv
  exact (mul_le_mul_of_nonneg_right htail (excess_nonneg _ _ _)).trans
    (integral_excess_ge_tail _ hint hm ht r (K * s) (mul_nonneg hK hs))

def gaussianVectorRotate (z : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (fun i => (gaussianRotate (z.1 i, z.2 i)).1, fun i => (gaussianRotate (z.1 i, z.2 i)).2)

lemma measurePreserving_gaussianVectorRotate : MeasurePreserving (gaussianVectorRotate (ι := ι))
    (gaussianVector.prod gaussianVector) (gaussianVector.prod gaussianVector) := by
  let PP := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hp := measurePreserving_pi (fun _ : ι => PP) (fun _ : ι => PP)
    (fun _ : ι => measurePreserving_gaussianRotate)
  have hs := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
  exact hs.comp (hp.comp hs.symm)

lemma integrable_gaussian_bilinear (a : ι → ℝ) :
    Integrable (fun z : (ι → ℝ) × (ι → ℝ) => ∑ i, a i * z.1 i * z.2 i)
      (gaussianVector.prod gaussianVector) := by
  apply integrable_finsetSum
  intro i _
  have hi := (gaussian_eval_hasLaw i).hasGaussianLaw.integrable
  exact (hi.const_mul _).mul_prod hi

lemma gaussian_bilinear_excess (a : ι → ℝ) (K t r : ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    (gaussianTail (Real.sqrt 2 * K) / 12) *
      excess t r (K * Real.sqrt (∑ i, a i ^ 2)) ≤
      ∫ z : (ι → ℝ) × (ι → ℝ), excess t r (∑ i, a i * z.1 i * z.2 i)
        ∂gaussianVector.prod gaussianVector := by
  let S : ℝ := ∑ i, a i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change (gaussianTail (Real.sqrt 2 * K) / 12) * excess t r (K * Real.sqrt S) ≤ _
  by_cases hS0 : S = 0
  · simp only [hS0, Real.sqrt_zero, mul_zero, excess, abs_zero, zero_sub,
      max_eq_right (neg_nonpos.mpr hr), mul_zero]
    exact integral_nonneg (fun _ => excess_nonneg _ _ _)
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
  let A : Set (ι → ℝ) := {x | S / 2 ≤ ∑ i, a i ^ 2 * x i ^ 2}
  have hA : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  let c := gaussianTail (Real.sqrt 2 * K) * excess t r (K * Real.sqrt S)
  have hc : 0 ≤ c := mul_nonneg (gaussianTail_nonneg _) (excess_nonneg _ _ _)
  have hint := integrable_excess (integrable_gaussian_bilinear a) t r
  rw [integral_prod _ hint]
  calc
    _ ≤ gaussianVector.real A * c := by
      have hp := gaussian_quadratic_tail a hSp
      have hh := mul_le_mul_of_nonneg_right hp hc
      dsimp [c, A, S] at hh ⊢
      nlinarith
    _ = ∫ x : ι → ℝ, A.indicator (fun _ => c) x ∂gaussianVector := by
      simp [integral_indicator hA, mul_comm]
    _ ≤ ∫ x : ι → ℝ, ∫ y : ι → ℝ, excess t r (∑ i, a i * x i * y i)
        ∂gaussianVector ∂gaussianVector := by
      apply integral_mono ((integrable_const _).indicator hA) hint.integral_prod_left
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        apply gaussian_weighted_excess (fun i => a i * x i) K (Real.sqrt S) t r hK
          (Real.sqrt_nonneg S) ht
        rw [Real.sq_sqrt hS]
        simpa only [A, Set.mem_ofPred_eq, mul_pow] using hx
      · simp only [Set.indicator_of_notMem hx]
        exact integral_nonneg (fun _ => excess_nonneg _ _ _)

end GaussianFinite
end IndependentProducts

end

end OAI
