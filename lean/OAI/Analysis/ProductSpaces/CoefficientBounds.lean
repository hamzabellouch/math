import OAI.Analysis.ProductSpaces.RandomSigns

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section CoefficientBound
variable {ι : Type uι} [Fintype ι]

lemma memLp_euclidSize {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (fun ω => euclidSize (fun i => X i ω)) 2 P := by
  apply (memLp_finsetSum _ (fun i _ => (hX i).norm)).mono'
  · unfold euclidSize
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    have ha := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hX i).aestronglyMeasurable.pow 2)
    convert ha using 1
    ext ω
    simp
  · filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclidSize_nonneg _)] using
      euclidSize_le_sum_abs (fun i => X i ω)

lemma integral_euclidSize_mul_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (a : ι → ℝ) :
    (∫ w : ι → ℝ, euclidSize (fun i => w i * a i) ∂Measure.pi (fun _ : ι => μ)) ≤
      Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ) * euclidSize a := by
  have hi : ∀ i, MemLp (fun w : ι → ℝ => w i * a i) 2 (Measure.pi (fun _ : ι => μ)) :=
    fun i => (hμ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).mul_const _
  have h := integral_abs_le_sqrt_sq (memLp_euclidSize _ hi)
  simp_rw [abs_of_nonneg (euclidSize_nonneg _), euclidSize_sq, mul_pow] at h
  have he : (∫ w : ι → ℝ, ∑ i, w i ^ 2 * a i ^ 2 ∂Measure.pi (fun _ : ι => μ)) =
      (∫ w : ℝ, w ^ 2 ∂μ) * ∑ i, a i ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => by
      exact ((hμ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).integrable_sq).mul_const _)]
    simp only [integral_mul_const]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simpa using (measurePreserving_eval (fun _ : ι => μ) i).hasLaw.integral_comp
      (f := fun w : ℝ => w ^ 2) (by fun_prop)
  rw [he, Real.sqrt_mul (integral_nonneg (fun w : ℝ => sq_nonneg w))] at h
  exact h

lemma independent_centered_sum_abs_le_of_indep {Ω : Type uΩ} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) P) (hXm : ∀ i, Measurable (X i))
    (hI : iIndepFun X P) :
    (∫ ω, |∑ i, (X i ω - ∫ ω, X i ω ∂P)| ∂P) ≤
      2 * ∫ ω, euclidSize (fun i => X i ω) ∂P := by
  let ν : ι → Measure ℝ := fun i => P.map (X i)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun _ => inferInstance
  have hl : HasLaw (fun ω i => X i ω) (Measure.pi ν) P :=
    ⟨(Measurable.of_eval hXm).aemeasurable, hI.map_fun_eq_pi_map (fun i => (hXm i).aemeasurable)⟩
  have hν : ∀ i, Integrable (fun x : ℝ => x) (ν i) := by
    intro i
    exact (integrable_map_measure (by fun_prop) (hXm i).aemeasurable).mpr (hX i)
  have hm : ∀ i, (∫ x : ℝ, x ∂ν i) = ∫ ω, X i ω ∂P := by
    intro i
    exact integral_map (hXm i).aemeasurable (by fun_prop)
  have hc := independent_centered_sum_abs_le ν hν
  rw [← hl.integral_comp (f := fun x : ι → ℝ => |∑ i, (x i - ∫ z : ℝ, z ∂ν i)|)
      ((by fun_prop : Continuous _).aestronglyMeasurable),
    ← hl.integral_comp (f := euclidSize) ((by unfold euclidSize; fun_prop : Continuous _).aestronglyMeasurable)] at hc
  simpa only [hm, Function.comp_apply] using hc

end CoefficientBound
end IndependentProducts

namespace IndependentProducts
section SignedFirstMoment
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]

lemma signed_first_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (B : ι → Ω → ℝ) (hB : ∀ i, Integrable (B i) (ν i)) (hBm : ∀ i, Measurable (B i)) :
    (∫ z : (ι → Ω) × (ι → ℝ),
      |∑ i, (B i (z.1 i) * z.2 i - ∫ b, B i b ∂ν i)| ∂(Measure.pi ν).prod (Measure.pi (fun _ : ι => μ))) ≤
      2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ) *
        ∫ b : ι → Ω, euclidSize (fun i => B i (b i)) ∂Measure.pi ν := by
  let Pb := Measure.pi ν
  let Pw := Measure.pi (fun _ : ι => μ)
  let Q := Measure.pi (fun i : ι => (ν i).prod μ)
  let X : ι → (ι → Ω × ℝ) → ℝ := fun i z => B i (z i).1 * (z i).2
  have hw : Integrable (fun w : ℝ => w) μ := hμ.integrable (by norm_num)
  have hX : ∀ i, Integrable (X i) Q := by
    intro i
    exact (measurePreserving_eval (fun i => (ν i).prod μ) i).integrable_comp
      (by fun_prop) |>.mpr ((hB i).mul_prod hw)
  have hXi : iIndepFun X Q := iIndepFun_pi (by intro i; exact ((hBm i).comp measurable_fst |>.mul measurable_snd).aemeasurable)
  have hm : ∀ i, (∫ z, X i z ∂Q) = ∫ b, B i b ∂ν i := by
    intro i
    have hh := (measurePreserving_eval (fun i => (ν i).prod μ) i).hasLaw.integral_comp
      (f := fun z : Ω × ℝ => B i z.1 * z.2) (by fun_prop)
    change (∫ z, B i (z i).1 * (z i).2 ∂Q) = _
    simp only [Function.comp_apply, Function.eval] at hh
    rw [hh, integral_prod_mul (B i) (fun w : ℝ => w), hmean, mul_one]
  have hmp := (measurePreserving_arrowProdEquivProdArrow Ω ℝ ι ν (fun _ : ι => μ)).symm
  have hcp := independent_centered_sum_abs_le_of_indep X hX (by intro i; dsimp [X]; fun_prop) hXi
  simp only [hm] at hcp
  have he1 := hmp.hasLaw.integral_comp
    (f := fun z : ι → Ω × ℝ => |∑ i, (X i z - ∫ b, B i b ∂ν i)|)
    (by dsimp [X]; fun_prop)
  have he2 := hmp.hasLaw.integral_comp
    (f := fun z : ι → Ω × ℝ => euclidSize (fun i => X i z))
    (by dsimp [X, euclidSize]; fun_prop)
  rw [← he1, ← he2] at hcp
  change (∫ z : (ι → Ω) × (ι → ℝ), |∑ i, (B i (z.1 i) * z.2 i - ∫ b, B i b ∂ν i)| ∂Pb.prod Pw) ≤
    2 * ∫ z : (ι → Ω) × (ι → ℝ), euclidSize (fun i => B i (z.1 i) * z.2 i) ∂Pb.prod Pw at hcp
  have hb : ∀ i, Integrable (fun b : ι → Ω => B i (b i)) Pb := by
    intro i
    exact (measurePreserving_eval ν i).integrable_comp (by fun_prop) |>.mpr (hB i)
  have hwc : ∀ i, Integrable (fun w : ι → ℝ => w i) Pw := by
    intro i
    exact (measurePreserving_eval (fun _ : ι => μ) i).integrable_comp (by fun_prop) |>.mpr hw
  have hs := integrable_euclidSize (fun i (z : (ι → Ω) × (ι → ℝ)) => B i (z.1 i) * z.2 i)
    (fun i => (hb i).mul_prod (hwc i))
  have hsb := integrable_euclidSize (fun i (b : ι → Ω) => B i (b i)) hb
  have hc : (∫ z : (ι → Ω) × (ι → ℝ), euclidSize (fun i => B i (z.1 i) * z.2 i) ∂Pb.prod Pw) ≤
      Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ) * ∫ b : ι → Ω, euclidSize (fun i => B i (b i)) ∂Pb := by
    rw [integral_prod _ hs, ← integral_const_mul]
    apply integral_mono hs.integral_prod_left (hsb.const_mul _)
    intro b
    simpa only [mul_comm] using integral_euclidSize_mul_le μ hμ (fun i => B i (b i))
  nlinarith

end SignedFirstMoment
end IndependentProducts

end

end OAI
