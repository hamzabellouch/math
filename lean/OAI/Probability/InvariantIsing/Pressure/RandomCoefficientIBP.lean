import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-!
Gaussian insertion when the finite coefficient vectors depend on external
disorder. This permits the Haar-dependent spectral-overlap tensor features.
The Gaussian coordinates remain independent of the external disorder.
-/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Countable X] [MeasurableSingletonClass X]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
  [∀ ω, IsProbabilityMeasure (ν ω)]

lemma measurable_randomCoefficient_mean (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {r : ℕ} (D : Ω → (Fin r → X) → ℝ) (hD : Measurable (Function.uncurry D)) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2) (D z.1)) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) hA
    (hD.comp (measurable_fst.fst.prodMk measurable_snd))

lemma integrable_randomCoefficient_mean (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {r : ℕ} (D : Ω → (Fin r → X) → ℝ) (hDm : Measurable (Function.uncurry D))
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ ω σ, |D ω σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2) (D z.1)) (P.prod gaussianCoordinates) := by
  exact integrable_of_measurable_abs_le (measurable_randomCoefficient_mean hν A hA D hDm)
    (fun z => referenceReplicaMean_abs_le (ν z.1) _ (D z.1)
      (measurable_of_countable _) hc (hD z.1))

lemma measurable_randomCoefficient_insertion (hν : Measurable ν)
    (A B : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hB : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (B p.1.1 p.2) p.1.2))
    {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2)
      (fun σ => cylinderField (B z.1 (σ 0)) z.2 * D z.1 σ)) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) hA
    ((hB.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
      (hD.comp (measurable_fst.fst.prodMk measurable_snd)))

lemma integrable_randomCoefficient_insertion (hν : Measurable ν)
    (A B : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hB : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (B p.1.1 p.2) p.1.2))
    {K L : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K)
    (hb : ∀ ω x, (B ω x).sum (fun _ c => c ^ 2) ≤ L)
    {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2)
      (fun σ => cylinderField (B z.1 (σ 0)) z.2 * D z.1 σ)) (P.prod gaussianCoordinates) := by
  have hm := measurable_randomCoefficient_insertion hν A B hA hB D hDm
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_replica_insertion_second (ν ω) (A ω) (B ω)
      (ha ω) (hb ω) (D ω) hc (hD ω)).1)
    (fun ω => (cylinder_replica_insertion_second (ν ω) (A ω) (B ω)
      (ha ω) (hb ω) (D ω) hc (hD ω)).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

/-- The countable Gaussian insertion identity with external-disorder-dependent
coefficients and replica tests. The uniform second-moment estimate
justifies Fubini for the countable cylinder law. -/
theorem joint_randomCoefficient_cylinder_insertion (hν : Measurable ν)
    (A B : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (hB : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (B p.1.1 p.2) p.1.2))
    (hcross : Measurable (fun p : Ω × (X × X) => cylinderCross (B p.1 p.2.1) (A p.1 p.2.2)))
    {K L : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K)
    (hb : ∀ ω x, (B ω x).sum (fun _ c => c ^ 2) ≤ L)
    {r : ℕ} (D : Ω → (Fin (r + 1) → X) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c) :
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2)
      (fun σ => cylinderField (B z.1 (σ 0)) z.2 * D z.1 σ) ∂P.prod gaussianCoordinates) =
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2)
      (fun σ => D z.1 σ * (∑ i, cylinderCross (B z.1 (σ 0)) (A z.1 (σ i))))
      ∂P.prod gaussianCoordinates) -
    (r + 1 : ℕ) * (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2)
      (fun τ : Fin (r + 1 + 1) → X => D z.1 (Fin.tail τ) *
        cylinderCross (B z.1 ((Fin.tail τ) 0)) (A z.1 (τ 0))) ∂P.prod gaussianCoordinates) := by
  let M : ℝ := (|K| + |L|) / 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcov (ω : Ω) (x y : X) : |cylinderCross (B ω x) (A ω y)| ≤ M := by
    calc
      _ ≤ ((B ω x).sum (fun _ t => t ^ 2) + (A ω y).sum (fun _ t => t ^ 2)) / 2 :=
        abs_cylinderCross_le _ _
      _ ≤ M := by dsimp [M]; linarith [hb ω x, ha ω y, le_abs_self K, le_abs_self L]
  let D₁ := fun (ω : Ω) (σ : Fin (r + 1) → X) =>
    D ω σ * ∑ i, cylinderCross (B ω (σ 0)) (A ω (σ i))
  let D₂ := fun (ω : Ω) (τ : Fin (r + 1 + 1) → X) =>
    D ω (Fin.tail τ) * cylinderCross (B ω ((Fin.tail τ) 0)) (A ω (τ 0))
  have hm₁ : Measurable (Function.uncurry D₁) := by
    apply hDm.mul
    apply Finset.measurable_sum
    intro i _
    have hp : Measurable (fun p : Ω × (Fin (r + 1) → X) =>
        (p.1, (p.2 0, p.2 i))) := measurable_fst.prodMk
      (((measurable_pi_apply 0).comp measurable_snd).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
    exact hcross.comp hp
  have htail : Measurable (fun p : Ω × (Fin (r + 1 + 1) → X) => (p.1, Fin.tail p.2)) :=
    measurable_fst.prodMk (Measurable.of_eval fun i =>
      (measurable_pi_apply i.succ).comp measurable_snd)
  have hm₂ : Measurable (Function.uncurry D₂) := by
    have hp : Measurable (fun p : Ω × (Fin (r + 1 + 1) → X) =>
        (p.1, (p.2 (0 : Fin (r + 1)).succ, p.2 0))) := measurable_fst.prodMk
      (((measurable_pi_apply (0 : Fin (r + 1)).succ).comp measurable_snd).prodMk
        ((measurable_pi_apply 0).comp measurable_snd))
    exact (hDm.comp htail).mul (hcross.comp hp)
  have hb₁ : ∀ ω σ, |D₁ ω σ| ≤ c * ((r + 1 : ℕ) * M) := by
    intro ω σ
    have hs : |∑ i, cylinderCross (B ω (σ 0)) (A ω (σ i))| ≤ (r + 1 : ℕ) * M := by
      calc
        _ ≤ ∑ i, |cylinderCross (B ω (σ 0)) (A ω (σ i))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ : Fin (r + 1), M := Finset.sum_le_sum fun _ _ => hcov ω _ _
        _ = _ := by simp
    exact (abs_mul _ _).trans_le (mul_le_mul (hD ω σ) hs (abs_nonneg _) hc)
  have hb₂ : ∀ ω τ, |D₂ ω τ| ≤ c * M := by
    intro ω τ
    exact (abs_mul _ _).trans_le (mul_le_mul (hD ω _) (hcov ω _ _) (abs_nonneg _) hc)
  have hi := integrable_randomCoefficient_insertion (P := P) hν A B hA hB ha hb D hDm hc hD
  have hi₁ := integrable_randomCoefficient_mean (P := P) hν A hA D₁ hm₁
    (by positivity : 0 ≤ c * ((r + 1 : ℕ) * M)) hb₁
  have hi₂ := integrable_randomCoefficient_mean (P := P) hν A hA D₂ hm₂ (mul_nonneg hc hM) hb₂
  change (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => cylinderField (A z.1 x) z.2)
    (fun σ => cylinderField (B z.1 (σ 0)) z.2 * D z.1 σ) ∂P.prod gaussianCoordinates) =
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2) (D₁ z.1) ∂P.prod gaussianCoordinates) -
    (r + 1 : ℕ) * (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
      (fun x => cylinderField (A z.1 x) z.2) (D₂ z.1) ∂P.prod gaussianCoordinates)
  rw [integral_prod _ hi, integral_prod _ hi₁, integral_prod _ hi₂]
  calc
    _ = ∫ ω, ((∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (A ω x) g)
        (D₁ ω) ∂gaussianCoordinates) - (r + 1 : ℕ) *
        (∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (A ω x) g)
          (D₂ ω) ∂gaussianCoordinates)) ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => countable_cylinder_reference_insertion (ν ω) (A ω) (B ω)
        (ha ω) (hb ω) (D ω) hc (hD ω)
    _ = _ := by
      rw [integral_sub hi₁.integral_prod_left (hi₂.integral_prod_left.const_mul _), integral_const_mul]

omit [IsProbabilityMeasure P] in
/-- All exponential tilts are integrable for almost every joint disorder.
Only integer tilts are intersected before extending to every real parameter. -/
lemma randomCoefficient_all_exp_ae (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {K : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1, hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t * cylinderField (A p.1.1 p.2) p.1.2)) := (hA.const_mul t).exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t * cylinderField (A z.1 x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((A ω x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (A ω x).sum (fun _ c => c ^ 2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha ω x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields (A ω))
      (fun x => cylinderField_law (A ω x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n : ℝ) * cylinderField (A z.1 x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n : ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

omit [Countable X] [MeasurableSingletonClass X] in
lemma measurable_randomCoefficient_cgf (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) =>
      cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) (hA.const_mul t)).log

/-- The external-disorder-dependent log partition is integrable, by the
uniform pointwise Gaussian second-moment estimate. -/
lemma integrable_randomCoefficient_cgf (hν : Measurable ν)
    (A : Ω → X → ℕ →₀ ℝ)
    (hA : Measurable (fun p : (Ω × (ℕ → ℝ)) × X => cylinderField (A p.1.1 p.2) p.1.2))
    {K : ℝ} (ha : ∀ ω x, (A ω x).sum (fun _ c => c ^ 2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) =>
      cgf (fun x => cylinderField (A z.1 x) z.2) (ν z.1) t) (P.prod gaussianCoordinates) := by
  have hm := measurable_randomCoefficient_cgf hν A hA t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) (A ω) (ha ω) t).1)
    (fun ω => (cylinder_cgf_second (ν ω) (A ω) (ha ω) t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

end InvariantIsing

end

end OAI
