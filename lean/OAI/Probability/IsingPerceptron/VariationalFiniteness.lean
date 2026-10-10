import Mathlib
import OAI.Probability.IsingPerceptron.ContactFaces

namespace OAI

/-! Variational Finiteness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTransform_zero_variance (d : ℝ) (U : ℝ → ℝ) :
    gaussianTransform 0 d U = U := by
  ext x
  by_cases hd : d = 0
  · simp [gaussianTransform, hd]
  · simp [gaussianTransform, hd]

lemma magneticRecursion_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticRecursion n (fun _ => 0) b = fun x => Real.log (Real.cosh x) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [magneticRecursion, ih, zero_pow (by decide : 2 ≠ 0),
      gaussianTransform_zero_variance]

lemma magneticFieldValue_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticFieldValue n b (fun _ => 0) = 0 := by
  simp [magneticFieldValue, pathAmplitude, pathIncrement, magneticRecursion_zero]

 
lemma enrichedMeanPressure_field_add_le {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b (fun i => h i + l i) u ν φ ≤
      enrichedMeanPressure P r n b h u ν φ := by
  have he := enrichedMeanPressure_field_insert hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r
    (a := 1) zero_le_one
  simp only [one_mul, Real.sqrt_one] at he
  have hc := (random_cylinder_cgf_mean_bounds (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) 1).2
  simp only [one_pow, one_mul] at hc
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : (∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
      cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
        (enrichedGibbsReference n h u ν φ z.1) 1
        ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates) / (N : ℝ) ≤ l n / 2 :=
    (div_le_iff₀ hn).mpr (hc.trans_eq (by ring))
  rw [he]
  linarith

lemma magneticFieldValue_nonpos (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) :
    magneticFieldValue n b h ≤ 0 := by
  let P : Measure Unit := Measure.dirac ()
  let φ : Unit → Spin 1 → ℝ := fun _ _ => 0
  have hm : Measurable φ := measurable_const
  have hφ : ∀ y x, |φ y x| ≤ (0 : ℝ) := by intros; simp [φ]
  have hu : ∀ j : Fin 1, |(0 : Fin 1 → ℝ) j| ≤ 2 := by simp
  have he := enrichedMeanPressure_field_add_le (N := 1) (by decide) n b hb
    (h := fun _ => 0) monotone_const le_rfl hh h0 0 hu (spinLaw 1) P hm le_rfl hφ 0
  simp only [zero_add] at he
  rw [enrichedMeanPressure_initial_zero (by decide) n b hb hh h0 P hm le_rfl hφ,
    enrichedMeanPressure_initial_zero (by decide) n b hb monotone_const le_rfl P hm le_rfl hφ,
    magneticFieldValue_zero] at he
  exact he

lemma fieldRecursion_nonpos (h : FieldStep) : fieldRecursion h ≤ 0 := by
  rcases h with ⟨⟨k, hk, ζ, hz, hz0, hz1⟩, v, hv0, hv⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change Fin (n + 1) → ℝ at v
  have hζ0 : ζ 0 = 0 := by
    convert hz0 using 1
    congr 1
  have hζ1 : ζ (Fin.last (n+1)) = 1 := hz1
  let w : ℕ → ℝ := fun i => v ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hw : Monotone w := by
    intro i j hij
    apply hv
    exact min_le_min_right n hij
  have hw0 : 0 ≤ w 0 := hv0 _
  have he : (⟨⟨n+1, hk, ζ, hz, hz0, hz1⟩, v, hv0, hv⟩ : FieldStep) =
      chainFieldStep n ζ hz hζ0 hζ1 w hw hw0 := by
    congr 1
    funext i
    apply congrArg v
    apply Fin.ext
    have hi : i.val < n+1 := i.isLt
    exact (min_eq_left (by omega : i.val ≤ n)).symm
  rw [he, fieldRecursion_chain]
  exact magneticFieldValue_nonpos _ _ (chainExponent_admissible hz hζ0 hζ1) hw hw0

 
def zeroFieldStep : FieldStep :=
  chainFieldStep 0 (uniformCut 0) (uniformCut_strict 0) (uniformCut_zero 0)
    (uniformCut_last 0) (fun _ => 0) monotone_const le_rfl

lemma fieldRecursion_zeroFieldStep : fieldRecursion zeroFieldStep = 0 := by
  rw [zeroFieldStep, fieldRecursion_chain, magneticFieldValue_zero]

lemma stepFunction_zeroFieldStep : stepFunction zeroFieldStep = fun _ => 0 := by
  funext u
  dsimp only [stepFunction, zeroFieldStep, chainFieldStep]
  simp only [ite_self, Finset.sum_const_zero]

 
lemma isingEntropy_nonneg (q : OverlapPath) : 0 ≤ isingEntropy q := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldRecursion h + (∫ u, stepFunction h u*q.val u ∂pathMeasure)/2 : ℝ) : EReal))
      zeroFieldStep
  simpa only [isingEntropy, fieldRecursion_zeroFieldStep, stepFunction_zeroFieldStep, zero_mul,
    integral_zero, zero_div, add_zero, EReal.coe_zero] using h

 
def zeroOverlapPath : OverlapPath :=
  overlapPathOfMonotone (fun _ => 0) monotone_const (by intro u; constructor <;> norm_num)

lemma zeroOverlapPath_ae : (fun _ => (0 : ℝ)) =ᵐ[pathMeasure] zeroOverlapPath.val :=
  overlapPathOfMonotone_ae _ _ _

lemma isingEntropy_zero : isingEntropy zeroOverlapPath = 0 := by
  apply le_antisymm _ (isingEntropy_nonneg _)
  apply iSup_le
  intro h
  have hi : (∫ u, stepFunction h u * zeroOverlapPath.val u ∂pathMeasure) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) ∂pathMeasure := integral_congr_ae (by
        filter_upwards [zeroOverlapPath_ae] with u hu
        rw [← hu, mul_zero])
      _ = 0 := integral_zero _ _
  simpa only [hi, zero_div, add_zero, EReal.coe_zero] using
    EReal.coe_le_coe (fieldRecursion_nonpos h)

lemma gaussianFold_measurable_bounded (L : List (ℝ × ℝ))
    (hd : ∀ sd ∈ L, 0 ≤ sd.2) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Measurable (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f) ∧
      ∀ x, |L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f x| ≤ K := by
  induction L with
  | nil => exact ⟨hf, hK⟩
  | cons sd L ih =>
    have hi := ih (fun sd hs => hd sd (List.mem_cons_of_mem _ hs))
    exact ⟨measurable_gaussianTransform hi.1 _ _,
      gaussianTransform_abs_le hi.1 hi.2 sd.1 (hd sd (List.mem_cons_self))⟩

lemma uniformPattern_abs_bound {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (q : OverlapPath) (n : ℕ) :
    |uniformPattern f q n| ≤ K := by
  apply (gaussianFold_measurable_bounded _ ?_ hf hK).2 0
  intro sd hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  simp only
  positivity

 

lemma patternFunctional_abs_bound {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (q : OverlapPath) :
    |patternFunctional f q| ≤ K := by
  exact le_of_tendsto (uniformPattern_tendsto q hf hK).abs
    (Eventually.of_forall (uniformPattern_abs_bound hf.measurable hK q))

 

theorem variationalValue_finite_of_continuous {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    (-(α*K) : EReal) ≤ variationalValue α f ∧
      variationalValue α f ≤ (α*K : ℝ) := by
  constructor
  · apply le_iInf
    intro q
    have hv : -(α*K) ≤ α*patternFunctional f q := by
      have hi := mul_le_mul_of_nonneg_left (abs_le.mp (patternFunctional_abs_bound hf hK q)).1 hα
      nlinarith
    calc
      (-(α*K) : EReal) ≤ (α*patternFunctional f q : ℝ) := by exact_mod_cast hv
      _ ≤ (α*patternFunctional f q : ℝ)+isingEntropy q := le_add_of_nonneg_right (isingEntropy_nonneg q)
  · calc
      variationalValue α f ≤ (α*patternFunctional f zeroOverlapPath : ℝ) + isingEntropy zeroOverlapPath :=
        iInf_le _ zeroOverlapPath
      _ = (α*patternFunctional f zeroOverlapPath : ℝ) := by rw [isingEntropy_zero, add_zero]
      _ ≤ (α*K : ℝ) := by
        exact_mod_cast mul_le_mul_of_nonneg_left (abs_le.mp (patternFunctional_abs_bound hf hK _)).2 hα

 

theorem variationalValue_real_of_continuous {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Continuous f) (hbounded : ∃ K : ℝ, ∀ x, |f x| ≤ K) :
    ∃ p : ℝ, variationalValue α f = (p : EReal) := by
  obtain ⟨K, hK⟩ := hbounded
  have hb := variationalValue_finite_of_continuous hα hf hK
  have hl : ⊥ < variationalValue α f := lt_of_lt_of_le (EReal.bot_lt_coe _) hb.1
  have hu : variationalValue α f < ⊤ := lt_of_le_of_lt hb.2 (EReal.coe_lt_top _)
  exact ⟨(variationalValue α f).toReal, (EReal.coe_toReal hu.ne hl.ne').symm⟩

end IsingPerceptron

end

end OAI
