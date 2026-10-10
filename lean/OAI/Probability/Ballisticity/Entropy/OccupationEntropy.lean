import Mathlib
import OAI.Probability.Ballisticity.Entropy.EntropyVariational

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience.Entropy
variable {X I : Type*} [MeasurableSpace X]

lemma restricted_exp_test (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hkl : klDiv μ ν ≠ ∞)
    (E : Set X) (hE : MeasurableSet E)
    (F : X → ℝ) (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    (∫ x, F x ∂μ.restrict E) - (∫ x, Real.exp (F x) ∂ν.restrict E) + ν.real E ≤
      (klDiv μ ν).toReal := by
  let G : X → ℝ := E.indicator F
  have hG : Measurable G := hF.indicator hE
  have hGB : ∃ B : ℝ, ∀ x, |G x| ≤ B := by
    obtain ⟨B,hB⟩ := hB
    refine ⟨max B 0,fun x => ?_⟩
    by_cases hx : x ∈ E
    · simpa [G,hx] using (hB x).trans (le_max_left B 0)
    · simp [G,hx]
  have h := entropy_exp_test_le μ ν hkl G (integrable_of_bounded hG hGB)
    (exp_integrable_of_bounded hG hGB)
  have heq : (fun x => Real.exp (G x)) =
      fun x => E.indicator (fun x => Real.exp (F x)) x + Eᶜ.indicator (fun _ => (1:ℝ)) x := by
    funext x
    by_cases hx : x ∈ E <;> simp [G,hx]
  have hei := (exp_integrable_of_bounded (μ:=ν) hF hB).indicator hE
  have hci := (integrable_const (μ:=ν) (1:ℝ)).indicator hE.compl
  rw [heq, integral_add hei hci, integral_indicator hE,
    integral_indicator_const 1 hE.compl, smul_eq_mul, mul_one,
    probReal_compl_eq_one_sub hE] at h
  rw [integral_indicator hE] at h
  linarith

noncomputable def activeSum (s : Finset I) (μ : I → Measure X) (E : I → Set X) : Measure X :=
  ∑ i ∈ s, (μ i).restrict (E i)

instance activeSum_finite (s : Finset I) (μ : I → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (E : I → Set X) : IsFiniteMeasure (activeSum s μ E) := by
  unfold activeSum
  infer_instance

lemma activeSum_integral (s : Finset I) (μ : I → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (E : I → Set X)
    (F : X → ℝ) (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    (∫ x, F x ∂activeSum s μ E) = ∑ i ∈ s, ∫ x, F x ∂(μ i).restrict (E i) := by
  unfold activeSum
  exact integral_finsetSum_measure (fun i _ => integrable_of_bounded hF hB)

lemma activeSum_mass (s : Finset I) (μ : I → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] (E : I → Set X) :
    (activeSum s μ E).real Set.univ = ∑ i ∈ s, (μ i).real (E i) := by
  have h := activeSum_integral s μ E (fun _ => (1:ℝ)) measurable_const ⟨1,fun _ => by norm_num⟩
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using h

theorem activeSum_exp_test (s : Finset I) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hkl : ∀ i ∈ s, klDiv (μ i) (ν i) ≠ ∞)
    (E : I → Set X) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (F : X → ℝ) (hF : Measurable F) (hB : ∃ B : ℝ, ∀ x, |F x| ≤ B) :
    (∫ x, F x ∂activeSum s μ E) - (∫ x, Real.exp (F x) ∂activeSum s ν E) +
      (activeSum s ν E).real Set.univ ≤ ∑ i ∈ s, (klDiv (μ i) (ν i)).toReal := by
  have heB : ∃ B : ℝ, ∀ x, |Real.exp (F x)| ≤ B := by
    obtain ⟨B,hB⟩ := hB
    exact ⟨Real.exp B,fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))⟩
  rw [activeSum_integral s μ E F hF hB,activeSum_integral s ν E _ hF.exp heB,
    activeSum_mass,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi => restricted_exp_test (μ i) (ν i) (hkl i hi)
    (E i) (hE i hi) F hF hB

theorem normalized_activeSum_kl_le [Nonempty X]
    (s : Finset I) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hkl : ∀ i ∈ s, klDiv (μ i) (ν i) ≠ ∞)
    (E : I → Set X) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hequal : ∀ i ∈ s, μ i (E i) = ν i (E i))
    (hpos : 0 < (activeSum s μ E).real Set.univ) :
    let μs : FiniteMeasure X := ⟨activeSum s μ E,inferInstance⟩
    let νs : FiniteMeasure X := ⟨activeSum s ν E,inferInstance⟩
    klDiv (μs.normalize : Measure X) (νs.normalize : Measure X) ≤
      ENNReal.ofReal ((∑ i ∈ s, (klDiv (μ i) (ν i)).toReal) /
        (activeSum s μ E).real Set.univ) := by
  let μs : FiniteMeasure X := ⟨activeSum s μ E,inferInstance⟩
  let νs : FiniteMeasure X := ⟨activeSum s ν E,inferInstance⟩
  have hm : (activeSum s ν E).real Set.univ = (activeSum s μ E).real Set.univ := by
    rw [activeSum_mass,activeSum_mass]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg ENNReal.toReal (hequal i hi).symm
  have hμne : μs ≠ 0 := by
    intro h
    have hz : (activeSum s μ E).real Set.univ = 0 := by
      change (μs : Measure X).real Set.univ = 0
      rw [h]; simp
    linarith
  have hνne : νs ≠ 0 := by
    intro h
    have hz : (activeSum s ν E).real Set.univ = 0 := by
      change (νs : Measure X).real Set.univ = 0
      rw [h]; simp
    linarith
  apply kl_le_of_expBudget
  intro F hF hB
  have h := activeSum_exp_test s μ ν hkl E hE F hF hB
  rw [hm] at h
  rw [← μs.average_eq_integral_normalize hμne,← νs.average_eq_integral_normalize hνne,
    average,average,integral_smul_measure,integral_smul_measure]
  change ((activeSum s μ E) Set.univ)⁻¹.toReal * _ -
    ((activeSum s ν E) Set.univ)⁻¹.toReal * _ + 1 ≤ _
  rw [ENNReal.toReal_inv,ENNReal.toReal_inv]
  change ((activeSum s μ E).real Set.univ)⁻¹ * _ -
    ((activeSum s ν E).real Set.univ)⁻¹ * _ + 1 ≤ _
  rw [hm]
  apply (le_div_iff₀ hpos).mpr
  field_simp
  exact h

end DirectionalTransience.Entropy

end

end OAI
