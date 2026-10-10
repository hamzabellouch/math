import OAI.Combinatorics.BalancedRyser.Candidates.ExposedExternalSum
import OAI.Combinatorics.BalancedRyser.Candidates.ExternalWitnessModel

namespace OAI

namespace Balanced.ExternalAssembly

noncomputable section
open scoped Classical BigOperators
open MeasureTheory CandidateValidityWitness CandidateExposure
open ExposedOppositeSum ExposedExternalSum ExposedWitnessProbability
open ExposedExternalFresh FreshWitnessProbability
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance freshGeneratorMeasurableSpace : MeasurableSpace F := ⊤

theorem witness_probability_le_lines (g : Direction F) (w : WitnessKey F)
    (law : PMF (MergedPairs F)) :
    (law.toOuterMeasure (witnessEvent g w)).toReal ≤
      ∑ c : F, (law.toOuterMeasure
        (externalEvent w.1.1 (g,c) w.2.1 w.2.2 w.1.2.1 w.1.2.2)).toReal := by
  apply (real_probability_mono_support (E := witnessEvent g w)
    (G := {M | ∃ c : F, M ∈ externalEvent w.1.1 (g,c)
      w.2.1 w.2.2 w.1.2.1 w.1.2.2}) law ?_).trans
    (probability_exists_le_sum _ _)
  rintro M ⟨hw, _⟩
  obtain ⟨hs, _, _, _, _, _, _, x, hx, _, hd, he⟩ := hw
  exact ⟨lineEval g (tuplePoint M w.1.1 0), hs, x, hx, hd, he⟩

omit [Fintype F] in
theorem witness_probability_eq_zero_of_first_target (g : Direction F)
    (w : WitnessKey F) (h : w.2.1 = g) (law : PMF (MergedPairs F)) :
    (law.toOuterMeasure (witnessEvent g w)).toReal = 0 := by
  have he : witnessEvent g w = ∅ := by
    ext M
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    exact hw.2.2.2.1 h
  rw [he]
  simp

omit [Fintype F] in
theorem witness_probability_eq_zero_of_second_generator (g : Direction F)
    (w : WitnessKey F) (h : w.2.2 ∈ generatorSet w.1.1)
    (law : PMF (MergedPairs F)) :
    (law.toOuterMeasure (witnessEvent g w)).toReal = 0 := by
  have he : witnessEvent g w = ∅ := by
    ext M
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    exact hw.2.2.2.2.2.2.1 h
  rw [he]
  simp

theorem old_key_probability_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (w : WitnessKey F)
    (hT : w.1.1 ∈ freshTuples D) (hdD : w.2.1 ∈ D) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure (witnessEvent g w)).toReal ≤
      2 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
  by_cases hd : w.2.1 = g
  · rw [witness_probability_eq_zero_of_first_target g w hd]
    positivity
  obtain ⟨hi, hf⟩ := (Finset.mem_filter.mp hT).2
  apply (witness_probability_le_lines g w _).trans
  calc
    _ ≤ ∑ _c : F, 2 * (Fintype.card F : ℝ)⁻¹ ^ 5 := by
      apply Finset.sum_le_sum
      intro c _
      exact successful_external_probability_le D a w.1.1 hi hf (g,c)
        w.2.1 hdD hd w.1.2.1
        (fun M x => PairWitness M w.2.2 x (tuplePoint M w.1.1 w.1.2.2))
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

theorem old_fresh_key_probability_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (w : WitnessKey F)
    (hT : w.1.1 ∈ freshTuples D) (hdD : w.2.1 ∈ D) (heD : w.2.2 ∉ D) :
    ((CandidateExposure.exposedLaw D a).toOuterMeasure (witnessEvent g w)).toReal ≤
      4 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
  by_cases hd : w.2.1 = g
  · rw [witness_probability_eq_zero_of_first_target g w hd]
    positivity
  by_cases he : w.2.2 ∈ generatorSet w.1.1
  · rw [witness_probability_eq_zero_of_second_generator g w he]
    positivity
  obtain ⟨hi, hf⟩ := (Finset.mem_filter.mp hT).2
  apply (witness_probability_le_lines g w _).trans
  calc
    _ ≤ ∑ _c : F, 4 * (Fintype.card F : ℝ)⁻¹ ^ 7 := by
      apply Finset.sum_le_sum
      intro c _
      exact successful_external_fresh_probability_le D a w.1.1 hi hf (g,c)
        w.2.1 hdD hd w.2.2 heD he w.1.2.1 w.1.2.2
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

def freshGeneratorLabels (D E : Finset (Direction F)) : Finset (WitnessKey F) :=
  (freshTuples D ×ˢ Finset.univ) ×ˢ (D ×ˢ E)

theorem filter_freshGeneratorLabels (g : Direction F) (D E : Finset (Direction F))
    (M : MergedPairs F) :
    (freshGeneratorLabels D E).filter (fun w => M ∈ witnessEvent g w) =
      (witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∈ E) := by
  ext w
  have hi : M ∈ witnessEvent g w → Function.Injective w.1.1.generator := fun h => h.1.1
  simp only [freshGeneratorLabels, freshTuples, witnesses, Finset.mem_filter,
    Finset.mem_product, Finset.mem_univ, true_and, and_true]
  tauto

theorem freshGenerators_oldOld_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∈ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤ 8192 * (D.card : ℝ)^2 := by
  simp_rw [← filter_freshGeneratorLabels]
  rw [integral_eventCount_eq_sum]
  calc
    _ ≤ ∑ _w ∈ freshGeneratorLabels D D, 2 * (Fintype.card F : ℝ)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro w hw
      rcases Finset.mem_product.mp hw with ⟨hTi, hde⟩
      exact old_key_probability_le g D a w (Finset.mem_product.mp hTi).1
        (Finset.mem_product.mp hde).1
    _ = ((freshTuples D).card : ℝ) * 16 * (D.card : ℝ)^2 *
        (2 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      simp only [Finset.sum_const, nsmul_eq_mul, freshGeneratorLabels,
        Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * 16 * (D.card : ℝ)^2 *
        (2 * (Fintype.card F : ℝ)⁻¹ ^ 4) := by
      have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
        exact_mod_cast freshTuples_card_le D
      gcongr
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
      ring

theorem freshGenerators_oldFresh_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) :
    (∫ M, (((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∉ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤ 32768 * (D.card : ℝ) / Fintype.card F := by
  let E : Finset (Direction F) := Finset.univ \ D
  have hE (e : Direction F) : e ∈ E ↔ e ∉ D := by simp [E]
  have hfilter (M : MergedPairs F) :
      (witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∉ D) =
      (freshGeneratorLabels D E).filter (fun w => M ∈ witnessEvent g w) := by
    rw [filter_freshGeneratorLabels]
    simp only [hE]
  simp_rw [hfilter]
  rw [integral_eventCount_eq_sum]
  have hc : ((freshTuples D).card : ℝ) ≤ 256 * (Fintype.card F : ℝ)^4 := by
    exact_mod_cast freshTuples_card_le D
  have he : (E.card : ℝ) ≤ 2 * Fintype.card F := by
    have hx := Finset.card_le_univ E
    have hq : 0 < Fintype.card F := Fintype.card_pos
    simp only [Direction, Fintype.card_option] at hx
    exact_mod_cast (show E.card ≤ 2 * Fintype.card F by omega)
  calc
    _ ≤ ∑ _w ∈ freshGeneratorLabels D E, 4 * (Fintype.card F : ℝ)⁻¹ ^ 6 := by
      apply Finset.sum_le_sum
      intro w hw
      rcases Finset.mem_product.mp hw with ⟨hTi, hde⟩
      exact old_fresh_key_probability_le g D a w (Finset.mem_product.mp hTi).1
        (Finset.mem_product.mp hde).1 ((hE _).mp (Finset.mem_product.mp hde).2)
    _ = ((freshTuples D).card : ℝ) * 16 * D.card * E.card *
        (4 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by
      simp only [Finset.sum_const, nsmul_eq_mul, freshGeneratorLabels,
        Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ (256 * (Fintype.card F : ℝ)^4) * 16 * D.card *
        (2 * Fintype.card F) * (4 * (Fintype.card F : ℝ)⁻¹ ^ 6) := by gcongr
    _ = _ := by
      have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
      ring

theorem freshGenerators_firstOld_integral_le (g : Direction F)
    (D : Finset (Direction F)) (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (∫ M, (((witnesses g M).filter (fun w =>
      (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D)).card : ℝ)
      ∂(CandidateExposure.exposedLaw D a).toMeasure) ≤
      8192 * (m : ℝ)^2 + 32768 * m := by
  have heq (M : MergedPairs F) :
      (((witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D)).card : ℝ) =
      (((witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∈ D)).card : ℝ) +
      (((witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D ∧ w.2.2 ∉ D)).card : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := (witnesses g M).filter (fun w =>
        (∀ i, w.1.1.generator i ∉ D) ∧ w.2.1 ∈ D)) (fun w => w.2.2 ∈ D)
    simp only [Finset.filter_filter, and_assoc] at hc
    exact_mod_cast hc.symm
  simp_rw [heq]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  have hm : (D.card : ℝ) ≤ m := by exact_mod_cast hD
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  apply (add_le_add (freshGenerators_oldOld_integral_le g D a)
    (freshGenerators_oldFresh_integral_le g D a)).trans
  have hdiv : 32768 * (D.card : ℝ) / Fintype.card F ≤ 32768 * (D.card : ℝ) :=
    div_le_self (by positivity) hq
  apply (add_le_add le_rfl hdiv).trans
  gcongr

end
end Balanced.ExternalAssembly

end OAI
