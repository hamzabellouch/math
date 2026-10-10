import OAI.Probability.ContinuumTransition.BadEndpoints

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_mono (F G : ConfigFamily) {A : Set Space} (hA : MeasurableSet A)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : ∀ n, IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : Summable (familyTerm F A)) (hGs : Summable (familyTerm G A))
    (hbound : ∀ n (x : Fin n → Space), (∀ i, x i ∈ A) → F (Fin n) x ≤ G (Fin n) x) :
    grandIntegral F A ≤ grandIntegral G A := by
  apply hFs.tsum_le_tsum _ hGs
  intro n
  change familyIntegral F A (Fin n)/(n.factorial : ℝ) ≤
    familyIntegral G A (Fin n)/(n.factorial : ℝ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold familyIntegral
  apply setIntegral_mono_on (hFi n) (hGi n)
  · convert MeasurableSet.iInter (fun i : Fin n => hA.preimage
      (measurable_pi_apply i : Measurable (fun x : Fin n → Space => x i))) using 1
    ext x
    simp
  · exact hbound n

theorem grandIntegral_nonneg (F : ConfigFamily) (A : Set Space)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) :
    0 ≤ grandIntegral F A := tsum_nonneg (familyTerm_nonneg F A hF)

theorem grandIntegral_mono_set (F : ConfigFamily) {A B : Set Space} (hAB : A ⊆ B)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ B})
    (hAs : Summable (familyTerm F A)) (hBs : Summable (familyTerm F B)) :
    grandIntegral F A ≤ grandIntegral F B := by
  apply hAs.tsum_le_tsum _ hBs
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply setIntegral_mono_set (hFi n) (Filter.Eventually.of_forall (hF0 (Fin n)))
  exact Filter.Eventually.of_forall (fun x hx i => hAB (hx i))

theorem familyTerm_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) (n : ℕ) :
    familyTerm (fun ι _ x => c*F ι x) A n = c*familyTerm F A n := by
  unfold familyTerm familyIntegral
  rw [integral_const_mul]
  ring

theorem grandIntegral_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) :
    grandIntegral (fun ι _ x => c*F ι x) A = c*grandIntegral F A := by
  unfold grandIntegral
  simp_rw [familyTerm_const_mul]
  exact tsum_mul_left

theorem familyTerm_add (F G : ConfigFamily) (A : Set Space) (n : ℕ)
    (hFi : IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A}) :
    familyTerm (fun ι _ x => F ι x+G ι x) A n = familyTerm F A n+familyTerm G A n := by
  unfold familyTerm familyIntegral
  rw [integral_add hFi hGi, add_div]

theorem grandIntegral_add (F G : ConfigFamily) (A : Set Space)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : ∀ n, IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : Summable (familyTerm F A)) (hGs : Summable (familyTerm G A)) :
    grandIntegral (fun ι _ x => F ι x+G ι x) A = grandIntegral F A+grandIntegral G A := by
  unfold grandIntegral
  simp_rw [familyTerm_add F G A _ (hFi _) (hGi _)]
  exact hFs.tsum_add hGs

theorem familyTerm_sum {κ : Type} [Fintype κ] (F : κ → ConfigFamily)
    (A : Set Space) (n : ℕ)
    (hFi : ∀ j, IntegrableOn (F j (Fin n)) {x | ∀ i, x i ∈ A}) :
    familyTerm (fun ι _ x => ∑ j, F j ι x) A n = ∑ j, familyTerm (F j) A n := by
  unfold familyTerm familyIntegral
  rw [integral_finsetSum _ (fun j _ => hFi j), Finset.sum_div]

theorem grandIntegral_sum {κ : Type} [Fintype κ] (F : κ → ConfigFamily)
    (A : Set Space)
    (hFi : ∀ j n, IntegrableOn (F j (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : ∀ j, Summable (familyTerm (F j) A)) :
    grandIntegral (fun ι _ x => ∑ j, F j ι x) A = ∑ j, grandIntegral (F j) A := by
  unfold grandIntegral
  simp_rw [familyTerm_sum F A _ (fun j => hFi j _)]
  exact Summable.tsum_finsetSum (fun j _ => hFs j)

end ContinuumTemperature
end

end OAI
