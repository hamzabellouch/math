import OAI.Probability.ContinuumTransition.GrandOn

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_product_bound (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hF : GrandFinite F (A ∪ B)) (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x ≤
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F (A ∪ B) ≤ grandIntegral G A*grandIntegral H B := by
  apply tsum_le_convolution hF.summable hGF.summable hHF.summable
  intro n
  have hb := integral_binary_bound hA hB hd
    (fun k => familyIntegral G A (Fin k)) (fun k => familyIntegral H B (Fin k))
    (hF.integrable (Fin n)) ?_
  swap
  · intro s
    have hprod := integrableOn_binary_product volume A B s
      (by simpa only [← volume_pi] using hGF.integrable {i : Fin n // i ∈ s})
      (by simpa only [← volume_pi] using hHF.integrable {i : Fin n // i ∉ s})
    have hi := setIntegral_mono_on
      ((hF.integrable (Fin n)).mono_set (binaryRegion_subset_union A B s))
      (by simpa only [← volume_pi] using hprod)
      (measurableSet_binaryRegion hA hB s) (hbound n s)
    rw [show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A B s (G {i : Fin n // i ∈ s})
        (H {i : Fin n // i ∉ s})] at hi
    simp only [← volume_pi] at hi
    have heg := familyIntegral_eq_Fin G hG A {i : Fin n // i ∈ s}
    have heh := familyIntegral_eq_Fin H hH B {i : Fin n // i ∉ s}
    have hc : Fintype.card {i : Fin n // i ∈ s} = s.card := Fintype.card_coe s
    rw [hc] at heg
    have hcc : Fintype.card {i : Fin n // i ∉ s} = n-s.card := by
      have hh := Fintype.card_subtype_compl (fun i : Fin n => i ∈ s)
      simpa only [Fintype.card_fin, hc] using hh
    rw [hcc] at heh
    change (∫ x in binaryRegion A B s, F (Fin n) x) ≤ _
    calc
      _ ≤ familyIntegral G A {i : Fin n // i ∈ s}*
          familyIntegral H B {i : Fin n // i ∉ s} := hi
      _ = _ := by rw [heg, heh, Fintype.card_fin]
  have hh := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (n.factorial) : (0 : ℝ) ≤ n.factorial)
  rw [Fintype.card_fin, factorial_binomial_sum
    (fun k => familyIntegral G A (Fin k)) (fun k => familyIntegral H B (Fin k)) n] at hh
  exact hh

end ContinuumTemperature
end

end OAI
