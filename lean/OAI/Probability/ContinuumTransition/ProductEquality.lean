import OAI.Probability.ContinuumTransition.PackingBalls

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_product_lower (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hF : GrandFinite F (A ∪ B)) (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s →
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i) ≤ F (Fin n) x) :
    grandIntegral G A*grandIntegral H B ≤ grandIntegral F (A ∪ B) := by
  have hG' : RelabelInvariant (fun ι _ x => (-1 : ℝ)*G ι x) := by
    intro ι κ _ _ e x
    change (-1 : ℝ)*G ι (x ∘ e) = (-1 : ℝ)*G κ x
    rw [hG ι κ e x]
  have hh := grandIntegral_product_bound (fun ι _ x => (-1 : ℝ)*F ι x)
    (fun ι _ x => (-1 : ℝ)*G ι x) H hG' hH hA hB hd (hF.const_mul (-1))
    (hGF.const_mul (-1)) hHF (fun n s x hx => by
      have hh := neg_le_neg (hbound n s x hx)
      simpa only [neg_one_mul, neg_mul, one_mul] using hh)
  rw [grandIntegral_const_mul, grandIntegral_const_mul] at hh
  linarith

theorem grandIntegral_product_eq (F G H : ConfigFamily)
    (hG : RelabelInvariant G) (hH : RelabelInvariant H) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hF : GrandFinite F (A ∪ B)) (hGF : GrandFinite G A) (hHF : GrandFinite H B)
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x =
        G {i : Fin n // i ∈ s} (fun i => x i)*H {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F (A ∪ B) = grandIntegral G A*grandIntegral H B :=
  le_antisymm (grandIntegral_product_bound F G H hG hH hA hB hd hF hGF hHF
    (fun n s x hx => (hbound n s x hx).le))
    (grandIntegral_product_lower F G H hG hH hA hB hd hF hGF hHF
      (fun n s x hx => (hbound n s x hx).ge))

end ContinuumTemperature
end

end OAI
