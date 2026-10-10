import OAI.NumberTheory.Ostmann.Construction.InitialMovingData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalWeightRelabel

namespace OAI

/-! # The two original cutoff weights commute with the alphabet inclusion -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_map {A B : Type*} (e : B → A) (b r : ℕ)
    (fallback : B) (L : List B) :
    initialRegularFromList b r (e fallback) (L.map e) =
      e ∘ initialRegularFromList b r fallback L := by
  funext i
  simp only [initialRegularFromList, List.getD_map, Function.comp_apply]

theorem initialMovingCutoffWeight_map {A B : Type*} (e : B → A) (value : A → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → B)
    (y : MovingRegularSlot 0 (r + r) (b + b) → B) :
    initialMovingCutoffWeight value b d r cb cd (e ∘ sl) (e ∘ sr) (e ∘ y) =
      initialMovingCutoffWeight (value ∘ e) b d r cb cd sl sr y := rfl

theorem initialMovingDataCutoff_map {A B : Type*} (e : B → A) (value : A → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → B) (fallback : B)
    {n : ℕ} (T : MovingSlotData B n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd (e ∘ sl) (e ∘ sr) (e fallback) (T.map e) s =
      initialMovingDataCutoff (value ∘ e) b d r cb cd sl sr fallback T s := by
  simp only [initialMovingDataCutoff, MovingSlotData.regularSlots_map,
    initialRegularFromList_map, initialMovingCutoffWeight_map]

end Ostmann

end OAI
