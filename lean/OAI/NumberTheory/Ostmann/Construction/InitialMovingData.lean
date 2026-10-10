import Mathlib.Data.List.GetD
import OAI.NumberTheory.Ostmann.Construction.InitialMovingCutoff
import OAI.NumberTheory.Ostmann.Construction.InitialMovingSupport

namespace OAI

/-! # The original cutoff weight as a function of the actual leaf data -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def initialRegularFromList {P : Type*} (b r : ℕ) (fallback : P)
    (L : List P) : MovingRegularSlot 0 (r + r) (b + b) → P :=
  fun i => L.getD ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).val fallback

theorem initialRegularFromList_mapped {P : Type*} (b r : ℕ) (fallback : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialRegularFromList b r fallback ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = y := by
  funext i
  unfold initialRegularFromList
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map] using ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).isLt)]
  rw [List.getElem_map]
  change y ((movingTemplateSlotList 0 (r + r) (b + b)).get
    ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i)) = y i
  rw [← movingTemplateListEquiv_apply, Equiv.apply_symm_apply]

/-- Internal states use the same total function, while only terminal data
are evaluated as leaves. The fallback is never used on a genuine template. -/
noncomputable def initialMovingDataCutoff {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) :
    {n : ℕ} → MovingSlotData P n → ℤ → ℂ :=
  fun {_n} T s => if s = 0 then 0 else
    initialMovingCutoffWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback T.regularSlots)

theorem initialMovingDataCutoff_zero {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) {n : ℕ} (T : MovingSlotData P n) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T 0 = 0 := by
  simp only [initialMovingDataCutoff, ↓reduceIte]

theorem initialMovingDataCutoff_leaf (P : Finset ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s v : ℤ) :
    initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback
      (initialMovingState P b r XL XR y s).data v =
      if v = 0 then 0 else initialMovingCutoffWeight (fun p : P => (p : ℕ))
        b d r cb cd sl sr y := by
  simp only [initialMovingDataCutoff, initialMovingState, MovingSlotData.regularSlots,
    initialRegularFromList_mapped]

theorem initialMovingState_modulus (P : Finset ℕ) (b r : ℕ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    movingSlotModulus (fun p : P => (p : ℕ)) (initialMovingState P b r XL XR y s) =
      (XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ) := by
  have ht := movingTemplate_product (fun p : P => (p : ℕ)) 0 (r + r) (b + b) y
  have h : MovingSlotReversal.naturalProduct (fun p : P => (p : ℕ))
      ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = ∏ i, (y i : ℕ) := by
    simpa only [MovingSlotReversal.naturalProduct, movingTemplateSlotList, List.map_append,
      List.map_map, Function.comp_def] using ht
  change (XL : ℕ) * (XR : ℕ) * _ = _
  rw [h]

theorem initialMovingLeaf_value {I : Type*} [Fintype I]
    (P : Finset ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) (hs : s ≠ 0)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hw : initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y ≠ 0 →
      (((XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback)
      g Dq Finset.univ (𝓕 ψ) X lo hi (initialMovingState P b r XL XR y s) s =
    initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y *
      normalizedFourierProfile (fun t => 𝓕 ψ t) s
        ((((XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ) : ℕ) : ℝ) / X) *
      ∏ i, spectatorHistoryLeaf (fun _ : Unit => (XL : ℕ) * (XR : ℕ) * ∏ j, (y j : ℕ))
        (g i) (Dq i) () s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_leaf]
  simp only [hs, ite_false]
  unfold movingFourierLeaf
  simp only [initialMovingState_modulus]
  by_cases hz : initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y = 0
  · simp only [hz, ite_self, zero_mul]
  · rw [ite_eq_left (hw hz)]
    simp only [spectatorHistoryLeaf, initialMovingState_modulus]

end Ostmann

end OAI
