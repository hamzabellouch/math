import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFullNormal
import OAI.Geometry.HyperbolicGroups.ActualFragment

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma all_area : actualArea n w d c hc f P (fun _ => true) = Fintype.card P.Face := by
  apply Fintype.card_congr
  exact { toFun := Subtype.val
          invFun := fun x => ⟨x,rfl⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

lemma area_le_darts (select : P.Face → Bool) :
    actualArea n w d c hc f P select ≤ Fintype.card P.Dart := by
  have h1 : Fintype.card (SelectedFace n w d c hc f P select) ≤ Fintype.card P.Face :=
    Fintype.card_le_of_injective _ Subtype.val_injective
  exact h1.trans (Fintype.card_le_of_surjective P.faceClass (fun x => ⟨x.out,P.faceClass_out x⟩))

lemma all_boundary_zero : actualBoundary n w d c hc f P (fun _ => true) = 0 := by
  have : IsEmpty (ActualRawBoundary n w d c hc f P (fun _ => true)) :=
    ⟨fun x => x.property.2.2 rfl⟩
  have : IsEmpty (RadialBoundarySide n w d c hc f P (fun _ => true)) :=
    ⟨fun x => x.property.2.2 rfl⟩
  simp only [actualBoundary,Fintype.card_of_isEmpty,Nat.add_zero]

/-- A bounded closed normal picture has no faces. This uses the genuine
rank event for its size, not an abstract incidence or link assumption. -/
theorem small_normal_empty {M : ℕ} {α β δ : ℝ}
    (ha : 0 < α) (hbeta : 7*α < β) (hd : 0 < δ)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hM : 8 * actualArea n w d c hc f P (fun _ => true) ≤ M) : IsEmpty P.Dart := by
  have hh := actual_fragment_bound n w d c hc f P (fun _ => true) hs hm hred hrad ha.le hgood hb hM
  rw [all_boundary_zero,all_area] at hh
  simp only [← Nat.card_eq_fintype_card,Nat.cast_zero] at hh
  have hk := defectConstant_pos ha hbeta hd
  have hz : Fintype.card P.Face = 0 := by
    rw [← Nat.card_eq_fintype_card]
    have hz : (Nat.card P.Face : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast (le_antisymm hz (Nat.cast_nonneg (α := ℝ) (Nat.card P.Face)))
  have : IsEmpty P.Face := Fintype.card_eq_zero_iff.mp hz
  exact ⟨fun x => isEmptyElim (P.faceClass x)⟩

/-- Bounded spherical-chain vanishing: the checked finite surgeries produce
normal form and preserve the literal chain. No topological realization is
asserted by this combinatorial statement. -/
theorem small_closed_chain_zero {M : ℕ} {α β δ : ℝ}
    (ha : 0 < α) (hbeta : 7*α < β) (hd : 0 < δ)
    (hgood : Occurrences.GoodUpTo M α β δ (Sum.elim w d))
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hM : 8 * Fintype.card P.Dart ≤ M) : P.chain = 0 := by
  obtain ⟨Q,⟨hPQ⟩,hmQ,hsQ,hbQ,hrQ,hradQ,hchain,_⟩ := normalizedPicture n w d c hc f P hm
  have hcard : Fintype.card Q.Dart ≤ Fintype.card P.Dart :=
    Fintype.card_le_of_injective hPQ.map hPQ.injective
  have hA := area_le_darts n w d c hc f Q (fun _ => true)
  have : IsEmpty Q.Dart := small_normal_empty n w d c hc f Q ha hbeta hd hgood hsQ hmQ hrQ hradQ hbQ (by omega)
  rw [← hchain]
  simp only [WalkPicture.chain,Finset.univ_eq_empty,Finset.sum_empty]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
