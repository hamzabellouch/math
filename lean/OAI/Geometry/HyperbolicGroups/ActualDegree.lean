import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualPartition

namespace OAI

section
section


noncomputable section
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

lemma same_frozen_face {x y : P.Dart} {k : FrozenCell n w d} {o : Bool}
    {i : Fin ((frozenBoundary n w d).size k)} (hx : P.index x = .inr ⟨k,o,i⟩)
    (hxy : P.pairing.face.SameCycle x y) :
    ∃ o' i', P.index y = .inr ⟨k,o',i'⟩ := by
  have hk := walkKind_cycle n w d c hc f P hxy
  rw [hx] at hk
  cases hy : P.index y with
  | inl s => rw [hy] at hk; cases hk
  | inr s =>
    rcases s with ⟨k',o',i'⟩
    rw [hy] at hk
    have he : k = k' := Sum.inr.inj hk
    subst k'
    exact ⟨o',i',rfl⟩

lemma frozen_face_degree_le (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (x : P.Dart) (k : FrozenCell n w d) (o : Bool) (i : Fin ((frozenBoundary n w d).size k))
    (hx : P.index x = .inr ⟨k,o,i⟩) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 12 := by
  let F := {y : P.Dart // P.pairing.face.SameCycle x y}
  have hF (y : F) : ∃ p : Bool × Fin ((frozenBoundary n w d).size k), P.index y.val = .inr ⟨k,p.1,p.2⟩ := by
    obtain ⟨o',i',he⟩ := same_frozen_face n w d c hc f P hx y.property
    exact ⟨⟨o',i'⟩,he⟩
  let g : F → Bool × Fin ((frozenBoundary n w d).size k) := fun y => (hF y).choose
  have hg (y : F) : P.index y.val = .inr ⟨k,(g y).1,(g y).2⟩ := (hF y).choose_spec
  have hinj : Function.Injective g := by
    intro y z he
    apply Subtype.ext
    apply P.normalized_index_inj hs _ hm (y.property.symm.trans z.property)
    rw [hg,hg,he]
  have hcard := Fintype.card_le_of_injective g hinj
  rw [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hcard
  have hk : (frozenBoundary n w d).size k ≤ 6 := by rcases k with k | (k | k) <;> norm_num [frozenBoundary,frozenCell,size]
  exact hcard.trans (by omega)

/-- The uniform degree bound for the literal dual multigraph.
Degree counts side copies, so parallel edges and loops are not discarded. -/
theorem actual_face_degree_le (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f)) (F : P.Face) :
    Fintype.card {y : P.Dart // P.faceClass y = F} ≤ 15 := by
  have he : Fintype.card {y : P.Dart // P.faceClass y = F} =
      Fintype.card {y : P.Dart // P.pairing.face.SameCycle F.out y} := by
    apply Fintype.card_congr (Equiv.subtypeEquivRight _)
    intro y
    rw [← P.faceClass_eq,P.faceClass_out,eq_comm]
  rw [he]
  cases hx : P.index F.out with
  | inl s =>
    let B := mappedMacroPolygon n w d c hc f P hs hb F.out s.1 s.2 hx
    exact B.perimeter_le
  | inr s =>
    rcases s with ⟨k,o,i⟩
    exact (frozen_face_degree_le n w d c hc f P hs hm F.out k o i hx).trans (by decide)

/-- With a small sparse partition, the closed normal picture is empty. -/
theorem normal_empty_of_sparse_partition {I : Type*} [Fintype I] (part : P.Face → I)
    {K : ℕ} {α β δ η : ℝ} (ha : 0 < α) (hbeta : 7*α < β) (hd : 0 < δ)
    (heta : 2*η < defectConstant α β δ)
    (hgood : Occurrences.GoodUpTo (8*K) α β δ (Sum.elim w d))
    (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (hb : P.NoBigon)
    (hsize : ∀ i, Fintype.card {F : P.Face // part F = i} ≤ K)
    (hcut : (Fintype.card (CutContact P.pairing (part ∘ P.faceClass)) : ℝ) ≤ η*Fintype.card P.Face) :
    IsEmpty P.Dart := by
  have halpha : 0 ≤ α := by
    have hdefect := defectConstant_pos ha hbeta hd
    have hbound : defectConstant α β δ ≤ α / 5 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hdefect, hbound]
  have h := actual_partition_bound n w d c hc f P part halpha hgood hs hm hred hrad hb
    (fun i => Nat.mul_le_mul_left 8 (hsize i))
  simp only [← Nat.card_eq_fintype_card] at h hcut
  have hz : (Nat.card P.Face : ℝ) = 0 := by
    have hnonneg := Nat.cast_nonneg (α := ℝ) (Nat.card P.Face)
    nlinarith
  have hf : Fintype.card P.Face = 0 := by rw [← Nat.card_eq_fintype_card]; exact_mod_cast hz
  have : IsEmpty P.Face := Fintype.card_eq_zero_iff.mp hf
  exact ⟨fun x => isEmptyElim (P.faceClass x)⟩

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
