import Mathlib
import OAI.Geometry.HyperbolicGroups.FiniteFanData

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
attribute [local instance] Classical.propDecidable
namespace Mark
@[simp] lemma plain_map {F G : Type*} (e : F ≃ G) (m : Mark F) :
    (map e m).plain = m.plain := by cases m <;> rfl
end Mark
namespace IndexedFanData
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

def state (z : I) := Mark.plain ∘ D.mark z
def triangles : ℕ := ∑ z, Q (D.state z)
def turns : ℕ := ∑ z, T (D.state z)
def payments : ℕ := ∑ z, P (D.next z) (D.state z) (D.line z)
def boundary : ℕ := ∑ z, B (D.next z) (D.state z)
def isPartial (z : I) : Prop := ∃ i, D.mark z i = .absent
def partialCount : ℕ := ∑ z, if D.isPartial z then 1 else 0
def multiplicity (a : O) : ℕ := Fintype.card {f : F // D.occurrence f = a}
def maxMultiplicity : ℕ := Finset.univ.sup D.multiplicity
def weight : ℕ := max (Fintype.card I) D.maxMultiplicity

lemma sum_transport (g : (z : I) → L z → ℕ) :
    (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z),
      g ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i)) = ∑ z, ∑ i, g z i := by
  calc
    _ = ∑ z : Fin (Fintype.card I), ∑ i, g ((Fintype.equivFin I).symm z) i :=
      Finset.sum_congr rfl (fun z _ => Equiv.sum_comp (D.linkEquiv z).symm _)
    _ = _ := Equiv.sum_comp (Fintype.equivFin I).symm (fun z : I => ∑ i : L z, g z i)

lemma state_toFin (z : Fin (Fintype.card I)) (i : Fin (D.numberLink z)) :
    D.toFin.state z i = D.state ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i) := by
  simp [FanData.state,toFin,markFin,state]

lemma triangles_toFin : D.toFin.triangles = D.triangles := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z), (D.markFin z i).plain.f) = _
  simp only [markFin,Mark.plain_map]
  exact D.sum_transport (fun z i => (D.state z i).f)
lemma turns_toFin : D.toFin.turns = D.turns := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z), (D.markFin z i).plain.turn) = _
  simp only [markFin,Mark.plain_map]
  exact D.sum_transport (fun z i => (D.state z i).turn)
lemma payments_toFin : D.toFin.payments = D.payments := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z), (D.markFin z i).plain.turn *
    (State.bit (!(D.line ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i))) +
     State.bit (!(D.line ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm (D.nextFin z i)))))) = _
  simp only [markFin,Mark.plain_map,D.nextFin_symm]
  exact D.sum_transport (fun z i => (D.state z i).turn *
    (State.bit (!(D.line z i)) + State.bit (!(D.line z (D.next z i)))))
lemma boundary_toFin : D.toFin.boundary = D.boundary := by
  change (∑ z : Fin (Fintype.card I), ∑ i : Fin (D.numberLink z),
    State.boundary (D.markFin z i).plain (D.markFin z (D.nextFin z i)).plain) = _
  simp only [markFin,Mark.plain_map,D.nextFin_symm]
  exact D.sum_transport (fun z i => State.boundary (D.state z i) (D.state z (D.next z i)))

lemma partial_toFin (z : Fin (Fintype.card I)) :
    D.toFin.isPartial z ↔ D.isPartial ((Fintype.equivFin I).symm z) := by
  simp only [FanData.isPartial,toFin,markFin,Mark.map_absent,isPartial]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨(D.linkEquiv z).symm i,hi⟩
  · rintro ⟨i,hi⟩; exact ⟨D.linkEquiv z i,by simpa only [Equiv.symm_apply_apply] using hi⟩
lemma partialCount_toFin : D.toFin.partialCount = D.partialCount := by
  simp only [FanData.partialCount,D.partial_toFin,partialCount]
  exact Equiv.sum_comp (Fintype.equivFin I).symm (fun z : I => if D.isPartial z then (1 : ℕ) else 0)
lemma multiplicity_toFin (a : Fin (Fintype.card O)) :
    D.toFin.multiplicity a = D.multiplicity ((Fintype.equivFin O).symm a) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Fintype.equivFin F).symm
  intro f
  change Fintype.equivFin O (D.occurrence ((Fintype.equivFin F).symm f)) = a ↔ _
  exact (Equiv.eq_symm_apply _).symm
lemma maxMultiplicity_toFin : D.toFin.maxMultiplicity = D.maxMultiplicity := by
  change Finset.univ.sup (fun a => D.toFin.multiplicity a) = Finset.univ.sup D.multiplicity
  simp_rw [D.multiplicity_toFin]
  apply le_antisymm
  · apply Finset.sup_le
    intro a _
    exact Finset.le_sup (f := D.multiplicity) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro a _
    have hh := Finset.le_sup (s := Finset.univ) (f := fun a => D.multiplicity ((Fintype.equivFin O).symm a))
      (Finset.mem_univ (Fintype.equivFin O a))
    simpa only [Equiv.symm_apply_apply] using hh
lemma weight_toFin : D.toFin.weight = D.weight := by
  simp only [FanData.weight,weight,D.maxMultiplicity_toFin]

/-- Coordinate-free apex estimate. -/
theorem apex_bound :
    (D.turns : ℝ) + 2 * ((D.weight : ℝ) - Fintype.card F) ≤
      ((D.triangles : ℝ) + D.payments) / 2 + 2 * D.partialCount := by
  simpa only [D.turns_toFin,D.weight_toFin,D.triangles_toFin,D.payments_toFin,D.partialCount_toFin]
    using D.toFin.apex_bound
lemma triangles_le : D.triangles ≤ 5 * D.weight := by
  simpa only [D.triangles_toFin,D.weight_toFin] using D.toFin.triangles_le
lemma partial_le_boundary : 2 * D.partialCount ≤ D.boundary := by
  simpa only [D.partialCount_toFin,D.boundary_toFin] using D.toFin.partial_le_boundary

end IndexedFanData
end HyperbolicObstruction.FanLink
end
end

section

end
end

end OAI
