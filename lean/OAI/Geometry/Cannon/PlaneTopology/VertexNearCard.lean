import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Consecutive

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric unitInterval

attribute [local instance] Classical.propDecidable
variable {X ι : Type*} [MetricSpace X] [Fintype ι]

lemma vertex_near_card_le (H : ι → Arc ℂ) (e : ℂ → X) (x : X) (R : ℝ) :
    Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<R} ≤
      2*Nat.card {i : ι | ∃ t:I,dist (e (H i t)) x<R} := by
  classical
  let J := {i : ι // ∃ t:I,dist (e (H i t)) x<R}
  let f : J × Bool → ℂ:=fun j=>if j.2 then H j.1.val 0 else H j.1.val 1
  have hsub : {v : ℂ | Vertex H v ∧ dist (e v) x<R}⊆range f := by
    rintro v ⟨⟨i,hi|hi⟩,hv⟩
    · refine ⟨(⟨i,⟨0,hi.symm ▸ hv⟩⟩,true),?_⟩
      simpa only [f,ite_true] using hi
    · refine ⟨(⟨i,⟨1,hi.symm ▸ hv⟩⟩,false),?_⟩
      simpa only [f,Bool.false_eq_true,ite_false] using hi
  have h1:=Nat.card_mono (finite_range f) hsub
  have h2 : Nat.card (range f)≤Nat.card (J × Bool) :=
    Nat.card_le_card_of_surjective (fun j=>(⟨f j,mem_range_self j⟩:range f)) (by
      rintro ⟨w,⟨j,rfl⟩⟩; exact ⟨j,rfl⟩)
  calc
    _ ≤ Nat.card (range f) := h1
    _ ≤ Nat.card (J × Bool) := h2
    _ = _ := by
      rw [Nat.card_prod]
      change Nat.card J*Nat.card Bool=2*Nat.card J
      have hb : Nat.card Bool=2 := by norm_num
      rw [hb,Nat.mul_comm]
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
