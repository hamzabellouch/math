import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ContextOutput

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Selection
open scoped Classical BigOperators
noncomputable section
variable {Ω F Γ : Type} [Fintype Ω] [Fintype F] [Fintype Γ]
  {ℓ m : ℕ} {p : Law Ω} {G : Ω→Fin ℓ→F} {DD : Γ→Finset F} {B C : ℝ}

def StreamReplacement.toContextOutput (e : StreamReplacement p G Fin.val m DD B C) :
    ContextOutput p G m B C 4 := by
  let X':={x : e.X // e.μ.mass x≠0}
  let S:=univ.image e.msg
  let msg : X'→S:=fun x=>⟨e.msg x.val,mem_image.mpr ⟨x.val,mem_univ _,rfl⟩⟩
  refine ⟨X',S,inferInstance,inferInstance,e.μ.nullFree,(fun x=>e.source x.val),msg,
    (fun x=>OrderEmbedding.ofStrictMono (e.index x.val) (e.ordered x.val)),
    (fun c _=>DD c.val),?_,?_,?_,?_,?_⟩
  · intro x
    exact e.supported x.val x.property
  · intro x i
    exact e.hit x.val x.property i
  · intro c i
    obtain ⟨x,_,hx⟩:=mem_image.mp c.property
    rw [←hx]
    exact e.size x
  · intro a
    rw [Law.nullFree_map]
    exact e.dominated a
  · have he:=entropy_map_eq_of_injective (e.μ.nullFree.map msg) (Subtype.val : S→Γ) Subtype.val_injective
    rw [Law.map_map] at he
    change entropy (e.μ.nullFree.map (fun x=>e.msg x.val))=entropy (e.μ.nullFree.map msg) at he
    rw [Law.nullFree_map] at he
    exact he ▸ e.cost
end
end SharpLogRamsey.ActualHighRank

end

end OAI
