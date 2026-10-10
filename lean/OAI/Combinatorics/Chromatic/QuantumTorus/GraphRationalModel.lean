import Mathlib
import OAI.Combinatorics.Chromatic.Model
import OAI.Combinatorics.Chromatic.Walls.RationalIntervalModel

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
variable {n:ℕ} (G:ElementaryPositivity.NaturalUnitIntervalGraph n)

def extendedH (i:ℕ) : ℕ := if hi:i < n then (G.h ⟨i,hi⟩).val else i
lemma extendedH_monotone : Monotone G.extendedH := by
  intro i j hij
  unfold extendedH
  split_ifs with hi hj
  · exact G.increasing hij
  · have hv: (G.h ⟨i,hi⟩).val < n := (G.h ⟨i,hi⟩).isLt
    omega
  · omega
  · exact hij

lemma rational_model : ∃t:Fin n → ℚ, (∀i,0 < t i) ∧ StrictMono t ∧
    ∀i j,i < j → (j≤G.h i → t j < t i+1) ∧ (G.h i < j → t i+1 < t j) := by
  obtain ⟨t,ht,he⟩:=ElementaryPositivity.rational_interval_prefix G.extendedH G.extendedH_monotone n
  refine ⟨fun i=>t i.val,fun i=>ht i.val i.isLt,?_,?_⟩
  · intro i j hij
    exact (he i.val j.val hij j.isLt).1
  · intro i j hij
    have H: G.extendedH i.val=(G.h i).val:=by simp [extendedH,i.isLt]
    change (j.val≤(G.h i).val → _) ∧ ((G.h i).val < j.val → _)
    simpa only [H] using (he i.val j.val hij j.isLt).2
end ElementaryPositivity.NaturalUnitIntervalGraph

namespace ElementaryPositivity
structure PhaseLabel (n:ℕ) where
  val:Fin n
  deriving DecidableEq, Fintype

lemma phase_rank {n:ℕ} (f:Fin n → ℚ) : ∃r:Equiv.Perm (Fin n),
    ∀i j,r i < r j ↔ f i < f j ∨ (f i=f j ∧ i < j) := by
  let key:PhaseLabel n → Lex (ℚ×Fin n):=fun a=>toLex (f a.val,a.val)
  have hkey:Function.Injective key:=by
    intro a b h
    have hh:=congrArg (fun p:Lex (ℚ×Fin n)=>(ofLex p).2) h
    cases a; cases b; congr 1
  let : LinearOrder (PhaseLabel n):=LinearOrder.lift' key hkey
  let e:Fin n ≃o PhaseLabel n:=Fintype.orderIsoFinOfCardEq (k:=n) (PhaseLabel n) (by
    let e:PhaseLabel n ≃ Fin n:={toFun:=PhaseLabel.val,invFun:=PhaseLabel.mk,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
    exact (Fintype.card_congr e).trans (Fintype.card_fin n))
  let r:Equiv.Perm (Fin n):={
    toFun:=fun i=>e.symm ⟨i⟩
    invFun:=fun i=>(e i).val
    left_inv:=fun i=>congrArg PhaseLabel.val (e.apply_symm_apply ⟨i⟩)
    right_inv:=fun i=>e.symm_apply_apply i }
  refine ⟨r,fun i j=>?_⟩
  change e.symm (PhaseLabel.mk i) < e.symm (PhaseLabel.mk j) ↔ _
  rw [e.symm.lt_iff_lt]
  change key (PhaseLabel.mk i) < key (PhaseLabel.mk j) ↔ _
  exact Prod.Lex.lt_iff
end ElementaryPositivity

end

end OAI
