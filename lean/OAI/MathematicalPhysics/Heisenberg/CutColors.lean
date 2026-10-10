import OAI.MathematicalPhysics.Heisenberg.SurfaceTail

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast
attribute [-instance] instDecidableEqFin instDecidableEqProd
@[reducible] local instance cutDecEq (α : Type*) : DecidableEq α := Classical.decEq α
namespace Heisenberg.Surface
open Heisenberg.LayeredExchange
variable {V : Type*} [Fintype V]

lemma rotate_pow_zero (n k : ℕ) : ((finRotate (n+1))^k) 0=(k : Fin (n+1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,finRotate_apply]
    simp

omit [Fintype V] in
lemma transport_succ_zero (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (k : ℕ) :
    transport (finRotate (n+1)) σ 0 (k+1)=σ (k : Fin (n+1))*transport (finRotate (n+1)) σ 0 k := by
  rw [transport,rotate_pow_zero]

def extendCut (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (c : V → Bool) : Fin (n+1)×V → Bool :=
  fun z=>c ((transport (finRotate (n+1)) σ 0 z.1.val).symm z.2)

omit [Fintype V] in
lemma extendCut_invariant (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V)
    (c : V → Bool) (hc : ∀ v,c (transport (finRotate (n+1)) σ 0 (n+1) v)=c v) :
    ∀ z,extendCut n σ c (wiring (finRotate (n+1)) σ z)=extendCut n σ c z := by
  rintro ⟨t,v⟩
  rw [wiring_apply]
  unfold extendCut
  dsimp only
  by_cases ht : t=Fin.last n
  · subst t
    simp only [finRotate_last,Fin.val_zero]
    change c (σ (Fin.last n) v)=c ((transport (finRotate (n+1)) σ 0 n).symm v)
    have hh:=hc ((transport (finRotate (n+1)) σ 0 n).symm v)
    rw [transport_succ_zero] at hh
    simp only [Equiv.Perm.mul_apply,Equiv.apply_symm_apply] at hh
    have hn : (n : Fin (n+1))=Fin.last n := by ext; simp
    rw [hn] at hh
    exact hh
  · rw [coe_finRotate_of_ne_last ht,transport_succ_zero]
    have ht' : ((t.val : ℕ) : Fin (n+1))=t := by simp
    rw [ht']
    change c ((transport (finRotate (n+1)) σ 0 t.val).symm ((σ t).symm ((σ t) v))) = _
    rw [Equiv.symm_apply_apply]

def cutColorEquiv (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) :
    SlotColor.ClosedColor (wiring (finRotate (n+1)) σ) ≃
      SlotColor.ClosedColor (transport (finRotate (n+1)) σ 0 (n+1)) where
  toFun c := ⟨fun v=>c.val (0,v),invariant_cut _ _ c.val c.property 0 (n+1) (by rw [rotate_pow_zero]; simp)⟩
  invFun c := ⟨extendCut n σ c.val,extendCut_invariant n σ c.val c.property⟩
  left_inv c := by
    apply Subtype.ext
    funext z
    obtain ⟨t,v⟩:=z
    have hh:=invariant_propagates (finRotate (n+1)) σ c.val c.property 0
      ((transport (finRotate (n+1)) σ 0 t.val).symm v) t.val
    rw [rotate_pow_zero,Equiv.apply_symm_apply] at hh
    simpa [extendCut] using hh.symm
  right_inv c := by
    apply Subtype.ext
    funext v
    rfl

lemma trace_closed_colors (π : Equiv.Perm V) (f : (V → Bool) → ℝ) :
    Matrix.trace (SlotColor.matrix π*Matrix.diagonal f)=∑ c : SlotColor.ClosedColor π,f c.val := by
  rw [SlotColor.trace_diagonal,←Finset.sum_filter]
  exact Finset.sum_subtype _ (fun c=>by simp) f

theorem trace_wiring_cut (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (f : (V → Bool) → ℝ) :
    Matrix.trace (SlotColor.matrix (wiring (finRotate (n+1)) σ)*
      Matrix.diagonal (fun c=>f (fun v=>c (0,v))))=
    Matrix.trace (SlotColor.matrix (transport (finRotate (n+1)) σ 0 (n+1))*Matrix.diagonal f) := by
  have hleft:=trace_closed_colors (wiring (finRotate (n+1)) σ) (fun c=>f (fun v=>c (0,v)))
  have hright:=trace_closed_colors (transport (finRotate (n+1)) σ 0 (n+1)) f
  calc _ = ∑ c : SlotColor.ClosedColor (wiring (finRotate (n+1)) σ), f (fun v=>c.val (0,v)) := by
         with_reducible convert hleft using 1
       _ = ∑ c : SlotColor.ClosedColor (transport (finRotate (n+1)) σ 0 (n+1)),f c.val := by
         with_reducible convert (cutColorEquiv n σ).sum_comp (fun c=>f c.val) using 1
         congr! 20
       _ = _ := by with_reducible convert hright.symm using 1

end Heisenberg.Surface
end
end

end OAI
