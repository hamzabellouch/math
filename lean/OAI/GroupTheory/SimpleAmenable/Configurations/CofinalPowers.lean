import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FiniteGroupHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace CofinalPowers

variable {P:Type} [CommMonoid P]
noncomputable def sequence (x:P) : ℕ ⥤ ActionCategory P P where
  obj n := (x^n:P)
  map {n m} f := ⟨x^(m-n),by
    change x^(m-n)*x^n=x^m
    rw [←pow_add,Nat.sub_add_cancel (leOfHom f)]⟩
  map_id n := by
    apply Functor.Elements.hom_ext
    change x^(n-n)=1
    simp
  map_comp {n m k} f g := by
    apply Functor.Elements.hom_ext
    change x^(k-n)=x^(k-m)*x^(m-n)
    rw [←pow_add]
    congr 1
    have h:=leOfHom f; have h':=leOfHom g; omega
lemma final (x:P) (hx:∀p:P,∃q n,p*q=x^n) : (sequence x).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro p
    obtain ⟨q,n,h⟩:=hx p.back
    exact ⟨n,⟨⟨q,by change q*p.back=x^n; simpa only [mul_comm] using h⟩⟩⟩
  · intro p n f g
    obtain ⟨q,k,h⟩:=hx p.back
    refine ⟨n+k,homOfLE (Nat.le_add_right n k),?_⟩
    apply Functor.Elements.hom_ext
    change x^(n+k-n)*f.hom=x^(n+k-n)*g.hom
    rw [Nat.add_sub_cancel_left]
    have eh : f.hom*p.back=g.hom*p.back:=f.map_val.trans g.map_val.symm
    rw [←h]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using congrArg (fun p:P=>p*q) eh
noncomputable def colimitIso {A:Type*} [Category A] (x:P) (hx:∀p:P,∃q n,p*q=x^n)
    (F:ActionCategory P P ⥤ A) [HasColimit F] [HasColimit (sequence x ⋙ F)] :
    colimit (sequence x ⋙ F) ≅ colimit F := by
  haveI := final x hx
  exact Functor.Final.colimitIso (sequence x) F
lemma finite_colimit_iff {R:Type} [Ring R] (x:P) (hx:∀p:P,∃q n,p*q=x^n)
    (F:ActionCategory P P ⥤ ModuleCat R) (N n:ℕ) (hn:N≤n)
    (hf : ∀ m : ℕ, N ≤ m → IsIso (F.map ((sequence x).map (homOfLE (Nat.le_succ m))))) :
    Module.Finite R (F.obj ((sequence x).obj n)) ↔ Module.Finite R (colimit F:ModuleCat R) := by
  exact (FixedStageReturn.finite_stage_iff_colimit (sequence x ⋙ F) N n hf hn).trans
    (Module.Finite.equiv_iff (colimitIso x hx F).toLinearEquiv)
end CofinalPowers

end

end OAI
