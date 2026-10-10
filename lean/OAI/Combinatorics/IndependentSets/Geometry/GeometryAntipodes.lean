import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.GeometryDistance
import OAI.Combinatorics.IndependentSets.PCP.GeometryPointTable

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def antiPoint (s : StaticPoint L R n D) : StaticPoint L R n D :=
  ⟨s.1,fun k => s.2 k + ((D/2:ℕ):ZMod D)⟩

def antiName (t : Table L R) (i : Fin (size L R n D t)) : Fin (size L R n D t) :=
  nodeEquiv L R n D t.nu t.nv
    (((nodeEquiv L R n D t.nu t.nv).symm i).1,antiPoint L R n D ((nodeEquiv L R n D t.nu t.nv).symm i).2)

lemma antiName_exact (t : Table L R) (i : Fin (size L R n D t)) :
    names L R n D t.nu t.nv (antiName L R n D t i)=gridAntipode (names L R n D t.nu t.nv i) := by
  rw [names,antiName,Equiv.symm_apply_apply]
  rfl

def antiExpr (x : Expr) : Expr :=
  .add (.mul (Expr.quotient x (.const (staticCount L R n D))) (.const (staticCount L R n D)))
    (pointLookup L R n D (fun a : StaticPoint L R n D => (pointEquiv L R n D (antiPoint L R n D a)).val)
      (pointExpr L R n D x))

lemma antiExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (antiExpr L R n D x).eval t.bits a=(antiName L R n D t i).val := by
  simp only [antiExpr,Expr.eval,Expr.quotient_eval,hi]
  rw [pointLookup_eval L R n D _ _ _ _ ((nodeEquiv L R n D t.nu t.nv).symm i).2
    (pointExpr_code L R n D t x a i hi)]
  have he : (finFunctionFinEquiv (((nodeEquiv L R n D t.nu t.nv).symm i).1.1)).val=
      ((finProdFinEquiv.symm (finProdFinEquiv.symm i).1).1).val := by
    change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  have he' : (finFunctionFinEquiv (((nodeEquiv L R n D t.nu t.nv).symm i).1.2)).val=
      ((finProdFinEquiv.symm (finProdFinEquiv.symm i).1).2).val := by
    change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [antiName,nodeEquiv_val,he,he']
  simp only [finProdFinEquiv,Equiv.coe_fn_symm_mk,Fin.divNat,Fin.modNat]
  have h := Nat.mod_add_div (i.val/staticCount L R n D) (t.nv^n)
  rw [h]
  ring

def payloadApply (e x : Expr) : Expr := (fromTable e).subst (fun _ => x)

lemma payloadApply_eval (t : Table L R) (e x : Expr) (a : ℕ → ℕ) :
    (payloadApply e x).eval (distances L R n D t).bits a=
      e.eval t.bits (fun _ => x.eval (distances L R n D t).bits a) := by
  rw [payloadApply,Expr.subst_eval,fromTable_eval]

def antiDistanceExpr (x : Expr) : Expr := payloadApply (antiExpr L R n D (.arg 0)) x

lemma antiDistanceExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval (distances L R n D t).bits a=i.val) :
    (antiDistanceExpr L R n D x).eval (distances L R n D t).bits a=(antiName L R n D t i).val := by
  rw [antiDistanceExpr,payloadApply_eval]
  apply antiExpr_eval L R n D t (.arg 0) _ i
  exact hi

def cliqueExpr : Expr := .sum StoredFloyd.sizeExpr
  (closeExpr D (.arg 0) (antiDistanceExpr L R n D (.arg 0)))

lemma cliqueExpr_nonzero (p : SamplerParameters) (t : Table L R) (a : ℕ → ℕ) :
    (cliqueExpr L R p.n (p.m*2^p.k)).eval (distances L R p.n (p.m*2^p.k) t).bits a≠0 ↔ p.CliqueTest t.lc := by
  rw [cliqueExpr,Expr.sum_ne_zero,FloydCarry.sizeExpr_eval]
  constructor
  · rintro ⟨w,hw,h⟩
    let i : Fin (size L R p.n (p.m*2^p.k) t) := ⟨w,hw⟩
    have hi : Expr.eval (distances L R p.n (p.m*2^p.k) t).bits (Expr.bind a w) (.arg 0)=i.val := rfl
    rw [closeExpr_nonzero L R p.n (p.m*2^p.k) t _ _ _ i
      (antiName L R p.n (p.m*2^p.k) t i) hi
      (antiDistanceExpr_eval L R p.n (p.m*2^p.k) t _ _ i hi),antiName_exact] at h
    exact ⟨_,h⟩
  · rintro ⟨z,hz⟩
    obtain ⟨i,rfl⟩ := names_surjective L R p.n (p.m*2^p.k) t.nu t.nv t.hu t.hv z
    refine ⟨i.val,i.isLt,?_⟩
    have hi : Expr.eval (distances L R p.n (p.m*2^p.k) t).bits (Expr.bind a i.val) (.arg 0)=i.val := rfl
    rw [closeExpr_nonzero L R p.n (p.m*2^p.k) t _ _ _ i
      (antiName L R p.n (p.m*2^p.k) t i) hi
      (antiDistanceExpr_eval L R p.n (p.m*2^p.k) t _ _ i hi),antiName_exact]
    exact hz

end
end LargeIndependentSets.GeometryNames

end OAI
