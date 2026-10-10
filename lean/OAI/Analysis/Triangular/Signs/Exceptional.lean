import OAI.Analysis.Triangular.Certificate.Param
import OAI.Analysis.Triangular.Taylor.Taylor
import OAI.Analysis.Triangular.Auxiliary.PolynomialShift

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def freezeParameter (z : ℝ) (e : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun r => if r.val=0 then z else e r
lemma polytope_one (e : Fin 8 → ℝ) (he : ParameterPolytope e) : e 1=1 := by
  rcases he with ⟨z,w,d,u,a,r,p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl⟩
  rfl
lemma freezeParameter_mem (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {z : ℝ} (hz : 0≤z) (hzZ : z≤Z) : ParameterPolytope (freezeParameter z e) := by
  rcases he with ⟨z₀,w,d,u,a,r,p,h₀,h₁,hw,hwB,hd,hdB,hu,huB,ha,haB,hr,hrB,hp,hpB,rfl⟩
  refine ⟨z,w,d,u,a,r,p,hz,hzZ,hw,hwB,hd,hdB,hu,huB,ha,haB,hr,hrB,hp,hpB,?_⟩
  ext j
  fin_cases j <;> rfl

def frozenTaylorRow (z : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  (if r.val=0 then 0 else -taylorRow 0 1 1 l r) -
    (if r.val=1 then z*taylorRow 0 1 1 l 0 else 0)
lemma frozenTaylorRow_eval (z : ℝ) (l : ℕ) (e : Fin 8 → ℝ) (he : e 1=1) :
    (∑ r : Fin 8, frozenTaylorRow z l r*e r) =
      -∑ r : Fin 8, taylorRow 0 1 1 l r*freezeParameter z e r := by
  simp only [frozenTaylorRow,freezeParameter,Fin.sum_univ_succ,Fin.val_zero,
    ite_true,Fin.val_succ,Fin.succ_zero_eq_one]
  norm_num
  rw [he]
  ring

def frozenTaylor (z : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l : Fin 21, (∑ r : Fin 8, frozenTaylorRow z l.val r*e r)*τ^l.val
lemma frozenTaylor_eq (z : ℝ) (e : Fin 8 → ℝ) (he : e 1=1) (τ : ℝ) :
    frozenTaylor z e τ = -finiteTaylor 0 1 1 (freezeParameter z e) τ := by
  simp_rw [frozenTaylor,frozenTaylorRow_eval z _ e he,neg_mul,Finset.sum_neg_distrib]
  rw [finiteTaylor,←Fin.sum_univ_eq_sum_range]

def exceptionalWeight (test : Fin 4) (endpt : Fin 2) (j : Fin 3) : ℝ :=
  if test.val=0 then (if endpt.val=0 ∧ j.val=1 then 1 else 0)
  else if test.val=1 then (if endpt.val=0 then
    (if j.val=1 then 4*Z/3 else if j.val=2 then 2/3 else 0)
    else if j.val=2 then 1/3 else 0)
  else if test.val=2 then (if endpt.val=0 then
    (if j.val=0 then 2*Z^2 else if j.val=1 then 4*Z/3 else 1/3)
    else (if j.val=1 then 4*Z/3 else if j.val=2 then 2/3 else 0))
  else (if endpt.val=1 then (if j.val=0 then 6*Z^2 else if j.val=1 then 4*Z else 1) else 0)

def exceptionalOffset (test : Fin 4) (l : ℕ) (r : Fin 8) : ℝ :=
  if r.val=1 then (if l=0 then Q 1*(if test.val=0 then 1 else test.val*Z)
    else if l=1 ∧ test.val≠0 then Q 1 else 0) else 0

def exceptionalRow (test : Fin 4) (l : Fin 23) (r : Fin 8) : ℝ :=
  exceptionalOffset test l.val r +
    ∑ ep : Fin 2, ∑ j : Fin 3, if j.val≤l.val ∧ l.val-j.val<21 then
      exceptionalWeight test ep j * frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0

def exceptionalValue (test : Fin 4) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  let A := frozenTaylor 0 e τ
  let D := frozenTaylor Z e τ
  if test.val=0 then Q 1+τ*A
  else if test.val=1 then Q 1*(τ+Z)+(2*(τ^2+2*Z*τ)*A+τ^2*D)/3
  else if test.val=2 then Q 1*(τ+2*Z)+((τ^2+4*Z*τ+6*Z^2)*A+2*(τ^2+2*Z*τ)*D)/3
  else Q 1*(τ+3*Z)+(τ^2+4*Z*τ+6*Z^2)*D
lemma exceptionalRow_eval (test : Fin 4) (e : Fin 8 → ℝ) (he : e 1=1) (τ : ℝ) :
    (∑ l : Fin 23, (∑ r : Fin 8, exceptionalRow test l r*e r)*τ^l.val) =
      exceptionalValue test e τ := by
  have hoff : (∑ l : Fin 23, (∑ r : Fin 8, exceptionalOffset test l.val r*e r)*τ^l.val) =
      (if test.val=0 then Q 1 else Q 1*(τ+test.val*Z)) := by
    simp only [exceptionalOffset,ite_mul,zero_mul]
    fin_cases test <;> norm_num [Fin.sum_univ_succ,Fin.succ,he] <;> ring
  have hshift (ep : Fin 2) (j : Fin 3) :
      (∑ l : Fin 23, (∑ r : Fin 8,
        (if j.val≤l.val ∧ l.val-j.val<21 then
          exceptionalWeight test ep j*frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0)*e r)*τ^l.val) =
        exceptionalWeight test ep j*τ^j.val*frozenTaylor (if ep.val=0 then 0 else Z) e τ := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp_rw [mul_assoc,←Finset.mul_sum]
    have hh := PolynomialShift.shift_sum (N:=20) (M:=22) (d:=j.val) (by omega)
      (fun l => ∑ r : Fin 8, frozenTaylorRow (if ep.val=0 then 0 else Z) l r*e r) τ
    have hcond (l : Fin 23) : (j.val≤l.val ∧ l.val-j.val<21) ↔ (j.val≤l.val ∧ l.val-j.val≤20) := by omega
    have hfac (c : Prop) [Decidable c] (x : ℝ) :
        (if c then exceptionalWeight test ep j*x else 0) =
          exceptionalWeight test ep j*(if c then x else 0) := by split_ifs <;> simp
    simp only [hcond,hfac, mul_assoc,←Finset.mul_sum]
    simp only [ite_mul,zero_mul] at hh
    rw [hh]
    rfl
  simp only [exceptionalRow,add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  simp only [Finset.sum_mul] at hoff
  rw [hoff]
  have hex : (∑ l : Fin 23, (∑ r : Fin 8, ∑ ep : Fin 2, ∑ j : Fin 3,
      (if j.val≤l.val ∧ l.val-j.val<21 then
          exceptionalWeight test ep j*frozenTaylorRow (if ep.val=0 then 0 else Z) (l.val-j.val) r else 0)*e r)*τ^l.val) =
      ∑ ep : Fin 2, ∑ j : Fin 3,
        exceptionalWeight test ep j*τ^j.val*frozenTaylor (if ep.val=0 then 0 else Z) e τ := by
    simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Fin 8)) (t:=Finset.univ (α:=Fin 2)),
      Finset.sum_comm (s:=Finset.univ (α:=Fin 8)) (t:=Finset.univ (α:=Fin 3)),Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ep _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Finset.sum_mul] using hshift ep j
  simp only [Finset.sum_mul] at hex
  rw [hex]
  fin_cases test <;> norm_num [exceptionalValue,exceptionalWeight,Fin.sum_univ_succ,Fin.succ] <;> ring
end AtomicTriangular.Construction
end

end OAI
