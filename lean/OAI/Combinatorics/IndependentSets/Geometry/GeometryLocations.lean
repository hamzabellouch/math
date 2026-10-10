import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.Witness
import OAI.Combinatorics.IndependentSets.Machines.ExprTables
import OAI.Combinatorics.IndependentSets.PCP.GeometryPointTable

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC PhaseTest Coefficient
open scoped Classical BigOperators
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters)

abbrev Outcome := (p.law L R).Expanded
abbrev outcomeCount := Fintype.card (Outcome L R p)
abbrev vertexCount (t : Table L R) := t.ne^p.n*outcomeCount L R p

lemma vertexCount_pos (t : Table L R) : 0<vertexCount L R p t :=
  Nat.mul_pos (pow_pos t.he _) Fintype.card_pos

def vertexEquiv (t : Table L R) : p.Vertices L R (Fin t.ne) ≃ Fin (vertexCount L R p t) :=
  (Equiv.prodCongr finFunctionFinEquiv (Fintype.equivFin (Outcome L R p))).trans finProdFinEquiv

def scheduleLC (f : Fin p.n → L → R) : LabelCoverData Unit Unit L R (Fin p.n) :=
  ⟨fun _ => (),fun _ => (),f⟩

def samplePoint (f : Fin p.n → L → R) (o : Outcome L R p) : StaticPoint L R p.n (p.m*2^p.k) :=
  ⟨(p.location (scheduleLC L R p f) (id,o)).1.1,
    (p.location (scheduleLC L R p f) (id,o)).2⟩

lemma samplePoint_decode (t : Table L R) (v : p.Vertices L R (Fin t.ne)) :
    decode (fun k => t.left (v.1 k)) (fun k => t.right (v.1 k))
      (samplePoint L R p (fun k => t.project (v.1 k)) v.2)=p.location t.lc v := by
  rfl

def locationName (t : Table L R) (v : p.Vertices L R (Fin t.ne)) : Fin (size L R p.n (p.m*2^p.k) t) :=
  nodeEquiv L R p.n (p.m*2^p.k) t.nu t.nv
    ((fun k => t.left (v.1 k),fun k => t.right (v.1 k)),
      samplePoint L R p (fun k => t.project (v.1 k)) v.2)

lemma locationName_exact (t : Table L R) (v : p.Vertices L R (Fin t.ne)) :
    names L R p.n (p.m*2^p.k) t.nu t.nv (locationName L R p t v)=p.location t.lc v := by
  rw [names,locationName,Equiv.symm_apply_apply]
  exact samplePoint_decode L R p t v

def vertexCountExpr : Expr := .mul (Expr.power neExpr p.n) (.const (outcomeCount L R p))
def outcomeExpr (x : Expr) : Expr := Expr.remainder x (.const (outcomeCount L R p))
def chainExpr (x : Expr) (k : Fin p.n) : Expr :=
  Expr.remainder (Expr.quotient (Expr.quotient x (.const (outcomeCount L R p)))
    (Expr.power neExpr k.val)) neExpr

@[simp] lemma vertexCountExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (vertexCountExpr L R p).eval t.bits a=vertexCount L R p t := by
  simp [vertexCountExpr,Expr.eval,vertexCount]

lemma chainExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (vertexCount L R p t))
    (hi : x.eval t.bits a=i.val) (k : Fin p.n) :
    (chainExpr L R p x k).eval t.bits a=(((vertexEquiv L R p t).symm i).1 k).val := by
  simp only [chainExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,neExpr_eval,Expr.eval,hi]
  rfl

lemma outcomeExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (vertexCount L R p t))
    (hi : x.eval t.bits a=i.val) :
    (outcomeExpr L R p x).eval t.bits a=
      (Fintype.equivFin (Outcome L R p) ((vertexEquiv L R p t).symm i).2).val := by
  simp only [outcomeExpr,Expr.remainder_eval,Expr.eval,hi]
  change _=(Fintype.equivFin _ ((Fintype.equivFin _).symm _)).val
  rw [Equiv.apply_symm_apply]
  rfl

def scheduleTest (x : Expr) (f : Fin p.n → L → R) : Expr :=
  Expr.listAll (List.finRange p.n) fun k =>
    Expr.equal (fieldExpr (chainExpr L R p x k) 2) (.const (projectCode (f k)))

lemma scheduleTest_nonzero (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (vertexCount L R p t))
    (hi : x.eval t.bits a=i.val) (f : Fin p.n → L → R) :
    (scheduleTest L R p x f).eval t.bits a≠0 ↔
      f=fun k => t.project (((vertexEquiv L R p t).symm i).1 k) := by
  have hh (k : Fin p.n) : (fieldExpr (chainExpr L R p x k) 2).eval t.bits a=
      projectCode (t.project (((vertexEquiv L R p t).symm i).1 k)) := by
    simpa using fieldExpr_eval t a (chainExpr L R p x k)
      (((vertexEquiv L R p t).symm i).1 k) (chainExpr_eval L R p t x a i hi k) (2:Fin 3)
  simp only [scheduleTest,Expr.listAll_eval,List.mem_finRange,forall_true_left]
  split_ifs with h
  · simp only [ne_eq,one_ne_zero,not_false_eq_true,true_iff]
    funext k
    have hk := h k
    rw [Expr.equal_eval,hh,Expr.eval] at hk
    have hc : projectCode (t.project (((vertexEquiv L R p t).symm i).1 k))=projectCode (f k) := by
      split_ifs at hk with he
      · exact he
      · exact False.elim (hk rfl)
    exact ((Fintype.equivFin (L → R)).injective (Fin.ext hc)).symm
  · simp only [ne_eq,not_true_eq_false,false_iff]
    intro he
    apply h
    intro k
    rw [Expr.equal_eval,hh,Expr.eval,he]
    simp

def scheduleCodeExpr (x : Expr) : Expr :=
  Expr.pick (fun f : Fin p.n → L → R => (Fintype.equivFin _ f).val) (scheduleTest L R p x)

lemma scheduleCodeExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (vertexCount L R p t))
    (hi : x.eval t.bits a=i.val) :
    (scheduleCodeExpr L R p x).eval t.bits a=
      (Fintype.equivFin (Fin p.n → L → R) (fun k => t.project (((vertexEquiv L R p t).symm i).1 k))).val := by
  apply Expr.pick_eval
  exact scheduleTest_nonzero L R p t x a i hi

def samplePointExpr (x : Expr) : Expr :=
  Expr.static2 (fun f o => (pointEquiv L R p.n (p.m*2^p.k) (samplePoint L R p f o)).val)
    (scheduleCodeExpr L R p x) (outcomeExpr L R p x)

lemma samplePointExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (vertexCount L R p t))
    (hi : x.eval t.bits a=i.val) :
    (samplePointExpr L R p x).eval t.bits a=
      (pointEquiv L R p.n (p.m*2^p.k) (samplePoint L R p
        (fun k => t.project (((vertexEquiv L R p t).symm i).1 k)) ((vertexEquiv L R p t).symm i).2)).val := by
  apply Expr.static2_eval
  · exact scheduleCodeExpr_eval L R p t x a i hi
  · exact outcomeExpr_eval L R p t x a i hi

def tupleCodeExpr (base : Expr) (f : Fin p.n → Expr) : Expr :=
  Expr.listSum (List.finRange p.n) (fun k => .mul (f k) (Expr.power base k.val))

lemma tupleCodeExpr_eval (s : List Bool) (a : ℕ → ℕ) (base : Expr) (f : Fin p.n → Expr)
    {m : ℕ} (v : Fin p.n → Fin m) (hb : base.eval s a=m) (hf : ∀ k, (f k).eval s a=(v k).val) :
    (tupleCodeExpr p base f).eval s a=(finFunctionFinEquiv v).val := by
  simp only [tupleCodeExpr,Expr.listSum_eval,Expr.eval,Expr.power_eval,hb,hf,finFunctionFinEquiv_apply]
  rw [← List.ofFn_eq_map,List.sum_ofFn]

def locationExpr (x : Expr) : Expr :=
  .add (.mul (.add (.mul (tupleCodeExpr p nuExpr (fun k => fieldExpr (chainExpr L R p x k) 0))
        (Expr.power nvExpr p.n))
      (tupleCodeExpr p nvExpr (fun k => fieldExpr (chainExpr L R p x k) 1)))
      (.const (staticCount L R p.n (p.m*2^p.k)))) (samplePointExpr L R p x)

lemma locationExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (vertexCount L R p t))
    (hi : x.eval t.bits a=i.val) :
    (locationExpr L R p x).eval t.bits a=
      (locationName L R p t ((vertexEquiv L R p t).symm i)).val := by
  have hf (k : Fin p.n) (j : Fin 3) := fieldExpr_eval t a (chainExpr L R p x k)
    (((vertexEquiv L R p t).symm i).1 k) (chainExpr_eval L R p t x a i hi k) j
  have hu : ∀ k, (fieldExpr (chainExpr L R p x k) 0).eval t.bits a=
      (t.left (((vertexEquiv L R p t).symm i).1 k)).val := by
    intro k; simpa using hf k 0
  have hv : ∀ k, (fieldExpr (chainExpr L R p x k) 1).eval t.bits a=
      (t.right (((vertexEquiv L R p t).symm i).1 k)).val := by
    intro k; simpa using hf k 1
  simp only [locationExpr,Expr.eval,Expr.power_eval,nvExpr_eval,
    tupleCodeExpr_eval p _ _ _ _ _ (nuExpr_eval t a) hu,
    tupleCodeExpr_eval p _ _ _ _ _ (nvExpr_eval t a) hv,samplePointExpr_eval L R p t x a i hi]
  rw [locationName,nodeEquiv_val]
  ring

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
