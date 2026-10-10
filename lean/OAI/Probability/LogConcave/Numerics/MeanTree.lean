import Mathlib
import OAI.Probability.LogConcave.Sampling.PrimitiveExpectedField

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

inductive MeanTree (X : Type*) [MeasurableSpace X] (d : ℕ) where
  | node (k : ℕ) (base : X → Point d) (measurable_base : Measurable base)
      (coeff scale : Fin k → ℝ) (center : Fin k → MeanTree X d)

namespace MeanTree
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def eval (F : Point d → ℝ) : MeanTree X d → X → Point d
  | .node _ b _ a r E,z => b z+∑i,a i • primitiveExpectedField F (eval F (E i) z) (r i)

def depth : MeanTree X d → ℕ
  | .node _ _ _ _ _ E => Finset.univ.sup (fun i => depth (E i)+1)

def terms : MeanTree X d → ℕ
  | .node k .. => k

def weight : MeanTree X d → ℝ
  | .node _ _ _ a _ _ => ∑i,|a i|

def anchor (b : X → Point d) (hb : Measurable b) : MeanTree X d :=
  .node 0 b hb Fin.elim0 Fin.elim0 Fin.elim0

def zero : MeanTree X d := anchor (fun _ => 0) measurable_const

def scale (s : ℝ) : MeanTree X d → MeanTree X d
  | .node k b hb a r E => .node k (fun z => s • b z) (by fun_prop) (fun i => s*a i) r E

def add : MeanTree X d → MeanTree X d → MeanTree X d
  | .node k b hb a r E,.node l c hc v t D =>
    .node (k+l) (fun z => b z+c z) (by fun_prop)
      (Fin.addCases a v) (Fin.addCases r t) (Fin.addCases E D)

def mean (r : ℝ) (E : MeanTree X d) : MeanTree X d :=
  .node 1 (fun _ => 0) measurable_const (fun _ => 1) (fun _ => r) (fun _ => E)

@[simp] theorem eval_anchor (F : Point d → ℝ) (b : X → Point d) (hb : Measurable b) (z : X) :
    eval F (anchor b hb) z=b z := by simp [eval,anchor]
@[simp] theorem eval_zero (F : Point d → ℝ) (z : X) : eval F zero z=0 := by simp [zero]
@[simp] theorem eval_scale (F : Point d → ℝ) (s : ℝ) (E : MeanTree X d) (z : X) :
    eval F (scale s E) z=s • eval F E z := by
  cases E
  simp only [eval,scale,smul_add,Finset.smul_sum,smul_smul]
@[simp] theorem eval_add (F : Point d → ℝ) (E D : MeanTree X d) (z : X) :
    eval F (add E D) z=eval F E z+eval F D z := by
  cases E; cases D
  simp only [eval,add,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
  abel
@[simp] theorem eval_mean (F : Point d → ℝ) (r : ℝ) (E : MeanTree X d) (z : X) :
    eval F (mean r E) z=primitiveExpectedField F (eval F E z) r := by
  simp [mean,eval]

@[simp] theorem depth_anchor (b : X → Point d) (hb : Measurable b) : depth (anchor b hb)=0 := by
  simp [anchor,depth]
@[simp] theorem depth_zero : depth (zero : MeanTree X d)=0 := by simp [zero]
@[simp] theorem depth_scale (s : ℝ) (E : MeanTree X d) : depth (scale s E)=depth E := by
  cases E; rfl
@[simp] theorem depth_mean (r : ℝ) (E : MeanTree X d) : depth (mean r E)=depth E+1 := by
  simp [mean,depth]

theorem depth_add_le (E D : MeanTree X d) {N : ℕ} (hE : depth E≤N) (hD : depth D≤N) :
    depth (add E D)≤N := by
  cases E with | node k b hb a r C =>
    cases D with | node l c hc v t B =>
      simp only [depth,Finset.sup_le_iff,Finset.mem_univ,true_implies] at hE hD
      simp only [add,depth,Finset.sup_le_iff,Finset.mem_univ,true_implies]
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.addCases_left] using hE j
      · simpa only [Fin.addCases_right] using hD j

def sumFin : (k : ℕ) → (Fin k → MeanTree X d) → MeanTree X d
  | 0,_ => zero
  | k+1,E => add (E 0) (sumFin k (fun i => E i.succ))

@[simp] lemma eval_sumFin (F : Point d → ℝ) (k : ℕ) (E : Fin k → MeanTree X d) (z : X) :
    eval F (sumFin k E) z=∑i,eval F (E i) z := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => simp only [sumFin,eval_add,ih,Fin.sum_univ_succ]

lemma depth_sumFin_le (k : ℕ) (E : Fin k → MeanTree X d) {N : ℕ}
    (hE : ∀i,depth (E i)≤N) : depth (sumFin k E)≤N := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => exact depth_add_le (E 0) (sumFin k _) (hE 0) (ih _ (fun i => hE i.succ))

def sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) : MeanTree X d :=
  sumFin (Fintype.card I) (fun i => E ((Fintype.equivFin I).symm i))

@[simp] lemma eval_sumFamily {I : Type*} [Fintype I] (F : Point d → ℝ)
    (E : I → MeanTree X d) (z : X) :
    eval F (sumFamily E) z=∑i,eval F (E i) z := by
  rw [sumFamily,eval_sumFin]
  exact (Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl))
lemma depth_sumFamily_le {I : Type*} [Fintype I] (E : I → MeanTree X d) {N : ℕ}
    (hE : ∀i,depth (E i)≤N) : depth (sumFamily E)≤N :=
  depth_sumFin_le _ _ (fun _ => hE _)

def conditional (r ρ : ℝ) (x y : MeanTree X d) : MeanTree X d :=
  mean (r*Real.sqrt (1-ρ^2)) (add x (scale (r*ρ) y))

lemma conditionalFieldMean_primitive {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r ρ : ℝ) (y : Point d) (ha : 0<1-ρ^2) :
    conditionalFieldMean F x r ρ y=
      primitiveExpectedField F (x+(r*ρ) • y) (r*Real.sqrt (1-ρ^2)) := by
  rw [conditionalFieldMean,←conditionalLaw_map hF x r ρ y ha]
  rw [integral_map (by fun_prop) (primitiveField_contDiff hF x r).continuous.aestronglyMeasurable]
  unfold primitiveExpectedField
  simp only [primitiveField,smul_add,smul_smul]
  congr 1
  funext z
  congr 1
  abel

@[simp] lemma eval_conditional {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r ρ : ℝ) (x y : MeanTree X d) (z : X) (ha : 0<1-ρ^2) :
    eval F (conditional r ρ x y) z=conditionalFieldMean F (eval F x z) r ρ (eval F y z) := by
  simp only [conditional,eval_mean,eval_add,eval_scale]
  exact (conditionalFieldMean_primitive hF _ r ρ _ ha).symm

lemma depth_conditional_le (r ρ : ℝ) (x y : MeanTree X d) {N : ℕ}
    (hx : depth x≤N) (hy : depth y≤N) : depth (conditional r ρ x y)≤N+1 := by
  simp only [conditional,depth_mean]
  exact Nat.add_le_add_right (depth_add_le _ _ hx (by simpa using hy)) 1

end MeanTree
end LogConcaveSampling

end

end

end OAI
