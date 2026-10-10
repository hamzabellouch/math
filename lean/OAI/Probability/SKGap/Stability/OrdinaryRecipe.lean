import Mathlib
import OAI.Probability.SKGap.Localization.CoefficientRow

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

structure OrdinaryData (n : ℕ) (ι κ σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] where
  J : Interaction n
  j : ℝ
  H : ι→VectorFields n
  predecessor : ι→VectorFields n
  θ : κ→Spin n→ℝ
  seed : σ→Fin n→ℝ
  seedFunction : ℕ→σ→Fin n→Args (ι:=ι) (κ:=κ)→ℝ
  seedDerivative : ℕ→σ→Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ
  auxFunction : (a : ℕ)→Fin a→Fin n→Args (ι:=ι) (κ:=κ)→ℝ
  auxDerivative : (a : ℕ)→Fin a→Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

def seedCoefficient (a : ℕ) (s : σ) : VectorFields n := coefficient D.H D.θ (D.seedFunction a s)
def auxCoefficient (a : ℕ) (b : Fin a) : VectorFields n := coefficient D.H D.θ (D.auxFunction a b)
def seedPartial (a : ℕ) (l : ι) (s : σ) : VectorFields n := localPartial D.H D.θ (D.seedDerivative a s) (.inl l)
def auxPartial (a : ℕ) (l : ι) (b : Fin a) : VectorFields n := localPartial D.H D.θ (D.auxDerivative a b) (.inl l)

def sourceOf (a : ℕ) (Y : Fin a→VectorFields n) : VectorFields n := fun x i=>
  (∑s,D.seedCoefficient a s x i*D.seed s i)+(∑b,D.auxCoefficient a b x i*Y b x i)

def partialOf (a : ℕ) (l : ι) (Y : Fin a→VectorFields n) : VectorFields n := fun x i=>
  (∑s,D.seedPartial a l s x i*D.seed s i)+(∑b,D.auxPartial a l b x i*Y b x i)

def fieldOf (a : ℕ) (W Y : Fin a→VectorFields n) : VectorFields n := fun x i=>
  D.J.mulVec (D.sourceOf a Y x) i-
    D.j*(∑l,siteMean (D.partialOf a l Y) x*D.predecessor l x i)-
    D.j*∑b,siteMean (D.auxCoefficient a b) x*W b x i

def evaluate (D : OrdinaryData n ι κ σ) (a : ℕ) : VectorFields n × VectorFields n :=
  let prev := fun b : Fin a=>evaluate D b
  (D.sourceOf a (fun b=>(prev b).2),D.fieldOf a (fun b=>(prev b).1) (fun b=>(prev b).2))
termination_by a

def source (a : ℕ) : VectorFields n := (D.evaluate a).1
def auxiliary (a : ℕ) : VectorFields n := (D.evaluate a).2
def sourcePartial (a : ℕ) (l : ι) : VectorFields n := D.partialOf a l (fun b=>D.auxiliary b)

lemma source_eq (a : ℕ) : D.source a=D.sourceOf a (fun b=>D.auxiliary b) := by
  rw [source,evaluate]; rfl
lemma auxiliary_eq (a : ℕ) : D.auxiliary a=D.fieldOf a (fun b=>D.source b) (fun b=>D.auxiliary b) := by
  rw [auxiliary,evaluate]; rfl

end OrdinaryData

structure CoefficientBound (a : VectorFields n) (x : Spin n) (A R : ℝ) : Prop where
  size_nonneg : 0≤A
  row_nonneg : 0≤R
  value : ∀i,|a x i|≤A
  difference : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2

lemma CoefficientBound.small_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) :=
  hU.coefficient a ha.size_nonneg ha.row_nonneg ha.value ha.difference

lemma CoefficientBound.mean_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>siteMean a x*U x i) x (C*(A+3*R)) :=
  hU.auxiliaryCorrection a ha.size_nonneg ha.row_nonneg ha.value ha.difference

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma sourceOf_bound (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) {A R : ℝ} (C : Fin a→ℝ)
    (hY : ∀b,SmallBound (Y b) x (C b))
    (hs : ∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀b,CoefficientBound (D.auxCoefficient a b) x A R) :
    SmallBound (D.sourceOf a Y) x (((∑s,vectorNorm (D.seed s))+(∑b,C b))*(A+3*R)) := by
  have H:=(SmallBound.sum fun s=>(hs s).small_product (SmallBound.seed (D.seed s) x)).add
    (SmallBound.sum fun b=>(ha b).small_product (hY b))
  convert! H using 1
  simp only [←Finset.sum_mul,add_mul]

lemma partialOf_bound (a : ℕ) (l : ι) (Y : Fin a→VectorFields n) (x : Spin n) {A R : ℝ} (C : Fin a→ℝ)
    (hY : ∀b,SmallBound (Y b) x (C b))
    (hs : ∀s,CoefficientBound (D.seedPartial a l s) x A R)
    (ha : ∀b,CoefficientBound (D.auxPartial a l b) x A R) :
    SmallBound (D.partialOf a l Y) x (((∑s,vectorNorm (D.seed s))+(∑b,C b))*(A+3*R)) := by
  have H:=(SmallBound.sum fun s=>(hs s).small_product (SmallBound.seed (D.seed s) x)).add
    (SmallBound.sum fun b=>(ha b).small_product (hY b))
  convert! H using 1
  simp only [←Finset.sum_mul,add_mul]

lemma fieldOf_bound (a : ℕ) (W Y : Fin a→VectorFields n) (x : Spin n) (hn : 0<n)
    {A R L P C : ℝ} (B : Fin a→ℝ) (hL : 0≤L) (hP : 0≤P) (hJ : SKGap.opNorm D.J≤L)
    (hw : SmallBound (D.sourceOf a Y) x C)
    (hp : ∀l,SmallBound (D.partialOf a l Y) x C)
    (hW : ∀b,SmallBound (W b) x (B b))
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (ha : ∀b,CoefficientBound (D.auxCoefficient a b) x A R) :
    SmallBound (D.fieldOf a W Y) x
      ((L*C+|D.j| *((Fintype.card ι:ℝ)*(C*(1+3*P))))+|D.j| *((∑b,B b)*(A+3*R))) := by
  have h0 := (hw.linear D.J).mono (mul_le_mul hJ le_rfl hw.nonneg hL)
  have h1 := (SmallBound.sum fun l=>(hp l).primaryCorrection (D.predecessor l) hn hP (hm l) (hdm l)).smul D.j
  have h2 := (SmallBound.sum fun b=>(ha b).mean_product (hW b)).smul D.j
  have H:= (h0.sub h1).sub h2
  convert! H using 1
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul]

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
