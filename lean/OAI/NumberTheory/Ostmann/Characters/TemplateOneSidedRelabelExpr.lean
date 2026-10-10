import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetSampled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationResidues

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedRelabel
open SymbolicHistory TemplateOneSidedCancellation
variable {ι κ ν : Type*}

def relabel (π : ι → κ) (e : Expr ι) : Expr κ := substitute (fun i=>.atom (π i)) e

@[simp] theorem relabel_integerEval (π : ι → κ) (e : Expr ι) (a : κ → ℤ) :
    (relabel π e).integerEval a = e.integerEval (fun i=>a (π i)) := by
  exact substitute_eval _ e a

@[simp] theorem relabel_rationalEval (π : ι → κ) (e : Expr ι) (a : κ → ℚ) :
    (relabel π e).rationalEval a = e.rationalEval (fun i=>a (π i)) := by
  induction e <;> simp_all [relabel,substitute,Expr.rationalEval]

@[simp] theorem relabel_denominator (π : ι → κ) (e : Expr ι) :
    (relabel π e).denominator = e.denominator := by
  induction e <;> simp_all [relabel,substitute,Expr.denominator]

@[simp] theorem relabel_valid (π : ι → κ) (e : Expr ι) :
    (relabel π e).Valid ↔ e.Valid := by
  induction e <;> simp_all [relabel,substitute,Expr.Valid]

@[simp] theorem relabel_integralAt (π : ι → κ) (e : Expr ι) (a : κ → ℤ) :
    (relabel π e).IntegralAt a ↔ e.IntegralAt (fun i=>a (π i)) := by
  induction e <;> simp_all [relabel,substitute,Expr.IntegralAt,substitute_eval,Expr.integerEval]

@[simp] theorem relabel_good (π : ι → κ) (e : Expr ι) (a : κ → ℤ) :
    HistoryReconstruction.Good a (relabel π e) ↔
      HistoryReconstruction.Good (fun i=>a (π i)) e := by
  simp only [HistoryReconstruction.Good,relabel_valid,relabel_integralAt]

@[simp] theorem relabel_syntaxSize (π : ι → κ) (e : Expr ι) :
    (relabel π e).syntaxSize = e.syntaxSize := by
  induction e <;> simp_all [relabel,substitute,Expr.syntaxSize]

@[simp] theorem relabel_degreeBudget (π : ι → κ) (e : Expr ι) :
    (relabel π e).degreeBudget = e.degreeBudget := by
  induction e <;> simp_all [relabel,substitute,Expr.degreeBudget]

@[simp] theorem relabel_fixedBound (π : ι → κ) (e : Expr ι) (B : ℝ) :
    (relabel π e).FixedBound B ↔ e.FixedBound B := by
  induction e <;> simp_all [relabel,substitute,Expr.FixedBound]

@[simp] theorem relabel_fixedLogBound (π : ι → κ) (e : Expr ι) (H : ℝ) :
    (relabel π e).FixedLogBound H ↔ e.FixedLogBound H :=
  relabel_fixedBound π e (Real.exp H)

@[simp] theorem relabel_supportModulus (π : ι → κ) (e : Expr ι) :
    (relabel π e).supportModulus = e.supportModulus := by
  have hd (q : Expr ι) : (substitute (fun i=>Expr.atom (π i)) q).denominator = q.denominator :=
    relabel_denominator π q
  induction e <;> simp_all [relabel,substitute,Expr.supportModulus]

@[simp] theorem relabel_numerator (π : ι → κ) (e : Expr ι) :
    (relabel π e).numerator = MvPolynomial.rename π e.numerator := by
  have hd (q : Expr ι) : (substitute (fun i=>Expr.atom (π i)) q).denominator = q.denominator :=
    relabel_denominator π q
  induction e <;> simp_all [relabel,substitute,Expr.numerator]

@[simp] theorem relabel_totalDegree (π : ι ≃ κ) (e : Expr ι) :
    (relabel π e).numerator.totalDegree = e.numerator.totalDegree := by
  rw [relabel_numerator]
  exact MvPolynomial.totalDegree_renameEquiv π e.numerator

@[simp] theorem relabel_comp (π : ι → κ) (ρ : κ → ν) (e : Expr ι) :
    relabel ρ (relabel π e) = relabel (fun i=>ρ (π i)) e := by
  induction e <;> simp_all [relabel,substitute]

@[simp] theorem relabel_id (e : Expr ι) : relabel (fun i=>i) e = e := by
  induction e <;> simp_all [relabel,substitute]

theorem relabel_numerator_ne_zero (π : ι ≃ κ) (e : Expr ι) :
    (relabel π e).numerator ≠ 0 ↔ e.numerator ≠ 0 := by
  rw [relabel_numerator]
  constructor
  · intro h he
    exact h (by rw [he]; exact map_zero _)
  · intro h he
    apply h
    apply MvPolynomial.rename_injective π π.injective
    simpa only [map_zero] using he

end Ostmann.Characters.TemplateOneSidedRelabel

end

end OAI
