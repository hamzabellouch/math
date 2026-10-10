import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationData
import OAI.NumberTheory.Ostmann.Characters.TemplateLeafSymbolic
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCoordinates

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval
variable {ι : Type*} [DecidableEq ι]

def sectionPolynomial (i : ι) (x : Other i → ℤ) (P : MvPolynomial ι ℤ) : Polynomial ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℝ))
    (fun j => if h : j=i then Polynomial.X else Polynomial.C (x ⟨j,h⟩ : ℝ)) P

theorem sectionPolynomial_eval (i : ι) (x : Other i → ℤ) (P : MvPolynomial ι ℤ) (t : ℤ) :
    (sectionPolynomial i x P).eval (t:ℝ) =
      (MvPolynomial.eval (insertCoordinate i x t) P : ℝ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [sectionPolynomial,MvPolynomial.eval₂_C,MvPolynomial.eval_C]
    simp
  | add P Q ih ih' => simpa only [sectionPolynomial,MvPolynomial.eval₂_add,
      Polynomial.eval_add,MvPolynomial.eval_add,Int.cast_add] using congrArg₂ (·+·) ih ih'
  | mul_X P j ih =>
    simp only [sectionPolynomial,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,
      Polynomial.eval_mul,MvPolynomial.eval_mul,MvPolynomial.eval_X,Int.cast_mul]
    rw [show (MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℝ))
      (fun j => if h : j=i then Polynomial.X else Polynomial.C (x ⟨j,h⟩ : ℝ)) P).eval (t:ℝ)=
        (MvPolynomial.eval (insertCoordinate i x t) P : ℝ) from ih]
    congr 1
    by_cases hj : j=i <;> simp [hj,insertCoordinate]

def argument (i : ι) (x : Other i → ℤ) (e : Expr ι) : Polynomial ℝ :=
  Polynomial.C (e.denominator : ℝ)*sectionPolynomial i x e.numerator

def denominator (e : Expr ι) : ℝ := (e.denominator : ℝ)^2

theorem denominator_pos {ι : Type*} [DecidableEq ι]
    (e : Expr ι) (he : e.Valid) : 0 < denominator e := by
  exact sq_pos_of_ne_zero (by exact_mod_cast e.denominator_ne_zero he)

theorem argument_eval (i : ι) (x : Other i → ℤ) (e : Expr ι) (t : ℤ)
    (he : e.IntegralAt (insertCoordinate i x t)) :
    (argument i x e).eval (t:ℝ) = denominator e*(e.integerEval (insertCoordinate i x t):ℝ) := by
  have hc := e.integerEval_cleared (insertCoordinate i x t) he
  have hcR : (e.denominator:ℝ)*(e.integerEval (insertCoordinate i x t):ℝ)=
      (MvPolynomial.eval (insertCoordinate i x t) e.numerator:ℝ) := by exact_mod_cast hc
  simp only [argument,Polynomial.eval_mul,Polynomial.eval_C,sectionPolynomial_eval]
  rw [← hcR]
  simp only [denominator,pow_two,mul_assoc]

theorem argument_ratio_eval (i : ι) (x : Other i → ℤ) (e : Expr ι) (t : ℤ)
    (he : HistoryReconstruction.Good (insertCoordinate i x t) e) :
    (argument i x e).eval (t:ℝ)/denominator e = (e.integerEval (insertCoordinate i x t):ℝ) := by
  rw [argument_eval i x e t he.2]
  exact mul_div_cancel_left₀ _ (denominator_pos e he.1).ne'

structure Guard (ι : Type*) where
  expression : Expr ι
  threshold : ℝ
  above : Bool
  strict : Bool

def Guard.holds (g : Guard ι) (a : ι → ℤ) : Prop :=
  let v : ℝ := g.expression.integerEval a
  if g.above then (if g.strict then g.threshold < v else g.threshold ≤ v)
  else (if g.strict then v < g.threshold else v ≤ g.threshold)

def Guard.polynomial (g : Guard ι) (i : ι) (x : Other i → ℤ) : Polynomial ℝ :=
  if g.above then argument i x g.expression-Polynomial.C (denominator g.expression*g.threshold)
  else Polynomial.C (denominator g.expression*g.threshold)-argument i x g.expression

theorem Guard.holds_iff (g : Guard ι) (i : ι) (x : Other i → ℤ) (t : ℤ)
    (hg : HistoryReconstruction.Good (insertCoordinate i x t) g.expression) :
    g.holds (insertCoordinate i x t) ↔
      if g.strict then 0 < (g.polynomial i x).eval (t:ℝ)
      else 0 ≤ (g.polynomial i x).eval (t:ℝ) := by
  have hp := denominator_pos g.expression hg.1
  have he := argument_eval i x g.expression t hg.2
  rcases g with ⟨e,c,b,s⟩
  cases b <;> cases s <;>
    simp only [Guard.holds,Guard.polynomial,Bool.false_eq_true,ite_false,ite_true,
      Polynomial.eval_sub,Polynomial.eval_C] at * <;>
    rw [he] <;> constructor <;> intro h <;> nlinarith

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
