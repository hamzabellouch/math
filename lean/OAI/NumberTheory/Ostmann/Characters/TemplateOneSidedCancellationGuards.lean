import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory TemplateSupportRemoval
variable {ι : Type*} [DecidableEq ι]

def Guard.realHolds (g : Guard ι) (i : ι) (x : Other i → ℤ) (t : ℝ) : Prop :=
  let v := (argument i x g.expression).eval t/denominator g.expression
  if g.above then (if g.strict then g.threshold < v else g.threshold ≤ v)
  else (if g.strict then v < g.threshold else v ≤ g.threshold)

theorem Guard.realHolds_iff (g : Guard ι) (i : ι) (x : Other i → ℤ) (t : ℝ)
    (hg : g.expression.Valid) :
    g.realHolds i x t ↔
      if g.strict then 0 < (g.polynomial i x).eval t
      else 0 ≤ (g.polynomial i x).eval t := by
  have hp := denominator_pos g.expression hg
  rcases g with ⟨e,c,b,s⟩
  cases b <;> cases s <;>
    simp only [Guard.realHolds,Guard.polynomial,Bool.false_eq_true,ite_false,ite_true,
      Polynomial.eval_sub,Polynomial.eval_C] at *
  · rw [div_le_iff₀ hp]; constructor <;> intro h <;> nlinarith
  · rw [div_lt_iff₀ hp]; constructor <;> intro h <;> nlinarith
  · rw [le_div_iff₀ hp]; constructor <;> intro h <;> nlinarith
  · rw [lt_div_iff₀ hp]; constructor <;> intro h <;> nlinarith

def guardPolynomials {σ : Type*} (g : σ → Guard ι) (i : ι) (x : Other i → ℤ) :
    σ → Polynomial ℝ := fun s => -(g s).polynomial i x

theorem polynomialSupport_iff_realGuards {σ : Type*} (g : σ → Guard ι)
    (i : ι) (x : Other i → ℤ) (t : ℝ) (hg : ∀ s, (g s).expression.Valid) :
    polynomialSupport (guardPolynomials g i x) (fun s => (g s).strict) t ↔
      ∀ s, (g s).realHolds i x t := by
  apply forall_congr'
  intro s
  rw [Guard.realHolds_iff _ _ _ _ (hg s)]
  simp only [guardPolynomials,Polynomial.eval_neg]
  cases (g s).strict <;> simp

theorem polynomialSupport_iff_guards {σ : Type*} (g : σ → Guard ι)
    (i : ι) (x : Other i → ℤ) (t : ℤ)
    (hg : ∀ s, HistoryReconstruction.Good (insertCoordinate i x t) (g s).expression) :
    polynomialSupport (guardPolynomials g i x) (fun s => (g s).strict) (t:ℝ) ↔
      ∀ s, (g s).holds (insertCoordinate i x t) := by
  apply forall_congr'
  intro s
  rw [Guard.holds_iff _ _ _ _ (hg s)]
  simp only [guardPolynomials,Polynomial.eval_neg]
  cases (g s).strict <;> simp

def windowGuards (e : Expr ι) (lo hi : ℝ) (strictUpper : Bool) : Bool → Guard ι
  | false => ⟨e,lo,true,false⟩
  | true => ⟨e,hi,false,strictUpper⟩

omit [DecidableEq ι] in
theorem windowGuards_holds [DecidableEq ι] (e : Expr ι) (lo hi : ℝ) (strictUpper : Bool) (a : ι → ℤ) :
    (∀ b, (windowGuards e lo hi strictUpper b).holds a) ↔
      lo ≤ (e.integerEval a : ℝ) ∧
        (if strictUpper then (e.integerEval a : ℝ) < hi else (e.integerEval a : ℝ) ≤ hi) := by
  simp only [Bool.forall_bool,windowGuards,Guard.holds,Bool.false_eq_true,ite_true,ite_false]
  rfl

def binGuards (e : Expr ι) (J : ℤ) : Bool → Guard ι :=
  windowGuards e (Real.exp J) (Real.exp ((J:ℝ)+1)) true

theorem binGuards_holds_iff (e : Expr ι) (J : ℤ) (a : ι → ℤ)
    (hp : 0 < (e.integerEval a : ℝ)) :
    (∀ b, (binGuards e J b).holds a) ↔ ⌊Real.log (e.integerEval a : ℝ)⌋ = J := by
  rw [binGuards,windowGuards_holds]
  simp only [ite_true]
  rw [Int.floor_eq_iff]
  exact and_congr (Real.le_log_iff_exp_le hp).symm (Real.log_lt_iff_lt_exp hp).symm

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
