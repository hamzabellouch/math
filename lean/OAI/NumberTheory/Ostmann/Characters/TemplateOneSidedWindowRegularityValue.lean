import OAI.NumberTheory.Ostmann.Characters.HistorySymbolicSupport
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightLog

namespace OAI

noncomputable section
namespace Ostmann.Characters.SymbolicHistory.Expr
variable {ι : Type*}

theorem integerEval_abs_le_numerator (e : Expr ι) (x : ι → ℤ)
    (hg : HistoryReconstruction.Good x e) :
    |(e.integerEval x : ℝ)| ≤ |(MvPolynomial.eval x e.numerator : ℝ)| := by
  have hd : (1:ℝ) ≤ |(e.denominator:ℝ)| := by
    exact_mod_cast Int.one_le_abs (e.denominator_ne_zero hg.1)
  have he : (e.denominator:ℝ)*(e.integerEval x:ℝ) =
      (MvPolynomial.eval x e.numerator:ℝ) := by
    exact_mod_cast e.integerEval_cleared x hg.2
  rw [← he,abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) hd

theorem integerEval_abs_le_exp_size (e : Expr ι) {H : ℝ} (hH : Real.log 2 ≤ H)
    (he : e.FixedLogBound H) (x : ι → ℤ) (hx : ∀ i, |(x i:ℝ)| ≤ Real.exp H)
    (hg : HistoryReconstruction.Good x e) :
    |(e.integerEval x:ℝ)| ≤ Real.exp ((e.syntaxSize:ℝ)*H) :=
  (e.integerEval_abs_le_numerator x hg).trans
    (e.integer_numerator_abs_le_exp_size hH he x hx)

theorem integerEval_log_le_size (e : Expr ι) {H : ℝ} (hH : Real.log 2 ≤ H)
    (he : e.FixedLogBound H) (x : ι → ℤ) (hx : ∀ i, |(x i:ℝ)| ≤ Real.exp H)
    (hg : HistoryReconstruction.Good x e) (hp : 0 < e.integerEval x) :
    Real.log (e.integerEval x:ℝ) ≤ (e.syntaxSize:ℝ)*H := by
  have hpR : (0:ℝ) < (e.integerEval x:ℝ) := by exact_mod_cast hp
  have hh := e.integerEval_abs_le_exp_size hH he x hx hg
  rw [abs_of_pos hpR] at hh
  simpa only [Real.log_exp] using Real.log_le_log hpR hh

end Ostmann.Characters.SymbolicHistory.Expr

end

end OAI
