import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCoordinates
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters
open MvPolynomial

namespace SymbolicHistory.Expr
variable {ι : Type*}

theorem cleared_abs_le_exp_size (e : Expr ι) {H : ℝ} (hH : Real.log 2≤H)
    (he : e.FixedLogBound H) (x : ι → ℝ) (hx : ∀i,|x i|≤Real.exp H) :
    |eval₂ (Int.castRingHom ℝ) x e.numerator|≤Real.exp ((e.syntaxSize:ℝ)*H) ∧
      |(e.denominator:ℝ)|≤Real.exp ((e.syntaxSize:ℝ)*H) := by
  have htwo : (2:ℝ)≤Real.exp H := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr hH
  have h := e.cleared_abs_le_pow_size htwo he x hx
  simpa only [← Real.exp_nat_mul] using h

theorem integer_numerator_abs_le_exp_size (e : Expr ι) {H : ℝ} (hH : Real.log 2≤H)
    (he : e.FixedLogBound H) (x : ι → ℤ) (hx : ∀i,|(x i:ℝ)|≤Real.exp H) :
    |((eval x e.numerator:ℤ):ℝ)|≤Real.exp ((e.syntaxSize:ℝ)*H) := by
  have h := (e.cleared_abs_le_exp_size hH he (fun i => (x i:ℝ)) hx).1
  have heval := MvPolynomial.eval₂_comp (Int.castRingHom ℝ) x e.numerator
  change ((eval x e.numerator:ℤ):ℝ)=_ at heval
  rw [heval]
  exact h

end SymbolicHistory.Expr

namespace TemplateSupportRemoval
open SymbolicHistory
variable {ι : Type*} [DecidableEq ι]

theorem erased_numerator_abs_le_exp_size (i : ι) (e : Expr ι) {H : ℝ}
    (hH : Real.log 2≤H) (he : e.FixedLogBound H)
    (x : Other i → ℤ) (hx : ∀j,|(x j:ℝ)|≤Real.exp H) :
    |((eval x (eraseCoordinate i e.numerator):ℤ):ℝ)|≤Real.exp ((e.syntaxSize:ℝ)*H) := by
  rw [eval_eraseCoordinate]
  apply e.integer_numerator_abs_le_exp_size hH he
  intro j
  by_cases hj : j=i
  · simp only [insertCoordinate,hj,↓reduceDIte,Int.cast_zero,abs_zero]
    exact (Real.exp_pos _).le
  · simpa only [insertCoordinate,hj,↓reduceDIte] using hx ⟨j,hj⟩

theorem erased_numerator_log_abs_le_size (i : ι) (e : Expr ι) {H : ℝ}
    (hH : Real.log 2≤H) (he : e.FixedLogBound H)
    (x : Other i → ℤ) (hx : ∀j,|(x j:ℝ)|≤Real.exp H)
    (hne : eval x (eraseCoordinate i e.numerator)≠0) :
    Real.log |((eval x (eraseCoordinate i e.numerator):ℤ):ℝ)|≤(e.syntaxSize:ℝ)*H := by
  have hp : 0 < |((eval x (eraseCoordinate i e.numerator):ℤ):ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hne
  have h := Real.log_le_log hp (erased_numerator_abs_le_exp_size i e hH he x hx)
  simpa only [Real.log_exp] using h

theorem erased_numerator_log_size_on_support (i : ι) (e : Expr ι) {H : ℝ}
    (hH : Real.log 2≤H) (he : e.FixedLogBound H) (S : Other i → Finset ℤ)
    (hS : ∀j a,a∈S j → |(a:ℝ)|≤Real.exp H) :
    ∀x,(∀j,x j∈S j) → eval x (eraseCoordinate i e.numerator)≠0 →
      Real.log |((eval x (eraseCoordinate i e.numerator):ℤ):ℝ)|≤(e.syntaxSize:ℝ)*H := by
  intro x hx hne
  exact erased_numerator_log_abs_le_size i e hH he x (fun j => hS j _ (hx j)) hne

end TemplateSupportRemoval
end Ostmann.Characters

end

end OAI
