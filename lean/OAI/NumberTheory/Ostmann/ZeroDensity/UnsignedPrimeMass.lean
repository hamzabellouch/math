import OAI.NumberTheory.Ostmann.ZeroDensity.VonMangoldtPole
import OAI.NumberTheory.Ostmann.ZeroDensity.RealPrimeSeries

namespace OAI

/-! # The total logarithmic prime mass near one, from the proved zeta pole -/

namespace Ostmann

open scoped BigOperators
open Complex LSeries

noncomputable def unsignedPrimeTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / (n : ℝ) ^ s else 0

theorem unsignedPrimeTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ unsignedPrimeTerm s n := by
  unfold unsignedPrimeTerm
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.one_lt.le))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_refl _

theorem unsignedPrimeTerm_eq_principal (s : ℝ) :
    unsignedPrimeTerm s = realPrimeTerm (1 : DirichletCharacter ℝ 1) s := by
  funext n
  have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp only [unsignedPrimeTerm, realPrimeTerm, hn, map_one, one_mul]

private theorem principal_logDerivative_eq (s : ℝ) (hs : 1 < s) :
    deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) (s : ℂ) /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (s : ℂ) =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hs' : 1 < (s : ℂ).re := hs
  have he := χ.LSeries_twist_vonMangoldt_eq hs'
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs', ← χ.LFunction_eq_LSeries hs'] at he
  have hf : (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one, one_mul]
  change LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) = _ at he
  rw [hf] at he
  simpa only [neg_div, neg_neg] using congrArg Neg.neg he.symm

theorem exists_unsignedPrimeMass_error :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      Summable (unsignedPrimeTerm s) ∧
      |(∑' n, unsignedPrimeTerm s n) - 1 / (s - 1)| ≤ C := by
  obtain ⟨Cp, hCp, hprime⟩ := exists_realPrimeSeries_error
  obtain ⟨Cv, hCv, hvon⟩ := exists_vonMangoldt_pole_error
  refine ⟨Cp + Cv, by positivity, ?_⟩
  intro s hs hs2
  have hc : (1 : DirichletCharacter ℝ 1).ringHomComp Complex.ofRealHom =
      (1 : DirichletCharacter ℂ 1) := by
    apply MulChar.ext
    intro a
    rw [Subsingleton.elim a 1, Units.val_one, map_one, map_one]
  obtain ⟨hsum, hp⟩ := hprime 1 1 s hs
  rw [hc, principal_logDerivative_eq s hs, Complex.neg_re,
    ← unsignedPrimeTerm_eq_principal] at hp
  have hv := (Complex.abs_re_le_norm _).trans (hvon s hs hs2)
  simp only [Complex.sub_re, Complex.ofReal_re] at hv
  refine ⟨by rwa [unsignedPrimeTerm_eq_principal], ?_⟩
  have he : (∑' n, unsignedPrimeTerm s n) - 1 / (s - 1) =
      ((∑' n, unsignedPrimeTerm s n) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)).re) +
      ((LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)).re - 1 / (s - 1)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hp hv)

end Ostmann

end OAI
