import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped ContDiff

theorem complex_schwartz_pairing_ae_eq {d : ℕ} (f h : Ambient d → ℂ)
    (hf : LocallyIntegrable f) (hh : LocallyIntegrable h)
    (heq : ∀ g : 𝓢(Ambient d, ℂ), (∫ x, f x * g x) = ∫ x, h x * g x) :
    f =ᵐ[volume] h := by
  apply ae_eq_of_integral_contDiff_smul_eq hf hh
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(Ambient d, ℂ) := hc'.toSchwartzMap hg'
  have hmul : ∀ (a : Ambient d → ℂ) x, g x • a x = a x * G x := by
    intro a x
    change g x • a x = a x * (g x : ℂ)
    erw [Complex.real_smul]
    exact mul_comm _ _
  calc
    _ = ∫ x, f x * G x := integral_congr_ae (Filter.Eventually.of_forall (hmul f))
    _ = ∫ x, h x * G x := heq G
    _ = _ := (integral_congr_ae (Filter.Eventually.of_forall (hmul h))).symm

theorem mvPolynomial_complex_eval_continuous {d : ℕ} (P : MvPolynomial (Fin d) ℂ) :
    Continuous (fun x : Ambient d => MvPolynomial.eval (fun j => (x j : ℂ)) P) := by
  exact P.continuous_eval.comp (by fun_prop)

theorem locallyIntegrable_complex_of_real {d : ℕ} (w : Ambient d → ℝ)
    (hw : LocallyIntegrable w) : LocallyIntegrable (fun x => (w x : ℂ)) := by
  intro x
  obtain ⟨U, hU, hi⟩ := hw x
  exact ⟨U, hU, hi.ofReal⟩

theorem real_height_ae_eq_polynomial_of_pairings {d : ℕ}
    (w : Ambient d → ℝ) (hw : LocallyIntegrable w) (P : MvPolynomial (Fin d) ℂ)
    (heq : ∀ g : 𝓢(Ambient d, ℂ), (∫ x, w x • g x) =
      ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) P * g x) :
    ∀ᵐ x, (w x : ℂ) = MvPolynomial.eval (fun j => (x j : ℂ)) P := by
  apply complex_schwartz_pairing_ae_eq _ _ (locallyIntegrable_complex_of_real w hw)
    (mvPolynomial_complex_eval_continuous P).locallyIntegrable
  intro g
  calc
    _ = ∫ x, w x • g x := by
      apply integral_congr_ae
      filter_upwards with x
      erw [Complex.real_smul]
    _ = _ := heq g

end

end RieszRectifiability

end OAI
