import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullDisintegrationBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction
attribute [local instance] Classical.propDecidable

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem productPrior_cmean_update_two (μ : I → FinitePrior Ω) (L S : I)
    (F : (I → Ω) → ℂ) :
    (productPrior μ).cmean F =
      (productPrior μ).cmean (fun p => (μ L).cmean (fun q =>
        (μ S).cmean (fun r => F (Function.update (Function.update p L q) S r)))) :=
  (productPrior_cmean_update μ S F).trans
    (productPrior_cmean_update μ L (fun p => (μ S).cmean (fun r => F (Function.update p S r))))

theorem norm_cmean_le_of_mass_support {A : Type*} [Fintype A]
    (μ : FinitePrior A) (F : A → ℂ) (ε : ℝ)
    (hF : ∀ a,μ.mass a ≠ 0 → ‖F a‖ ≤ ε) : ‖μ.cmean F‖ ≤ ε := by
  apply (μ.norm_cmean_le F).trans
  rw [← μ.mean_const ε]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hm : μ.mass a = 0
  · simp only [hm,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (hF a hm) (μ.mass_nonneg a)

theorem norm_productPrior_cmean_le_of_two_coordinate (μ : I → FinitePrior Ω) (L S : I)
    (F : (I → Ω) → ℂ) (ε : ℝ)
    (hF : ∀ p,(productPrior μ).mass p ≠ 0 →
      ‖(μ L).cmean (fun q => (μ S).cmean
        (fun r => F (Function.update (Function.update p L q) S r)))‖ ≤ ε) :
    ‖(productPrior μ).cmean F‖ ≤ ε := by
  rw [productPrior_cmean_update_two μ L S F]
  exact norm_cmean_le_of_mass_support (productPrior μ) _ ε hF

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
