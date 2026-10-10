import OAI.Analysis.KadisonKastler.RegularCoreAlgebra

namespace OAI

/-! # Covariance of the concrete regular generators -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem regularTranslation_embedding (s : Multiplicative ℝ) (a : H →L[ℂ] H) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularCoreEmbedding U hU a =
      regularCoreEmbedding U hU (unitaryConj (star (U s)) a) *
        (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularRightTranslation_apply_ae s (regularCoreEmbedding U hU a f),
    (measurePreserving_add_right (volume : Measure ℝ) s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularCoreEmbedding_apply_ae U hU a f),
    regularCoreEmbedding_apply_ae U hU (unitaryConj (star (U s)) a)
      ((regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularRightTranslation_apply_ae s f] with t hρ hπ hright hf
  simp only [Function.comp_def] at hπ
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreEmbedding U hU a f) t =
      regularCoreEmbedding U hU (unitaryConj (star (U s)) a)
        ((regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) t
  rw [hρ, hπ, hright, hf]
  have he : U (Multiplicative.ofAdd (t + s.toAdd)) = U s * U (Multiplicative.ofAdd t) := by
    rw [add_comm]
    exact map_mul U s (Multiplicative.ofAdd t)
  rw [he, Submonoid.coe_mul, star_mul]
  simp only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp]

def regularCoreMonomial (a : H →L[ℂ] H) (s : Multiplicative ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularCoreEmbedding U hU a * (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)

theorem regularCoreMonomial_mul (a b : H →L[ℂ] H) (s t : Multiplicative ℝ) :
    regularCoreMonomial U hU a s * regularCoreMonomial U hU b t =
      regularCoreMonomial U hU (a * unitaryConj (star (U s)) b) (s * t) := by
  unfold regularCoreMonomial
  calc
    _ = regularCoreEmbedding U hU a *
        (((regularRightTranslation (H := H) s :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * regularCoreEmbedding U hU b) *
            (regularRightTranslation (H := H) t :
              RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by simp only [mul_assoc]
    _ = regularCoreEmbedding U hU a *
        ((regularCoreEmbedding U hU (unitaryConj (star (U s)) b) *
          (regularRightTranslation (H := H) s :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) *
              (regularRightTranslation (H := H) t :
                RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by
      rw [regularTranslation_embedding U hU]
    _ = (regularCoreEmbedding U hU a *
        regularCoreEmbedding U hU (unitaryConj (star (U s)) b)) *
          ((regularRightTranslation (H := H) s :
            RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
              (regularRightTranslation (H := H) t :
                RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) := by simp only [mul_assoc]
    _ = _ := by
      rw [← map_mul]
      congr 1
      exact congrArg Subtype.val (map_mul (regularRightTranslation (H := H)) s t).symm

end

end KadisonKastler

end OAI
