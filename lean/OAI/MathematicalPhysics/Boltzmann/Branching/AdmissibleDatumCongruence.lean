import OAI.MathematicalPhysics.Boltzmann.Admissibility

namespace OAI

/-! # The global admissibility datum depends only on its almost-everywhere class -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness

theorem AdmissibleGlobal.congr_datum {f g : Density} {F : Evolution}
    (S : AdmissibleGlobal f F) (hg : FiniteEntropyDatum g) (he : f =ᵐ[volume] g) :
    AdmissibleGlobal g F := by
  have hH : relativeEntropy f = relativeEntropy g :=
    integral_congr_ae (he.mono (fun p hp => by dsimp only; rw [hp]))
  have hE : energy f = energy g :=
    integral_congr_ae (he.mono (fun p hp => congrArg (fun a => ‖p.2‖^2*a) hp))
  have hP : momentum f = momentum g :=
    integral_congr_ae (he.mono (fun p hp => congrArg (fun a => a • p.2) hp))
  refine {
    datum := hg
    spacetime_measurable := S.spacetime_measurable
    finite_each_time := S.finite_each_time
    initial := S.initial.trans he
    weak_continuity := S.weak_continuity
    uniform_moment := S.uniform_moment
    collision_fibers := S.collision_fibers
    gain_integrable := S.gain_integrable
    loss_integrable := S.loss_integrable
    renormalized_integrable := S.renormalized_integrable
    renormalized_equation := ?_
    local_mass_integrable := S.local_mass_integrable
    local_mass := ?_
    momentum_conservation := fun t ht => (S.momentum_conservation t ht).trans hP
    energy_inequality := fun t ht => (S.energy_inequality t ht).trans_eq hE
    entropy_inequality := fun t ht => (S.entropy_inequality t ht).trans_eq (congrArg _ hH)
  }
  · intro β φ
    have hi : (∫ p : Phase, maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun 0 p.1 p.2) =
        ∫ p : Phase, maxwellian p.2*β.toFun (g p/maxwellian p.2)*φ.toFun 0 p.1 p.2 :=
      integral_congr_ae (he.mono (fun p hp => by dsimp only; rw [hp]))
    rw [← hi]
    exact S.renormalized_equation β φ
  · intro φ
    have hi : (∫ p : Phase, f p*φ.toFun 0 p.1) = ∫ p : Phase, g p*φ.toFun 0 p.1 :=
      integral_congr_ae (he.mono (fun p hp => congrArg (fun a => a*φ.toFun 0 p.1) hp))
    rw [← hi]
    exact S.local_mass φ

end BoltzmannNonuniqueness

end

end OAI
