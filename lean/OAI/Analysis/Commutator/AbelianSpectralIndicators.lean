import Mathlib
import OAI.Analysis.Commutator.AbelianGNSMaximal
import OAI.Analysis.Commutator.AbelianGNSSpectral
import OAI.Analysis.Commutator.MaximalAbelianTransport
import OAI.Analysis.Commutator.ScalarIndicator

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma conjugate_eq_of_intertwines {Domain Codomain : Type*}
    [NormedAddCommGroup Domain] [InnerProductSpace ℂ Domain] [CompleteSpace Domain]
    [NormedAddCommGroup Codomain] [InnerProductSpace ℂ Codomain] [CompleteSpace Codomain]
    (equiv : Domain ≃ₗᵢ[ℂ] Codomain)
    (first : Domain →L[ℂ] Domain) (second : Codomain →L[ℂ] Codomain)
    (intertwines : ∀ vector,equiv (first vector)=second (equiv vector)) :
    equiv.conjStarAlgEquiv first=second := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,intertwines,equiv.apply_symm_apply]

variable (M : VonNeumannAlgebra H)

variable (τ : (CentralCorner.center M) →ₚ[ℂ] ℂ)

variable (μ : Measure (Spectrum M))

variable (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] τ.GNS)

lemma scalar_indicator_commutes (f : C(Spectrum M,ℂ)) (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    Commute (scalarMultiplier μ f) (indicatorOperator (H:=ℂ) μ s hs) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ f (indicatorOperator μ s hs v),
    indicatorOperator_ae μ s hs v,indicatorOperator_ae μ s hs (scalarMultiplier μ f v),
    scalarMultiplier_ae μ f v] with x h₁ h₂ h₃ h₄
  change scalarMultiplier μ f (indicatorOperator μ s hs v) x=
    indicatorOperator μ s hs (scalarMultiplier μ f v) x
  rw [h₁,h₃]
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx]
    rw [h₂,Set.indicator_of_mem hx,h₄]
  · simp [hx,h₂]

lemma scalar_conjugate
    (hU : ∀ (a : CentralCorner.center M) (v : Lp ℂ 2 μ),
      U (scalarMultiplier μ (gelfandStarTransform _ a) v)=τ.gnsStarAlgHom a (U v))
    (a : CentralCorner.center M) :
    U.conjStarAlgEquiv (scalarMultiplier μ (gelfandStarTransform _ a))=τ.gnsStarAlgHom a := by
  exact conjugate_eq_of_intertwines (Domain:=Lp ℂ 2 μ) (Codomain:=τ.GNS) U
    (scalarMultiplier μ (gelfandStarTransform _ a)) (τ.gnsStarAlgHom a) (hU a)

theorem indicator_in_scalar_spectral_range
    (hn : NormalGNS.BoundedWOTContinuous (CentralCorner.center M) τ)
    (hU : ∀ (a : CentralCorner.center M) (v : Lp ℂ 2 μ),
      U (scalarMultiplier μ (gelfandStarTransform _ a) v)=τ.gnsStarAlgHom a (U v))
    (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    ∃ a : CentralCorner.center M,
      scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs := by
  exact range_of_maximal_conjugate U
    (fun a : CentralCorner.center M => scalarMultiplier μ (gelfandStarTransform _ a))
    τ.gnsStarAlgHom
    (NormalGNS.commutant_range_eq_of_commutative (CentralCorner.center M) τ
      (fun _ _ => mul_comm _ _) hn)
    (scalar_conjugate M τ μ U hU) (indicatorOperator μ s hs)
    (fun a => scalar_indicator_commutes M μ (gelfandStarTransform _ a) s hs)

end Kadison.CentralSpectral

end

end
end

end OAI
