import OAI.MathematicalPhysics.Boltzmann.Branching.MainParameters
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapUniformFiniteHorizon
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.ContinuationAdmissibility

namespace OAI

/-! # Conditional nonuniqueness for the periodic hard-sphere Boltzmann equation

All mathematical inputs from earlier publications are explicit arguments.
`NonuniquenessStatement` includes bounded velocity support and two distinct
global admissible renormalized solutions with strong initial continuity.
-/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
open JetCopyDatum

theorem nonuniqueness_conditional
    (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    (hDPhot : Published.DunfordPettis1940HotWindows)
    (hDPpair : Published.DunfordPettis1940HotPairWindows)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement := by
  obtain ⟨P⟩ := exists_construction_parameters hDPpair hcarleman hGLPS hMityagin
  obtain ⟨B⟩ := exists_dormant_family hcarleman P.scale_pos P.scale_le P.eta_pos P.eta_le
    P.density_pos.le P.alpha_pos P.alpha_le P.gamma_pos P.width_pos P.width_le P.width_small
    P.comparison_small P.q_lower P.q_upper
  obtain ⟨D⟩ := B.exists_limit hcarleman hGLPS hDP P.scale_pos P.scale_le P.eta_pos P.eta_le
    P.density_pos P.alpha_pos P.alpha_le P.gamma_pos P.width_pos P.width_le P.width_small
    P.comparison_small P.q_lower P.q_upper
  obtain ⟨A,L,hAB,t,ht,hneq⟩ := exists_separated_cap_limit hcarleman hGLPS hDP hDPhot hDPpair
    hMityagin D P.scale_pos P.scale_le P.eta_pos P.eta_le P.density_pos P.alpha_pos P.alpha_le
    P.gamma_pos P.width_pos P.width_le P.width_small P.comparison_small P.q_lower P.q_upper P.finite_horizon
  obtain ⟨F,hF,hFs,hFe⟩ := L.admissible.exists_global_extension hperiodic
  obtain ⟨G,hG,hGs,hGe⟩ := D.admissible.exists_global_extension hperiodic
  refine ⟨JetPeriodicDatum.datum P.s₀ P.η P.K P.α P.γ P.d₀,
    JetPeriodicDatum.boundedVelocitySupport P.scale_pos P.scale_le P.eta_pos.le P.width_pos
      P.width_small P.alpha_pos.le P.alpha_le P.K P.γ,
    F,G,A.time,hF,hG,hFs,hGs.restrict A.time_pos hAB,t,ht,?_⟩
  rw [hFe t ht,hGe t ⟨ht.1,ht.2.trans hAB⟩]
  exact hneq

end BoltzmannNonuniqueness

end

end OAI
