import OAI.Geometry.NodalSets.Elliptic.RealLocalCaccioppoli
import OAI.Geometry.NodalSets.Elliptic.RealLocalJetErrorEquation

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_jet_cutoff_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (k L M : ℝ) (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W eta : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ eta → HasCompactSupport eta → tsupport eta ⊆ O →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      ∀ ds : List (Fin 4),
      Integrable (fun x ↦ eta x^2*realGradientSquare (partialJet W ds) x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2) ∧
      Integrable (fun x ↦ eta x^2*(realJetErrorSource V W ds x)^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2)) ∧
      (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2)+
          (∫ x, eta x^2*(realJetErrorSource V W ds x)^2)+
          (∫ x, eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2))) := by
  obtain ⟨K,hK,h⟩ := real_local_inhomogeneous_caccioppoli k L M hk hL hM
  refine ⟨K,hK,?_⟩
  intro C V W eta hC hV hW heta hc hsO hs hlo hhi hpot he ds
  exact h C V (partialJet W ds) (realJetErrorSource V W ds) eta (realJetErrorFlux C W ds)
    hC hV (partialJet_smooth W hW ds) (realJetErrorSource_smooth V W hV hW ds) heta
    (realJetErrorFlux_smooth C W hC hW ds) hc hs hlo hhi hpot
    (fun x hx ↦ real_local_jet_error_equation O hO C V W hC hV hW he ds x (hsO hx))

end
end Yau.Geometry

end OAI
