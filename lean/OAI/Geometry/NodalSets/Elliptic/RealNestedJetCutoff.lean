import OAI.Geometry.NodalSets.Elliptic.RealJetSuccessorCutoff
import OAI.Geometry.NodalSets.Elliptic.RealNestedCutoffWeight

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_nested_jet_cutoff (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (eta chi : Yau.Jets.Coord → ℝ) (heta : ContDiff ℝ ∞ eta) (hchi : ContDiff ℝ ∞ chi)
    (hce : HasCompactSupport eta) (hcc : HasCompactSupport chi)
    (hnest : ∀ x ∈ tsupport eta, chi x=1) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta x^2*realFiniteJetSquare W (n+1) x) ∧
      Integrable (fun x ↦ chi x^2*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realFiniteJetSquare W (n+1) x) ≤
        K*(∫ x, chi x^2*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_jet_successor_cutoff n k L M B hk hL hM hB
  obtain ⟨D,hD,hweight⟩ := real_nested_cutoff_weight eta chi heta hce hnest
  refine ⟨K*D,by positivity,?_⟩
  intro C V W hC hV hW hs hlo hhi hpot hb he
  obtain ⟨hI,hJ,hest⟩ := hcut C V W eta hC hV hW heta hce hs hlo hhi hpot hb he
  have hQ := realFiniteJetSquare_integrable chi W hchi hcc hW n
  have hm := integral_mono hJ (hQ.const_mul D) (fun x ↦ by
    have hh := mul_le_mul_of_nonneg_right (hweight x) (realFiniteJetSquare_nonneg W n x)
    simpa only [mul_assoc] using hh)
  rw [integral_const_mul] at hm
  refine ⟨hI,hQ,?_⟩
  have hh := mul_le_mul_of_nonneg_left hm hK.le
  nlinarith only [hest,hh]

end
end Yau.Geometry

end OAI
