import OAI.Geometry.NodalSets.Elliptic.RealCutoffIntegralsLemmas
import OAI.Geometry.NodalSets.Elliptic.RealJetErrorBound
import OAI.Geometry.NodalSets.Elliptic.RealLocalJetCutoffEstimate

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_jet_closed_cutoff (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B) :
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
      (∀ x ∈ tsupport eta, ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      ∀ ds : List (Fin 4), ds.length ≤ n →
      Integrable (fun x ↦ eta x^2*realGradientSquare (partialJet W ds) x) ∧
      Integrable (fun x ↦ realCutoffWeight eta x*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤
        K*(∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_local_jet_cutoff_estimate O hO k L M hk hL hM
  obtain ⟨E,hE,herror⟩ := real_jet_error_bound n B hB
  refine ⟨K*(1+E),by positivity,?_⟩
  intro C V W eta hC hV hW heta hc hsO hs hlo hhi hpot hb he ds hd
  obtain ⟨hG,hI,hS,hF,hest⟩ := hcut C V W eta hC hV hW heta hc hsO hs hlo hhi hpot he ds
  have hJ := realCutoffWeight_integrable_mul eta _ heta hc (realFiniteJetSquare_smooth W hW n).continuous
  have hbase : (∫ x, (eta x^2+realGradientSquare eta x)*(partialJet W ds x)^2) ≤
      ∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x := by
    apply integral_mono hI hJ
    intro x
    exact mul_le_mul_of_nonneg_left (partialJet_sq_le_realFiniteJetSquare W n ds hd x)
      (realCutoffWeight_nonneg eta x)
  have hpoint (x : Yau.Jets.Coord) :
      eta x^2*(realJetErrorSource V W ds x)^2 +
        eta x^2*(∑ i, (realJetErrorFlux C W ds x i)^2) ≤
      E*(realCutoffWeight eta x*realFiniteJetSquare W n x) := by
    by_cases hx : x ∈ tsupport eta
    · have herr := herror C V W hC hV hW x ds hd (hb x hx)
      have hm := mul_le_mul_of_nonneg_left herr (sq_nonneg (eta x))
      have hw : eta x^2 ≤ realCutoffWeight eta x :=
        le_add_of_nonneg_right (realGradientSquare_nonneg eta x)
      have hcomp := mul_le_mul_of_nonneg_right hw
        (mul_nonneg hE.le (realFiniteJetSquare_nonneg W n x))
      nlinarith only [hm,hcomp]
    · rw [image_eq_zero_of_notMem_tsupport hx,realCutoffWeight_zero_off_support eta hx]
      simp
  have herr := integral_mono (hS.add hF) (hJ.const_mul E) hpoint
  simp only [Pi.add_apply] at herr
  rw [integral_add hS hF,integral_const_mul] at herr
  refine ⟨hG,hJ,?_⟩
  have hh := mul_le_mul_of_nonneg_left (add_le_add hbase herr) hK.le
  nlinarith only [hest,hh]

end
end Yau.Geometry

end OAI
