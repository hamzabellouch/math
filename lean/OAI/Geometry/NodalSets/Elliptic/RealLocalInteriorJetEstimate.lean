import OAI.Geometry.NodalSets.Elliptic.RealInteriorJetEstimate
import OAI.Geometry.NodalSets.Elliptic.RealLocalNestedJetCutoff

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_interior_jet_estimate (O : Set Yau.Jets.Coord) (hO : IsOpen O)
    (n : ℕ) (k L M B : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (eta : ℕ → Yau.Jets.Coord → ℝ) (heta : ∀ j, ContDiff ℝ ∞ (eta j))
    (hc : ∀ j, HasCompactSupport (eta j))
    (hnest : ∀ j x, x ∈ tsupport (eta (j+1)) → eta j x=1)
    (hsO : tsupport (eta 0) ⊆ O) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W : Yau.Jets.Coord → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V → ContDiff ℝ ∞ W →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport (eta 0), ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport (eta 0), ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport (eta 0), |V x| ≤ M) →
      (∀ x ∈ tsupport (eta 0), ∀ es : List (Fin 4), es.length ≤ n →
        (∀ i j, |partialJet (fun y ↦ C y i j) es x| ≤ B) ∧ |partialJet V es x| ≤ B) →
      (∀ x ∈ O, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) →
      Integrable (fun x ↦ eta n x^2*realFiniteJetSquare W n x) ∧
      Integrable (fun x ↦ eta 0 x^2*W x^2) ∧
      (∫ x, eta n x^2*realFiniteJetSquare W n x) ≤
        K*(∫ x, eta 0 x^2*W x^2) := by
  induction n with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro C V W hC hV hW hs hlo hhi hpot hb he
    have hi := real_cutoff_square_integrable (eta 0) _ (heta 0) (hc 0) (hW.pow 2).continuous
    simpa only [realFiniteJetSquare_zero,one_mul] using And.intro hi (And.intro hi (le_refl (∫ x, eta 0 x^2*W x^2)))
  | succ n ih =>
    obtain ⟨K0,hK0,hprevious⟩ := ih
    obtain ⟨K1,hK1,hstep⟩ := real_local_nested_jet_cutoff O hO n k L M B hk hL hM hB
      (eta (n+1)) (eta n) (heta (n+1)) (heta n) (hc (n+1)) (hc n) (hnest n) ((real_cutoff_chain_support eta hnest (n+1)).trans hsO)
    refine ⟨K1*K0,by positivity,?_⟩
    intro C V W hC hV hW hs hlo hhi hpot hb he
    obtain ⟨_,hQ,hprev⟩ := hprevious C V W hC hV hW hs hlo hhi hpot
      (fun x hx es hes ↦ hb x hx es (by omega)) he
    have hsub := real_cutoff_chain_support eta hnest (n+1)
    obtain ⟨hI,_,hnext⟩ := hstep C V W hC hV hW hs
      (fun x hx ↦ hlo x (hsub hx)) (fun x hx ↦ hhi x (hsub hx))
      (fun x hx ↦ hpot x (hsub hx))
      (fun x hx es hes ↦ hb x (hsub hx) es (by omega)) he
    refine ⟨hI,hQ,?_⟩
    have hh := mul_le_mul_of_nonneg_left hprev hK1.le
    nlinarith only [hnext,hh]

end
end Yau.Geometry

end OAI
