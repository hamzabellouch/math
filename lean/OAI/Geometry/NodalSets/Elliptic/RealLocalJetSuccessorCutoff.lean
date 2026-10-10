import OAI.Geometry.NodalSets.Elliptic.RealFiniteJetIntegrals
import OAI.Geometry.NodalSets.Elliptic.RealLocalJetClosedCutoff

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_local_jet_successor_cutoff (O : Set Yau.Jets.Coord) (hO : IsOpen O)
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
      Integrable (fun x ↦ eta x^2*realFiniteJetSquare W (n+1) x) ∧
      Integrable (fun x ↦ realCutoffWeight eta x*realFiniteJetSquare W n x) ∧
      (∫ x, eta x^2*realFiniteJetSquare W (n+1) x) ≤
        K*(∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x) := by
  obtain ⟨K,hK,hcut⟩ := real_local_jet_closed_cutoff O hO n k L M B hk hL hM hB
  let N : ℝ := ∑ r ∈ Finset.range (n+2), (4:ℝ)^r
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  refine ⟨N*(K+1)+1,by positivity,?_⟩
  intro C V W eta hC hV hW heta hc hsO hs hlo hhi hpot hb he
  let J : ℝ := ∫ x, realCutoffWeight eta x*realFiniteJetSquare W n x
  have hJ := realCutoffWeight_integrable_mul eta _ heta hc (realFiniteJetSquare_smooth W hW n).continuous
  have hJn : 0 ≤ J := integral_nonneg (fun x ↦
    mul_nonneg (realCutoffWeight_nonneg eta x) (realFiniteJetSquare_nonneg W n x))
  have hi (ds : List (Fin 4)) : Integrable (fun x ↦ eta x^2*(partialJet W ds x)^2) :=
    real_cutoff_square_integrable eta _ heta hc ((partialJet_smooth W hW ds).pow 2).continuous
  have hw (ds : List (Fin 4)) (hd : ds.length ≤ n+1) :
      (∫ x, eta x^2*(partialJet W ds x)^2) ≤ (K+1)*J := by
    cases ds with
    | nil =>
      have hp (x : Yau.Jets.Coord) : eta x^2*(partialJet W [] x)^2 ≤
          realCutoffWeight eta x*realFiniteJetSquare W n x :=
        mul_le_mul (le_add_of_nonneg_right (realGradientSquare_nonneg eta x))
          (partialJet_sq_le_realFiniteJetSquare W n [] (by simp) x) (sq_nonneg _)
          (realCutoffWeight_nonneg eta x)
      have hh := integral_mono (hi []) hJ hp
      change (∫ x, eta x^2*(partialJet W [] x)^2) ≤ J at hh
      nlinarith [mul_nonneg hK.le hJn]
    | cons l ds =>
      obtain ⟨hG,_,hest⟩ := hcut C V W eta hC hV hW heta hc hsO hs hlo hhi hpot hb he ds (by simpa using hd)
      have hh : (∫ x, eta x^2*(partialJet W (l::ds) x)^2) ≤
          ∫ x, eta x^2*realGradientSquare (partialJet W ds) x := by
        apply integral_mono (hi (l::ds)) hG
        intro x
        exact mul_le_mul_of_nonneg_left (real_partial_sq_le_gradient (partialJet W ds) x l) (sq_nonneg _)
      change (∫ x, eta x^2*realGradientSquare (partialJet W ds) x) ≤ K*J at hest
      nlinarith only [hh,hest,hJn]
  refine ⟨realFiniteJetSquare_integrable eta W heta hc hW _,hJ,?_⟩
  rw [realFiniteJetSquare_integral_sum eta W heta hc hW]
  have hh := Finset.sum_le_sum (s := Finset.range (n+2)) (fun r hr ↦
    Finset.sum_le_sum (s := Finset.univ) (fun w _ ↦ hw (List.ofFn w) (by
      simp only [List.length_ofFn]; exact Nat.le_of_lt_succ (Finset.mem_range.mp hr))))
  have hcN : (∑ r ∈ Finset.range (n+2), ∑ _w : Fin r → Fin 4, (K+1)*J) = N*((K+1)*J) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    exact (Finset.sum_mul ..).symm
  rw [hcN] at hh
  change (∑ r ∈ Finset.range (n+1+1), ∑ w : Fin r → Fin 4,
    ∫ x, eta x^2*(partialJet W (List.ofFn w) x)^2) ≤ (N*(K+1)+1)*J
  nlinarith only [hh,hJn]

end
end Yau.Geometry

end OAI
