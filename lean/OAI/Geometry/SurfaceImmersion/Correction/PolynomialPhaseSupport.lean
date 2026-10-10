import OAI.Geometry.SurfaceImmersion.Correction.PolynomialZeroPhaseExpansion
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanSupport

namespace OAI

/-! Every polynomial quadratic phase coefficient is smooth and supported
in the intersection of its two amplitude supports. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets WeightedEstimates

lemma quadraticComplex_zero_right_at (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) (hK : ∀ w a, K w a z.1 = 0) :
    quadraticComplex e G J K z = 0 := by
  have he : quadraticComplex e G J K z = quadraticComplex e G J 0 z := by
    apply MixedExpression.evalComplex_congr
    intro i w a
    fin_cases i
    · rfl
    · rfl
    · exact hK w a
    · rfl
  rw [he]
  change quadraticComplexBilinear e G z J 0 = 0
  exact map_zero _

namespace Perturbation

lemma quadraticPhaseCoefficient_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Base → Space} {φ ψ : Base → ℝ} {H K : Base → Fin 4 → ℂ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (hQ : Set.MapsTo (lowJet G) U O) (ε τ t : ℝ) :
    ContDiffOn ℝ ∞ (quadraticPhaseCoefficient P ε G φ ψ H K τ t) U := by
  exact (ContDiffOn.sum fun l _ =>
    (conjugatedVariation_smooth (hP l) hG (pairPhases_smooth hφ hψ)
      (pairDirections_smooth hH hK) hO hQ τ 1 t).const_smul _).div_const 4

lemma quadraticPhaseCoefficient_zero_of_notMem {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ)
    (τ t : ℝ) {p : Base} (hp : p ∉ tsupport H ∩ tsupport K) :
    quadraticPhaseCoefficient P ε G φ ψ H K τ t p = 0 := by
  have hz (l : Fin n) : conjugatedVariation (P l) G (pairPhases φ ψ)
      (pairDirections H K) τ 1 (p,t) = 0 := by
    have hn : phase τ φ p * phase τ ψ p ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    have he : quadraticComplex (P l) G (complexJet (fun x => phase τ φ x • H x))
        (complexJet (fun x => phase τ ψ x • K x)) (p,t) = 0 := by
      by_cases hH : p ∈ tsupport H
      · have hK : p ∉ tsupport K := fun hk => hp ⟨hH, hk⟩
        have hk : p ∉ tsupport (fun x => phase τ ψ x • K x) :=
          fun hx => hK (tsupport_smul_subset_right (phase τ ψ) K hx)
        exact quadraticComplex_zero_right_at (P l) G _ _ _
          (fun w a => complexJet_zero_of_notMem hk w a)
      · have hh : p ∉ tsupport (fun x => phase τ φ x • H x) :=
          fun hx => hH (tsupport_smul_subset_right (phase τ φ) H hx)
        exact quadraticComplex_zero_at (P l) G _ _ _
          (fun w a => complexJet_zero_of_notMem hh w a)
    rw [quadraticComplex_phase_factor] at he
    exact (mul_eq_zero.mp he).resolve_left hn
  simp only [quadraticPhaseCoefficient, conjugated, hz, smul_zero, Finset.sum_const_zero,
    zero_div]

lemma quadraticPhaseCoefficient_tsupport {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ) (τ t : ℝ) :
    tsupport (quadraticPhaseCoefficient P ε G φ ψ H K τ t) ⊆ tsupport H ∩ tsupport K := by
  apply closure_minimal _ ((isClosed_tsupport H).inter (isClosed_tsupport K))
  intro p hp
  by_contra hn
  exact hp (quadraticPhaseCoefficient_zero_of_notMem P ε G φ ψ H K τ t hn)

def polynomialPhaseField {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hP : ∀ l, (P l).SmoothCoeffs O) {G : Base → Space} {φ ψ : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hQ : Set.MapsTo (lowJet G) U O) (C : Compacts Base) (hCU : (C : Set Base) ⊆ U)
    (H K : Base → Fin 4 → ℂ) (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (hC : tsupport H ∩ tsupport K ⊆ C) (ε τ t : ℝ) : SupportedField (F := ℂ) C :=
  let hs := (quadraticPhaseCoefficient_tsupport P ε G φ ψ H K τ t).trans hC
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset hU (hs.trans hCU)
      (quadraticPhaseCoefficient_smooth hO hP hG hφ hψ hH hK hQ ε τ t))
    (subset_closure.trans hs)

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
