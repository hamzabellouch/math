import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanPairBounds
import OAI.Geometry.SurfaceImmersion.Geometry.ConjugatedOperatorBounds

namespace OAI

/-! The zero-phase Hessian estimate in the actual supported seminorms. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma quadraticMeanPair_zero_left {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ 0 K τ t p = 0 := by
  have hh := quadraticMeanPair_add_left P ε G hφ
    (H := 0) (K := 0) contDiff_const contDiff_const K τ t p
  have he : (fun x => (0 : Base → Fin 4 → ℂ) x + (0 : Base → Fin 4 → ℂ) x) = 0 := by
    funext x
    exact zero_add _
  rw [he] at hh
  linarith

lemma quadraticMeanPair_zero_right {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ H 0 τ t p = 0 := by
  have hh := quadraticMeanPair_add_right P ε G hφ
    (H := 0) (K := 0) contDiff_const contDiff_const H τ t p
  have he : (fun x => (0 : Base → Fin 4 → ℂ) x + (0 : Base → Fin 4 → ℂ) x) = 0 := by
    funext x
    exact zero_add _
  rw [he] at hh
  linarith

theorem supported_quadraticMeanPair_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B F : ℝ) (hB : 1 ≤ B) (hF : 0 ≤ F) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (_hG : ContDiff ℝ ∞ G) (_hφ : ContDiff ℝ ∞ φ) (K : Compacts Base)
      (H J : SupportedField (F := Fin 4 → ℂ) K) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) F (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * supportedWeightedSeminorm K s (m + order P) H *
          supportedWeightedSeminorm K s (m + order P) J / τ ^ loss P)
          (quadraticMeanPair P ε G φ H J τ t) := by
  obtain ⟨E, hE, he⟩ := quadraticMeanPair_bound hU hO hQ hQO P hP m B F hB hF
  refine ⟨E, hE, ?_⟩
  intro G φ hG hφ K H J s τ ε hτ hs hτs hs1 hε hε1 hGQ hGb hφb t ht
  let C := supportedWeightedSeminorm K s (m + order P) H
  let D := supportedWeightedSeminorm K s (m + order P) J
  have hC : 0 ≤ C := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  change WeightedBound U s m (E * ε * C * D / τ ^ loss P) _
  by_cases hC0 : C = 0
  · have hH0 : H = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + order P) hC0
    have hfun : (H : Base → Fin 4 → ℂ) = 0 := congrArg
      (fun Z : SupportedField (F := Fin 4 → ℂ) K => (Z : Base → Fin 4 → ℂ)) hH0
    have hz : quadraticMeanPair P ε G φ H J τ t = 0 := by
      funext x
      rw [hfun]
      exact quadraticMeanPair_zero_left P ε G hφ J τ t x
    rw [hC0, mul_zero, zero_mul, zero_div, hz]
    exact weightedBound_zero U s m
  by_cases hD0 : D = 0
  · have hJ0 : J = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + order P) hD0
    have hfun : (J : Base → Fin 4 → ℂ) = 0 := congrArg
      (fun Z : SupportedField (F := Fin 4 → ℂ) K => (Z : Base → Fin 4 → ℂ)) hJ0
    have hz : quadraticMeanPair P ε G φ H J τ t = 0 := by
      funext x
      rw [hfun]
      exact quadraticMeanPair_zero_right P ε G hφ H τ t x
    rw [hD0, mul_zero, zero_div, hz]
    exact weightedBound_zero U s m
  exact he G φ H J s τ ε C D hτ hs hτs hs1 hε hε1
    (lt_of_le_of_ne hC (Ne.symm hC0)) (lt_of_le_of_ne hD (Ne.symm hD0))
    hG hφ H.contDiff J.contDiff hGQ hGb
    ((weightedBound_of_supportedSeminorm s (m + order P) H).restrict_open hU)
    ((weightedBound_of_supportedSeminorm s (m + order P) J).restrict_open hU) hφb t ht

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
