import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanPair

namespace OAI

/-! Difference identity for the actual polynomial zero-phase mean. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma quadraticMeanPair_sub_left {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ (fun x => H x - K x) L τ t p =
      quadraticMeanPair P ε G φ H L τ t p - quadraticMeanPair P ε G φ K L τ t p := by
  have hh := quadraticMeanPair_add_left P ε G hφ (hH.sub hK) hK L τ t p
  have he : (fun x => (H x - K x) + K x) = H := by funext x; exact sub_add_cancel _ _
  rw [he] at hh
  exact eq_sub_of_add_eq hh.symm

lemma quadraticMeanPair_sub_right {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (L : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanPair P ε G φ L (fun x => H x - K x) τ t p =
      quadraticMeanPair P ε G φ L H τ t p - quadraticMeanPair P ε G φ L K τ t p := by
  have hh := quadraticMeanPair_add_right P ε G hφ (hH.sub hK) hK L τ t p
  have he : (fun x => (H x - K x) + K x) = H := by funext x; exact sub_add_cancel _ _
  rw [he] at hh
  exact eq_sub_of_add_eq hh.symm

lemma quadraticMeanCoefficient_difference {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H K : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (τ t : ℝ) (p : Base) :
    quadraticMeanCoefficient P ε G φ H τ t p - quadraticMeanCoefficient P ε G φ K τ t p =
      quadraticMeanPair P ε G φ (fun x => H x - K x) H τ t p +
        quadraticMeanPair P ε G φ K (fun x => H x - K x) τ t p := by
  rw [quadraticMeanPair_sub_left P ε G hφ hH hK,
    quadraticMeanPair_sub_right P ε G hφ hH hK,
    quadraticMeanPair_self P ε G hφ hH, quadraticMeanPair_self P ε G hφ hK]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
