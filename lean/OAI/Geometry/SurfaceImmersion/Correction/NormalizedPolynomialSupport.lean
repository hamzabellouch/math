import OAI.Geometry.SurfaceImmersion.Correction.NormalizedPolynomialMean
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanSupport

namespace OAI

/-! Support and global smoothness of the normalized polynomial mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma normalizedPolynomialMean_tsupport {n : ℕ} (P : Fin n → Expression) (δ ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (τ t : ℝ) :
    tsupport (normalizedPolynomialMean P δ ε G φ H τ t) ⊆ tsupport H :=
  tsupport_mul_subset_right.trans (quadraticMeanCoefficient_tsupport P ε G hφ hH τ t)

lemma normalizedPolynomialMean_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hP : ∀ l, (P l).SmoothCoeffs O) {G : Base → Space} {φ : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H : SupportedField (F := Fin 4 → ℂ) K) (δ ε τ t : ℝ) :
    ContDiff ℝ ∞ (normalizedPolynomialMean P δ ε G φ H τ t) := by
  exact ((polynomialMeanField hU hO hP hG hφ hQ K hKU H ε τ t).contDiff).const_smul (δ⁻¹ ^ 2)

lemma normalizedPolynomialMean_extend {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} (hU : IsOpen U) {G : Base → Space} {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H : SupportedField (F := Fin 4 → ℂ) K) (δ ε τ t : ℝ)
    {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C (normalizedPolynomialMean P δ ε G φ H τ t)) :
    WeightedBound Set.univ s m C (normalizedPolynomialMean P δ ε G φ H τ t) :=
  hb.extend_support hU
    (((normalizedPolynomialMean_tsupport P δ ε G hφ H.contDiff τ t).trans H.tsupport_subset).trans hKU) hC

lemma normalizedPolynomialMean_difference_extend {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} (hU : IsOpen U) {G : Base → Space} {φ : Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (H J : SupportedField (F := Fin 4 → ℂ) K) (δ ε τ t : ℝ)
    {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C (fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
      normalizedPolynomialMean P δ ε G φ J τ t x)) :
    WeightedBound Set.univ s m C (fun x => normalizedPolynomialMean P δ ε G φ H τ t x -
      normalizedPolynomialMean P δ ε G φ J τ t x) := by
  apply hb.extend_support hU _ hC
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact ((normalizedPolynomialMean_tsupport P δ ε G hφ H.contDiff τ t).trans H.tsupport_subset).trans hKU
  · exact ((normalizedPolynomialMean_tsupport P δ ε G hφ J.contDiff τ t).trans J.tsupport_subset).trans hKU

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
