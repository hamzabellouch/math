import OAI.Geometry.SurfaceImmersion.Geometry.TensorPerturbationOperator

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma first_variation_phase_factor (e : Expression) (G : Base → Space)
    (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ : ℝ) (z : Base × ℝ) :
    phase τ φ z.1 * conjugatedVariation e G (singlePhase φ) (singleDirection H) τ 0 z =
      ((ofExpression e).differentiate 0).evalComplex G
        (complexDirectionData G (fun p => phase τ φ p • H p)) z := by
  have hp : phaseProduct (singlePhase φ) τ 0 z.1 = phase τ φ z.1 := by
    simp [phaseProduct, singlePhase]
  rw [conjugatedVariation, hp, ← mul_assoc,
    mul_inv_cancel₀ (show phase τ φ z.1 ≠ 0 from Complex.exp_ne_zero _), one_mul,
    single_oscillatoryData]
  rfl

namespace Perturbation

def linearized {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space)
    (t : ℝ) (p : Base) : ℝ := ∑ l, ε ^ (l.val + 1) * (P l).variation G H (p,t)

lemma linearized_real_mode {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ t : ℝ) (p : Base) :
    linearized P ε G (realField (fun x => phase τ φ x • H x)) t p =
      (phase τ φ p * conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p,t)).re := by
  have hs : ContDiff ℝ ∞ (fun x => phase τ φ x • H x) := (phase_smooth hφ τ).smul hH
  unfold linearized conjugated
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [show phase τ φ p * (ε ^ (l.val + 1) •
      conjugatedVariation (P l) G (singlePhase φ) (singleDirection H) τ 0 (p,t)) =
      ε ^ (l.val + 1) • (phase τ φ p *
        conjugatedVariation (P l) G (singlePhase φ) (singleDirection H) τ 0 (p,t)) by
    simp only [Complex.real_smul]; ring]
  rw [first_variation_phase_factor (P l) G φ H τ (p,t), complex_first_variation (P l) G hs]
  simp [-Complex.ofReal_pow]

lemma conjugatedLM_realization {n : ℕ} {O : Set LowJet} {U : Set Base}
    {G : Base → Space} (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    linearized P ε G (realField (fun x => phase τ φ x • H x)) t p =
      (phase τ φ p * conjugatedLM hO hU P hP hG hQ K hKU hφ τ ε t H p).re := by
  rw [conjugatedLM_apply]
  exact linearized_real_mode P ε G hφ H.contDiff τ t p

lemma linearized_add {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (p : Base) :
    linearized P ε G (fun x => H x + K x) t p =
      linearized P ε G H t p + linearized P ε G K t p := by
  simp only [linearized, Expression.variation_add _ G hH hK, mul_add, Finset.sum_add_distrib]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
