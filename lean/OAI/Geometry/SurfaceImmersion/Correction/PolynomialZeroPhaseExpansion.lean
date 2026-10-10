import OAI.Geometry.SurfaceImmersion.Correction.FinitePolynomialPhases
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanCoefficient

namespace OAI

/-! Separate the actual polynomial Hessian into its zero-phase part and
explicit doubled and mixed phases. Ordered pairs retain all multiplicities. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets
namespace Perturbation

def quadraticPhaseCoefficient {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ)
    (τ t : ℝ) (p : Base) : ℂ :=
  conjugated P ε G (pairPhases φ ψ) (pairDirections H K) τ 1 (p, t) / 4

lemma phase_mul (τ : ℝ) (φ ψ : Base → ℝ) (p : Base) :
    phase τ φ p * phase τ ψ p = phase τ (fun x => φ x + ψ x) p := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

def quadraticOscillation {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) : ℝ :=
  (∑ i, ∑ j, (phase τ (fun x => φ i x + φ j x) p *
    quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re) +
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (phase τ (fun x => φ i x - φ j x) p *
      quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
        (H i) (starField (H j)) τ t p).re

lemma quadraticMeanCoefficient_eq_phaseCoefficient {n : ℕ}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanCoefficient P ε G φ H τ t p =
      (quadraticPhaseCoefficient P ε G φ (fun x => -φ x) H (starField H) τ t p).re := by
  simp only [quadraticMeanCoefficient, quadraticPhaseCoefficient, Complex.div_ofNat_re]

lemma quadraticPhaseCoefficient_oscillation {n : ℕ}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ) (τ : ℝ) (z : Base × ℝ) :
    (phase τ (fun x => φ x + ψ x) z.1 *
      quadraticPhaseCoefficient P ε G φ ψ H K τ z.2 z.1).re =
    ∑ l, ε ^ (l.val + 1) *
      ((phase τ φ z.1 * phase τ ψ z.1) *
        conjugatedVariation (P l) G (pairPhases φ ψ) (pairDirections H K) τ 1 z).re / 4 := by
  rw [← phase_mul]
  simp only [quadraticPhaseCoefficient, conjugated, div_eq_mul_inv, Finset.mul_sum,
    Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.inv_re, Complex.inv_im,
    Complex.normSq_ofNat]
  norm_num
  ring

lemma weighted_half_second_variation_phases {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (τ : ℝ) (z : Base × ℝ) :
    (∑ l : Fin n, ε ^ (l.val + 1) * ((1 / 2 : ℝ) * ((P l).variations 1).eval
      ![G, realField (oscillatorySum τ φ H), realField (oscillatorySum τ φ H), 0] z)) =
    (∑ i, ∑ j, (phase τ (fun x => φ i x + φ j x) z.1 *
      quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ z.2 z.1).re) +
    ∑ i, ∑ j, (phase τ (fun x => φ i x - φ j x) z.1 *
      quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
        (H i) (starField (H j)) τ z.2 z.1).re := by
  classical
  simp only [half_second_variation_phases _ G φ H hφ hH τ z,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro j hj
  · simpa only [mul_div_assoc] using (quadraticPhaseCoefficient_oscillation P ε G (φ i) (φ j) (H i) (H j) τ z).symm
  · simpa only [mul_div_assoc, sub_eq_add_neg] using (quadraticPhaseCoefficient_oscillation P ε G (φ i) (fun x => -φ j x)
      (H i) (starField (H j)) τ z).symm

/-- The omitted terms have exactly the doubled/sum/difference phases. The
geometric good-phase hypothesis is only needed later to solve these modes. -/
theorem quadratic_zero_phase_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (τ t : ℝ) (p : Base) :
    (∑ l : Fin n, ε ^ (l.val + 1) * ((1 / 2 : ℝ) * ((P l).variations 1).eval
      ![G, realField (oscillatorySum τ φ H), realField (oscillatorySum τ φ H), 0] (p,t))) =
    (∑ i, quadraticMeanCoefficient P ε G (φ i) (H i) τ t p) +
      quadraticOscillation P ε G φ H τ t p := by
  rw [weighted_half_second_variation_phases P ε G φ H hφ hH τ (p,t)]
  have hrow (i : ι) :
      (∑ j, (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
          (H i) (starField (H j)) τ t p).re) =
      quadraticMeanCoefficient P ε G (φ i) (H i) τ t p +
      ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
          (H i) (starField (H j)) τ t p).re := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    have hz : phase τ (fun _ : Base => (0 : ℝ)) p = 1 := by simp [phase]
    simp only [sub_self, hz, one_mul, quadraticMeanCoefficient_eq_phaseCoefficient]
    ring
  simp only [hrow, Finset.sum_add_distrib, quadraticOscillation]
  ring

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
