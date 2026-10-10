import OAI.Analysis.LipschitzHilbert.Estimates.ReferenceSynthesisL1
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace OAI

/-! Finite Hilbert duality for coefficients defined by actual analyzing
integrals. The self-pairing uses the same selected synthesizing packets. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ] [Fintype κ]

def analyzingCoefficient (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (i : σ) :
    EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ((area i)⁻¹ : ℂ) * ∫ z, g z k * conj (wave i k z) ∂μ)

def diagonalSynthesis (wave : σ → κ → Ω → ℂ)
    (c : σ → EuclideanSpace ℂ κ) (z : Ω) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ i, c i k * wave i k z)

omit [Fintype σ] [Fintype κ] in
theorem analyzingCoefficient_mul_area (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0) (i : σ) (k : κ) :
    (area i : ℂ) * analyzingCoefficient μ area wave g i k =
      ∫ z, g z k * conj (wave i k z) ∂μ := by
  change (area i : ℂ) * (((area i)⁻¹ : ℂ) * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (show (area i : ℂ) ≠ 0 by exact_mod_cast ha i), one_mul]

theorem analyzingCoefficient_self_pairing (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0)
    (hint : ∀ i k, Integrable (fun z => g z k * conj (wave i k z)) μ) :
    ((∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 : ℝ) : ℂ) =
      ∫ z, inner ℂ (diagonalSynthesis wave (analyzingCoefficient μ area wave g) z) (g z) ∂μ := by
  let a := analyzingCoefficient μ area wave g
  have hterm (i : σ) : ((area i * ‖a i‖^2 : ℝ) : ℂ) =
      ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
    have hnorm : (‖a i‖ : ℂ)^2 = inner ℂ (a i) (a i) :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a i)).symm
    rw [Complex.ofReal_mul, Complex.ofReal_pow, hnorm]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← analyzingCoefficient_mul_area μ area wave g ha i k]
    ring
  have hInt (i : σ) (k : κ) :
      Integrable (fun z => conj (a i k) * (g z k * conj (wave i k z))) μ :=
    (hint i k).const_mul _
  calc
    _ = ∑ i, ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∫ z, ∑ i, ∑ k, conj (a i k) * (g z k * conj (wave i k z)) ∂μ := by
      simp_rw [← integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum _ (fun k _ => hInt i k))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [diagonalSynthesis, PiLp.inner_apply, RCLike.inner_apply,
        map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem analyzingCoefficient_energy_le (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, 0 < area i)
    (hint : ∀ i k, Integrable (fun z => g z k * conj (wave i k z)) μ)
    (hg : ∀ z, ‖g z‖ ≤ 1) :
    ENNReal.ofReal (∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2) ≤
      ∫⁻ z, ENNReal.ofReal ‖diagonalSynthesis wave (analyzingCoefficient μ area wave g) z‖ ∂μ := by
  have hn : ‖((∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 : ℝ) : ℂ)‖ =
      ∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg
      (fun i _ => mul_nonneg (ha i).le (sq_nonneg _)))]
  rw [← hn, analyzingCoefficient_self_pairing μ area wave g (fun i => (ha i).ne') hint]
  rw [ofReal_norm]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro z
  dsimp only
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg z) (norm_nonneg _))

end LipschitzHilbert

end

end OAI
