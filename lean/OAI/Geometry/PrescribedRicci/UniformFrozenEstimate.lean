import Mathlib
import OAI.Geometry.PrescribedRicci.HermitianCoercivity
import OAI.Geometry.PrescribedPotential.SobolevParametrix

namespace OAI

/-! Uniform Frozen Estimate. -/

noncomputable section
open Matrix MeasureTheory TemperedDistribution
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise SchwartzMap Real
namespace FrozenPoisson
open EllipticKernel SobolevChart MongeAmpere
variable {n : ℕ}

lemma trace_rankOne_hermPair (H : Matrix (Fin n) (Fin n) ℂ) (ξ : EC n) :
    traceBilin H (rankOne ξ) = (1/4:ℝ)*(hermPair H⁻¹ (coordinateEquiv n ξ) (coordinateEquiv n ξ)).re := by
  rw [traceBilin_apply,pull_rankOne,Matrix.mul_smul,Matrix.trace_smul]
  simp only [Complex.smul_re,smul_eq_mul]
  congr 1
  rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]
  rfl

lemma coordinate_coercivity (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {M : ℝ} (hM : ‖H‖ ≤ M) (ξ : EC n) :
    ‖ξ‖^2 ≤ (n:ℝ)*M*(hermPair H⁻¹ (coordinateEquiv n ξ) (coordinateEquiv n ξ)).re := by
  let : Invertible H := Matrix.invertibleOfIsUnitDet H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  have hp := hermPair_nonneg hH.inv.posSemidef (coordinateEquiv n ξ)
  have hc (i : Fin n) : ‖ξ i‖^2 ≤ M*(hermPair H⁻¹ (coordinateEquiv n ξ) (coordinateEquiv n ξ)).re := by
    apply (component_sq_le_hermPair hH.inv (coordinateEquiv n ξ) i).trans
    rw [Matrix.inv_inv_of_invertible]
    exact mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans
      ((norm_entry_le_entrywise_sup_norm H).trans hM)) hp
  rw [PiLp.norm_sq_eq_of_L2]
  apply (Finset.sum_le_sum (fun i _ => hc i)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]

def uniformEllipticBound (n : ℕ) (M : ℝ) : ℝ := 1+(n:ℝ)*M/Real.pi^2

lemma uniformEllipticBound_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < uniformEllipticBound n M := by unfold uniformEllipticBound; positivity

lemma gainSymbol_uniform_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {M : ℝ} (hM : 0 ≤ M) (hHM : ‖H‖ ≤ M) (ξ : EC n) :
    ‖gainSymbol H ξ‖ ≤ uniformEllipticBound n M := by
  have hc := coordinate_coercivity H hH hHM ξ
  have hs : symbol H ξ = Real.pi^2*(hermPair H⁻¹ (coordinateEquiv n ξ) (coordinateEquiv n ξ)).re := by
    rw [symbol,trace_rankOne_hermPair]; ring
  have he : ‖ξ‖^2 ≤ ((n:ℝ)*M/Real.pi^2)*symbol H ξ := by
    rw [hs]
    convert hc using 1
    field_simp
  have hp := symbol_nonneg H hH ξ
  simp only [gainSymbol,inverseSymbol,← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity),mul_inv_le_iff₀ (by positivity)]
  have hq : 0 ≤ (n:ℝ)*M/Real.pi^2 := by positivity
  dsimp [uniformEllipticBound]
  nlinarith only [he,hp,hq]

lemma hilbertResolvent_uniform_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {M : ℝ} (hM : 0 ≤ M) (hHM : ‖H‖ ≤ M) (u : L2 (EC n)) :
    ‖hilbertResolvent H hH u‖ ≤ uniformEllipticBound n M*‖u‖ := by
  apply (multiplier_norm_le (gainSymbolBCF H hH) u).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  exact (BoundedContinuousFunction.norm_le (uniformEllipticBound_pos hM).le).mpr
    (gainSymbol_uniform_bound H hH hM hHM)
end FrozenPoisson

end

end OAI
