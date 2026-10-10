import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralBounds
open MeasureTheory PrimeCellFreezing HistoryPrincipalIntegralAverage HistoryGiantPriorGrid
open scoped BigOperators

theorem norm_prime_giantIntegral_le {G Z A : ℝ} (hG : 2 ≤ G)
    (hZ : 0 < Z) (hZi : Z⁻¹ ≤ 2*G) (hA : 0 ≤ A)
    (f : (Bool → ℝ) → ℂ)
    (hf : ∀ t ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
      ‖f (fun i => Real.exp (t i))‖ ≤ A) :
    ‖primeIntegral (fun _ : Bool => G-1) (fun _ => G+1) (fun _ => Z) (primeCutoff G f)‖ ≤ 64*A := by
  have hcut : ∀ t ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
      ‖primeCutoff G f (fun i => Real.exp (t i))‖ ≤ A := by
    intro t ht
    have hb := giantCell_bounds G (Real.exp (t false))
    have hc := giantCell_bounds G (Real.exp (t true))
    rw [primeCutoff,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    exact (mul_le_mul ((mul_le_mul hb.2 hc.2 hc.1 zero_le_one).trans_eq (one_mul 1)) (hf t ht) (norm_nonneg _) zero_le_one).trans_eq (one_mul A)
  have h := primeIntegral_norm_le_prod (fun _ : Bool => G-1) (fun _ => G+1) (fun _ => Z)
    (fun _ => by linarith) (fun _ => by linarith) (fun _ => hZ) (primeCutoff G f) hcut
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_bool] at h
  have hm := normalized_giant_harmonic_mass_le hG hZ hZi
  have hm0 : 0 ≤ Z⁻¹*(∫ t in (G-1)..(G+1), (t : ℝ)⁻¹) := by
    apply mul_nonneg (inv_nonneg.mpr hZ.le)
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact inv_nonneg.mpr (by linarith [ht.1])
  exact h.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hm 2) hA).trans_eq (by ring))

end Ostmann.Arithmetic.HistoryPrincipalIntegralBounds

end

end OAI
