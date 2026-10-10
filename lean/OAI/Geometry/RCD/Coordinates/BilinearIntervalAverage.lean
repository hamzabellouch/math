import OAI.Geometry.RCD.Coordinates.IntervalBilinearEnergy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Weighted quadratic energy of an actual time average

Positivity of the bilinear form gives Jensen's inequality directly on the
finite interval used to smooth the Sobolev time family.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem positive_bilinear_interval_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ x, 0 ≤ P x x)
    (hsymm : ∀ x y, P x y = P y x)
    {a b : ℝ} (hab : a < b) (u : ℝ → E) (hu : IntegrableOn u (Icc a b))
    (hE : IntegrableOn (fun t => P (u t) (u t)) (Icc a b)) :
    let m := (b-a)⁻¹ • ∫ t in Icc a b, u t
    P m m ≤ (b-a)⁻¹ * ∫ t in Icc a b, P (u t) (u t) := by
  intro m
  have hmass : volume.real (Icc a b) = b-a := by
    rw [Real.volume_real_Icc_of_le hab.le]
  have hmean : (b-a) • m = ∫ t in Icc a b, u t := by
    dsimp only [m]
    rw [smul_smul,mul_inv_cancel₀ (sub_pos.mpr hab).ne',one_smul]
  have hpair : (∫ t in Icc a b, P m (u t)) = (b-a)*P m m := by
    rw [(P m).integral_comp_comm hu,← hmean,map_smul,smul_eq_mul]
  have hconst : (∫ _ in Icc a b, P m m) = (b-a)*P m m := by
    rw [setIntegral_const,hmass,smul_eq_mul]
  have hmix : IntegrableOn (fun t => P m (u t)) (Icc a b) :=
    (P m).integrable_comp hu
  have hle : (∫ t in Icc a b, 2*P m (u t)-P m m) ≤
      ∫ t in Icc a b, P (u t) (u t) := by
    apply integral_mono_ae ((hmix.const_mul 2).sub (integrableOn_const
      (isCompact_Icc.measure_lt_top.ne))) hE
    exact Eventually.of_forall fun t => by
      change 2*P m (u t)-P m m ≤ P (u t) (u t)
      have hh := hpos (u t-m)
      simp only [map_sub,sub_apply] at hh
      rw [hsymm (u t) m] at hh
      linarith
  have he : (∫ t in Icc a b, 2*P m (u t)-P m m) = (b-a)*P m m := by
    rw [integral_sub (hmix.const_mul 2) (integrableOn_const (isCompact_Icc.measure_lt_top.ne)),
      integral_const_mul,hpair,hconst]
    ring
  rw [he] at hle
  have hh := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (sub_pos.mpr hab).le)
  simpa only [← mul_assoc,inv_mul_cancel₀ (sub_pos.mpr hab).ne',one_mul] using hh

end RegularPointCoordinates

end

end OAI
