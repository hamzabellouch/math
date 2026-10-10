import Mathlib
import OAI.Analysis.Commutator.SpectralThreshold

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma threshold_lower {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    r • threshold B r≤B*threshold B r := by
  have hh := CFC.posPart_nonneg (B-r • (1:H →L[ℂ] H))
  rw [←threshold_mul_shift hB r,mul_sub,mul_smul_comm,mul_one,
    (threshold_commute hB r).eq] at hh
  exact sub_nonneg.mp hh

lemma threshold_remainder {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    B*(1-threshold B r)≤r • (1-threshold B r) := by
  let a := B-r • (1:H →L[ℂ] H)
  have ha : IsSelfAdjoint a := hB.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have he : (1-threshold B r)*a= -a⁻ := by
    rw [sub_mul,one_mul,threshold_mul_shift hB r]
    change a-a⁺= -a⁻
    nth_rw 1 [←CFC.posPart_sub_negPart a ha]
    abel
  have hh : (1-threshold B r)*a≤0 := he ▸ neg_nonpos.mpr (CFC.negPart_nonneg a)
  dsimp only [a] at hh
  rw [mul_sub,mul_smul_comm,mul_one] at hh
  have hc : Commute (1-threshold B r) B := (Commute.one_left B).sub_left (threshold_commute hB r)
  rw [hc.eq] at hh
  exact sub_nonpos.mp hh

lemma threshold_remainder_nonneg {B : H →L[ℂ] H} (hB : 0≤B) (r : ℝ) :
    0≤B*(1-threshold B r) := by
  exact Commute.mul_nonneg hB (threshold_projection B r).one_sub.nonneg
    (((Commute.one_left B).sub_left (threshold_commute (IsSelfAdjoint.of_nonneg hB) r)).symm)

lemma threshold_lower_whole {B : H →L[ℂ] H} (hB : 0≤B) (r : ℝ) :
    r • threshold B r≤B := by
  have hh := threshold_lower (IsSelfAdjoint.of_nonneg hB) r
  have hl : B*threshold B r≤B := by
    have hh := threshold_remainder_nonneg hB r
    rw [mul_sub,mul_one] at hh
    exact sub_nonneg.mp hh
  exact hh.trans hl

lemma threshold_remainder_norm {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0≤r) :
    ‖B*(1-threshold B r)‖≤r := by
  have hh := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (threshold_remainder (IsSelfAdjoint.of_nonneg hB) r) (threshold_remainder_nonneg hB r)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hh
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left ((threshold_projection B r).one_sub.norm_le _) hr)

lemma threshold_completion_unit {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0<r) :
    IsUnit (B+r • (1-threshold B r)) := by
  let E := threshold B r
  have hdecomp : r • (1:H →L[ℂ] H)=r • E+r • (1-E) := by
    rw [smul_sub]
    abel
  have hlow : r • E≤B := threshold_lower_whole hB r
  have hl : r • (1:H →L[ℂ] H)≤B+r • (1-E) := by
    rw [hdecomp]
    exact add_le_add hlow le_rfl
  have hs : IsStrictlyPositive (1:H →L[ℂ] H) := by cfc_tac
  exact CStarAlgebra.isUnit_of_le _ hl (IsStrictlyPositive.smul hr hs)

end Kadison.PositiveWOT

end

end
end

end OAI
