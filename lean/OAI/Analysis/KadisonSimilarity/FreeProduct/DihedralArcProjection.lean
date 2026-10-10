import OAI.Analysis.KadisonSimilarity.FreeProduct.SpectralArc
import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! The concrete projection underlying the centered dihedral arc.  Its
Fourier moments are separate from the operator construction: the projection
is the open spectral cut of the real part of the rotation at `cos θ`.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Spectral cuts preserve every star commutation relation. -/
theorem upperSpectralCut_commutes (A T : H →L[ℂ] H) (t : ℝ)
    (h : Commute A T) (hs : Commute A (star T)) :
    Commute (upperSpectralCut A t) T := by
  apply rangeSupport_commutes
  · exact (h.sub_left ((Commute.one_left T).smul_left t)).cfcₙ_real (fun x => x⁺)
  · exact (hs.sub_left ((Commute.one_left (star T)).smul_left t)).cfcₙ_real
      (fun x => x⁺)

/-- Centering a projection by any scalar in `[0,1]` keeps norm at most one. -/
theorem norm_projection_sub_scalar_le_one (p : H →L[ℂ] H)
    (hp : IsStarProjection p) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖p - r • 1‖ ≤ 1 := by
  have hp1 : p ≤ 1 := sub_nonneg.mp hp.one_sub.nonneg
  have hrl : r • (1 : H →L[ℂ] H) ≤ 1 := by
    simpa only [one_smul] using
      smul_le_smul_of_nonneg_right hr1 (zero_le_one : (0 : H →L[ℂ] H) ≤ 1)
  have hru : 0 ≤ r • (1 : H →L[ℂ] H) := smul_nonneg hr zero_le_one
  have hlo : -(1 : H →L[ℂ] H) ≤ p - r • 1 := by
    calc
      _ ≤ -(r • (1 : H →L[ℂ] H)) := neg_le_neg hrl
      _ ≤ p - r • 1 := by simpa only [zero_sub] using sub_le_sub_right hp.nonneg _
  have hhi : p - r • 1 ≤ (1 : H →L[ℂ] H) :=
    (sub_le_self _ hru).trans hp1
  have hself : IsSelfAdjoint (p - r • 1) :=
    hp.isSelfAdjoint.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have hn : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hself).trans
    (by simpa only [norm_neg, max_self] using hn)

/-- The open centered angular arc, expressed as a spectral cut of the real part. -/
def dihedralArcProjection (w : H →L[ℂ] H) (θ : ℝ) : H →L[ℂ] H :=
  upperSpectralCut (realPart w) (Real.cos θ)

theorem dihedralArcProjection_isStarProjection (w : H →L[ℂ] H) (θ : ℝ) :
    IsStarProjection (dihedralArcProjection w θ) := upperSpectralCut_isStarProjection _ _

/-- The actual centered operator used for the Haar arc. -/
def centeredDihedralArc (w : H →L[ℂ] H) (θ : ℝ) : H →L[ℂ] H :=
  dihedralArcProjection w θ - (θ / Real.pi) • 1

theorem centeredDihedralArc_selfAdjoint (w : H →L[ℂ] H) (θ : ℝ) :
    IsSelfAdjoint (centeredDihedralArc w θ) :=
  (dihedralArcProjection_isStarProjection w θ).isSelfAdjoint.sub
    ((IsSelfAdjoint.all (θ / Real.pi)).smul (IsSelfAdjoint.one _))

theorem centeredDihedralArc_norm_le (w : H →L[ℂ] H)
    {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    ‖centeredDihedralArc w θ‖ ≤ 1 :=
  norm_projection_sub_scalar_le_one _ (dihedralArcProjection_isStarProjection w θ)
    (div_nonneg hθ Real.pi_pos.le) ((div_le_one Real.pi_pos).mpr hπ)

theorem dihedralArcProjection_mem (P : VonNeumannAlgebra H)
    (w : H →L[ℂ] H) (hw : w ∈ P) (θ : ℝ) : dihedralArcProjection w θ ∈ P := by
  have hstar : star w ∈ P := star_mem hw
  apply upperSpectralCut_mem
  rw [realPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem (P.toStarSubalgebra.add_mem hw hstar) _

theorem centeredDihedralArc_mem (P : VonNeumannAlgebra H)
    (w : H →L[ℂ] H) (hw : w ∈ P) (θ : ℝ) : centeredDihedralArc w θ ∈ P := by
  apply P.toStarSubalgebra.sub_mem (dihedralArcProjection_mem P w hw θ)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact P.toStarSubalgebra.smul_mem P.one_mem _

/-- Normality makes the rotation commute with the real spectral variable. -/
theorem realPart_commutes_rotation (w : H →L[ℂ] H)
    (hw : Commute w (star w)) : Commute (realPart w : H →L[ℂ] H) w := by
  rw [realPart_apply_coe]
  exact ((Commute.refl w).add_left hw.symm).smul_left _

/-- Reflection interchanges the two summands of the real spectral variable. -/
theorem realPart_commutes_reflection (w d : H →L[ℂ] H)
    (hd : d * d = 1) (h : d * w = star w * d) :
    Commute (realPart w : H →L[ℂ] H) d := by
  have h' : d * star w = w * d := by
    calc
      d * star w = d * star w * (d * d) := by rw [hd, mul_one]
      _ = (d * (star w * d)) * d := by simp only [mul_assoc]
      _ = (d * (d * w)) * d := by rw [← h]
      _ = w * d := by rw [← mul_assoc d d w, hd, one_mul]
  rw [realPart_apply_coe]
  apply Commute.smul_left
  change (w + star w) * d = d * (w + star w)
  simp only [add_mul, mul_add, h, h', add_comm]

theorem centeredDihedralArc_commutes_rotation (w : H →L[ℂ] H)
    (hw : Commute w (star w)) (θ : ℝ) : Commute (centeredDihedralArc w θ) w := by
  apply Commute.sub_left _ ((Commute.one_left w).smul_left _)
  apply upperSpectralCut_commutes
  · exact realPart_commutes_rotation w hw
  · rw [realPart_apply_coe]
    exact (hw.add_left (Commute.refl (star w))).smul_left _

theorem centeredDihedralArc_commutes_reflection (w d : H →L[ℂ] H)
    (hd : d * d = 1) (hs : star d = d) (h : d * w = star w * d) (θ : ℝ) :
    Commute (centeredDihedralArc w θ) d := by
  apply Commute.sub_left _ ((Commute.one_left d).smul_left _)
  apply upperSpectralCut_commutes
  · exact realPart_commutes_reflection w d hd h
  · rw [hs]
    exact realPart_commutes_reflection w d hd h

omit [CompleteSpace H] in
/-- Once the projection's trace is known, its centered second moment is
forced algebraically; no separate spectral calculation is necessary. -/
theorem centeredProjection_second_moment (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (p : H →L[ℂ] H) (hp : p * p = p) (r : ℂ)
    (hτ : τ 1 = 1) (ht : τ p = r) :
    τ ((p - r • 1) * (p - r • 1)) = r * (1 - r) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul, hp, map_sub, map_smul, hτ, ht, smul_eq_mul]
  ring

omit [CompleteSpace H] in
/-- Vanishing of the reflection-coset moments also controls the square. -/
theorem centeredProjection_square_reflection (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (p d : H →L[ℂ] H) (hp : p * p = p) (r : ℂ)
    (hτd : τ d = 0) (hτpd : τ (p * d) = 0) :
    τ (((p - r • 1) * (p - r • 1)) * d) = 0 := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    mul_one, one_mul, hp, map_sub, map_smul, hτd, hτpd,
    smul_zero, sub_self]

end KadisonSimilarity

end

end OAI
