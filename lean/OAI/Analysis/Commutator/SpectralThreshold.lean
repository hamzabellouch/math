import Mathlib
import OAI.Analysis.Commutator.PositiveCauchySchwarz
import OAI.Analysis.Commutator.PositiveWOT
import OAI.Analysis.Commutator.SpectralCutoff

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positive_apply_eq_zero {A : H →L[ℂ] H} (ha : 0≤A) {x : H}
    (hx : (inner ℂ (A x) x).re=0) : A x=0 := by
  have hh := positive_cauchySchwarz A ha x (A x)
  rw [hx,zero_mul] at hh
  have hn : inner ℂ (A x) (A x)=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (inner ℂ (A x) (A x))])
  exact (inner_self_eq_zero (𝕜:=ℂ)).mp hn

lemma rightSupport_mono {A B : H →L[ℂ] H} (hA : 0≤A) (hB : 0≤B) (hab : A≤B) :
    Polar.rightSupport A≤Polar.rightSupport B := by
  have hp := Polar.isProjection_rightSupport B
  have hfix : B*Polar.rightSupport B=B := by
    simpa only [CFC.abs_of_nonneg B hB] using Polar.abs_mul_initial B
  have he : B*(1-Polar.rightSupport B)=0 := by rw [mul_sub,mul_one,hfix,sub_self]
  have ha : A*(1-Polar.rightSupport B)=0 := by
    ext x
    change A ((1-Polar.rightSupport B) x)=0
    apply positive_apply_eq_zero hA
    have hh := inner_mono hab ((1-Polar.rightSupport B) x)
    have hz : B ((1-Polar.rightSupport B) x)=0 := congrArg (fun T : H →L[ℂ] H => T x) he
    rw [hz,inner_zero_left,Complex.zero_re] at hh
    exact le_antisymm hh ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_left _)
  apply Polar.rightSupport_le A (Polar.rightSupport B) hp
  rw [mul_sub,mul_one,sub_eq_zero] at ha
  exact ha.symm

lemma cfc_shift_posPart (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (r : ℝ) :
    (B-r • (1:H →L[ℂ] H))⁺=cfc (fun t : ℝ => (t-r)⁺) B := by
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  have he : cfc (fun t : ℝ => t-r) B=B-r • (1:H →L[ℂ] H) := by
    change cfc (fun t : ℝ => id t - (fun _ : ℝ => r) t) B = _
    rw [cfc_sub (id : ℝ → ℝ) (fun _ => r),cfc_id ℝ B hB,cfc_const r B hB]
    exact congrArg (B-·) (Algebra.algebraMap_eq_smul_one r)
  rw [←he]
  exact (cfc_comp (fun t : ℝ => t⁺) (fun t : ℝ => t-r) B).symm

def threshold (B : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  Polar.rightSupport (B-r • (1:H →L[ℂ] H))⁺

lemma threshold_projection (B : H →L[ℂ] H) (r : ℝ) : IsStarProjection (threshold B r) :=
  Polar.isProjection_rightSupport _

lemma threshold_mem (M : VonNeumannAlgebra H) {B : H →L[ℂ] H} (hB : B∈M) (r : ℝ) :
    threshold B r∈M := by
  apply Polar.rightSupport_mem M
  apply Polar.posPart_mem M
  apply M.toStarSubalgebra.sub_mem hB
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  change (Complex.ofReal r) • (1:H →L[ℂ] H)∈M
  exact M.toStarSubalgebra.smul_mem M.one_mem _

lemma threshold_antitone {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) : Antitone (threshold B) := by
  intro r s hrs
  have hle : (B-s • (1:H →L[ℂ] H))⁺≤(B-r • (1:H →L[ℂ] H))⁺ := by
    rw [cfc_shift_posPart B hB,cfc_shift_posPart B hB]
    exact cfc_mono (R:=ℝ) (a:=B) (fun t _ => sup_le_sup (sub_le_sub_left hrs t) le_rfl)
      (Continuous.continuousOn ((continuous_id.sub continuous_const).max continuous_const))
      (Continuous.continuousOn ((continuous_id.sub continuous_const).max continuous_const))
  exact rightSupport_mono (CFC.posPart_nonneg (B-s • (1:H →L[ℂ] H)))
    (CFC.posPart_nonneg (B-r • (1:H →L[ℂ] H))) hle

lemma threshold_commute {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    Commute (threshold B r) B := by
  let a : H →L[ℂ] H := B-r • (1:H →L[ℂ] H)
  have hr : Commute (r • (1:H →L[ℂ] H)) B := (Commute.one_left B).smul_left r
  have hc : Commute a B := (Commute.refl B).sub_left hr
  have hp : Commute a⁺ B := hc.cfcₙ_real (·⁺)
  have hs : Commute a⁺ (star B) := by rwa [hB.star_eq]
  have hh : Commute (Polar.partialIsometry a⁺) B := Polar.partialIsometry_commutes a⁺ B hp hs
  rw [Polar.partialIsometry_of_nonneg (CFC.posPart_nonneg a)] at hh
  exact hh

lemma threshold_mul_shift {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    threshold B r*(B-r • (1:H →L[ℂ] H))=(B-r • (1:H →L[ℂ] H))⁺ := by
  let a := B-r • (1:H →L[ℂ] H)
  have ha : IsSelfAdjoint a := hB.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have hp : Polar.rightSupport a⁺*a⁺=a⁺ := by
    simpa only [CFC.abs_of_nonneg _ (CFC.posPart_nonneg a)] using Polar.initial_mul_abs a⁺
  have hn : Polar.rightSupport a⁺*a⁻=0 :=
    Polar.rightSupport_mul_eq_zero_of_nonneg (CFC.posPart_nonneg a) (CFC.posPart_mul_negPart a)
  change Polar.rightSupport a⁺*a=a⁺
  nth_rw 2 [←CFC.posPart_sub_negPart a ha]
  rw [mul_sub,hp,hn,sub_zero]

end Kadison.PositiveWOT

end

end
end

end OAI
