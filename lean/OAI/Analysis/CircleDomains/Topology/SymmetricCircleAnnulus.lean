import OAI.Analysis.CircleDomains.Reflection.UnitCircleReflection
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Fixed two-sided annuli subordinate to neighborhoods of the unit
circle. Their reflection symmetry is exact. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def symmetricCircleAnnulus (R:ℝ) : Set ℂ := {z | R⁻¹<‖z‖ ∧ ‖z‖<R}

lemma isOpen_symmetricCircleAnnulus (R:ℝ) : IsOpen (symmetricCircleAnnulus R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma symmetricCircleAnnulus_ne_zero {R:ℝ} (hR:0<R) {z:ℂ}
    (hz:z∈symmetricCircleAnnulus R) : z≠0 :=
  norm_pos_iff.mp ((inv_pos.mpr hR).trans hz.1)

lemma symmetricCircleAnnulus_reflection {R:ℝ} (hR:0<R) {z:ℂ}
    (hz:z∈symmetricCircleAnnulus R) : unitCircleReflection z∈symmetricCircleAnnulus R := by
  have hzn : 0<‖z‖ := (inv_pos.mpr hR).trans hz.1
  change R⁻¹<‖unitCircleReflection z‖ ∧ ‖unitCircleReflection z‖<R
  rw [unitCircleReflection_norm]
  exact ⟨(inv_lt_inv₀ hR hzn).mpr hz.2,(inv_lt_comm₀ hzn hR).mpr hz.1⟩

lemma unit_circle_subset_symmetricCircleAnnulus {R:ℝ} (hR:1<R) :
    sphere (0:ℂ) 1⊆symmetricCircleAnnulus R := by
  intro z hz
  have he : ‖z‖=1 := mem_sphere_zero_iff_norm.mp hz
  change R⁻¹<‖z‖ ∧ ‖z‖<R
  rw [he]
  exact ⟨(inv_lt_one₀ (zero_lt_one.trans hR)).mpr hR,hR⟩

lemma exists_symmetricCircleAnnulus_subset {U:Set ℂ} (hU:IsOpen U)
    (hcircle:sphere (0:ℂ) 1⊆U) :
    ∃R:ℝ,1<R ∧ symmetricCircleAnnulus R⊆U := by
  obtain ⟨ε,hε,hεU⟩ := (isCompact_sphere (0:ℂ) 1).exists_thickening_subset_open hU hcircle
  let R := 1+ε/2
  have hR : 1<R := by dsimp [R];linarith
  have hRp : 0<R := zero_lt_one.trans hR
  have hRi : 1-R⁻¹≤R-1 := by
    have he : 1-R⁻¹=(R-1)/R := by field_simp
    rw [he]
    exact div_le_self (by linarith) hR.le
  refine ⟨R,hR,?_⟩
  intro z hz
  have hz0 := symmetricCircleAnnulus_ne_zero hRp hz
  have hnorm : ‖NormedSpace.normalize z‖=1 := NormedSpace.norm_normalize hz0
  apply hεU
  apply mem_thickening_iff.mpr
  refine ⟨NormedSpace.normalize z,mem_sphere_zero_iff_norm.mpr hnorm,?_⟩
  have he : z-NormedSpace.normalize z=(‖z‖-1) • NormedSpace.normalize z := by
    rw [sub_smul,one_smul,NormedSpace.norm_smul_normalize]
  rw [dist_eq_norm,he,norm_smul,hnorm,mul_one,Real.norm_eq_abs]
  apply abs_lt.mpr
  constructor
  · have hzlo := hz.1
    have hsmall : R-1<ε := by dsimp [R];linarith
    linarith
  · have hzhi := hz.2
    dsimp [R] at hzhi
    linarith

end CircleDomainRigidity

end

end OAI
