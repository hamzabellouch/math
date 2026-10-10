import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedNuclearHardy
import OAI.Analysis.CoulombRadii.FormDomain.CubeGradient

namespace OAI

/-! One fixed smooth cutoff supplies all translated and scaled near-nucleus
Hardy estimates; its constants are independent of the mesh and particle count. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def nuclearBump : ContDiffBump (0 : Position) := ⟨1,2,by norm_num,by norm_num⟩

def nuclearCutoff {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) (x : Configuration n) : ℝ :=
  nuclearBump (r⁻¹ • (Coulomb.position x i-a))

theorem nuclearBump_derivative_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x, ‖fderiv ℝ (nuclearBump : Position → ℝ) x‖ ≤ C := by
  have hβ : ContDiff ℝ ∞ (nuclearBump : Position → ℝ) := nuclearBump.contDiff
  have hc := ((nuclearBump.hasCompactSupport.fderiv ℝ).isCompact_range
    (hβ.continuous_fderiv (by simp))).exists_bound_of_continuousOn
      (f := fun z => z) continuous_id.continuousOn
  obtain ⟨C,hC⟩ := hc
  exact ⟨max C 1,le_max_right _ _,fun x => (hC _ ⟨x,rfl⟩).trans (le_max_left _ _)⟩

theorem nuclearCutoff_contDiff {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) :
    ContDiff ℝ ∞ (nuclearCutoff r a i) :=
  nuclearBump.contDiff.comp (((Coulomb.positionCLM i).contDiff.sub contDiff_const).const_smul r⁻¹)

theorem nuclearCutoff_abs_le_one {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) (x : Configuration n) :
    |nuclearCutoff r a i x| ≤ 1 := by
  unfold nuclearCutoff
  rw [abs_of_nonneg nuclearBump.nonneg]
  exact nuclearBump.le_one

theorem nuclearCutoff_fderiv {n : ℕ} (r : ℝ) (a : Position) (i : Fin n) (x : Configuration n) :
    fderiv ℝ (nuclearCutoff r a i) x =
      (fderiv ℝ (nuclearBump : Position → ℝ) (r⁻¹ • (Coulomb.position x i-a))).comp
        (r⁻¹ • Coulomb.positionCLM i) := by
  have hβ : ContDiff ℝ ∞ (nuclearBump : Position → ℝ) := nuclearBump.contDiff
  exact ((hβ.differentiable (by simp) _).hasFDerivAt.comp x
    (((Coulomb.positionCLM i).hasFDerivAt.sub_const a).const_smul r⁻¹)).fderiv

theorem nuclearCutoff_partial_bound {C r : ℝ} (hC : ∀ x, ‖fderiv ℝ (nuclearBump : Position → ℝ) x‖ ≤ C)
    (hr : 0 < r) {n : ℕ} (a : Position) (i : Fin n) (j : Fin n × Fin 3) (x : Configuration n) :
    |fderiv ℝ (nuclearCutoff r a i) x (EuclideanSpace.single j 1)| ≤ C/r := by
  rw [nuclearCutoff_fderiv,ContinuousLinearMap.comp_apply,smul_apply,
    map_smul,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hr)]
  have hv : ‖Coulomb.positionCLM i (EuclideanSpace.single j 1)‖ ≤ 1 := by
    rcases j with ⟨j,k⟩
    rw [Coulomb.positionCLM_single]
    split_ifs <;> simp [PiLp.norm_single]
  have h := (fderiv ℝ (nuclearBump : Position → ℝ) (r⁻¹ • (Coulomb.position x i-a))).le_opNorm
    (Coulomb.positionCLM i (EuclideanSpace.single j 1))
  rw [Real.norm_eq_abs] at h
  calc
    _ ≤ r⁻¹*(‖fderiv ℝ (nuclearBump : Position → ℝ) (r⁻¹ • (Coulomb.position x i-a))‖*1) :=
      mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))) (inv_pos.mpr hr).le
    _ ≤ r⁻¹*C := by gcongr; simpa only [mul_one] using hC _
    _ = _ := by ring

theorem nuclearCutoff_one {n : ℕ} {r : ℝ} (hr : 0 < r) (a : Position) (i : Fin n)
    (x : Configuration n) (hx : ‖Coulomb.position x i-a‖ ≤ r) : nuclearCutoff r a i x = 1 := by
  apply nuclearBump.one_of_mem_closedBall
  change ‖r⁻¹ • (Coulomb.position x i-a)-0‖ ≤ 1
  rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have h := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hr).le
  simpa only [inv_mul_cancel₀ hr.ne'] using h

theorem nuclearCutoff_outside {n : ℕ} {r : ℝ} (hr : 0 < r) (a : Position) (i : Fin n)
    (x : Configuration n) (hx : 2*r < ‖Coulomb.position x i-a‖) :
    nuclearCutoff r a i x = 0 ∧ fderiv ℝ (nuclearCutoff r a i) x = 0 := by
  have hs : 2 < ‖r⁻¹ • (Coulomb.position x i-a)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),mul_comm,← div_eq_mul_inv]
    exact (lt_div_iff₀ hr).mpr hx
  constructor
  · apply nuclearBump.zero_of_le_dist
    simpa only [dist_zero_right,nuclearBump] using hs.le
  · rw [nuclearCutoff_fderiv]
    have hnot : r⁻¹ • (Coulomb.position x i-a) ∉ tsupport (nuclearBump : Position → ℝ) := by
      rw [nuclearBump.tsupport_eq,Metric.mem_closedBall,dist_zero_right]
      exact not_le.mpr hs
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    rfl

end ContinuumCoulomb

end

end OAI
