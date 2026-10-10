import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OrbitalJetBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedDensityMoment

namespace OAI

/-! Expanding smooth cutoffs for the actual orbitals. Their first four
jets are bounded independently of the radius and center. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def orbitalCutoffBump : ContDiffBump (0 : Position) := ⟨1,2,by norm_num,by norm_num⟩

def orbitalCutoff (R : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  orbitalCutoffBump (R⁻¹ • (x-planarCenter u))

theorem orbitalCutoff_smooth (R : ℝ) (u : PlanarPosition) :
    ContDiff ℝ ∞ (orbitalCutoff R u) :=
  orbitalCutoffBump.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

theorem orbitalCutoff_nonnegative (R : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ orbitalCutoff R u x := orbitalCutoffBump.nonneg

theorem orbitalCutoff_le_one (R : ℝ) (u : PlanarPosition) (x : Position) :
    orbitalCutoff R u x ≤ 1 := orbitalCutoffBump.le_one

theorem orbitalCutoff_eq_one {R : ℝ} (hR : 0 < R) (u : PlanarPosition)
    {x : Position} (hx : ‖x-planarCenter u‖ ≤ R) : orbitalCutoff R u x = 1 := by
  apply orbitalCutoffBump.one_of_mem_closedBall
  change dist (R⁻¹ • (x-planarCenter u)) 0 ≤ 1
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  rw [← div_eq_inv_mul]
  exact (div_le_one hR).mpr hx

theorem orbitalCutoff_support {R : ℝ} (hR : 0 < R) (u : PlanarPosition) :
    tsupport (orbitalCutoff R u) ⊆ Metric.closedBall (planarCenter u) (2*R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  apply hx
  apply orbitalCutoffBump.zero_of_le_dist
  change 2 ≤ dist (R⁻¹ • (x-planarCenter u)) 0
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  rw [← div_eq_inv_mul]
  have hh : 2*R < ‖x-planarCenter u‖ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hn
  exact (le_div_iff₀ hR).mpr hh.le

theorem orbitalCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) (u : PlanarPosition) :
    HasCompactSupport (orbitalCutoff R u) :=
  (isCompact_closedBall (planarCenter u) (2*R)).of_isClosed_subset (isClosed_tsupport _)
    (orbitalCutoff_support hR u)

theorem orbitalCutoff_jets_bounded :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ R, 1 ≤ R → ∀ u k, k ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ k (orbitalCutoff R u) x‖ ≤ B := by
  obtain ⟨B,hB,hb⟩ := orbitalCutoffBump.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) orbitalCutoffBump.contDiff 4
  refine ⟨B+1,by linarith,?_⟩
  intro R hR u k hk x
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let L : Position →L[ℝ] Position := R⁻¹ • ContinuousLinearMap.id ℝ Position
  have hL : ‖L‖ ≤ 1 := by
    dsimp [L]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR0),ContinuousLinearMap.norm_id]
    simpa only [mul_one] using inv_le_one_of_one_le₀ hR
  change ‖iteratedFDeriv ℝ k (fun y => (orbitalCutoffBump ∘ L) (y-planarCenter u)) x‖ ≤ B+1
  rw [iteratedFDeriv_comp_sub]
  have h := fourJet_linear_comp L orbitalCutoffBump (orbitalCutoffBump.contDiff : ContDiff ℝ 4 (orbitalCutoffBump : Position → ℝ))
    hB (show (1:ℝ) ≤ 1 from le_rfl) hL hb hk (x-planarCenter u)
  simpa only [one_pow,mul_one] using h.trans (show B*1^4 ≤ B+1 by nlinarith)

end ContinuumCoulomb

end

end OAI
