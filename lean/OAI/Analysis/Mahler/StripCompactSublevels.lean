import OAI.Analysis.Mahler.StripRankGeometry
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

namespace OAI

/-! The compact-sublevel property, with no regular-value
or compactness premise, for stripTau and stripDomain. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex Metric Real
open MahlerConformal
variable {I J : Type*} [Fintype I] [Fintype J]

lemma stripTau_term_le (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) (j : J) :
    ‖inverseF (stripCoordinate A z j)‖ ^ (2 * (m : ℝ)) ≤ stripTau A m z := by
  unfold stripTau
  exact single_le_sum (fun k _ => Real.rpow_nonneg (norm_nonneg (inverseF (stripCoordinate A z k))) _) (mem_univ j)

/-- The coordinate bound using a closed disk
of radius R^(1/(2m)). -/
theorem strip_sublevel_coordinate_bound (A : J → I → ℝ) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) {z : (I → ℝ) × (I → ℝ)}
    (hz : z ∈ stripDomain A) (hτ : stripTau A m z ≤ R) (j : J) :
    stripCoordinate A z j ∈ F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹) := by
  refine ⟨inverseF (stripCoordinate A z j), ?_, inverseF_right (hz j)⟩
  rw [mem_closedBall_zero_iff]
  exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hR (by positivity)).mpr
    ((stripTau_term_le A m z j).trans hτ)

lemma strip_radius_lt_one {m : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    R ^ (2 * (m : ℝ))⁻¹ < 1 := by
  exact (Real.rpow_lt_one_iff' hR (by positivity)).mpr hR1

lemma strip_disk_compact {m : ℕ} (hm : 0 < m) {R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹)) ∧
    F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹) ⊆ Omega := by
  have hs : closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹) ⊆ ball (0 : ℂ) 1 :=
    closedBall_subset_ball (strip_radius_lt_one hm hR hR1)
  exact ⟨(isCompact_closedBall _ _).image_of_continuousOn (differentiableOn_F.continuousOn.mono hs),
    image_mono hs⟩

/-- Rank gives a compact subset of U containing the closed
R-sublevel. The compact set is the inverse image of the product
of the F-images of closed disks. -/
theorem strip_sublevel_compact_container (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    ∃ K : Set ((I → ℝ) × (I → ℝ)), IsCompact K ∧ K ⊆ stripDomain A ∧
      {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} ⊆ K := by
  let C := F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹)
  have hC := strip_disk_compact hm hR hR1
  refine ⟨stripCoordinate A ⁻¹' {u : J → ℂ | ∀ j, u j ∈ C},
    stripCoordinate_compact_preimage A hA (isCompact_pi_infinite (fun _ => hC.1)), ?_, ?_⟩
  · intro z hz j
    exact hC.2 (hz j)
  · intro z hz j
    exact strip_sublevel_coordinate_bound A hm hR hz.1 hz.2 j

/-- The compact-sublevel mass hypothesis holds for the
finite-strip construction for every 0<R<1. Closure is ambient closure,
and is contained in the open domain. -/
theorem strip_sublevel_compact_closure (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure {z | z ∈ stripDomain A ∧ stripTau A m z < R}) ∧
      closure {z | z ∈ stripDomain A ∧ stripTau A m z < R} ⊆ stripDomain A := by
  obtain ⟨K, hK, hKU, hsub⟩ := strip_sublevel_compact_container A hA hm hR.le hR1
  have hs : {z | z ∈ stripDomain A ∧ stripTau A m z < R} ⊆ K :=
    fun z hz => hsub ⟨hz.1, hz.2.le⟩
  have hc := closure_minimal hs hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hc, hc.trans hKU⟩

end SymmetricMahler

end

end OAI
