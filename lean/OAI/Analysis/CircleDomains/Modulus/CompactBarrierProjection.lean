import OAI.Analysis.CircleDomains.Sobolev.SobolevBarrierCollapse
import OAI.Analysis.CircleDomains.Topology.PhysicalFrontierCrossings

namespace OAI

/-! A compact set trapped inside bounded regions whose boundary barriers
have vanishing energy has zero projection measure in both directions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem abs_planeTransverse_le_norm (i : Fin 2) (z : EuclideanPlane) :
    |planeTransverse i z| ≤ ‖z‖ := by
  unfold planeTransverse
  split <;> simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z _

 theorem projection_measure_zero_of_compact_barriers
    {K : Set EuclideanPlane} (hK : IsCompact K)
    {U : ℕ → Set EuclideanPlane} (hU : ∀ n, IsOpen (U n))
    (hUc : ∀ n, IsCompact (closure (U n)))
    {v : ℕ → EuclideanPlane → ℝ} (W : ∀ n, DeGiorgi.MemW1pWitness 2 (v n) univ)
    (hv : ∀ n, Continuous (v n)) {L : ℝ} (hL : 0 < L)
    (hs : ∀ n, tsupport (v n) ⊆ ball 0 L)
    (hE : Tendsto (fun n => ∫ x, ‖(W n).weakGrad x‖^2) atTop (𝓝 0))
    (htrap : ∀ᶠ n in atTop, K ⊆ closure (U n) ∧ ∀ x ∈ frontier (U n), v n x = 1)
    (i : Fin 2) : volume (planeTransverse i '' K) = 0 := by
  have hcross : ∀ᶠ n in atTop, ∀ y ∈ planeTransverse i '' K,
      ∃ c ∈ Icc (-L) L, v n (physicalCoordinateLine i y c) = 1 := by
    filter_upwards [htrap] with n hn
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨c,hc⟩ := exists_coordinate_frontier (hU n) (hUc n) i ⟨z,hn.1 hz,rfl⟩
    have hone := hn.2 _ hc
    have hsup : physicalCoordinateLine i (planeTransverse i z) c ∈ tsupport (v n) := by
      apply subset_tsupport
      change v n _ ≠ 0
      rw [hone]
      norm_num
    have hnorm := mem_ball_zero_iff.mp (hs n hsup)
    have hcoord := PiLp.norm_apply_le (physicalCoordinateLine i (planeTransverse i z) c) i
    rw [physicalCoordinateLine_coordinate,Real.norm_eq_abs] at hcoord
    exact ⟨c,abs_le.mp (hcoord.trans hnorm.le),hone⟩
  have hJL : planeTransverse i '' K ⊆ Icc (-L) L := by
    obtain ⟨n,hn⟩ := hcross.exists
    intro y hy
    obtain ⟨c,hc,hvone⟩ := hn y hy
    have hsup : physicalCoordinateLine i y c ∈ tsupport (v n) := by
      apply subset_tsupport
      change v n _ ≠ 0
      rw [hvone]
      norm_num
    have hnorm := mem_ball_zero_iff.mp (hs n hsup)
    have hcoord := abs_planeTransverse_le_norm i (physicalCoordinateLine i y c)
    rw [physicalCoordinateLine_transverse] at hcoord
    exact abs_le.mp (hcoord.trans hnorm.le)
  exact measure_zero_of_vanishing_sobolev_barriers W hv hL hs hE i
    (hK.image (continuous_planeTransverse i)).measurableSet hJL hcross

 theorem physical_subsingleton_of_zero_projection_measure
    {K : Set EuclideanPlane} (hK : IsCompact K) (hconn : IsConnected K)
    (hz : ∀ i : Fin 2, volume (planeTransverse i '' K) = 0) : K.Subsingleton := by
  have hone (i : Fin 2) : (planeTransverse i '' K).Subsingleton := by
    have hc := hconn.image _ (continuous_planeTransverse i).continuousOn
    have he := eq_Icc_of_connected_compact hc (hK.image (continuous_planeTransverse i))
    have hle := nonempty_Icc.mp (he ▸ hc.nonempty)
    have hm := hz i
    rw [he,Real.volume_Icc,ENNReal.ofReal_eq_zero] at hm
    intro a ha b hb
    rw [he] at ha hb
    linarith [ha.1,ha.2,hb.1,hb.2]
  intro x hx y hy
  ext i
  fin_cases i
  · simpa [planeTransverse] using hone 1 (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  · simpa [planeTransverse] using hone 0 (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)

end CircleDomainRigidity

end

end OAI
