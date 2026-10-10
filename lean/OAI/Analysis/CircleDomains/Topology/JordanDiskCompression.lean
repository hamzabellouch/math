import OAI.Analysis.CircleDomains.Topology.RadialDiskCompression
import OAI.Analysis.CircleDomains.Topology.CellularJordanNeighborhood
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Compact subsets of a Jordan disk can be shrunk by an ambient
homeomorphism which fixes the whole exterior of that disk. -/
open Set Metric Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_compression_in_jordan_disk (H : ℂ ≃ₜ ℂ)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ jordanInterior H)
    {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℂ ≃ₜ ℂ, (∀ z ∉ jordanInterior H, F z=z) ∧
      ∀ z ∈ K, dist (F z) (H 0)<ε := by
  classical
  by_cases hne : K.Nonempty
  · let A := H.symm '' K
    have hA : IsCompact A := hK.image H.symm.continuous
    have hAball : A ⊆ ball (0 : ℂ) 1 := by
      rintro _ ⟨z,hz,rfl⟩
      obtain ⟨w,hw,he⟩ := hKD hz
      simpa only [← he,H.symm_apply_apply] using hw
    obtain ⟨x,hx,hmax⟩ := hA.exists_isMaxOn (hne.image H.symm) continuous_norm.continuousOn
    have hR : ‖x‖<1 := mem_ball_zero_iff.mp (hAball hx)
    obtain ⟨δ,hδ,hδH⟩ := Metric.continuousAt_iff.mp H.continuous.continuousAt ε hε
    obtain ⟨a,ha,hshrink⟩ := exists_disk_compression (norm_nonneg x) hR hδ
    let F := H.symm.trans ((diskCompressionHomeomorph a ha).trans H)
    refine ⟨F,?_,?_⟩
    · intro z hz
      have hz1 : 1≤‖H.symm z‖ := by
        by_contra hn
        have hb : H.symm z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
        exact hz ⟨H.symm z,hb,H.apply_symm_apply z⟩
      change H (diskCompression a (H.symm z))=z
      rw [diskCompression_eq_self hz1,H.apply_symm_apply]
    · intro z hz
      have hzmax : ‖H.symm z‖≤‖x‖ := hmax ⟨z,hz,rfl⟩
      have hs := hshrink (H.symm z) hzmax
      change dist (H (diskCompression a (H.symm z))) (H 0)<ε
      exact hδH (by simpa only [dist_zero_right] using hs)
  · refine ⟨Homeomorph.refl ℂ,fun _ _ => rfl,?_⟩
    intro z hz
    exact (hne ⟨z,hz⟩).elim

lemma exists_small_supported_continuum_compression
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {K U : Set ℂ} (hK : IsCompact K) (hKc : IsConnected K)
    (hcomp : IsConnected Kᶜ) (hU : IsOpen U) (hKU : K ⊆ U)
    {ε : ℝ} (hε : 0<ε) :
    ∃ F : ℂ ≃ₜ ℂ, (∀ z ∉ U, F z=z) ∧
      ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y)<ε := by
  obtain ⟨H,hKH,hHU⟩ :=
    exists_jordan_neighborhood_of_nonseparating_continuum hsard hsch hK hKc hcomp hU hKU
  obtain ⟨F,hF,hsmall⟩ := exists_compression_in_jordan_disk H hK hKH
    (half_pos hε)
  refine ⟨F,fun z hz => hF z (fun hd => hz (hHU (subset_closure hd))),?_⟩
  intro x hx y hy
  have hxy := dist_triangle (F x) (H 0) (F y)
  have h1 := hsmall x hx
  have h2 := hsmall y hy
  rw [dist_comm (F y) (H 0)] at h2
  linarith

end CircleDomainRigidity

end

end OAI
