import Mathlib.Geometry.Manifold.PartitionOfUnity
import OAI.Geometry.NodalSets.Elliptic.PositiveLocalExtension

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem compact_smooth_cutoff {K U : Set Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ beta : Coord → ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      tsupport beta ⊆ U ∧ (∀ x, 0 ≤ beta x ∧ beta x ≤ 1) ∧
      ∀ x ∈ K, beta =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hb1,hb0,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Coord)) hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hsupp : tsupport (b : Coord → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra h
    exact hx (hb0 x h)
  refine ⟨b,b.contMDiff.contDiff,hL.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans hLU,hb,?_⟩
  intro x hx
  exact Filter.Eventually.filter_mono (nhds_le_nhdsSet hx) hb1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem compact_smooth_extension {K U : Set Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : Coord → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : Coord → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  have hsupp : tsupport G ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [G,hz])
  refine ⟨G,hG,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_⟩
  intro x hx
  filter_upwards [hb1 x hx] with z hz
  simp [G,hz]

theorem compact_positive_metric_extension {K U : Set Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v) :
    ∃ G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ,
      ContDiff ℝ ∞ G ∧ (∀ x u v, G x u v = G x v u) ∧
      (∀ x v, v ≠ 0 → 0 < G x v v) ∧ ∀ x ∈ K, G =ᶠ[𝓝 x] g := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  obtain ⟨x0,hx0⟩ := hUn
  let G := fun x ↦ b x • g x + (1-b x) • g x0
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact (hb.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hbU hx)))).add
        ((contDiffAt_const.sub hb.contDiffAt).smul contDiffAt_const)
    · apply (contDiffAt_const (c := g x0)).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x u v
    by_cases hx : x ∈ tsupport b
    · change b x*g x u v+(1-b x)*g x0 u v = b x*g x v u+(1-b x)*g x0 v u
      rw [hs x (hbU hx),hs x0 hx0]
    · simp [G,image_eq_zero_of_notMem_tsupport hx,hs x0 hx0]
  · intro x v hv
    by_cases hx : x ∈ tsupport b
    · have h1 := hp x (hbU hx) v hv
      have h2 := hp x0 hx0 v hv
      have hb0 := (hbr x).1
      have hb1 := (hbr x).2
      change 0 < b x*g x v v+(1-b x)*g x0 v v
      by_cases hz : b x = 0
      · simpa [hz] using h2
      · have ha : 0 < b x := lt_of_le_of_ne hb0 (Ne.symm hz)
        have hleft := mul_pos ha h1
        have hright := mul_nonneg (sub_nonneg.mpr hb1) h2.le
        linarith
    · simpa [G,image_eq_zero_of_notMem_tsupport hx] using hp x0 hx0 v hv
  · intro x hx
    filter_upwards [hb1 x hx] with z hz
    simp [G,hz]

end
end Yau.Geometry

end OAI
