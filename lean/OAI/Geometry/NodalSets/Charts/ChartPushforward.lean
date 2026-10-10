import OAI.Geometry.NodalSets.Charts.CommonSmoothChart
import OAI.Geometry.NodalSets.Elliptic.SmoothJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def chartPushforward (F : OpenPartialHomeomorph Coord Coord) (u : Coord → ℂ)
    (z : Coord) : ℂ := by
  classical
  exact if z ∈ F.target then u (F.symm z) else 0

lemma chartPushforward_eventually (F : OpenPartialHomeomorph Coord Coord)
    (u : Coord → ℂ) (z : Coord) (hz : z ∈ F.target) :
    chartPushforward F u =ᶠ[𝓝 z] u ∘ F.symm := by
  filter_upwards [F.open_target.mem_nhds hz] with w hw
  simp [chartPushforward,hw]

lemma chartPushforward_pullback (F : OpenPartialHomeomorph Coord Coord)
    (u : Coord → ℂ) (x : Coord) (hx : x ∈ F.source) :
    chartPushforward F u (F x) = u x := by
  simp [chartPushforward,F.map_source hx,F.left_inv hx]

lemma chartPushforward_support (F : OpenPartialHomeomorph Coord Coord)
    (u : Coord → ℂ) (hu : HasCompactSupport u) (hs : tsupport u ⊆ F.source) :
    tsupport (chartPushforward F u) ⊆ F '' tsupport u := by
  have hc : IsCompact (F '' tsupport u) := hu.image_of_continuousOn (F.continuousOn.mono hs)
  apply closure_minimal _ hc.isClosed
  intro z hz
  by_cases ht : z ∈ F.target
  · refine ⟨F.symm z, ?_, F.right_inv ht⟩
    apply subset_closure
    intro he
    exact hz (by simp [chartPushforward,ht,he])
  · exact False.elim (hz (by simp [chartPushforward,ht]))

theorem chartPushforward_smooth (F : OpenPartialHomeomorph Coord Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ F.source) :
    ContDiff ℝ ∞ (chartPushforward F u) ∧ HasCompactSupport (chartPushforward F u) ∧
      tsupport (chartPushforward F u) ⊆ F '' tsupport u := by
  have hsupport := chartPushforward_support F u hc hs
  have hcompact : IsCompact (F '' tsupport u) := hc.image_of_continuousOn (F.continuousOn.mono hs)
  refine ⟨?_,hcompact.of_isClosed_subset isClosed_closure hsupport,hsupport⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ F.target
  · exact (hu.contDiffAt.comp z (hF.contDiffAt (F.open_target.mem_nhds hz))).congr_of_eventuallyEq
      (chartPushforward_eventually F u z hz)
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    obtain ⟨x,hx,rfl⟩ := hsupport h
    exact hz (F.map_source (hs hx))

theorem chartPushforward_derivative (F : OpenPartialHomeomorph Coord Coord)
    (u : Coord → ℂ) (z : Coord) (hz : z ∈ F.target) (k : ℕ) :
    iteratedFDeriv ℝ k (chartPushforward F u) z = iteratedFDeriv ℝ k (u ∘ F.symm) z :=
  ((chartPushforward_eventually F u z hz).iteratedFDeriv ℝ k).self_of_nhds

end
end Yau.Geometry

end OAI
