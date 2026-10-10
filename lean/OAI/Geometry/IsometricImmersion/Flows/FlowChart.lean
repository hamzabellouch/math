import OAI.Geometry.IsometricImmersion.Flows.FlowInverse
import Mathlib.Topology.IsLocalHomeomorph

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem exists_global_triangularFlow_chart
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      e.source = pairRectangle 2 (-2) 2 ∧
      e.target = triangularFlow Y '' pairRectangle 2 (-2) 2 ∧
      (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D := pairRectangle 2 (-2) 2
  have hD : IsOpen D := pairRectangle_isOpen 2 (-2) 2
  have hTF : ContDiffOn ℝ ∞ (triangularFlow Y) D :=
    contDiffOn_fst.prodMk (cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode)
  have hinj : InjOn (triangularFlow Y) D := triangularFlow_injOn hq hU hSU hY hrange hstart hode
  have hlocal : IsLocalHomeomorphOn (triangularFlow Y) D := by
    intro x hx
    obtain ⟨e, he, hsub, heq, hf, hi⟩ :=
      exists_triangularFlow_smooth_chart hq hU hSU hY hrange hstart hode hx
    exact ⟨e, he, heq.symm⟩
  have hopen : IsOpenMap (D.domRestrict (triangularFlow Y)) := by
    apply IsOpenMap.of_nhds_le
    intro x
    have he : (𝓝 x).map (D.domRestrict (triangularFlow Y)) =
        𝓝 (triangularFlow Y x) := by
      change (𝓝 x).map ((triangularFlow Y) ∘ (Subtype.val : D → ℝ × ℝ)) = _
      rw [← Filter.map_map, hD.isOpenEmbedding_subtypeVal.map_nhds_eq,
        hlocal.map_nhds_eq x.2]
    exact he.ge
  let pe := hinj.toPartialEquiv (triangularFlow Y) D
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hTF.continuousOn hopen hD
  have heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y := rfl
  have hsource : e.source = D := rfl
  refine ⟨e, hsource, rfl, heq, ?_, ?_⟩
  · rw [heq, hsource]
    exact hTF
  · intro y hy
    have hx : e.symm y ∈ D := by
      rw [← hsource]
      exact e.map_target hy
    obtain ⟨A, hA⟩ := triangularFlow_hasFDerivAt_equiv hq hU hSU hY hrange hstart hode hx
    have hAe : HasFDerivAt e (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (e.symm y) := by
      rw [heq]
      exact hA
    have hfe : ContDiffAt ℝ ∞ e (e.symm y) := by
      rw [heq]
      exact hTF.contDiffAt (hD.mem_nhds hx)
    exact (e.contDiffAt_symm hy hAe hfe).contDiffWithinAt

def flowCap (Y : ℝ → ℝ → ℝ) (b : ℝ) : Set (ℝ × ℝ) :=
  triangularFlow Y '' pairRectangle 2 (-2) b

theorem flowCap_mono (Y : ℝ → ℝ → ℝ) {b1 b2 : ℝ} (hb : b1 ≤ b2) :
    flowCap Y b1 ⊆ flowCap Y b2 := by
  apply image_mono
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.trans_le hb⟩

theorem flowCap_isOpen_of_chart {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {b : ℝ} (hb : b ≤ 2) : IsOpen (flowCap Y b) := by
  let C := pairRectangle 2 (-2) b
  have hC : IsOpen C := pairRectangle_isOpen 2 (-2) b
  have hsub : C ⊆ e.source := by
    rw [hsource]
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le hb⟩
  let eb := e.restrOpen C hC
  have hes : eb.source = C := by
    change e.source ∩ C = C
    exact inter_eq_right.mpr hsub
  have het : eb.target = flowCap Y b := by
    rw [← eb.image_source_eq_target, hes]
    change e '' C = triangularFlow Y '' C
    rw [heq]
  rw [← het]
  exact eb.open_target

end SmoothLocal.Flow

end

end OAI
