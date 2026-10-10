import OAI.MeasureTheory.Falconer.Angular.CircleMaskCoordinates
import Mathlib.Topology.Maps.Basic

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem continuous_circleTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Continuous (circleTestMask G d hd) := by
  let A := Set.Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let f : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hf : Continuous f := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro dir
    refine ⟨⟨sourceAngle dir,?_,?_⟩,sourceUnitDirection_sourceAngle dir⟩
    · exact (Complex.neg_pi_lt_arg _).le
    · exact Complex.arg_le_pi _
  apply (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr
  have he : circleTestMask G d hd ∘ f = fun θ : A => sourceTestMask G d hd θ := by
    funext θ
    exact circleTestMask_comp G d hd θ
  rw [he]
  exact (sourceTestMask_contDiff G d hd).continuous.comp continuous_subtype_val

noncomputable def circleAntipode (dir : UnitCircle) : UnitCircle :=
  ⟨-(dir:Plane),by simpa using dir.property⟩

theorem sourceUnitDirection_add_pi (θ : ℝ) :
    sourceUnitDirection (θ+Real.pi) = circleAntipode (sourceUnitDirection θ) := by
  apply Subtype.ext
  exact sourceDirection_add_pi θ

theorem circleTestMask_antipodal {G : Set UnitCircle}
    (hG : ∀ dir : UnitCircle, circleAntipode dir ∈ G ↔ dir ∈ G)
    (d : ℝ) (hd : 0 < d) (dir : UnitCircle) :
    circleTestMask G d hd (circleAntipode dir) = circleTestMask G d hd dir := by
  have hp : Function.Periodic (sourceTestMask G d hd) Real.pi := by
    apply smoothAngleMask_periodic
    intro θ
    simpa only [mem_preimage,sourceUnitDirection_add_pi] using hG (sourceUnitDirection θ)
  rw [← sourceUnitDirection_sourceAngle dir,← sourceUnitDirection_add_pi,
    circleTestMask_comp,circleTestMask_comp,hp]

theorem circleTestMask_support_near (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.support (circleTestMask G d hd) ⊆ thickening (d/10) G := by
  intro dir hdir
  have hh : sourceAngle dir ∈ Function.support (sourceTestMask G d hd) := hdir
  obtain ⟨φ,hφ,hclose⟩ := mem_thickening_iff.mp (smoothAngleMask_support _ _ _ hh)
  refine mem_thickening_iff.mpr ⟨sourceUnitDirection φ,hφ,?_⟩
  rw [← sourceUnitDirection_sourceAngle dir]
  change dist (sourceDirection (sourceAngle dir)) (sourceDirection φ) < d/10
  have hl := sourceDirection_dist_le (sourceAngle dir) φ
  linarith

theorem circleTestMask_tsupport_transfer {G H : Set UnitCircle} {d : ℝ} (hd : 0 < d)
    (htransfer : ∀ dir ∈ G, ∀ dir' : UnitCircle, dist (dir:Plane) (dir':Plane) ≤ d → dir' ∈ H) :
    tsupport (circleTestMask G d hd) ⊆ H := by
  have hs := (closure_mono (circleTestMask_support_near G d hd)).trans
    ((closure_thickening_subset_cthickening (d/10) G).trans
      (cthickening_subset_thickening' hd (by linarith) G))
  intro dir hdir
  obtain ⟨v,hv,hclose⟩ := mem_thickening_iff.mp (hs hdir)
  exact htransfer v hv dir (by simpa only [Subtype.dist_eq,dist_comm] using hclose.le)

end PlanarFalconer

end OAI
