import OAI.Analysis.CircleDomains.Topology.DiskArcIndexLocal
import OAI.Analysis.CircleDomains.Topology.CircleQuantileArcs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! A Borel version of the explicit index, including a value on the
coincidence set. Its deck identity holds everywhere, before averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology Classical

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

instance {X : Type*} [TopologicalSpace X] (f : X → UnitAddCircle) :
    MeasurableSpace (CircleLiftCover f) := borel _

instance {X : Type*} [TopologicalSpace X] (f : X → UnitAddCircle) :
    BorelSpace (CircleLiftCover f) := ⟨rfl⟩

theorem measurable_normalizedArgument : Measurable normalizedArgument := by
  have h : Measurable (fun z : ℂ =>
      ((Complex.arg z / (2 * Real.pi) : ℝ) : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp
      (Complex.measurable_arg.div_const _)
  convert h using 1
  funext z
  exact normalizedArgument_eq z

theorem measurable_circleRepresentative : Measurable circleRepresentative := by
  exact measurable_unitCircleCut

theorem measurable_diskInitialArgument :
    Measurable (fun p : ℂ × ℂ => diskInitialArgument p.1 p.2) := by
  unfold diskInitialArgument
  exact (measurable_circleRepresentative.comp
    (measurable_normalizedArgument.comp measurable_fst)).add
      ((Complex.measurable_arg.comp
        (measurable_const.sub (measurable_snd.div measurable_fst))).div_const _)

def totalPathArgumentIncrement (p : C(PathTime, ℂ) × ℂ) : ℝ :=
  if h : p ∉ pathHitSet then pathArgumentIncrement ⟨p, h⟩ else 0

theorem measurable_totalPathArgumentIncrement : Measurable totalPathArgumentIncrement := by
  have hm := Measurable.dite (s := (pathHitSet (X := ℂ))ᶜ)
    continuous_pathArgumentIncrement.measurable
    (measurable_const (a := (0 : ℝ))) isClosed_pathHitSet.measurableSet.compl
  convert hm using 1
  funext p
  unfold totalPathArgumentIncrement
  simp only [mem_compl_iff]

theorem totalPathArgumentIncrement_of_avoids (p : AvoidingPathPoint) :
    totalPathArgumentIncrement p.val = pathArgumentIncrement p := by
  unfold totalPathArgumentIncrement
  rw [dite_eq_left p.property]

theorem continuousOn_totalPathArgumentIncrement :
    ContinuousOn totalPathArgumentIncrement (pathHitSet (X := ℂ))ᶜ := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_pathArgumentIncrement.congr
    (fun p => (totalPathArgumentIncrement_of_avoids p).symm)

def totalDiskArcIndex (γ : C(PathTime, ℂ)) (p : CircleLiftCover normalizedArgument) : ℝ :=
  p.height + 1 / 2 - diskInitialArgument (γ 0) p.base -
    totalPathArgumentIncrement (γ, p.base) - 1

theorem measurable_totalDiskArcIndex :
    Measurable (fun p : C(PathTime, ℂ) × CircleLiftCover normalizedArgument =>
      totalDiskArcIndex p.1 p.2) := by
  have hb : Measurable (fun p : C(PathTime, ℂ) × CircleLiftCover normalizedArgument => p.2.base) :=
    (CircleLiftCover.continuous_base normalizedArgument).measurable.comp measurable_snd
  have hh : Measurable (fun p : C(PathTime, ℂ) × CircleLiftCover normalizedArgument => p.2.height) :=
    (CircleLiftCover.continuous_height normalizedArgument).measurable.comp measurable_snd
  exact (((hh.add measurable_const).sub (measurable_diskInitialArgument.comp
    (((continuous_eval_const 0).measurable.comp measurable_fst).prodMk hb))).sub
      (measurable_totalPathArgumentIncrement.comp (measurable_fst.prodMk hb))).sub measurable_const

theorem totalDiskArcIndex_of_avoids (γ : C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) (hp : (γ, p.base) ∉ pathHitSet) :
    totalDiskArcIndex γ p = diskArcIndex ⟨(γ, p.base), hp⟩ p.height := by
  unfold totalDiskArcIndex totalPathArgumentIncrement diskArcIndex
  rw [dite_eq_left hp]

theorem totalDiskArcIndex_translate (γ : C(PathTime, ℂ))
    (p : CircleLiftCover normalizedArgument) (n : ℤ) :
    totalDiskArcIndex γ (p.translate n) = totalDiskArcIndex γ p + (n : ℝ) := by
  simp only [totalDiskArcIndex, CircleLiftCover.base_translate, CircleLiftCover.height_translate]
  ring

theorem continuousAt_totalDiskArcIndex (γ : C(PathTime, ℂ))
    (hstart : ‖γ 0‖ = 1) (p : CircleLiftCover normalizedArgument)
    (hp : ‖p.base‖ < 1) (hmiss : (γ, p.base) ∉ pathHitSet) :
    ContinuousAt (totalDiskArcIndex γ) p := by
  have hb : Continuous (CircleLiftCover.base (f := normalizedArgument)) :=
    CircleLiftCover.continuous_base normalizedArgument
  have hi : ContinuousAt (fun q : CircleLiftCover normalizedArgument =>
      diskInitialArgument (γ 0) q.base) p :=
    (continuousAt_diskInitialArgument hstart hp).comp
      (f := CircleLiftCover.base) hb.continuousAt
  have ht : ContinuousAt totalPathArgumentIncrement (γ, p.base) :=
    continuousOn_totalPathArgumentIncrement.continuousAt
      (isClosed_pathHitSet.isOpen_compl.mem_nhds hmiss)
  exact ((((CircleLiftCover.continuous_height normalizedArgument).continuousAt.add
    continuousAt_const).sub hi).sub
      (ht.comp (f := fun q : CircleLiftCover normalizedArgument => (γ, q.base))
        (continuous_const.prodMk hb).continuousAt)).sub continuousAt_const

end CircleDomainRigidity.FiniteTransfer

end

end OAI
