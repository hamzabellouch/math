import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpace
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CylinderUniqueness

namespace OAI

noncomputable section
namespace VelocityDetection.Cylinder
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

theorem probability_vertical : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
  constructor
  simp [Real.volume_Ioc]

theorem measurePreserving_horizontal :
    MeasurePreserving (Prod.fst : Space → Coord 2) measure volume := by
  let := probability_vertical
  exact measurePreserving_fst

def liftL2 : Lp ℝ 2 (volume : Measure (Coord 2)) →L[ℝ] L2Space :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_horizontal).toContinuousLinearMap

theorem coeFn_liftL2 (f : Lp ℝ 2 (volume : Measure (Coord 2))) :
    (fun x => liftL2 f x) =ᵐ[measure] (fun x => f x.1) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_horizontal

theorem norm_liftL2 (f : Lp ℝ 2 (volume : Measure (Coord 2))) : ‖liftL2 f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_horizontal).norm_map f

theorem liftL2_rep {f : Coord 2 → ℝ} {F : Lp ℝ 2 (volume : Measure (Coord 2))}
    (hF : (fun X => F X) =ᵐ[volume] f) :
    (fun x => liftL2 F x) =ᵐ[measure] (fun x => f x.1) :=
  (coeFn_liftL2 F).trans (measurePreserving_horizontal.quasiMeasurePreserving.ae_eq_comp hF)

theorem memLp_lift {f : Coord 2 → ℝ} (hf : MemLp f 2 volume) :
    MemLp (fun x : Space => f x.1) 2 measure :=
  hf.comp_measurePreserving measurePreserving_horizontal

def tailsToL2 : TailSpace.compatible 2 →L[ℝ] L2Space :=
  liftL2.comp (TailSpace.toL2 2)

theorem coeFn_tailsToL2 (f : TailSpace.compatible 2) :
    (fun x => tailsToL2 f x) =ᵐ[measure] (fun x => f.val.1 x.1) :=
  liftL2_rep (TailSpace.coeFn_toL2 f)

end VelocityDetection.Cylinder
end

end OAI
