import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.CompletedRealification
import OAI.Geometry.PrescribedPotential.NonlinearRemainder
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealNonlinearCommutator

namespace OAI

/-! Real Map Smooth. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance rmapNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance rmapNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance rmapTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance rmapCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

variable [ConnectedSpace X]

omit [ConnectedSpace X] in
lemma realNonlinearRemainder_as_projection (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) :
    D.realNonlinearRemainder k hk p v = fun u =>
      D.realProjection k (D.nonlinearRemainder k hk p v u.val) := by
  funext u
  exact (D.realProjection_of_real k (D.realNonlinearRemainder k hk p v u)).symm

omit [ConnectedSpace X] in
lemma realNonlinearRemainder_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) : ContDiff ℝ ∞ (D.realNonlinearRemainder k hk p v) := by
  rw [D.realNonlinearRemainder_as_projection k hk p v]
  exact (D.realProjection k).contDiff.comp
    ((D.nonlinearRemainder_contDiff k hk p v).comp
      (D.localizers.realCompletion ((k : ℝ)+2)).subtypeL.contDiff)
end GluingData
end GlobalElliptic

end
end

end OAI
