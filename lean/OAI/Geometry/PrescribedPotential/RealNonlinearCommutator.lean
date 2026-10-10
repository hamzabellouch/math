import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalNonlinearCommutator
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealNonlinearDerivative
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.RegularityCutoffs

namespace OAI

/-! Real Nonlinear Commutator. -/

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
local instance realNonlinearCommutatorNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance realNonlinearCommutatorNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance realNonlinearCommutatorIsTopologicalAddGroup (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance realNonlinearCommutatorContinuousSMul (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma realVolumeDerivative_val (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u w : D.localizers.RealSobolev ((k : ℝ)+2)) :
    (D.realVolumeDerivative k hk u w).val =
      fderiv ℝ (D.completedVolume k hk) u.val w.val := by
  let J := (D.localizers.realCompletion ((k : ℝ)+2)).subtypeL
  have hd := ((D.completedVolume_contDiff k hk).differentiable (by simp) u.val).hasFDerivAt.comp u
    J.hasFDerivAt
  change (fderiv ℝ (fun y : D.localizers.RealSobolev ((k : ℝ)+2) =>
    D.completedVolume k hk y.val) u) w = _
  exact congrArg (fun L : D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ]
    D.localizers.Sobolev (k : ℝ) => L w) hd.fderiv

lemma nonlinearRemainder_core_real (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (f : RealSmooth A) :
    D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) f.val) ∈
      D.localizers.realCompletion (k : ℝ) := by
  have hh := D.nonlinear_commutator_core k hk p v f.source
  rw [f.ofReal_source] at hh
  have he : D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) f.val) =
      (D.realVolumeDerivative k hk (D.localizers.realEmbed ((k : ℝ)+2) f)
        (D.localizers.realEmbed ((k : ℝ)+2) (D.realLocalizedDerivative p v f))).val -
      D.localizers.embed (k : ℝ) (D.localizedDerivative p v (Smooth.ofReal (g.potentialDensity f.source))) := by
    rw [D.realVolumeDerivative_val]
    change D.nonlinearRemainder k hk p v (D.localizers.embed ((k : ℝ)+2) f.val) =
      fderiv ℝ (D.completedVolume k hk) (D.localizers.embed ((k : ℝ)+2) f.val)
        (D.localizers.embed ((k : ℝ)+2) (D.localizedDerivative p v f.val)) -
      D.localizers.embed (k : ℝ) (D.localizedDerivative p v (Smooth.ofReal (g.potentialDensity f.source)))
    rw [hh,add_sub_cancel_left]
  rw [he]
  apply (D.localizers.realCompletion (k : ℝ)).sub_mem
  · exact Subtype.property _
  · exact (D.localizers.realEmbed (k : ℝ)
      (D.realLocalizedDerivative p v (RealSmooth.ofReal (g.potentialDensity f.source)))).property

lemma nonlinearRemainder_real (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.nonlinearRemainder k hk p v u.val ∈ D.localizers.realCompletion (k : ℝ) := by
  have hc : Continuous (fun u : D.localizers.RealSobolev ((k : ℝ)+2) =>
      D.nonlinearRemainder k hk p v u.val) :=
    (D.nonlinearRemainder_contDiff k hk p v).continuous.comp continuous_subtype_val
  exact (D.localizers.realEmbed_dense ((k : ℝ)+2)).induction_on u
    ((Submodule.isClosed_topologicalClosure _).preimage hc)
    (D.nonlinearRemainder_core_real k hk p v)

def realNonlinearRemainder (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.localizers.RealSobolev (k : ℝ) :=
  ⟨D.nonlinearRemainder k hk p v u.val,D.nonlinearRemainder_real k hk p v u⟩

lemma realNonlinearRemainder_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) : Continuous (D.realNonlinearRemainder k hk p v) :=
  ((D.nonlinearRemainder_contDiff k hk p v).continuous.comp continuous_subtype_val).subtype_mk _

lemma real_commutator_core (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (f : RealSmooth A) :
    D.realVolumeDerivative k hk (D.localizers.realEmbed ((k : ℝ)+2) f)
      (D.localizers.realEmbed ((k : ℝ)+2) (D.realLocalizedDerivative p v f)) =
    D.localizers.realEmbed (k : ℝ)
      (D.realLocalizedDerivative p v (RealSmooth.ofReal (g.potentialDensity f.source))) +
    D.realNonlinearRemainder k hk p v (D.localizers.realEmbed ((k : ℝ)+2) f) := by
  apply Subtype.ext
  rw [D.realVolumeDerivative_val]
  have hh := D.nonlinear_commutator_core k hk p v f.source
  rwa [f.ofReal_source] at hh

def realCompletedDerivative (k : ℕ) (p : ι) (v : EC d) :
    D.localizers.RealSobolev ((k : ℝ)+1) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  ((D.completedDerivative k p v).comp (D.localizers.realCompletion ((k : ℝ)+1)).subtypeL).codRestrict
    (D.localizers.realCompletion (k : ℝ)) (fun u => D.completedDerivative_real k p v u.val u.property)

lemma realCompletedDerivative_embed (k : ℕ) (p : ι) (v : EC d) (f : RealSmooth A) :
    D.realCompletedDerivative k p v (D.localizers.realEmbed ((k : ℝ)+1) f) =
      D.localizers.realEmbed (k : ℝ) (D.realLocalizedDerivative p v f) := by
  apply Subtype.ext
  exact D.completedDerivative_embed k p v f.val

end GluingData
end GlobalElliptic

end
end

end OAI
