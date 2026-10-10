import Mathlib
import OAI.Geometry.PrescribedPotential.RealVolume

namespace OAI

/-! Real Nonlinear Derivative. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace ClosedDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma derivative_mem (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → S) {J : E →L[ℝ] F} {x : E}
    (hJ : HasFDerivAt (fun y => (f y).val) J x) (v : E) : J v ∈ S := by
  have hc : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x
  have hJ' : HasFDerivAt (fun y => (f y).val) J (x+(0 : ℝ) • v) := by simpa using hJ
  have hd := hJ'.comp_hasDerivAt (0 : ℝ) hc
  apply hS.mem_of_tendsto hd.tendsto_slope
  filter_upwards [] with t
  exact S.smul_mem _ (S.sub_mem (f (x+t • v)).property (f (x+(0 : ℝ) • v)).property)

def restrict (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → S) (hf : Differentiable ℝ (fun y => (f y).val)) (x : E) : E →L[ℝ] S :=
  (fderiv ℝ (fun y => (f y).val) x).codRestrict S
    (derivative_mem S hS f (hf x).hasFDerivAt)

lemma restrict_comp (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → S) (hf : Differentiable ℝ (fun y => (f y).val)) (x : E) :
    S.subtypeL ∘L restrict S hS f hf x = fderiv ℝ (fun y => (f y).val) x := by
  ext v; rfl

lemma hasStrictFDerivAt (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → S) (hf : ContDiff ℝ ∞ (fun y => (f y).val)) (x : E) :
    HasStrictFDerivAt f (restrict S hS f (hf.differentiable (by simp)) x) x := by
  apply (RealClosedDerivative.subtype_iff S f _ x).mpr
  rw [restrict_comp]
  exact hf.hasStrictFDerivAt (by simp)

lemma restrict_continuous (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    (f : E → S) (hf : ContDiff ℝ ∞ (fun y => (f y).val)) :
    Continuous (restrict S hS f (hf.differentiable (by simp))) := by
  let e : (E →L[ℝ] S) →ₗᵢ[ℝ] (E →L[ℝ] F) := S.subtypeₗᵢ.postcomp
  have hIso : Isometry (e : (E →L[ℝ] S) → (E →L[ℝ] F)) := e.isometry
  apply hIso.isEmbedding.continuous_iff.mpr
  change Continuous (fun x => S.subtypeL ∘L restrict S hS f _ x)
  simp_rw [restrict_comp]
  exact (hf.fderiv_right (m := ∞) (by simp)).continuous
end ClosedDerivative

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance nonlinDerivNormedGroup (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance nonlinDerivNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance nonlinDerivTopologicalGroup (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance nonlinDerivContinuousSMul (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def realVolumeDerivative (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  ClosedDerivative.restrict (D.localizers.realCompletion (k : ℝ))
    (Submodule.isClosed_topologicalClosure _) (D.realVolume k hk)
    ((D.realVolume_ambient_contDiff k hk).differentiable (by simp)) u

omit [ConnectedSpace X] in
lemma realVolume_hasStrictFDerivAt (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    HasStrictFDerivAt (D.realVolume k hk) (D.realVolumeDerivative k hk u) u :=
  ClosedDerivative.hasStrictFDerivAt _ (Submodule.isClosed_topologicalClosure _)
    _ (D.realVolume_ambient_contDiff k hk) _

omit [ConnectedSpace X] in
lemma realVolumeDerivative_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    Continuous (D.realVolumeDerivative k hk) :=
  ClosedDerivative.restrict_continuous _ (Submodule.isClosed_topologicalClosure _)
    _ (D.realVolume_ambient_contDiff k hk)

omit [ConnectedSpace X] in
lemma realVolumeDerivative_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    D.realVolumeDerivative k hk 0 = D.realLOrder k :=
  (D.realVolume_hasStrictFDerivAt k hk 0).hasFDerivAt.unique
    (D.realVolume_hasStrictFDerivAt_zero k hk).hasFDerivAt

end GluingData
end GlobalElliptic

end
end

end OAI
