import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.AugmentedVolume
import OAI.Geometry.PrescribedPotential.CompletedResolvent

namespace OAI

/-! Sobolev Openness. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace LocalNonlinearInverse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
lemma image_mem_nhds {f : E → F} {L : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f L a) (hL : Function.Surjective L)
    {U : Set E} (hU : U ∈ 𝓝 a) : f '' U ∈ 𝓝 (f a) := by
  rw [← hf.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hL)]
  change f ⁻¹' (f '' U) ∈ 𝓝 a
  exact mem_of_superset hU (fun x hx => ⟨x,hx,rfl⟩)
end LocalNonlinearInverse

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance sobolevOpennessNormedAddCommGroup (s : ℝ) :
    NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance sobolevOpennessNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance sobolevOpennessIsTopologicalAddGroup (s : ℝ) :
    IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance sobolevOpennessContinuousSMul (s : ℝ) :
    ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma augmentedVolume_image_nhds (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X)
    {U : Set (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ)} (hU : U ∈ 𝓝 0) :
    D.augmentedVolume k hk x₀ '' U ∈ 𝓝 (D.realConstants (k : ℝ) 1, 0) := by
  obtain ⟨m,hm,he⟩ := D.exists_completedError_small
  obtain ⟨P⟩ := D.localizers.constantProjection_exists
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hi := LocalNonlinearInverse.image_mem_nhds
    (D.augmentedVolume_hasStrictFDerivAt_zero k hk x₀)
    (D.realAugmentedL_bijective m hm he P k hs x₀).2 hU
  rwa [D.augmentedVolume_zero] at hi

 

theorem volume_eventually_solvable (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X)
    {U : Set (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ)} (hU : U ∈ 𝓝 0) :
    ∀ᶠ f in 𝓝 (D.realConstants (k : ℝ) 1),
      ∃ (u : D.localizers.RealSobolev ((k : ℝ)+2)) (b : ℝ),
        (u,b) ∈ U ∧ D.realVolume k hk u = Real.exp b • f ∧
        D.realEvaluation ((k : ℝ)+2) x₀ u = 0 := by
  have hi := D.augmentedVolume_image_nhds k hk x₀ hU
  have ht : Tendsto (fun f : D.localizers.RealSobolev (k : ℝ) => (f, (0 : ℝ)))
      (𝓝 (D.realConstants (k : ℝ) 1)) (𝓝 (D.realConstants (k : ℝ) 1, 0)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [ht hi] with f hf
  obtain ⟨⟨u,b⟩,hu,hv⟩ := hf
  refine ⟨u,b,hu,?_,congrArg Prod.snd hv⟩
  have hh := congrArg (fun z => Real.exp b • z.1) hv
  change Real.exp b • (Real.exp (-b) • D.realVolume k hk u) = Real.exp b • f at hh
  simpa only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul] using hh

end GluingData
end GlobalElliptic

end
end

end OAI
