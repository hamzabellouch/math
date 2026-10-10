import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealVolume
import OAI.Geometry.PrescribedPotential.RealPoisson
import OAI.Geometry.PrescribedPotential.RealPoissonEquivalence

namespace OAI

/-! Augmented Volume. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace ExponentialAugment
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma derivative (V : E → F) (L : E →L[ℝ] F) (C : ℝ →L[ℝ] F) (e : E →L[ℝ] ℝ)
    (hv : HasStrictFDerivAt V L 0) (h0 : V 0 = C 1) :
    HasStrictFDerivAt (fun z : E × ℝ => (Real.exp (-z.2) • V z.1, e z.1))
      (((L ∘L ContinuousLinearMap.fst ℝ E ℝ) - (C ∘L ContinuousLinearMap.snd ℝ E ℝ)).prod
        (e ∘L ContinuousLinearMap.fst ℝ E ℝ)) 0 := by
  let π₁ := ContinuousLinearMap.fst ℝ E ℝ
  let π₂ := ContinuousLinearMap.snd ℝ E ℝ
  have hv' : HasStrictFDerivAt (fun z : E × ℝ => V z.1) (L ∘L π₁) 0 :=
    hv.comp 0 π₁.hasStrictFDerivAt
  have he : HasStrictFDerivAt (fun z : E × ℝ => Real.exp (-z.2)) (-π₂) 0 := by
    simpa [π₂] using ((-π₂).hasStrictFDerivAt (x := (0 : E × ℝ))).exp
  have hh := he.smul hv'
  have hn := (e ∘L π₁).hasStrictFDerivAt (x := (0 : E × ℝ))
  have hj := hh.prodMk hn
  have hlin : (Real.exp (-(0 : E × ℝ).2) • (L ∘L π₁) +
      (-π₂).smulRight (V (0 : E × ℝ).1)).prod (e ∘L π₁) =
      ((L ∘L π₁) - (C ∘L π₂)).prod (e ∘L π₁) := by
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · change Real.exp (-0) • L z.1 + (-z.2) • V 0 = L z.1 - C z.2
      rw [neg_zero, Real.exp_zero, one_smul, h0, ← map_smul]
      simp [sub_eq_add_neg]
    · rfl
  rw [hlin] at hj
  exact hj
end ExponentialAugment

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

local instance augmentedVolumeNormedAddCommGroup (s : ℝ) :
    NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance augmentedVolumeNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance augmentedVolumeIsTopologicalAddGroup (s : ℝ) :
    IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance augmentedVolumeContinuousSMul (s : ℝ) :
    ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def augmentedVolume (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X)
    (z : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) :
    D.localizers.RealSobolev (k : ℝ) × ℝ :=
  (Real.exp (-z.2) • D.realVolume k hk z.1, D.realEvaluation ((k : ℝ)+2) x₀ z.1)

lemma augmentedVolume_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    D.augmentedVolume k hk x₀ 0 = (D.realConstants (k : ℝ) 1, 0) := by
  simp [augmentedVolume, D.realVolume_zero]

lemma augmentedVolume_hasStrictFDerivAt_zero (k : ℕ)
    (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    HasStrictFDerivAt (D.augmentedVolume k hk x₀) (D.realAugmentedL k x₀) 0 := by
  exact ExponentialAugment.derivative (D.realVolume k hk) (D.realLOrder k)
    (D.realConstants (k : ℝ)) (D.realEvaluation ((k : ℝ)+2) x₀)
    (D.realVolume_hasStrictFDerivAt_zero k hk) (D.realVolume_zero k hk)

end GluingData
end GlobalElliptic

end
end

end OAI
