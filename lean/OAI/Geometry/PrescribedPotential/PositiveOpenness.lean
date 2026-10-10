import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.WeakPositive
import OAI.Geometry.PrescribedPotential.SobolevOpenness

namespace OAI

/-! Positive Openness. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance positiveOpennessNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance positiveOpennessNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance positiveOpennessTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance positiveOpennessCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

omit [T2Space X] [CompactSpace X] in
lemma exists_weight_support (x : X) : ∃ p, x ∈ tsupport (D.localizers.weight p : X → ℂ) := by
  by_contra! hn
  have hz : ∑ p, D.localizers.weight p x = 0 := Finset.sum_eq_zero (fun p _ =>
    image_eq_zero_of_notMem_tsupport (hn p))
  rw [D.localizers.sum_one] at hz
  exact one_ne_zero hz

lemma weakPositive_embed_iff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (f : RealSmooth A) :
    D.WeakPositive k (D.localizers.realEmbed ((k : ℝ)+2) f) ↔ g.PositivePotential f.source := by
  constructor
  · intro h i z hz
    let x := (A.chart i).symm z
    have hi : x ∈ (A.chart i).source := (A.chart i).mapsTo_symm hz
    have hiz : A.chart i x = z := (A.chart i).right_inv hz
    obtain ⟨p,hp⟩ := D.exists_weight_support x
    have hj : x ∈ (A.chart (D.patch p).index).source := by simpa using D.patch_source p hp
    have hpos := h p x hp
    rw [D.weakMatrix_embed k hk f p hp] at hpos
    rw [← hiz, g.compatibility i (D.patch p).index x hi hj,
      f.source.hessian_compatibility i (D.patch p).index hi hj, ← add_mul, ← mul_add]
    exact hpos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_det_ne_zero
      (g.transition_det_isUnit i (D.patch p).index hi hj).ne_zero)
  · intro h p x hx
    rw [D.weakMatrix_embed k hk f p hx]
    exact h _ _ ((A.chart (D.patch p).index).mapsTo (by simpa using D.patch_source p hx))

 

theorem positive_volume_eventually_solvable [ConnectedSpace X]
    (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    ∀ᶠ f in 𝓝 (D.realConstants (k : ℝ) 1),
      ∃ (u : D.localizers.RealSobolev ((k : ℝ)+2)) (b : ℝ),
        D.WeakPositive k u ∧ D.realVolume k hk u = Real.exp b • f ∧
        D.realEvaluation ((k : ℝ)+2) x₀ u = 0 := by
  have hU : {z : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ | D.WeakPositive k z.1} ∈ 𝓝 0 :=
    (show Tendsto (Prod.fst : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ → _)
      (𝓝 0) (𝓝 0) from continuous_fst.tendsto 0) (D.weakPositive_nhds k hk)
  exact D.volume_eventually_solvable k hk x₀ hU

end GluingData
end GlobalElliptic

end
end

end OAI
