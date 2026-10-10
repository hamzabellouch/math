import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevExponential
import OAI.Geometry.PrescribedPotential.AugmentedVolume
import OAI.Geometry.PrescribedPotential.ClosedRangeSmooth

namespace OAI

/-! Smooth Local Inverse. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace ExponentialEvaluation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma orbit_contDiff (L : E →L[ℝ] E) (v : E) : ContDiff ℝ ∞ (orbit L v) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    contDiff_iff_contDiffAt.mpr (fun w => (NormedSpace.exp_analytic (𝕂 := ℝ) w).contDiffAt)
  exact (ContinuousLinearMap.apply ℝ E v).contDiff.comp
    (he.comp (contDiff_id.smul contDiff_const))
end ExponentialEvaluation
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance inverseRealNormedGroup (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance inverseRealNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance inverseRealTopologicalGroup (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance inverseRealContinuousSMul (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

omit [ConnectedSpace X] in
lemma exponentialDensity_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) : ContDiff ℝ ∞ (D.exponentialDensity k hk F) :=
  ExponentialEvaluation.orbit_contDiff _ _

 
theorem exists_volume_localInverse (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    ∃ R : (D.localizers.RealSobolev (k : ℝ) × ℝ) →
        (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ),
      R (D.realConstants (k : ℝ) 1,0) = 0 ∧
      ContDiffAt ℝ ∞ R (D.realConstants (k : ℝ) 1,0) ∧
      (∀ᶠ y in 𝓝 (D.realConstants (k : ℝ) 1,0), D.augmentedVolume k hk x₀ (R y) = y) ∧
      (∀ᶠ u in 𝓝 0, R (D.augmentedVolume k hk x₀ u) = u) := by
  obtain ⟨m,hm,he⟩ := D.exists_completedError_small
  obtain ⟨P⟩ := D.localizers.constantProjection_exists
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let L := D.realPoissonEquiv m hm he P k hs x₀
  have hL : HasFDerivAt (D.augmentedVolume k hk x₀) (L : _ →L[ℝ] _) 0 :=
    (D.augmentedVolume_hasStrictFDerivAt_zero k hk x₀).hasFDerivAt
  have hf := (D.augmentedVolume_contDiff k hk x₀).contDiffAt (x := 0)
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let R := hf.localInverse hL hn
  refine ⟨R,?_,?_,?_,?_⟩
  · simpa only [D.augmentedVolume_zero] using hf.localInverse_apply_image hL hn
  · simpa only [D.augmentedVolume_zero] using hf.to_localInverse hL hn
  · have hh : ∀ᶠ y in 𝓝 (D.augmentedVolume k hk x₀ 0),
        D.augmentedVolume k hk x₀ (R y) = y :=
      (hf.hasStrictFDerivAt' hL hn).eventually_right_inverse
    rwa [D.augmentedVolume_zero] at hh
  · exact (hf.hasStrictFDerivAt' hL hn).eventually_left_inverse

 

theorem exists_smooth_sobolev_path (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (x₀ : X) (F : RealSmooth A) :
    ∃ γ : ℝ → D.localizers.RealSobolev ((k : ℝ)+2) × ℝ,
      γ 0 = 0 ∧ ContDiffAt ℝ ∞ γ 0 ∧
      ∀ᶠ t in 𝓝 0,
        D.realVolume k hk (γ t).1 = Real.exp (γ t).2 • D.exponentialDensity k hk F t ∧
        D.realEvaluation ((k : ℝ)+2) x₀ (γ t).1 = 0 := by
  obtain ⟨R,hR,hr,hh,_⟩ := D.exists_volume_localInverse k hk x₀
  let f : ℝ → D.localizers.RealSobolev (k : ℝ) × ℝ := fun t =>
    (D.exponentialDensity k hk F t,0)
  have hf : ContDiff ℝ ∞ f := (D.exponentialDensity_contDiff k hk F).prodMk contDiff_const
  have hz : f 0 = (D.realConstants (k : ℝ) 1,0) := by
    simp only [f,D.exponentialDensity_zero]
  refine ⟨R ∘ f,by rw [Function.comp_apply,hz,hR],?_,?_⟩
  · apply ContDiffAt.comp 0 _ hf.contDiffAt
    rwa [hz]
  · have ht : Tendsto f (𝓝 0) (𝓝 (D.realConstants (k : ℝ) 1,0)) := by
      simpa only [hz] using hf.continuous.tendsto 0
    filter_upwards [ht.eventually hh] with t ht
    refine ⟨?_,congrArg Prod.snd ht⟩
    have he := congrArg (fun z => Real.exp (R (f t)).2 • z.1) ht
    change Real.exp (R (f t)).2 •
      (Real.exp (-(R (f t)).2) • D.realVolume k hk (R (f t)).1) = _ at he
    simpa only [Function.comp_apply, f, smul_smul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, one_smul] using he
end GluingData
end GlobalElliptic

end
end

end OAI
