import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearScale
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.TwoScaleRegularity
import OAI.Geometry.PrescribedPotential.WeakPositive
import OAI.Geometry.PrescribedRicci.FiniteCofactorPatch
import OAI.Geometry.PrescribedRicci.FixedCofactorBootstrap
import OAI.Geometry.PrescribedRicci.PositiveOpenness
import OAI.Geometry.PrescribedRicci.SmoothLocalInverse

namespace OAI

/-! Smooth Positive Path. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace RealSmooth

def expAffine (F : RealSmooth A) (t b : ℝ) : RealSmooth A := ofReal {
  value := fun x => Real.exp (t*F.source.value x+b)
  smooth i := ((contDiffOn_const.mul (F.source.smooth i)).add contDiffOn_const).exp }

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma expAffine_apply (F : RealSmooth A) (t b : ℝ) (x : X) :
    (F.expAffine t b).val x = (Real.exp (t*F.source.value x+b) : ℂ) := rfl
end RealSmooth
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance smoothPathNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance smoothPathNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance smoothPathTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance smoothPathCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma exponentialDensity_embedViaEnergy (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) (t b : ℝ) :
    Real.exp b • D.exponentialDensity k hk F t = D.localizers.realEmbed (k:ℝ) (F.expAffine t b) := by
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by
    have hh : (Module.finrank ℝ (EC d):ℝ) < (k:ℝ) := by exact_mod_cast hk
    linarith only [hh,Nat.cast_nonneg (α:=ℝ) k]
  apply Subtype.ext
  apply D.localizers.strong_injective (k:ℝ) hs
  ext x
  change D.localizers.strong (k:ℝ) (Real.exp b • (D.exponentialDensity k hk F t).val) x =
    D.localizers.strong (k:ℝ) (D.localizers.embed (k:ℝ) (F.expAffine t b).val) x
  rw [ContinuousLinearMap.map_smul_of_tower,D.localizers.strong_embed _ hs]
  simp only [BoundedContinuousFunction.smul_apply,D.exponentialDensity_strong,
    Complex.real_smul]
  change (Real.exp b:ℂ) * (Real.exp (t*F.source.value x):ℂ) = (F.expAffine t b).val x
  rw [RealSmooth.expAffine_apply,Real.exp_add,Complex.ofReal_mul]
  ring

include D in
 

theorem smooth_positive_path_eventually (F : RealSmooth A) (x₀ : X) :
    ∀ᶠ t : ℝ in 𝓝 0, ∃ (φ : SmoothRealFunction A) (b : ℝ),
      g.PositivePotential φ ∧ φ.value x₀ = 0 ∧
      ∀ x, (g.potentialDensity φ).value x = Real.exp (t*F.source.value x+b) := by
  let k := Module.finrank ℝ (EC d)+1
  have hk : Module.finrank ℝ (EC d) < k := by dsimp [k]; omega
  have hk1 : Module.finrank ℝ (EC d) < k+1 := by omega
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ) := by
    dsimp [k]; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) (Module.finrank ℝ (EC d))]
  obtain ⟨γ,hγ,hγc,hγeq⟩ := D.exists_smooth_sobolev_path (k+1) hk1 x₀ F
  have hfst : Tendsto (fun t => (γ t).1) (𝓝 0) (𝓝 (0 : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))) := by
    simpa only [hγ,Prod.fst_zero] using hγc.continuousAt.fst.tendsto
  have hval : Tendsto (fun t => (γ t).1.val) (𝓝 0) (𝓝 (0 : D.localizers.Sobolev (((k+1:ℕ):ℝ)+2))) :=
    continuous_subtype_val.tendsto 0 |>.comp hfst
  filter_upwards [hγeq,hfst.eventually (D.weakPositive_nhds (k+1) hk1),
    hval.eventually (D.cofactor_small_nhds (k+1) hk1 hs)] with t he hp hc
  obtain ⟨hEq,hn⟩ := he
  rw [D.exponentialDensity_embedViaEnergy] at hEq
  obtain ⟨φ,hφ⟩ := D.cofactor_solution_smooth k hk hs (γ t).1 hc (F.expAffine t (γ t).2) hEq
  refine ⟨φ.source,(γ t).2,?_,?_,?_⟩
  · rw [← hφ] at hp
    exact (D.weakPositive_embed_iffViaEnergy (k+1) hk1 φ).mp hp
  · rw [← hφ,D.realEvaluation_embed (by linarith only [hs] : (Module.finrank ℝ (EC d):ℝ) < 2*(((k+1:ℕ):ℝ)+2))] at hn
    exact hn
  · rw [← hφ,D.realVolume_embed] at hEq
    have hcore := D.localizers.embed_injective ((k+1:ℕ):ℝ) (congrArg Subtype.val hEq)
    intro x
    have hv := congrArg (fun f : Smooth A => (f x).re) hcore
    exact hv
end GluingData
end GlobalElliptic

end
end

end OAI
