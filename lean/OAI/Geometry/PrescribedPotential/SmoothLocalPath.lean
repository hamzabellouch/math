import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SobolevExponential
import OAI.Geometry.PrescribedPotential.FixedScaleBootstrap
import OAI.Geometry.PrescribedPotential.PositiveOpenness
import OAI.Geometry.PrescribedPotential.TwoScaleRegularity

namespace OAI

/-! Smooth Local Path. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace RealSmooth

def exponentialForcing (F : RealSmooth A) (t : ℝ) : SmoothRealFunction A where
  value := fun x => Real.exp (t * F.source.value x)
  smooth i := by
    exact (contDiffOn_const.mul (F.source.smooth i)).exp

end RealSmooth
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance smPathNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance smPathNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance smPathTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance smPathCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma exponentialDensity_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (F : RealSmooth A) (t : ℝ) :
    D.exponentialDensity k hk F t =
      D.localizers.realEmbed (k : ℝ) (RealSmooth.ofReal (F.exponentialForcing t)) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  apply Subtype.ext
  apply D.localizers.strong_injective (k : ℝ) hs
  ext x
  rw [D.exponentialDensity_strong]
  change _ = D.localizers.strong (k : ℝ) (D.localizers.embed (k : ℝ) _) x
  rw [D.localizers.strong_embed _ hs]
  rfl

include D in
 

theorem smooth_path_eventually_solvable (F : RealSmooth A) (x₀ : X) :
    ∀ᶠ t : ℝ in 𝓝 0, ∃ (φ : SmoothRealFunction A) (b : ℝ),
      g.PositivePotential φ ∧ φ.value x₀ = 0 ∧
      ∀ x, (g.potentialDensity φ).value x = Real.exp (t * F.source.value x + b) := by
  let s := Module.finrank ℝ (EC d) + 1
  have hs : Module.finrank ℝ (EC d) < s := by dsimp [s]; omega
  have hk : Module.finrank ℝ (EC d) < s+1 := by omega
  let U : Set (D.localizers.RealSobolev (((s+1 : ℕ) : ℝ)+2) × ℝ) := {z |
    (∀ R : RealSmooth A, D.realVolume (s+1) hk z.1 = D.localizers.realEmbed ((s+1 : ℕ) : ℝ) R →
      ∃ φ : RealSmooth A, D.localizers.realEmbed (((s+1 : ℕ) : ℝ)+2) φ = z.1) ∧
    D.WeakPositive (s+1) z.1}
  have hU : U ∈ 𝓝 0 := by
    have ht : Tendsto (Prod.fst : D.localizers.RealSobolev (((s+1 : ℕ) : ℝ)+2) × ℝ → _)
        (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
    exact ht ((D.fixed_spatial_smoothness s hs x₀).and (D.weakPositive_nhds (s+1) hk))
  have ht := (D.exponentialDensity_continuous (s+1) hk F).tendsto 0
  rw [D.exponentialDensity_zero] at ht
  filter_upwards [ht.eventually (D.volume_eventually_solvable (s+1) hk x₀ hU)] with t ht
  obtain ⟨u,b,hu,hV,hN⟩ := ht
  obtain ⟨hSm,hP⟩ := hu
  have he : D.realVolume (s+1) hk u = D.localizers.realEmbed ((s+1 : ℕ) : ℝ)
      (Real.exp b • RealSmooth.ofReal (F.exponentialForcing t)) := by
    rw [hV,D.exponentialDensity_embed,map_smul]
  obtain ⟨φ,hφ⟩ := hSm _ he
  change D.localizers.realEmbed (((s+1 : ℕ) : ℝ)+2) φ = u at hφ
  refine ⟨φ.source,b,?_,?_,?_⟩
  · apply (D.weakPositive_embed_iff (s+1) hk φ).mp
    rwa [hφ]
  · rw [← hφ,D.realEvaluation_embed] at hN
    · exact hN
    · have hh : (Module.finrank ℝ (EC d) : ℝ) < (s : ℝ) := by exact_mod_cast hs
      push_cast
      linarith only [hh, Nat.cast_nonneg (α := ℝ) s]
  · intro x
    rw [← hφ,D.realVolume_embed,D.exponentialDensity_embed] at hV
    have hh := congrArg (D.realEvaluation ((s+1 : ℕ) : ℝ) x) hV
    have hpos : (Module.finrank ℝ (EC d) : ℝ) < 2*((s+1 : ℕ) : ℝ) := by
      have hh : (Module.finrank ℝ (EC d) : ℝ) < (s : ℝ) := by exact_mod_cast hs
      push_cast
      linarith only [hh, Nat.cast_nonneg (α := ℝ) s]
    rw [map_smul,D.realEvaluation_embed hpos,D.realEvaluation_embed hpos] at hh
    change (g.potentialDensity φ.source).value x = Real.exp b * Real.exp (t * F.source.value x) at hh
    rw [hh,Real.exp_add]
    ring
end GluingData
end GlobalElliptic

end
end

end OAI
