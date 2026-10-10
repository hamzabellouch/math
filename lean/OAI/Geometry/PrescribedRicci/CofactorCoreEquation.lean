import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.PotentialDensityDifferential
import OAI.Geometry.PrescribedPotential.RealNonlinearCommutator
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SobolevProduct
import OAI.Geometry.PrescribedRicci.CofactorLocalization

namespace OAI

/-! Cofactor Core Equation. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction Matrix.Norms.Elementwise
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance cofactorCoreEquationNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance cofactorCoreEquationNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance cofactorCoreEquationTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance cofactorCoreEquationCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

omit [ConnectedSpace X] in
lemma cofactor_core_forcing (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (φ ψ : RealSmooth A) :
    schwartzCoord (k:ℝ) (SchwartzMap.smulLeftCLM ℂ (D.weightCore p)
      (schwartzDifferential (extendedCoefficient (D.patch p).matrix
        (coefficientBCF (D.cofactorLocalCore p · · φ.val))) (D.outerCore p ψ.val))) =
      (D.realVolumeDerivative k hk (D.localizers.realEmbed ((k:ℝ)+2) φ)
        (D.localizers.realEmbed ((k:ℝ)+2) ψ)).val.val p := by
  have hs : (Module.finrank ℝ (EC d):ℝ) < 2*(k:ℝ) := by
    have hh : (Module.finrank ℝ (EC d):ℝ) < (k:ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  apply realize_injective (k:ℝ)
  rw [← strongEmbedding_distribution (k:ℝ) hs,← strongEmbedding_distribution (k:ℝ) hs]
  congr 1
  ext y
  rw [strongEmbedding_schwartz,SchwartzMap.toBoundedContinuousFunction_apply,D.localizers.strong_localized (k:ℝ) hs,
    SchwartzMap.smulLeftCLM_apply_apply (D.weightCore p).hasTemperateGrowth,smul_eq_mul,
    D.weightCore_apply,D.index_eq]
  split_ifs with hy
  · by_cases hw : D.localizers.weight p ((A.euclideanChart (D.patch p).index).symm y) = 0
    · rw [hw,zero_mul,zero_mul]
    · have hx := subset_tsupport (D.localizers.weight p : X → ℂ) hw
      have he := (A.euclideanChart (D.patch p).index).right_inv hy
      have hh := D.cofactorDifferential_source p φ.source ψ.source hx
      rw [φ.ofReal_source,ψ.ofReal_source,he] at hh
      rw [hh]
      congr 1
      have hv := D.completedVolumeDerivative_source k hk φ.source ψ.source (D.patch p).index
        (x:=((A.euclideanChart (D.patch p).index).symm y)) (by simpa using D.patch_source p hx)
      rw [φ.ofReal_source,ψ.ofReal_source] at hv
      rw [← hv]
      have hd := D.realVolumeDerivative_val k hk
        (D.localizers.realEmbed ((k:ℝ)+2) φ) (D.localizers.realEmbed ((k:ℝ)+2) ψ)
      simp only [Localizers.realEmbed_val] at hd
      simp only [← hd]
      apply Complex.ext
      · rfl
      · exact (D.localizers.real_strong hs _ _).symm
  · exact zero_mul _

end GluingData
end GlobalElliptic

end
end

end OAI
