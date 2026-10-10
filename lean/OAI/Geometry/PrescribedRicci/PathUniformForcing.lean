import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SobolevExponential
import OAI.Geometry.PrescribedRicci.PathUniformSobolevBase
import OAI.Geometry.PrescribedRicci.SmoothPositivePath
import OAI.Geometry.PrescribedRicci.UniformSchwartz
import OAI.Geometry.PrescribedPotential.VolumeNormalization

namespace OAI

/-! Path Uniform Forcing. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical SchwartzMap
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance pathForcingNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance pathForcingNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance pathForcingTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance pathForcingCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma expAffine_uniform_bound (F : RealSmooth A) (B : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ b : ℝ, b ≤ B →
      ‖D.localizers.embed (k:ℝ) (F.expAffine t b).val‖ ≤ C := by
  let m := max k (Module.finrank ℝ (EC d)+1)
  have hm : Module.finrank ℝ (EC d) < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  obtain ⟨Q,hQ⟩ := isCompact_Icc.bddAbove_image
    ((D.exponentialDensity_continuous m hm F).norm.continuousOn)
  have hq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖D.exponentialDensity m hm F t‖ ≤ max Q 0 :=
    (hQ (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  let L := D.localizers.lower (m:ℝ) (k:ℝ)
  refine ⟨‖L‖*(Real.exp B*max Q 0),by positivity,fun t ht b hb => ?_⟩
  have hh : ‖D.localizers.embed (m:ℝ) (F.expAffine t b).val‖ ≤ Real.exp B*max Q 0 := by
    change ‖D.localizers.realEmbed (m:ℝ) (F.expAffine t b)‖ ≤ _
    rw [← D.exponentialDensity_embedViaEnergy m hm F t b,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos b)]
    exact mul_le_mul (Real.exp_le_exp.mpr hb) (hq t ht) (norm_nonneg _) (Real.exp_pos B).le
  have he : L (D.localizers.embed (m:ℝ) (F.expAffine t b).val) =
      D.localizers.embed (k:ℝ) (F.expAffine t b).val :=
    D.localizers.lower_embed (by exact_mod_cast (le_max_left k (Module.finrank ℝ (EC d)+1))) _
  rw [← he]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _))

lemma volumePath_forcing_uniform (line : SemipositiveAnticanonicalMetric A) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed (k:ℝ)
        ((RealSmooth.ofReal (prescribedForcing g line)).expAffine z.time z.constant).val‖ ≤ C := by
  let F := RealSmooth.ofReal (prescribedForcing g line)
  let B := ‖(⟨(prescribedForcing g line).value,(prescribedForcing g line).continuous⟩ : C(X,ℝ))‖
  obtain ⟨C,hC,hb⟩ := D.expAffine_uniform_bound F B k
  refine ⟨C,hC,fun z => hb z.time z.time_mem z.constant ?_⟩
  exact (le_abs_self _).trans (volumePath_scalar_bound g line z.time_mem ⟨z.positive,z.equation⟩)

omit [ConnectedSpace X] in
lemma uniform_localize {Z : Type*} (k : ℕ) (F : Z → Smooth A)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖D.localizers.embed (k:ℝ) (F z)‖ ≤ C)
    (i : Fin A.count) (ρ : Smooth A) (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) :
    UniformSobolev (k:ℝ) (fun z => localize A i ρ hρ (F z)) := by
  obtain ⟨C,hC,hc⟩ := hb
  obtain ⟨B,hB,hb⟩ := D.localization_integer_bound i ρ hρ k
  exact ⟨B*C,mul_nonneg hB hC,fun z => (hb _).trans (mul_le_mul_of_nonneg_left (hc z) hB)⟩
end GluingData

omit [ConnectedSpace X] in
lemma localize_cutoff_product (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) (F : Smooth A) :
    localize A i (cutoffGlobal i κ) (cutoffGlobal_support i κ) F =
      κ.product (A.euclideanChart i).open_target (F.smooth i) := by
  ext y
  by_cases hy : y ∈ (A.euclideanChart i).target
  · rw [localize_apply,localizeFun_apply A _ _ hy]
    have hx : (A.euclideanChart i).symm y ∈ (A.euclideanChart i).source := (A.euclideanChart i).symm.mapsTo hy
    change (if (A.euclideanChart i).symm y ∈ (A.euclideanChart i).source then _ else 0)*_ = _
    rw [ite_eq_left hx,(A.euclideanChart i).right_inv hy]
    rfl
  · have hκ : κ y = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hy (κ.support_sub hs))
    rw [localize_apply]
    change (if y ∈ (A.euclideanChart i).target then _ else 0) = _
    rw [ite_eq_right hy,ChartCutoff.product_apply,hκ,zero_mul]
end GlobalElliptic

end
end

end OAI
