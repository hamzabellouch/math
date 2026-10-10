import Mathlib
import OAI.Geometry.PrescribedPotential.AugmentedVolume
import OAI.Geometry.PrescribedPotential.RealNonlinearDerivative

namespace OAI

/-! Closed Range Smooth. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace ClosedRangeSmooth
universe u
variable {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma isometry_derivative_iff (e : F →ₗᵢ[ℝ] G) (f : E → F) (L : E →L[ℝ] F) (x : E) :
    HasFDerivAt f L x ↔ HasFDerivAt (fun y => e (f y)) (e.toContinuousLinearMap ∘L L) x := by
  simp only [hasFDerivAt_iff_isLittleO]
  conv_lhs => rw [← Asymptotics.isLittleO_norm_left]
  conv_rhs => rw [← Asymptotics.isLittleO_norm_left]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    ← map_sub, e.norm_map]

lemma lift_derivative [CompleteSpace F] (e : F →ₗᵢ[ℝ] G) (f : E → F)
    {x : E} {J : E →L[ℝ] G} (hJ : HasFDerivAt (fun y => e (f y)) J x) :
    ∃ L : E →L[ℝ] F, HasFDerivAt f L x ∧ e.toContinuousLinearMap ∘L L = J := by
  let S := e.range
  have hS : IsClosed (S : Set G) := e.isometry.isClosedEmbedding.isClosed_range
  let r : E → S := fun y => e.equivRange (f y)
  have hmem : ∀ v, J v ∈ S :=
    ClosedDerivative.derivative_mem S hS r hJ
  let L := e.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L J.codRestrict S hmem
  have hcomp : e.toContinuousLinearMap ∘L L = J := by
    ext v
    change e (e.equivRange.symm ⟨J v,hmem v⟩) = J v
    exact congrArg Subtype.val (e.equivRange.apply_symm_apply ⟨J v,hmem v⟩)
  refine ⟨L,(isometry_derivative_iff e f L x).mpr ?_,hcomp⟩
  rwa [hcomp]

 

lemma contDiff_of_isometry (n : ℕ) [CompleteSpace F] (e : F →ₗᵢ[ℝ] G) (f : E → F)
    (hf : ContDiff ℝ n (fun y => e (f y))) : ContDiff ℝ n f := by
  induction n generalizing F G with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero] at hf ⊢
    exact e.isEmbedding.continuous_iff.mpr hf
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt] at hf ⊢
    obtain ⟨J,hJ,hd⟩ := hf
    choose L hL he using fun x => lift_derivative e f (hd x)
    refine ⟨L,?_,hL⟩
    let ep : (E →L[ℝ] F) →ₗᵢ[ℝ] (E →L[ℝ] G) := e.postcomp
    apply ih ep L
    convert hJ using 1
    funext x
    exact he x

lemma contDiff_infty_of_isometry [CompleteSpace F] (e : F →ₗᵢ[ℝ] G) (f : E → F)
    (hf : ContDiff ℝ ∞ (fun y => e (f y))) : ContDiff ℝ ∞ f := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_of_isometry n e f (contDiff_infty.mp hf n)
end ClosedRangeSmooth

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance closedRangeNormedGroup (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance closedRangeNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance closedRangeTopologicalGroup (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance closedRangeContinuousSMul (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma realVolume_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ContDiff ℝ ∞ (D.realVolume k hk) :=
  ClosedRangeSmooth.contDiff_infty_of_isometry
    (D.localizers.realCompletion (k : ℝ)).subtypeₗᵢ _ (D.realVolume_ambient_contDiff k hk)

lemma augmentedVolume_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    ContDiff ℝ ∞ (D.augmentedVolume k hk x₀) := by
  apply ContDiff.prodMk
  · exact (contDiff_snd.neg.exp).smul ((D.realVolume_contDiff k hk).comp contDiff_fst)
  · exact (D.realEvaluation ((k : ℝ)+2) x₀).contDiff.comp contDiff_fst
end GluingData
end GlobalElliptic

end
end

end OAI
