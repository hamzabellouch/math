import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEquicontinuity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaL2Cutoff
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict

namespace OAI

/-! Compactness of the local L2 restrictions of the actual unit-energy
cusp test functions. Arzela--Ascoli is applied only on a bounded height interval. -/
noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace CubicFirstMoment

def cubicThetaRadialExtension (R : ℝ) (hR : 0 ≤ R) :
    (Icc (0:ℝ) R →ᵇ ℂ) →L[ℝ] CubicThetaRadialL2 :=
  (Lp.extendByZeroₗᵢ (μ:=volume) (E:=ℂ) (p:=2) (s:=Icc 0 R) measurableSet_Icc).toContinuousLinearMap.comp
    ((BoundedContinuousFunction.toLp 2 (volume.restrict (Icc 0 R)) ℝ).comp
      (BoundedContinuousFunction.compContinuousCLM ℂ ℝ ⟨projIcc 0 R hR,continuous_projIcc⟩))

lemma cubicThetaRadialExtension_test (A R : ℝ) (hR : 0 ≤ R) (f : CubicThetaRadialUnitTests A) :
    cubicThetaRadialExtension R hR (cubicThetaRadialCompactRestriction A R f)=
      cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
        (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val)) := by
  let g := (cubicThetaRadialCompactRestriction A R f).compContinuous
    (⟨projIcc 0 R hR,continuous_projIcc⟩:C(ℝ,Icc (0:ℝ) R))
  let G := BoundedContinuousFunction.toLp 2 (volume.restrict (Icc 0 R)) ℝ g
  have hg := BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict (Icc 0 R)) ℝ g
  have hg' := (ae_restrict_iff' measurableSet_Icc).mp hg
  have hE := Lp.extendByZeroₗᵢ_ae_eq (μ:=volume) (p:=2) (s:=Icc 0 R) (hs:=measurableSet_Icc) G
  apply Lp.ext
  filter_upwards [hE,hg',cubicThetaL2Cutoff_coe (Icc 0 R) measurableSet_Icc
    (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val)),
    cubicThetaRadialInclusion_test A f.val] with t he hb hk hf
  change (Lp.extendByZeroₗᵢ (μ:=volume) (E:=ℂ) (p:=2) (s:=Icc 0 R) measurableSet_Icc) G t=_
  rw [he,hk]
  by_cases ht : t∈Icc 0 R
  · rw [indicator_of_mem ht,indicator_of_mem ht,hb ht,hf]
    change (f.val:ℝ → ℂ) (projIcc 0 R hR t).val=(f.val:ℝ → ℂ) t
    rw [projIcc_of_mem hR ht]
  · simp only [indicator_of_notMem ht]

theorem cubicThetaRadialLocal_precompact (A : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (closure (Set.range (fun f : CubicThetaRadialUnitTests A =>
      cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
        (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val))))) := by
  have hK := (cubicThetaRadialRestriction_precompact A hR).image
    (cubicThetaRadialExtension R hR).continuous
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  rintro y ⟨f,rfl⟩
  exact ⟨cubicThetaRadialCompactRestriction A R f,
    subset_closure ⟨f,rfl⟩,cubicThetaRadialExtension_test A R hR f⟩

end CubicFirstMoment

end

end OAI
