import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.GlobalParametrix
import OAI.Geometry.PrescribedPotential.PatchDifferential

namespace OAI

/-! Global Smooth. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff Classical BoundedContinuousFunction
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzCoord_order_zero (f : 𝓢(E, ℂ)) :
    schwartzCoord 0 f = SchwartzMap.toLpCLM ℝ ℂ 2 volume f := by
  apply l2_injective
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [schwartzCoord_distribution, besselPotential_zero, ContinuousLinearMap.id_apply]
  exact (Lp.toTemperedDistribution_toLp_eq f).symm

end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

lemma allRegular_distribution {u : D.Sobolev 0} (hu : D.AllRegular u) (p : ι) :
    ∀ k : ℕ, MemSobolev (2 * (k : ℝ)) 2 (D.distribution 0 p u) := by
  intro k
  obtain ⟨v, hv⟩ := hu (2 * k)
  have h : MemSobolev ((2 * k : ℕ) : ℝ) 2 (D.distribution 0 p u) := by
    rw [← hv, D.distribution_lower (Nat.cast_nonneg _)]
    exact realize_memSobolev _ _
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

 

def globalizeL2 (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target) :
    L2 (EC d) →L[ℝ] D.Sobolev 0 :=
  ((D.embed 0).comp (globalize i κ)).extendOfNorm
    (SchwartzMap.toLpCLM ℝ ℂ 2 volume).toLinearMap

lemma globalizeL2_schwartz (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target)
    (f : 𝓢(EC d, ℂ)) :
    D.globalizeL2 i κ (schwartzCoord 0 f) = D.embed 0 (globalize i κ f) := by
  rw [schwartzCoord_order_zero]
  have hb := globalize_integer_bound D i κ 0
  rw [Nat.cast_zero] at hb
  obtain ⟨C, hC, h⟩ := hb
  have hn : ∀ f : 𝓢(EC d, ℂ),
      ‖D.embed 0 (globalize i κ f)‖ ≤ C * ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume f‖ := by
    intro f
    rw [← schwartzCoord_order_zero]
    exact h f
  exact LinearMap.extendOfNorm_eq (SchwartzMap.denseRange_toLpCLM (by norm_num)) ⟨C, hn⟩ f

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma cutoff_forcing (p : ι) (f : Smooth A) :
    SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val (D.forcing p f) = D.forcing p f := by
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (D.cutoff p).val.hasTemperateGrowth, smul_eq_mul]
  by_cases hy : D.forcing p f y = 0
  · rw [hy, mul_zero]
  · have hs := localizeFun_support A (D.localizers.index p) (D.localizers.weight p) f hy
    obtain ⟨x, hx, he⟩ := hs
    rw [D.index_eq] at he
    rw [← he, D.cutoff_one p x hx, one_mul]

lemma cutoff_distribution (p : ι) (u : D.localizers.Sobolev 0) :
    smulLeftCLM ℂ (D.cutoff p).val (D.localizers.distribution 0 p u) =
      D.localizers.distribution 0 p u := by
  have he : smulLeftCLM ℂ (D.cutoff p).val ∘ D.localizers.distribution 0 p =
      D.localizers.distribution 0 p := by
    apply (D.localizers.embed_dense 0).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, D.localizers.distribution_embed]
    change smulLeftCLM ℂ (D.cutoff p).val (SchwartzMap.toTemperedDistributionCLM (EC d) ℂ volume (D.forcing p f)) = _
    rw [← schwartz_temperate_product_distribution (D.cutoff p).val.hasTemperateGrowth,
      D.cutoff_forcing]
    rfl
  exact congr_fun he u

 

lemma allRegular_coordinate {u : D.localizers.Sobolev 0} (hu : D.localizers.AllRegular u) (p : ι) :
    ∃ f : 𝓢(EC d, ℂ), schwartzCoord 0 f = u.val p := by
  obtain ⟨F, hF, he⟩ := all_even_smooth_representative (D.localizers.allRegular_distribution hu p)
  let f := SchwartzMap.smulLeftCLM ℂ F (D.cutoff p).val
  have hf : SchwartzMap.toTemperedDistributionCLM (EC d) ℂ volume f =
      D.localizers.distribution 0 p u := by
    rw [schwartz_mul_temperate_distribution _ hF, temperateDistribution_bounded, he,
      D.cutoff_distribution]
  refine ⟨f, ?_⟩
  apply realize_injective 0
  rw [realize_schwartzCoord, hf]
  rfl

def reconstruct : D.localizers.Sobolev 0 →L[ℝ] D.localizers.Sobolev 0 :=
  ∑ p, (D.localizers.globalizeL2 (D.patch p).index (D.cutoff p)) ∘L
    (ContinuousLinearMap.proj p) ∘L (D.localizers.closedSpace 0).subtypeL

lemma reconstruct_apply (u : D.localizers.Sobolev 0) :
    D.reconstruct u = ∑ p, D.localizers.globalizeL2 (D.patch p).index (D.cutoff p) (u.val p) := by
  simp only [reconstruct, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.subtypeL_apply]

lemma reconstruct_eq (u : D.localizers.Sobolev 0) : D.reconstruct u = u := by
  have he : D.reconstruct = ContinuousLinearMap.id ℝ _ := by
    apply DFunLike.coe_injective
    apply (D.localizers.embed_dense 0).equalizer (by fun_prop) continuous_id
    funext f
    change D.reconstruct (D.localizers.embed 0 f) = D.localizers.embed 0 f
    rw [D.reconstruct_apply]
    change (∑ p, D.localizers.globalizeL2 (D.patch p).index (D.cutoff p)
      (schwartzCoord 0 (D.forcing p f))) = D.localizers.embed 0 f
    simp_rw [D.localizers.globalizeL2_schwartz]
    rw [← map_sum, D.forcing_reconstruction]
  rw [he, ContinuousLinearMap.id_apply]

 

theorem allRegular_smooth {u : D.localizers.Sobolev 0} (hu : D.localizers.AllRegular u) :
    ∃ f : Smooth A, D.localizers.embed 0 f = u := by
  choose f hf using D.allRegular_coordinate hu
  refine ⟨∑ p, globalize (D.patch p).index (D.cutoff p) (f p), ?_⟩
  rw [map_sum, ← D.reconstruct_eq u, D.reconstruct_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [← hf p, D.localizers.globalizeL2_schwartz]

 

theorem exists_smooth_shifted (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (f : Smooth A) : ∃ u : Smooth A, (m^2 : ℝ) • u - complexL g u = f := by
  obtain ⟨u, hu⟩ := D.allRegular_smooth (D.completedResolvent_regular m hm he f)
  have h2 : D.localizers.embed 2 u = D.completedResolvent m hm he (D.localizers.embed 0 f) := by
    apply D.localizers.lower_injective (by norm_num : (0 : ℝ) ≤ 2)
    rw [D.localizers.lower_embed (by norm_num : (0 : ℝ) ≤ 2), hu]
  refine ⟨u, D.localizers.embed_injective 0 ?_⟩
  have h := D.completedResolvent_equation m hm he (D.localizers.embed 0 f)
  rw [← h2] at h
  simpa only [shiftedOperator, completedL, _root_.sub_apply,
    _root_.smul_apply, D.localizers.lower_embed (by norm_num : (0 : ℝ) ≤ 2),
    D.localizers.extendCore_embed D.complexL_bound, map_sub, map_smul] using h

end GluingData
end GlobalElliptic

end
end

end OAI
