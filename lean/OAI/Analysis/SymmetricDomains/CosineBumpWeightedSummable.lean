import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective
import OAI.Analysis.SymmetricDomains.SmoothFlatWeightedFourier

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma exists_boundary_of_weighted_summable (f : C(Circle,ℂ))
    (hf : Summable (fun n : ℤ => weight n*‖fourierCoeff f n‖)) :
    ∃ F : Space, boundary F = f := by
  have hs : Summable (fun n : ℤ => (fourierCoeff f n) •
      ((AddMonoidAlgebra.single n 1 : Poly) : Space)) := by
    apply hf.of_norm_bounded
    intro n
    rw [norm_smul,UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
    simp only [norm_one,mul_one]
    exact le_of_eq (mul_comm _ _)
  have ha : Summable (fourierCoeff f) := by
    apply hf.of_norm_bounded
    intro n
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_weight n)
  refine ⟨∑' n : ℤ, (fourierCoeff f n) • ((AddMonoidAlgebra.single n 1 : Poly) : Space),?_⟩
  have hb := boundary.hasSum hs.hasSum
  simp only [map_smul,boundary_single,one_smul] at hb
  exact hb.unique (hasSum_fourier_series_of_summable ha)

lemma exists_real_boundary_of_weighted_summable (f : C(Circle,ℝ))
    (hf : Summable (fun n : ℤ => weight n*
      ‖fourierCoeff (fun θ => (f θ : ℂ)) n‖)) :
    ∃ F : realAlgebra, ∀ θ, realEvaluation θ F = f θ := by
  let g : C(Circle,ℂ) := ⟨fun θ => f θ,by fun_prop⟩
  obtain ⟨F,hF⟩ := exists_boundary_of_weighted_summable g hf
  have hr : conjugate F = F := by
    apply boundary_injective
    ext θ
    rw [boundary_conjugate,hF]
    simp [g]
  refine ⟨⟨F,hr⟩,?_⟩
  intro θ
  change (boundary F θ).re = f θ
  rw [hF]
  rfl

def circleCos : C(Circle,ℝ) :=
  ⟨fun θ => (fourier 1 θ).re,Complex.continuous_re.comp (fourier 1).continuous⟩

lemma circleCos_zero : circleCos 0 = 1 := by simp [circleCos]

lemma circleCos_coe (t : ℝ) : circleCos (t : Circle) = Real.cos (2*Real.pi*t) := by
  change (fourier 1 (t : Circle)).re = _
  rw [fourier_coe_apply,Complex.exp_re]
  simp [Complex.mul_re,Complex.mul_im]

lemma circleCos_half : circleCos ((1/2 : ℝ) : Circle) = -1 := by
  rw [circleCos_coe]
  have hh : 2*Real.pi*(1/2) = Real.pi := by ring
  rw [hh,Real.cos_pi]

def cosineBump (r R : ℝ) (hr : 0 < r) (hR : r < R) : C(Circle,ℝ) :=
  let B : ContDiffBump (-1 : ℝ) := ⟨r,R,hr,hR⟩
  ⟨fun θ => B (circleCos θ),B.continuous.comp circleCos.continuous⟩

lemma cosineBump_weighted_summable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (hR2 : R < 2) :
    Summable (fun n : ℤ => weight n*
      ‖fourierCoeff (fun θ => (cosineBump r R hr hR θ : ℂ)) n‖) := by
  let B : ContDiffBump (-1 : ℝ) := ⟨r,R,hr,hR⟩
  let f : ℝ → ℂ := fun t => B (Real.cos (2*Real.pi*t))
  have hfc : ContDiff ℝ ∞ f := by
    apply Complex.ofRealCLM.contDiff.comp
    exact B.contDiff.comp (by fun_prop)
  have hevent (a : ℝ) (ha : Real.cos (2*Real.pi*a) = 1) : f =ᶠ[𝓝 a] 0 := by
    have hc : ContinuousAt (fun t : ℝ => dist (Real.cos (2*Real.pi*t)) (-1 : ℝ)) a := by fun_prop
    have hn : R < dist (Real.cos (2*Real.pi*a)) (-1 : ℝ) := by
      norm_num [ha,Real.dist_eq]
      exact hR2
    filter_upwards [hc.eventually (Ioi_mem_nhds hn)] with t ht
    change (B (Real.cos (2*Real.pi*t)) : ℂ) = 0
    rw [B.zero_of_le_dist ht.le,Complex.ofReal_zero]
  have h0 := hevent 0 (by simp)
  have h1 := hevent 1 (by simp [Real.cos_two_pi])
  have hs := Release061.smooth_flat_weighted_fourier hfc h0 h1
  have heq : (fun θ => (cosineBump r R hr hR θ : ℂ)) = AddCircle.liftIoc 1 0 f := by
    funext θ
    let t := (AddCircle.equivIoc 1 0 θ).val
    have ht : t ∈ Ioc (0 : ℝ) (0+1) := (AddCircle.equivIoc 1 0 θ).property
    have htθ : (t : Circle) = θ := AddCircle.coe_equivIoc (p := 1) (a := 0) (y := θ)
    rw [← htθ,AddCircle.liftIoc_coe_apply ht]
    simp [cosineBump,B,f,circleCos_coe]
  simpa only [weight,heq,fourierCoeff_liftIoc_eq,zero_add] using hs

end Release061.Wiener

end

end OAI
