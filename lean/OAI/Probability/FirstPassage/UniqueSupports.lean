import OAI.Probability.FirstPassage.GlobalDifferentiability
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

namespace PlanarFPP
open Set Filter

lemma norm_derivative_subgradient (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (ℓ : Plane →L[ℝ] ℝ) (hd : HasFDerivAt μ ℓ v) (w : Plane) :
    μ v+ℓ (w-v) ≤ μ w := by
  have hc := convex_transverse_profile μ v (w-v) hμ.triangle (norm_positive_homogeneous μ hμ)
  have ha : HasDerivAt (fun t : ℝ => v+t • (w-v)) (w-v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (w-v)).const_add v
  have hd' : HasFDerivAt μ ℓ (v+(0 : ℝ) • (w-v)) := by simpa using hd
  have hp := hd'.comp_hasDerivAt 0 ha
  have hh := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num) hp
  simp only [slope_def_field,sub_zero,div_one,one_smul,zero_smul,add_zero,add_sub_cancel] at hh
  linarith

lemma norm_derivative_support (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (ℓ : Plane →L[ℝ] ℝ) (hd : HasFDerivAt μ ℓ v) :
    ℓ v=μ v ∧ ∀ w, ℓ w ≤ μ w := by
  have h0 := norm_derivative_subgradient μ hμ v ℓ hd 0
  have h2 := norm_derivative_subgradient μ hμ v ℓ hd ((2 : ℝ) • v)
  have hzero : μ 0=0 := (hμ.zero_iff 0).mpr rfl
  have htwo : μ ((2 : ℝ) • v)=2*μ v := by rw [hμ.homogeneous]; norm_num
  have he : (2 : ℝ) • v-v=v := by module
  simp only [zero_sub,map_neg,hzero] at h0
  rw [htwo,he] at h2
  have hv : ℓ v=μ v := by linarith
  refine ⟨hv,?_⟩
  intro w
  have hh := norm_derivative_subgradient μ hμ v ℓ hd w
  rw [map_sub,hv] at hh
  linarith

lemma norm_support_unique (μ : Plane → ℝ) (v : Plane) (ℓ g : Plane →L[ℝ] ℝ)
    (hd : HasFDerivAt μ ℓ v) (hg : g v=μ v) (hlower : ∀ w, g w ≤ μ w) : g=ℓ := by
  have hmin : IsLocalMin (fun w => μ w-g w) v := by
    apply Filter.Eventually.of_forall
    intro w
    have hv : μ v-g v=0 := by rw [hg]; ring
    change μ v-g v ≤ μ w-g w
    rw [hv]
    exact sub_nonneg.mpr (hlower w)
  have he := hmin.hasFDerivAt_eq_zero (hd.sub g.hasFDerivAt)
  exact (sub_eq_zero.mp he).symm

theorem unique_supports_of_differentiable (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) : UniqueNormalizedSupports μ := by
  intro v hv
  have hne : v ≠ 0 := by intro he; have hh := (hμ.zero_iff v).mpr he; linarith
  obtain ⟨ℓ,hℓ⟩ := hd v hne
  obtain ⟨he,hl⟩ := norm_derivative_support μ hμ v ℓ hℓ
  refine ⟨ℓ,⟨by rw [he,hv],hl⟩,?_⟩
  intro g hg
  exact norm_support_unique μ v ℓ g hℓ (by rw [hg.1,hv]) hg.2

end PlanarFPP

end OAI
