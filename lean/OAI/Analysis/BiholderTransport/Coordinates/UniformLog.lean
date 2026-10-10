import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.FactorNorm

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section UniformLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_prefix_log_derivative_bounds :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4), ∀ y : M,
      ∀ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
      DifferentiableAt ℝ q p → q p=0 →
      (∀ᶠ a in 𝓝 p, riemannianExp y (q a)=riemannianExp x (t • a)) →
      ∀ v, c*‖v‖≤‖fderiv ℝ q p v‖ ∧ ‖fderiv ℝ q p v‖≤C*‖v‖ := by
  obtain ⟨l,u,hl,hu,H⟩ := uniform_split_exp_bounds (n := n) (M := M)
  refine ⟨l/4,u,div_pos hl (by norm_num),hu,?_⟩
  intro x p hp t ht y q hq hqp hqr v
  have htpos : 0<t := by linarith [ht.1]
  have htone : t≤1 := by linarith [ht.2]
  have hb := (H (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp t ht).1 (t • v)
  rw [←prefix_zero_log_fderiv_norm hq hqp hqr v] at hb
  change l*‖t • v‖≤‖fderiv ℝ q p v‖ ∧ ‖fderiv ℝ q p v‖≤u*‖t • v‖ at hb
  rw [norm_smul_of_nonneg htpos.le] at hb
  constructor
  · have hmul := mul_le_mul_of_nonneg_right ht.1 (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hl.le
    nlinarith [hb.1]
  · have hmul := mul_le_mul_of_nonneg_right htone (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hu.le
    nlinarith [hb.2]

lemma uniform_suffix_log_derivative_bounds :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ t∈Icc (1/4:ℝ) (3/4),
      ∀ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p),
      DifferentiableAt ℝ q p → q p∈injectivityDomain (riemannianExp x p) →
      (∀ᶠ a in 𝓝 p, riemannianExp (riemannianExp x p) (q a)=riemannianExp x (t • a)) →
      ∀ v, c*‖v‖≤‖fderiv ℝ q p v‖ ∧ ‖fderiv ℝ q p v‖≤C*‖v‖ := by
  obtain ⟨l,u,hl,hu,H⟩ := uniform_split_exp_bounds (n := n) (M := M)
  refine ⟨l/(4*u),u/l,div_pos hl (mul_pos (by norm_num) hu),div_pos hu hl,?_⟩
  intro x p hp t ht q hq hqI hqr v
  have htpos : 0<t := by linarith [ht.1]
  have htone : t<1 := by linarith [ht.2]
  have htotal := suffix_log_total_eq_reverse hp htpos htone hqI hqr.self_of_nhds
  have hr := (H (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp t ht).2
  change ∀ v, let r := reverseRay (tangentScale (1-t) (sprayFlow t
      (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)));
      l*‖v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
        (riemannianExp r.1) r.2 v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) r.1) 𝓘(ℝ,Model n)
        (riemannianExp r.1) r.2 v‖≤u*‖v‖ at hr
  rw [←htotal] at hr
  have hb := hr (fderiv ℝ q p v)
  dsimp only at hb
  rw [prefix_log_fderiv_exp_norm hq hqr v] at hb
  change l*‖fderiv ℝ q p v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ ∧
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖≤u*‖fderiv ℝ q p v‖ at hb
  have hpre := (H (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp t ht).1 (t • v)
  change l*‖t • v‖≤‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖ ∧
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) (t • p) (t • v)‖≤u*‖t • v‖ at hpre
  rw [norm_smul_of_nonneg htpos.le] at hpre
  constructor
  · rw [div_mul_eq_mul_div,div_le_iff₀ (mul_pos (by norm_num) hu)]
    have hmul := mul_le_mul_of_nonneg_right ht.1 (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hl.le
    nlinarith [hpre.1.trans hb.2]
  · rw [div_mul_eq_mul_div,le_div_iff₀ hl]
    have hmul := mul_le_mul_of_nonneg_right htone.le (norm_nonneg v)
    have hh := mul_le_mul_of_nonneg_left hmul hu.le
    nlinarith [hb.1.trans hpre.2]

end UniformLog
end WeakMTWTransport

end

end

end

end OAI
