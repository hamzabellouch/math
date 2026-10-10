import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.PositiveSingular
import OAI.Analysis.BiholderTransport.LinearAlgebra.JoinOperator
import OAI.Analysis.BiholderTransport.Duality.DualFactor

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section JoinSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def endpointExpDifferential (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p) :=
  mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p

lemma uniform_join_exp_norm_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ t ∈ Icc (1/4:ℝ) (3/4), ∀ v,
      ‖splitJoinHessianOperator x t p v‖ ≤ C * ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
        𝓘(ℝ,Model n) (riemannianExp x) p v‖ ∧
      ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p v‖ ≤
        c * ‖splitJoinHessianOperator x t p v‖ := by
  obtain ⟨l,u,hl,hu,H⟩ := uniform_join_endpoint_factorization (n := n) (M := M)
  refine ⟨1/l,4*u,div_pos (by norm_num) hl,mul_pos (by norm_num) hu,?_⟩
  intro x p hp t ht v
  obtain ⟨L,hL,hLn,hfac⟩ := H x p hp t ht
  have hs : 0 < 1-t := by linarith [ht.2]
  have hn := dual_factor_norm_comparison (splitJoinHessianOperator x t p) L
    (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p)
    hs hl hu hL.2 hLn (fun a k => by rw [hfac]; field_simp [hs.ne']; rfl) v
  change l * ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp x) p v‖ ≤ (1-t)*‖splitJoinHessianOperator x t p v‖ ∧
    (1-t)*‖splitJoinHessianOperator x t p v‖ ≤ u*‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x)
      𝓘(ℝ,Model n) (riemannianExp x) p v‖ at hn
  constructor
  · have hm := mul_le_mul_of_nonneg_right (show (1/4:ℝ) ≤ 1-t by linarith [ht.2])
      (norm_nonneg (splitJoinHessianOperator x t p v))
    have hh := hm.trans hn.2
    linarith only [hh]
  · rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
    have hm := mul_le_mul_of_nonneg_right (show 1-t ≤ 1 by linarith [ht.1])
      (norm_nonneg (splitJoinHessianOperator x t p v))
    have hh := hn.1.trans hm
    nlinarith only [hh]

lemma uniform_join_exp_ordered_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ hp : p ∈ minimizingVectors x, ∀ t : ℝ, ∀ ht : t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)),
      (splitJoinHessianOperator_positive hp (by linarith [ht.1])
        (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ C *
        (endpointExpDifferential x p).toLinearMap.singularValues i ∧
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ c *
        (splitJoinHessianOperator_positive hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_join_exp_norm_comparison (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp t ht i
  let Q := splitJoinHessianOperator x t p
  let E := endpointExpDifferential x p
  have hQ := splitJoinHessianOperator_positive hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  have h1 := ordered_singularValues_pullback (A := Q.toLinearMap) (B := E.toLinearMap)
    (LinearMap.id) hC.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1 * ‖v‖; simp) (fun v => (H x p hp t ht v).1) rfl rfl i
  have h2 := ordered_singularValues_pullback (A := E.toLinearMap) (B := Q.toLinearMap)
    (LinearMap.id) hc.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1 * ‖v‖; simp) (fun v => (H x p hp t ht v).2) rfl rfl i
  rw [positive_singularValues_eq_eigenvalues hQ rfl i] at h1 h2
  simpa only [mul_one] using And.intro h1 h2

end JoinSpectrum
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section UniformCongruence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_split_join_hessian_congruence :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p ∈ minimizingVectors x → ∀ h ∈ Icc (1/4:ℝ) (3/4),
    ∃ P : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      Function.Bijective P ∧ (∀ v, c*‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ C*‖v‖) ∧ ∀ a,
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x h)) (p,p) (0,a) (0,a)=
        middleHessian (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) h 1 (P a) (P a) := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_prefix_log_derivative_bounds (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro x p hp h ht
  have hh : 0 < h := by linarith [ht.1]
  have hh1 : h < 1 := by linarith [ht.2]
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hleft := contracted_minimizer_mem_injectivityDomain hp hh hh1
  obtain ⟨q,hqp,hq,hqinj,hqr⟩ := exists_join_normal_coordinates hh.ne' hleft
  have hf := middleCenteredAction_contDiffAt (z := z) hp hh hh1
  have hf' : ContDiffAt ℝ 2 (middleCenteredAction z h) (q p) := by rwa [hqp]
  have hz : fderiv ℝ (middleCenteredAction z h) (q p)=0 := by
    rw [hqp]
    exact (middleCenteredAction_minimum (z := z) hp hh hh1).fderiv_eq_zero
  have hF : ContDiffAt ℝ 2 (diagonalSplitAction x h) (p,p) :=
    (diagonalSplitAction_contDiffAt hleft (proper_suffix_in_injectivityDomain
      (z := z) hp hh hh1 le_rfl)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := middle_action_in_join_coordinates hp hh hh1 hqr
  have heD := he.fderiv (𝕜 := ℝ)
  have heDD := heD.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fderiv ℝ (middleCenteredAction z h ∘ q)) p =
    fderiv ℝ (fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))) p at heDD
  have hsub : fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))=
      fderiv ℝ (fun a => diagonalSplitAction x h (p,a)) := by
    funext a; exact fderiv_sub_const _
  rw [hsub] at heDD
  have hqs : Function.Surjective (fderiv ℝ q p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ q p).toLinearMap) rfl).mp hqinj
  refine ⟨fderiv ℝ q p,⟨hqinj,hqs⟩,
    H x p hp h ht _ q (hq.differentiableAt (by simp)) hqp hqr,?_⟩
  intro a
  have H := second_fderiv_comp_at_critical hf' (hq.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hz a a
  rw [heDD,hqp,second_derivative_target_slice hF] at H
  exact H.trans (middleCenteredAction_hessian (z := z) hp hh hh1 _)

end UniformCongruence
end WeakMTWTransport

end

end

end

end OAI
