import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.SpectralContinuity
import OAI.Analysis.BiholderTransport.LinearAlgebra.JoinSpectrum

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport
section CongruenceSpectrum
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma ordered_eigenvalues_bounded_congruence {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
    (hA : A.IsPositive) (hB : B.IsPositive) (P : E →ₗ[ℝ] F)
    (hP : Function.Bijective P) {l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
    (hPn : ∀ v, l*‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ u*‖v‖)
    (h : ∀ v, inner ℝ (A v) v = inner ℝ (B (P v)) (P v))
    {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
    hA.isSymmetric.eigenvalues hnE i ≤ u^2 * hB.isSymmetric.eigenvalues hnF i ∧
    hB.isSymmetric.eigenvalues hnF i ≤ (1/l)^2 * hA.isSymmetric.eigenvalues hnE i := by
  constructor
  · have H := ordered_eigenvalue_pullback_comparison hA.isSymmetric hB P
      (by norm_num : (0:ℝ) ≤ 1) hu (fun v => (hPn v).2)
      (a := 1) (b := 0) (fun v => by simp [h]) hnE hnF i
    simpa only [one_mul,add_zero] using H
  · let e := LinearEquiv.ofBijective P hP
    have hnorm : ∀ w, ‖e.symm w‖ ≤ (1/l)*‖w‖ := by
      intro w
      rw [one_div,mul_comm,←div_eq_mul_inv,le_div_iff₀ hl]
      have H := (hPn (e.symm w)).1
      change l*‖e.symm w‖ ≤ ‖e (e.symm w)‖ at H
      simpa only [e.apply_symm_apply,mul_comm] using H
    have heq : ∀ w, inner ℝ (B w) w = inner ℝ (A (e.symm w)) (e.symm w) := by
      intro w
      have H := h (e.symm w)
      change inner ℝ (A (e.symm w)) (e.symm w) = inner ℝ (B (e (e.symm w))) (e (e.symm w)) at H
      simpa only [e.apply_symm_apply] using H.symm
    have H := ordered_eigenvalue_pullback_comparison hB.isSymmetric hA e.symm.toLinearMap
      (by norm_num : (0:ℝ) ≤ 1) (div_nonneg (by norm_num) hl.le) hnorm
      (a := 1) (b := 0) (fun v => by simp [heq]) hnF hnE i
    simpa only [one_mul,add_zero] using H

end CongruenceSpectrum
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section EndpointMiddle
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma middleHessianOperator_positive_one {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2 ∈ minimizingVectors z.1) {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    (middleHessianOperator z h 1).toLinearMap.IsPositive := by
  refine ⟨middleHessianOperator_symmetric hz hh hh1 hh1 le_rfl,?_⟩
  intro v
  change 0 ≤ inner ℝ (middleHessianOperator z h 1 v) v
  rw [inner_middleHessianOperator]
  exact middleHessian_one_nonneg hz hh hh1 v

lemma uniform_join_middle_ordered_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ hp : p ∈ minimizingVectors x, ∀ t : ℝ, ∀ ht : t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)),
      (splitJoinHessianOperator_positive hp (by linarith [ht.1])
        (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ C *
        (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ∧
      (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ c *
        (splitJoinHessianOperator_positive hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_split_join_hessian_congruence (n := n) (M := M)
  refine ⟨(1 / c)^2, C ^ 2, sq_pos_of_pos (div_pos (by norm_num) hc),sq_pos_of_pos hC,?_⟩
  intro x p hp t ht i
  obtain ⟨P,hP,hPn,h⟩ := H x p hp t ht
  have hpQ := splitJoinHessianOperator_positive hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  have hpD := middleHessianOperator_positive_one (z := ⟨x,p⟩) hp
    (show 0 < t by linarith [ht.1]) (show t < 1 by linarith [ht.2])
  exact ordered_eigenvalues_bounded_congruence hpQ hpD P.toLinearMap hP hc hC.le hPn
    (fun v => by
      change inner ℝ (splitJoinHessianOperator x t p v) v =
        inner ℝ (middleHessianOperator (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) t 1 (P v)) (P v)
      rw [inner_splitJoinHessianOperator,inner_middleHessianOperator,h]) rfl rfl i

lemma uniform_endpoint_middle_ordered_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ∀ hp : p ∈ minimizingVectors x, ∀ t : ℝ, ∀ ht : t ∈ Icc (1/4:ℝ) (3/4),
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) x)),
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ C *
        (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ∧
      (middleHessianOperator_positive_one (z := ⟨x,p⟩) hp (by linarith [ht.1])
          (by linarith [ht.2])).isSymmetric.eigenvalues rfl i ≤ c *
        (endpointExpDifferential x p).toLinearMap.singularValues i := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_join_middle_ordered_comparison (n := n) (M := M)
  obtain ⟨d,e,hd,he,J⟩ := uniform_join_exp_ordered_comparison (n := n) (M := M)
  refine ⟨a*e,d*b,mul_pos ha he,mul_pos hd hb,?_⟩
  intro x p hp t ht i
  have H1 := H x p hp t ht i
  have J1 := J x p hp t ht i
  constructor
  · simpa only [mul_assoc] using J1.2.trans (mul_le_mul_of_nonneg_left H1.1 hd.le)
  · simpa only [mul_assoc] using H1.2.trans (mul_le_mul_of_nonneg_left J1.1 ha.le)

end EndpointMiddle
end WeakMTWTransport

end

end

end

end OAI
