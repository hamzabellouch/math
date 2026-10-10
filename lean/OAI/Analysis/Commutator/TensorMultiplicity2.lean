import Mathlib
import OAI.Analysis.Commutator.TensorMultiplicity

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.HilbertTensor

variable {E F J K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] lemma map_pair (f : E →L[ℂ] F) (g : J →L[ℂ] K) (x : E) (a : J) :
    map f g (pair x a) = pair (f x) (g a) := map_coe_tmul _ _ _ _

lemma insertRight_adjoint_map [CompleteSpace E] [CompleteSpace F]
    (b : J) (f : E →L[ℂ] F) :
    (insertRight b).adjoint.comp (map f (1 : J →L[ℂ] J)) =
      f.comp (insertRight b).adjoint := by
  apply completion_ext
  intro x a
  change (insertRight b).adjoint (map f (1 : J →L[ℂ] J) (pair x a)) =
    f ((insertRight b).adjoint (pair x a))
  simp only [map_pair, one_apply_eq_self, insertRight_adjoint_pair, map_smul]

lemma scalarSlice_covariant [CompleteSpace E] [CompleteSpace F]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (F ⊗[ℂ] K))
    (f : E →L[ℂ] E) (g : F →L[ℂ] F)
    (h : T.comp (map f (1 : J →L[ℂ] J)) = (map g (1 : K →L[ℂ] K)).comp T)
    (a : J) (b : K) : (scalarSlice T a b).comp f = g.comp (scalarSlice T a b) := by
  ext x
  have ht := congrArg (fun R : Completion (E ⊗[ℂ] J) →L[ℂ]
    Completion (F ⊗[ℂ] K) => R (pair x a)) h
  have ho := congrArg (fun R : Completion (F ⊗[ℂ] K) →L[ℂ] F =>
    R (T (pair x a))) (insertRight_adjoint_map b g)
  simp only [ContinuousLinearMap.comp_apply, map_pair, one_apply_eq_self] at ht
  change (insertRight b).adjoint (T (pair (f x) a)) =
    g ((insertRight b).adjoint (T (pair x a)))
  rw [ht]
  exact ho

def multiplicityCompression [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) : J →L[ℂ] J :=
  ((insertLeft v).adjoint.comp T).comp (insertLeft v)

lemma multiplicityCompression_inner [CompleteSpace E] [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) (a b : J) :
    inner ℂ b (multiplicityCompression T v a) = inner ℂ v (scalarSlice T a b v) := by
  simp only [multiplicityCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, insertLeft_apply, scalarSlice_inner]

lemma norm_multiplicityCompression_le [CompleteSpace J]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J)) (v : E) (hv : ‖v‖ = 1) :
    ‖multiplicityCompression T v‖ ≤ ‖T‖ := by
  have hi : ‖insertLeft (J := J) v‖ ≤ 1 := by simpa only [hv] using norm_insertLeft_le (J := J) v
  have hia : ‖(insertLeft (J := J) v).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hi
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
      (calc
        ‖(insertLeft (J := J) v).adjoint‖ * ‖T‖ * ‖insertLeft (J := J) v‖
            ≤ (1 * ‖T‖) * ‖insertLeft (J := J) v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hia (norm_nonneg T))
            (norm_nonneg (insertLeft (J := J) v))
        _ ≤ ‖T‖ := by
          simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left hi (norm_nonneg T)))

theorem repeated_pair [CompleteSpace E] [CompleteSpace J]
    {ι : Type*} [Fintype ι]
    (T : Completion (E ⊗[ℂ] J) →L[ℂ] Completion (E ⊗[ℂ] J))
    (U : ι → E →L[ℂ] E)
    (hclass : ∀ a b : J, ∃ c : ι → ℂ, scalarSlice T a b = ∑ i, c i • U i)
    (v w : E) (hv : ‖v‖ = 1) (hUv : ∀ i, U i v = v) (hUw : ∀ i, U i w = w)
    (a : J) : T (pair w a) = pair w (multiplicityCompression T v a) := by
  classical
  apply pair_inner_ext
  intro x b
  obtain ⟨c, hc⟩ := hclass a b
  have hc_v : scalarSlice T a b v = (∑ i, c i) • v := by
    simp only [hc, sum_apply, smul_apply, hUv, Finset.sum_smul]
  have hc_w : scalarSlice T a b w = (∑ i, c i) • w := by
    simp only [hc, sum_apply, smul_apply, hUw, Finset.sum_smul]
  have hsum : inner ℂ b (multiplicityCompression T v a) = ∑ i, c i := by
    rw [multiplicityCompression_inner, hc_v, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [← scalarSlice_inner, hc_w, inner_smul_right, inner_pair, hsum]
  exact mul_comm _ _

end Kadison.HilbertTensor
end

end OAI
