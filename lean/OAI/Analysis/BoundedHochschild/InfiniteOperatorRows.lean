import OAI.Analysis.BoundedHochschild.SubnormalizedOperatorRows
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Completeness

namespace OAI

/-! Strongly convergent operator rows. The left row need not be normal: the
summability estimate uses the square-sum bound on the right row only. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma summable_row_vectors (a : I → (K →L[ℂ] K))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (y : I → K) (hy : Summable (fun i => ‖y i‖ ^ 2)) :
    Summable (fun i => a i (y i)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hy (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨s, fun t ht => ?_⟩
  have h := norm_sum_row_apply_sq_le (fun i : t => a i)
    (by rw [Finset.sum_coe_sort t (fun i => a i * star (a i))]; exact ha t) (fun i : t => y i)
  rw [Finset.sum_coe_sort t (fun i => a i (y i)),
    Finset.sum_coe_sort t (fun i => ‖y i‖ ^ 2)] at h
  have hpos : 0 ≤ ∑ i ∈ t, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hh := hs t ht
  rw [Real.norm_eq_abs, abs_of_nonneg hpos] at hh
  have hsq := h.trans_lt hh
  nlinarith [norm_nonneg (∑ i ∈ t, a i (y i))]

lemma summable_adjoint_row_sq (b : I → (H →L[ℂ] H))
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1) (ξ : H) :
    Summable (fun i => ‖(b i).adjoint ξ‖ ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := ‖ξ‖ ^ 2)
  intro s
  rw [← Finset.sum_coe_sort s (fun i => ‖(b i).adjoint ξ‖ ^ 2)]
  exact sum_norm_adjoint_sq_le (fun i : s => b i)
      (by rw [Finset.sum_coe_sort s (fun i => b i * star (b i))]; exact hb s) ξ

lemma summable_operator_row_apply (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    Summable (fun i => a i (W ((b i).adjoint ξ))) := by
  apply summable_row_vectors a ha
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => pow_le_pow_left₀ (norm_nonneg _) (W.le_opNorm _) 2)
  simpa only [mul_pow] using (summable_adjoint_row_sq b hb ξ).mul_left (‖W‖ ^ 2)

lemma tsum_operator_row_apply_norm_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    ‖∑' i, a i (W ((b i).adjoint ξ))‖ ≤ ‖W‖ * ‖ξ‖ := by
  have ht := (summable_operator_row_apply a b ha hb W ξ).hasSum.norm
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro s
  have h := (operatorRowAverage_norm_le_of_le (fun i : s => a i) (fun i : s => b i)
    (by rw [Finset.sum_coe_sort s (fun i => a i * star (a i))]; exact ha s)
    (by rw [Finset.sum_coe_sort s (fun i => b i * star (b i))]; exact hb s) W)
  have h' := (operatorRowAverage (fun i : s => a i) (fun i : s => b i) W).le_opNorm ξ
  rw [operatorRowAverage_apply,
    Finset.sum_coe_sort s (fun i => a i (W ((b i).adjoint ξ)))] at h'
  exact h'.trans (mul_le_mul_of_nonneg_right h (norm_nonneg ξ))

def infiniteOperatorRow (a : I → (K →L[ℂ] K)) (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) : H →L[ℂ] K :=
  LinearMap.mkContinuous
    { toFun := fun ξ => ∑' i, a i (W ((b i).adjoint ξ))
      map_add' := by
        intro ξ η
        simp only [map_add]
        exact (summable_operator_row_apply a b ha hb W ξ).tsum_add
          (summable_operator_row_apply a b ha hb W η)
      map_smul' := by
        intro c ξ
        simp only [map_smul, RingHom.id_apply]
        exact tsum_const_smul'' c }
    ‖W‖ (tsum_operator_row_apply_norm_le a b ha hb W)

lemma infiniteOperatorRow_norm_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) : ‖infiniteOperatorRow a b ha hb W‖ ≤ ‖W‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W)
    (tsum_operator_row_apply_norm_le a b ha hb W)

lemma infiniteOperatorRow_hasSum (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    HasSum (fun i => a i (W ((b i).adjoint ξ))) (infiniteOperatorRow a b ha hb W ξ) :=
  (summable_operator_row_apply a b ha hb W ξ).hasSum

end BoundedHochschild.KadisonRingrose

end

end OAI
