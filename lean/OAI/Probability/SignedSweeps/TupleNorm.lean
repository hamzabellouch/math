import OAI.Probability.SignedSweeps.KernelBounds

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def firstRowStabilizer {n : ℕ} (lam : Partition n) : Subgroup (SymmetricGroup n) :=
  supportedSubgroup (Finset.univ.filter fun i => lam.rowOf i = 0)

lemma firstRowStabilizer_fixes {n : ℕ} (lam : Partition n)
    (h : firstRowStabilizer lam) (i : OffFirstRow lam) : h.1 i.1 = i.1 := by
  apply h.property
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using i.property

def restrictToTuple {n : ℕ} (lam : Partition n) (g : SymmetricGroup n) :
    InjectiveTuple (OffFirstRow lam) n := (Function.Embedding.subtype _).trans g.toEmbedding

@[simp] lemma restrictToTuple_apply {n : ℕ} (lam : Partition n)
    (g : SymmetricGroup n) (i : OffFirstRow lam) : restrictToTuple lam g i = g i.1 := rfl

lemma extendDifference_mem {n : ℕ} (lam : Partition n) (g : SymmetricGroup n) :
    (extendOffFirstRow lam (restrictToTuple lam g))⁻¹ * g ∈ firstRowStabilizer lam := by
  intro i hi
  have hr : lam.rowOf i ≠ 0 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  change (extendOffFirstRow lam (restrictToTuple lam g)).symm (g i) = i
  rw [← Equiv.eq_symm_apply]
  have ht := (extendOffFirstRow_apply lam (restrictToTuple lam g) ⟨i, hr⟩).symm
  change g i = (extendOffFirstRow lam (restrictToTuple lam g)) i at ht
  exact ht

def permutationTupleEquiv {n : ℕ} (lam : Partition n) :
    SymmetricGroup n ≃ InjectiveTuple (OffFirstRow lam) n × firstRowStabilizer lam where
  toFun g := (restrictToTuple lam g,
    ⟨(extendOffFirstRow lam (restrictToTuple lam g))⁻¹ * g, extendDifference_mem lam g⟩)
  invFun p := extendOffFirstRow lam p.1 * p.2.1
  left_inv g := by simp only [mul_inv_cancel_left]
  right_inv p := by
    have he : restrictToTuple lam (extendOffFirstRow lam p.1 * p.2.1) = p.1 := by
      apply Function.Embedding.ext
      intro i
      change extendOffFirstRow lam p.1 (p.2.1 i.1) = p.1 i
      rw [firstRowStabilizer_fixes, extendOffFirstRow_apply]
    apply Prod.ext he
    apply Subtype.ext
    dsimp
    rw [he, inv_mul_cancel_left]

lemma tupleRealization_norm_sq {n : ℕ} (lam : Partition n) (v : Specht lam) :
    ‖v‖ ^ 2 = (Fintype.card (firstRowStabilizer lam) : ℝ) * ‖tupleRealization lam v‖ ^ 2 := by
  change ‖spechtInclusion lam v‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ p : InjectiveTuple (OffFirstRow lam) n × firstRowStabilizer lam,
        ‖tupleRealization lam v p.1‖ ^ 2 := by
      apply Fintype.sum_equiv (permutationTupleEquiv lam)
      intro g
      change ‖spechtInclusion lam v g‖ ^ 2 = ‖tupleRealization lam v (restrictToTuple lam g)‖ ^ 2
      rw [tupleRealization_apply_perm lam v (restrictToTuple lam g) g (fun _ => rfl)]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

def tupleSweep (I : Type*) [Fintype I] (d : ℕ) : TupleSpace I (2 ^ d) →ₗ[ℂ] TupleSpace I (2 ^ d) :=
  ((List.ofFn fun i : Fin d => groupAverage
    ((tupleRepresentation I (2 ^ d)).comp (coordinateSubgroup d i).subtype)).reverse).prod

lemma tupleRealization_intertwines_average {n : ℕ} (lam : Partition n)
    (H : Subgroup (SymmetricGroup n)) (v : Specht lam) :
    tupleRealization lam (groupAverage ((spechtRepresentation lam).comp H.subtype) v) =
      groupAverage ((tupleRepresentation (OffFirstRow lam) n).comp H.subtype) (tupleRealization lam v) := by
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    MonoidHom.comp_apply, Subgroup.subtype_apply, tupleRealization_intertwines]

lemma tupleRealization_intertwines_sweep {d : ℕ} (lam : Partition (2 ^ d)) (v : Specht lam) :
    tupleRealization lam (sweepOperator lam v) = tupleSweep (OffFirstRow lam) d (tupleRealization lam v) := by
  have aux (L : List (Fin d)) (v : Specht lam) :
      tupleRealization lam ((L.map (layerOperator lam)).prod v) =
        (L.map (fun i => groupAverage ((tupleRepresentation (OffFirstRow lam) (2 ^ d)).comp
          (coordinateSubgroup d i).subtype))).prod (tupleRealization lam v) := by
    induction L with
    | nil => rfl
    | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [show layerOperator lam i = groupAverage ((spechtRepresentation lam).comp
        (coordinateSubgroup d i).subtype) from rfl, tupleRealization_intertwines_average, ih]
  simpa only [sweepOperator, tupleSweep, List.ofFn_eq_map, List.map_reverse] using
    aux (List.finRange d).reverse v

theorem sweep_norm_le_of_tuple_bound {d : ℕ} (lam : Partition (2 ^ d))
    {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ v : Specht lam, ‖tupleSweep (OffFirstRow lam) d (tupleRealization lam v)‖ ≤
      a * ‖tupleRealization lam v‖) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤ a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro v
  change ‖sweepOperator lam v‖ ≤ a * ‖v‖
  have hh := h v
  rw [← tupleRealization_intertwines_sweep] at hh
  have hc : (0 : ℝ) < Fintype.card (firstRowStabilizer lam) := by
    exact_mod_cast Fintype.card_pos
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hc.le
  rw [mul_pow, ← mul_assoc, mul_comm (Fintype.card (firstRowStabilizer lam) : ℝ) (a ^ 2),
    mul_assoc, ← tupleRealization_norm_sq, ← tupleRealization_norm_sq] at hs
  nlinarith [norm_nonneg (sweepOperator lam v), norm_nonneg v, mul_nonneg ha (norm_nonneg v)]

end SignedSweeps
end

end OAI
