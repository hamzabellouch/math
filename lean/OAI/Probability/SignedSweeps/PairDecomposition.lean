import OAI.Probability.SignedSweeps.PairCentral
import OAI.Probability.SignedSweeps.IsotypicDecomposition

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairDecompositionTraceWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairDecompositionTraceSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma starProjection_trace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (S : Submodule ℂ E) :
    LinearMap.trace ℂ E S.starProjection.toLinearMap = (finrank ℂ S : ℂ) := by
  have hi : IsIdempotentElem S.starProjection.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection.eq
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rwa [Submodule.range_starProjection] at h

lemma wordTypeProjection_trace {p : ℕ} (mu : Partition p) (C : Type*) [Fintype C] :
    LinearMap.trace ℂ (WordSpace p C) (wordTypeProjection mu C) =
      (finrank ℂ (isotypicSubrepresentation (spechtRepresentation mu)
        (wordRepresentation p C)).toSubmodule : ℂ) := starProjection_trace _

lemma pairTypeProjection_trace {u v p : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (C : Type*) [Fintype C] :
    LinearMap.trace ℂ (WordSpace p (C ⊕ C)) (pairTypeProjection h a b C) =
      (p.choose u : ℂ) *
        (finrank ℂ (isotypicSubrepresentation (spechtRepresentation a)
          (wordRepresentation u C)).toSubmodule : ℂ) *
        (finrank ℂ (isotypicSubrepresentation (spechtRepresentation b)
          (wordRepresentation v C)).toSubmodule : ℂ) := by
  simp only [pairTypeProjection, map_sum, hilbertBlock_trace,
    LinearMap.trace_tensorProduct', wordTypeProjection_trace, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card (EvenAllocation u p) = p.choose u := by
    simpa only [Fintype.card_fin] using (Fintype.card_finset_len (α := Fin p) u)
  rw [hc, mul_assoc]

lemma pairTypeProjection_finrank_le {u v p : ℕ} (h : u+v=p) (a : Partition u) (b : Partition v)
    (C : Type*) [Fintype C] :
    finrank ℂ (pairTypeProjection h a b C).range ≤
      p.choose u * spechtDimension a * spechtDimension b *
        (p+1)^(2*(Fintype.card C * Fintype.card C)) := by
  have hi : IsIdempotentElem (pairTypeProjection h a b C) := pairTypeProjection_idempotent h a b C
  have ht := ((LinearMap.IsIdempotentElem.isProj_range _ hi).trace).symm.trans (pairTypeProjection_trace h a b C)
  have he : finrank ℂ (pairTypeProjection h a b C).range = p.choose u *
      finrank ℂ (isotypicSubrepresentation (spechtRepresentation a) (wordRepresentation u C)).toSubmodule *
      finrank ℂ (isotypicSubrepresentation (spechtRepresentation b) (wordRepresentation v C)).toSubmodule := by
    exact_mod_cast ht
  rw [he]
  have ha := word_isotypic_finrank_le a C
  have hb := word_isotypic_finrank_le b C
  have hua : (u+1)^(Fintype.card C * Fintype.card C) ≤ (p+1)^(Fintype.card C * Fintype.card C) :=
    Nat.pow_le_pow_left (by omega) _
  have hvb : (v+1)^(Fintype.card C * Fintype.card C) ≤ (p+1)^(Fintype.card C * Fintype.card C) :=
    Nat.pow_le_pow_left (by omega) _
  calc
    _ ≤ p.choose u * (spechtDimension a * (p+1)^(Fintype.card C * Fintype.card C)) *
        (spechtDimension b * (p+1)^(Fintype.card C * Fintype.card C)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (ha.trans (Nat.mul_le_mul_left _ hua)))
        (hb.trans (Nat.mul_le_mul_left _ hvb))
    _ = _ := by rw [two_mul, pow_add]; ring

lemma pairTypeProjection_zero_of_height {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v)
    (hab : Fintype.card C < a.1.colLen 0 ∨ Fintype.card C < b.1.colLen 0) :
    pairTypeProjection h a b C = 0 := by
  unfold pairTypeProjection
  apply Finset.sum_eq_zero
  intro S _
  rcases hab with ha | hb
  · rw [wordTypeProjection_zero_of_height a ha, TensorProduct.map_zero_left, map_zero]
  · rw [wordTypeProjection_zero_of_height b hb, TensorProduct.map_zero_right, map_zero]

abbrev PairType (p : ℕ) := Σ u : Fin (p+1), Partition u.1 × Partition (p-u.1)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.PairType
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairDecompositionTypeWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairDecompositionTypeSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

def projector {p : ℕ} (t : PairType p) (C : Type*) [Fintype C] :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  pairTypeProjection (Nat.add_sub_of_le (Nat.le_of_lt_succ t.1.2)) t.2.1 t.2.2 C

def entropy {p : ℕ} (t : PairType p) : ℝ := signedEntropy t.2.1 t.2.2

def height {p : ℕ} (t : PairType p) : ℕ := max (t.2.1.1.colLen 0) (t.2.2.1.colLen 0)

end SignedSweeps.PairType
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
local instance (priority := 2000) pairDecompositionProjectionWordDecidableEq {C : Type*} (p : ℕ) :
    DecidableEq (Fin p → C) := Classical.decEq _
local instance (priority := 2000) pairDecompositionProjectionSumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma sum_pairTypeProjection_fixed {u v p : ℕ} (h : u+v=p) (C : Type*) [Fintype C] :
    (∑ a : Partition u, ∑ b : Partition v, pairTypeProjection h a b C) =
      ∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S)) 1 := by
  unfold pairTypeProjection
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (α := EvenAllocation u p)]
  apply Finset.sum_congr rfl
  intro S _
  simp_rw [← map_sum]
  congr 1
  change ∑ b : Partition v, ∑ a : Partition u,
    (TensorProduct.mapBilinear (RingHom.id ℂ) _ _ _ _ (wordTypeProjection a C))
      (wordTypeProjection b C) = 1
  simp only [← LinearMap.sum_apply, ← map_sum, wordTypeProjection_sum]
  exact TensorProduct.map_one

lemma pairAllocationProjection_apply {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (x : WordSpace p (C ⊕ C))
    (w : Fin p → C ⊕ C) :
    hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S)) 1 x w =
      if wordEvenSites w = S.1 then x w else 0 := by
  by_cases hw : wordEvenSites w = S.1
  · rw [ite_eq_left hw]
    obtain ⟨⟨z,t⟩,hzt⟩ := (pairColorEmbedding_range h S w).mpr hw
    have hj : pairWordEmbedding (allocationEquiv h S)
        (EuclideanSpace.single z 1 ⊗ₜ[ℂ] EuclideanSpace.single t 1) =
        EuclideanSpace.single w 1 := by
      rw [pairWordEmbedding_single]
      exact congrArg (fun w => EuclideanSpace.single w (1:ℂ)) hzt
    have hs := hilbertBlock_symmetric (pairWordEmbedding (C:=C) (allocationEquiv h S))
      (show (1 : (WordSpace u C ⊗[ℂ] WordSpace v C) →ₗ[ℂ] _).IsSymmetric from LinearMap.IsSymmetric.id)
    have he := hs (EuclideanSpace.single w 1) x
    rw [← hj, hilbertBlock_on, Module.End.one_apply, hj] at he
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using he.symm
  · rw [ite_eq_right hw]
    exact pairWordEmbedding_off h S _ w hw

theorem pairTypeProjection_sum (p : ℕ) (C : Type*) [Fintype C] :
    (∑ t : PairType p, t.projector C) = 1 := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, PairType.projector,
]
  have hs (k : Fin (p+1)) := sum_pairTypeProjection_fixed (Nat.add_sub_of_le (Nat.le_of_lt_succ k.2)) C
  simp_rw [hs]
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro w
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    pairAllocationProjection_apply, Module.End.one_apply]
  let k : Fin (p+1) := ⟨(wordEvenSites w).card, Nat.lt_succ_of_le (by
    exact (Finset.card_le_univ (wordEvenSites w)).trans_eq (Fintype.card_fin p))⟩
  rw [Finset.sum_eq_single k]
  · let S : EvenAllocation k.1 p := ⟨wordEvenSites w,rfl⟩
    rw [Finset.sum_eq_single S]
    · simp [S]
    · intro T _ hT
      exact ite_eq_right (fun he => hT (Subtype.ext he.symm))
    · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro T _
    apply ite_eq_right
    intro he
    apply hj
    apply Fin.ext
    have hc := congrArg Finset.card he
    rw [T.2] at hc
    exact hc.symm
  · simp

end SignedSweeps
end

end OAI
