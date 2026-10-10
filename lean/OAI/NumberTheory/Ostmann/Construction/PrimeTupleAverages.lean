import OAI.NumberTheory.Ostmann.Construction.PrimeTupleTranslation
import OAI.NumberTheory.Ostmann.Construction.DistinctTupleProducts

namespace OAI

/-! # Exact transfer between ordered prime tuples and their products -/

namespace Ostmann

open scoped BigOperators Classical

theorem distinct_tuple_statistic_sum {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (F : Finset A → ℝ) :
    (∑ e : Fin k ↪ A, F (tupleImage e)) =
      (k.factorial : ℝ) * ∑ U ∈ (Finset.univ : Finset A).powersetCard k, F U := by
  have hmaps (e : Fin k ↪ A) (_ : e ∈ (Finset.univ : Finset (Fin k ↪ A))) :
      tupleImage e ∈ (Finset.univ : Finset A).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hc : (Finset.univ.image e).card = (Finset.univ : Finset (Fin k)).card :=
      Finset.card_image_iff.mpr e.injective.injOn
    simpa only [tupleImage, Finset.card_univ, Fintype.card_fin] using hc
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  calc
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin k ↪ A)).filter (fun e => tupleImage e = U), F U := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_filter.mp he).2]
    _ = _ := by
      rw [Finset.sum_const]
      have hc : ((Finset.univ : Finset (Fin k ↪ A)).filter
          (fun e => tupleImage e = U)).card = k.factorial := by
        simpa only [Fintype.card_subtype] using
          card_tupleImage_fiber k U (Finset.mem_powersetCard.mp hU).2
      rw [hc, nsmul_eq_mul]

theorem primeTuple_statistic_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (f : ℕ → ℝ) :
    (∑ e : Fin k ↪ P, f (primeTupleProduct P e)) =
      (k.factorial : ℝ) * ∑ m ∈ primeSubsetProducts P k, f m := by
  have he (e : Fin k ↪ P) : primeTupleProduct P e = ∏ p ∈ tupleImage e, p.val := by
    rw [tupleImage, Finset.prod_image e.injective.injOn]
    rfl
  simp_rw [he]
  rw [distinct_tuple_statistic_sum k (fun U : Finset P => f (∏ p ∈ U, p.val))]
  congr 1
  let emb : P ↪ ℕ := Function.Embedding.subtype _
  have hmap : (Finset.univ : Finset P).map emb = P := by ext p; simp [emb]
  have hs := congrArg (fun R : Finset ℕ => ∑ U ∈ R.powersetCard k, f (∏ p ∈ U, p)) hmap
  simp only [Finset.powersetCard_map, Finset.sum_map] at hs
  change (∑ U ∈ (Finset.univ : Finset P).powersetCard k, f (∏ p ∈ U.map emb, p)) =
    ∑ U ∈ P.powersetCard k, f (∏ p ∈ U, p) at hs
  simp only [Finset.prod_map] at hs
  change (∑ U ∈ (Finset.univ : Finset P).powersetCard k, f (∏ p ∈ U, p.val)) =
    ∑ U ∈ P.powersetCard k, f (∏ p ∈ U, p) at hs
  rw [hs, primeSubsetProducts, Finset.sum_image]
  intro U hU V hV hprod
  exact primeSubset_product_injective P hP
    (Finset.mem_powersetCard.mp hU).1 (Finset.mem_powersetCard.mp hV).1 hprod

theorem primeTuple_uniform_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (f : ℕ → ℝ) :
    (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ * (∑ e : Fin k ↪ P, f (primeTupleProduct P e)) =
      (P.card.choose k : ℝ)⁻¹ * ∑ m ∈ primeSubsetProducts P k, f m := by
  rw [primeTuple_statistic_sum P hP k f, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_fin, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [mul_inv_rev]
  field_simp

end Ostmann

end OAI
