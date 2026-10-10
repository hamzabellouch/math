import OAI.NumberTheory.TotientAsymptotic.CollisionTuples
import OAI.NumberTheory.TotientAsymptotic.CollisionIndices

namespace OAI

/-! The finite set of distinct arithmetic tuples used in the collision count. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma basic_tuple_head_bound {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) : τ.head < ⌊t⌋₊+2 := by
  have hpos := basic_prefix_data_positive hPH hτ.2.2.1
  have hd : 0 < τ.tail.d*∏ i, (τ.tail.primes i-1) := by
    apply Nat.mul_pos hpos.1
    exact Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hpos.2 i).one_lt)
  have hv : tupleValue τ = (τ.head-1)*(τ.tail.d*∏ i, (τ.tail.primes i-1)) := by
    unfold tupleValue tuplePrimes
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  have hl : τ.head-1 ≤ tupleValue τ := by rw [hv]; nlinarith
  have hfloor : τ.head-1 ≤ ⌊t⌋₊ := Nat.le_floor ((by exact_mod_cast hl : ((τ.head-1 : ℕ) : ℝ) ≤ tupleValue τ).trans hτ.2.2.2)
  omega

def tupleFinset (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) := by
  classical
  exact (((Finset.range (⌊t⌋₊+2)) ×ˢ prefixDataFinset x H).image
    (fun p => TotientTuple.mk p.1 p.2)).filter (IsBasicTuple x H t)

lemma mem_tupleFinset {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) : τ ∈ tupleFinset x H t ↔ IsBasicTuple x H t τ := by
  classical
  constructor
  · exact fun ht => (Finset.mem_filter.mp ht).2
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨?_, ht⟩
    apply Finset.mem_image.mpr
    exact ⟨(τ.head, τ.tail), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (basic_tuple_head_bound hPH ht), mem_prefixDataFinset.mpr ht.2.2.1⟩, rfl⟩

/-- The tuple fiber over a fixed tail is exactly the allowed largest-prime
interval. The prime number theorem is applied to this finite set later. -/
lemma tuple_fiber_card (x : ℝ) (H : ℕ) (t : ℝ) (ζ : PrefixDatum (R x H)) :
    ((tupleFinset x H t).filter (fun τ : TotientTuple (R x H) => τ.tail = ζ)).card =
      if IsPrefixDatum x H ζ then
        ((Finset.range (⌊t⌋₊+2)).filter (fun p : ℕ => p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧
          (tupleValue (TotientTuple.mk p ζ) : ℝ) ≤ t)).card
      else 0 := by
  classical
  by_cases hζ : IsPrefixDatum x H ζ
  · rw [ite_eq_left hζ]
    apply Finset.card_bij (fun τ _ => τ.head)
    · intro τ hτ
      obtain ⟨hτ, ht⟩ := Finset.mem_filter.mp hτ
      obtain ⟨hu, hb⟩ := Finset.mem_filter.mp hτ
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hu
      have hpr : τ.head ∈ Finset.range (⌊t⌋₊+2) := by
        rw [← he]
        exact (Finset.mem_product.mp hp).1
      exact Finset.mem_filter.mpr ⟨hpr, hb.1, hb.2.1, by simpa [← ht] using hb.2.2.2⟩
    · intro τ hτ σ hσ hh
      have ht := (Finset.mem_filter.mp hτ).2
      have hs := (Finset.mem_filter.mp hσ).2
      cases τ
      cases σ
      simp_all
    · intro p hp
      obtain ⟨hr, hprime, hlo, hval⟩ := Finset.mem_filter.mp hp
      refine ⟨⟨p, ζ⟩, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hprime, hlo, hζ, hval⟩
      exact Finset.mem_image.mpr ⟨(p, ζ), Finset.mem_product.mpr
        ⟨hr, mem_prefixDataFinset.mpr hζ⟩, rfl⟩
  · rw [ite_eq_right hζ]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro τ hτ
    obtain ⟨hτ, ht⟩ := Finset.mem_filter.mp hτ
    have hb := (Finset.mem_filter.mp hτ).2.2.2.1
    exact hζ (ht ▸ hb)

end TotientAsymptotic

end

end OAI
