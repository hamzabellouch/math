import OAI.NumberTheory.CubicMoment.Estimates.StructuredConvolution

namespace OAI

/-!
# Norm fibers for a fixed number of primary prime factors

Equal norms give `b * conjugate b = b₀ * conjugate b₀`.  Consequently every
prime factor of `b` is one of the prime factors of `b₀` or its conjugate.
For products of `k` primary primes this bounds every norm fiber by
`(2 * k)^k`, uniformly in all prime supports and the norm.  No general
divisor estimate is needed for the structured coefficients.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A prime in a tuple of the same norm must occur in the reference tuple
or in its conjugate. Primary normalization turns association into equality. -/
lemma prime_tuple_norm_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hn : normNat (∏ i, g i) = normNat (∏ i, f i)) (i : ι) :
    g i ∈ Finset.univ.image f ∪ Finset.univ.image (fun j => conjugate (f j)) := by
  have heq : (∏ j, g j) * conjugate (∏ j, g j) =
      (∏ j, f j) * conjugate (∏ j, f j) := by
    rw [← normNat_cast_eq_mul_conjugate, ← normNat_cast_eq_mul_conjugate, hn]
  have hd : g i ∣ (∏ j, f j) * conjugate (∏ j, f j) :=
    heq ▸ dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem g (Finset.mem_univ i)) _
  rcases (hg i).2.dvd_or_dvd hd with hd | hd
  · obtain ⟨j, _, hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
    have hj' : g i = f j := primary_associated_eq (hg i).1 (hf j).1
      (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj'.symm⟩))
  · rw [map_prod] at hd
    obtain ⟨j, _, hj⟩ := ((hg i).2.dvd_finsetProd_iff (fun j => conjugate (f j))).mp hd
    have hj' : g i = conjugate (f j) := primary_associated_eq (hg i).1
      (primaryPrime_conjugate (hf j)).1
      (((hg i).2.dvd_prime_iff_associated (primaryPrime_conjugate (hf j)).2).mp hj)
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj'.symm⟩))

/-- The number of distinct products with a prescribed norm is bounded
solely in terms of the number of prime factors, even with repetitions. -/
theorem primeProduct_norm_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (n : ℕ) :
    ((orderedConvolutionSupport S).filter (fun b => normNat b = n)).card ≤
      (2 * Fintype.card ι) ^ (Fintype.card ι) := by
  let T := (orderedConvolutionSupport S).filter (fun b => normNat b = n)
  by_cases ht : T.Nonempty
  · obtain ⟨b, hb⟩ := ht
    obtain ⟨hbs, hbn⟩ := Finset.mem_filter.mp hb
    obtain ⟨f, hf, hfb⟩ := Finset.mem_image.mp hbs
    let A := Finset.univ.image f ∪ Finset.univ.image (fun j => conjugate (f j))
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hf) i)
    have hsub : T ⊆ (Fintype.piFinset (fun _ : ι => A)).image (fun g => ∏ i, g i) := by
      intro b' hb'
      obtain ⟨hb's, hb'n⟩ := Finset.mem_filter.mp hb'
      obtain ⟨g, hg, hgb⟩ := Finset.mem_image.mp hb's
      have hn : normNat (∏ i, g i) = normNat (∏ i, f i) := by
        rw [hgb, hfb, hb'n, hbn]
      refine Finset.mem_image.mpr ⟨g, Fintype.mem_piFinset.mpr ?_, hgb⟩
      intro i
      exact prime_tuple_norm_range_subset f g hprime
        (fun j => hS j (g j) ((Fintype.mem_piFinset.mp hg) j)) hn i
    have hcard : A.card ≤ 2 * Fintype.card ι := by
      have hfcard : (Finset.univ.image f).card ≤ Fintype.card ι := by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := f))
      have hccard : (Finset.univ.image (fun j => conjugate (f j))).card ≤ Fintype.card ι := by
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset ι))
          (f := fun j => conjugate (f j)))
      calc
        A.card ≤ (Finset.univ.image f).card +
            (Finset.univ.image (fun j => conjugate (f j))).card := Finset.card_union_le _ _
        _ ≤ Fintype.card ι + Fintype.card ι := add_le_add hfcard hccard
        _ = 2 * Fintype.card ι := by omega
    calc
      T.card ≤ ((Fintype.piFinset (fun _ : ι => A)).image (fun g => ∏ i, g i)).card :=
        Finset.card_le_card hsub
      _ ≤ (Fintype.piFinset (fun _ : ι => A)).card := Finset.card_image_le
      _ = A.card ^ (Fintype.card ι) := by simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left hcard _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

end CubicFirstMoment

end

end OAI
