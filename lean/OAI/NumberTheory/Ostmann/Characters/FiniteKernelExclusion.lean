import OAI.NumberTheory.Ostmann.Quadratic.KernelPairSelection

namespace OAI

/-! # Removing a finite family of exceptional signed kernel products -/

namespace Ostmann

open scoped BigOperators Classical

theorem kernel_pair_filter_mem_card (S T : Finset ℤ) (f g : ℤ → ℤ) (D : Finset ℤ) :
    ((S.product T).filter fun z => f z.1 * g z.2 ∈ D).card =
      ∑ d ∈ D, ((S.product T).filter fun z => f z.1 * g z.2 = d).card := by
  let U := (S.product T).filter fun z => f z.1 * g z.2 ∈ D
  have hm : (U : Set (ℤ × ℤ)).MapsTo (fun z => f z.1 * g z.2) D :=
    fun _ hz => (Finset.mem_filter.mp hz).2
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  ext z
  simp only [U, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, h.2 ▸ hd⟩, h.2⟩

theorem kernel_pair_finite_exclusion_bound (S T : Finset ℤ) (f g : ℤ → ℤ)
    (D : Finset ℤ) (E : ℝ)
    (hE : ∀ d ∈ D, (((S.product T).filter fun z => f z.1 * g z.2 = d).card : ℝ) ≤ E) :
    (((S.product T).filter fun z => f z.1 * g z.2 ∈ D).card : ℝ) ≤ D.card * E := by
  rw [kernel_pair_filter_mem_card, Nat.cast_sum]
  exact (Finset.sum_le_sum hE).trans_eq (by simp)

/-- The surviving kernel pair carries a large product of the actual endpoint
populations, after deletion of every product in D. -/
theorem exists_populated_outside_kernel_family (S T : Finset ℤ) (f g : ℤ → ℤ)
    (D : Finset ℤ) (E K : ℝ) (hK : 0 ≤ K)
    (hbad : (((S.product T).filter fun z => f z.1 * g z.2 ∈ D).card : ℝ) ≤ E)
    (hlarge : ((S.image f).card : ℝ) * (T.image g).card * K + E <
      (S.card : ℝ) * T.card) :
    ∃ u ∈ S.image f, ∃ v ∈ T.image g, u * v ∉ D ∧
      K < ((S.filter fun x => f x = u).card : ℝ) * (T.filter fun y => g y = v).card := by
  let V := ((S.image f).product (T.image g)).filter fun q => q.1 * q.2 ∉ D
  have hsum := kernel_pair_population_sum S T f g (fun u v => u * v ∉ D)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.product T)
    (fun z : ℤ × ℤ => f z.1 * g z.2 ∈ D)
  have hsplitR : (((S.product T).filter fun z => f z.1 * g z.2 ∈ D).card : ℝ) +
      (((S.product T).filter fun z => f z.1 * g z.2 ∉ D).card : ℝ) =
      (S.card : ℝ) * T.card := by
    exact_mod_cast (hsplit.trans (Finset.card_product S T))
  have hcard : (V.card : ℝ) ≤ ((S.image f).card : ℝ) * (T.image g).card := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_product (S.image f) (T.image g))
  have hsumR : ∑ q ∈ V,
      ((S.filter fun x => f x = q.1).card : ℝ) * (T.filter fun y => g y = q.2).card =
      (((S.product T).filter fun z => f z.1 * g z.2 ∉ D).card : ℝ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) hsum.symm
    push_cast at hh
    convert! hh using 1
    · apply Finset.sum_congr
      · ext q
        simp only [V, Finset.mem_filter]
      · intro q hq
        rfl
    · apply congrArg (fun U : Finset (ℤ × ℤ) => (U.card : ℝ))
      ext q
      simp only [Finset.mem_filter]
  have htotal : (V.card : ℝ) * K < ∑ q ∈ V,
      ((S.filter fun x => f x = q.1).card : ℝ) * (T.filter fun y => g y = q.2).card := by
    rw [hsumR]
    have hc := mul_le_mul_of_nonneg_right hcard hK
    linarith
  obtain ⟨q, hq, hqpop⟩ := Finset.exists_lt_of_sum_lt (s := V) (f := fun _ => K)
    (g := fun q => ((S.filter fun x => f x = q.1).card : ℝ) * (T.filter fun y => g y = q.2).card)
    (by simpa only [Finset.sum_const, nsmul_eq_mul] using htotal)
  obtain ⟨hq, hqd⟩ := Finset.mem_filter.mp hq
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp hq
  exact ⟨q.1, hu, q.2, hv, hqd, hqpop⟩

end Ostmann

end OAI
