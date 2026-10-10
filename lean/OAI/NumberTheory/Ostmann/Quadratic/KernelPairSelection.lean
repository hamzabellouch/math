import Mathlib.Combinatorics.Pigeonhole
import OAI.NumberTheory.Ostmann.Construction.EndpointKernelPairCount

namespace OAI

/-! # Selecting populated kernels after removal of an exceptional product -/

namespace Ostmann

open scoped BigOperators Classical

/-- The finite-set count and the subtype count use exactly the same pairs. -/
theorem kernel_pair_filter_card (S T : Finset ℤ) (f g : ℤ → ℤ) (d : ℤ) :
    ((S.product T).filter fun z => f z.1 * g z.2 = d).card =
      Fintype.card {z : S × T // f z.1 * g z.2 = d} := by
  let e : {z : S × T // f z.1 * g z.2 = d} ≃
      {z : ℤ × ℤ // z ∈ (S.product T).filter fun z => f z.1 * g z.2 = d} :=
    { toFun := fun z => ⟨(z.1.1, z.1.2), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨z.1.1.property, z.1.2.property⟩, z.2⟩⟩
      invFun := fun z => ⟨(⟨z.1.1, (Finset.mem_product.mp (Finset.mem_filter.mp z.2).1).1⟩,
        ⟨z.1.2, (Finset.mem_product.mp (Finset.mem_filter.mp z.2).1).2⟩),
          (Finset.mem_filter.mp z.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

theorem kernel_pair_population_sum (S T : Finset ℤ) (f g : ℤ → ℤ)
    (R : ℤ → ℤ → Prop) :
    ((S.product T).filter fun z => R (f z.1) (g z.2)).card =
      ∑ q ∈ ((S.image f).product (T.image g)).filter (fun q => R q.1 q.2),
        (S.filter fun x => f x = q.1).card * (T.filter fun y => g y = q.2).card := by
  let U := (S.product T).filter fun z => R (f z.1) (g z.2)
  let V := ((S.image f).product (T.image g)).filter fun q => R q.1 q.2
  have hmap : (U : Set (ℤ × ℤ)).MapsTo (fun z => (f z.1, g z.2)) V := by
    intro z hz
    obtain ⟨hz, hR⟩ := Finset.mem_filter.mp hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f hx, Finset.mem_image_of_mem g hy⟩, hR⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro q hq
  rcases q with ⟨u, v⟩
  have hqR := (Finset.mem_filter.mp hq).2
  have heq : (U.filter fun z => (f z.1, g z.2) = (u, v)) =
      (S.filter fun x => f x = u).product (T.filter fun y => g y = v) := by
    ext z
    simp only [U, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, _⟩, hf, hg⟩
      exact ⟨⟨hx, hf⟩, hy, hg⟩
    · rintro ⟨⟨hx, hf⟩, hy, hg⟩
      exact ⟨⟨⟨hx, hy⟩, by simpa only [hf, hg] using hqR⟩, hf, hg⟩
  rw [heq, Finset.product_eq_sprod, Finset.card_product]

/-- After deleting at most E pairs belonging to one signed product, one of
the other kernel pairs has a large population product. -/
theorem exists_populated_nonexceptional_kernels (S T : Finset ℤ) (f g : ℤ → ℤ)
    (d : ℤ) (E K : ℝ) (hK : 0 ≤ K)
    (hbad : (((S.product T).filter fun z => f z.1 * g z.2 = d).card : ℝ) ≤ E)
    (hlarge : ((S.image f).card : ℝ) * (T.image g).card * K + E <
      (S.card : ℝ) * T.card) :
    ∃ u ∈ S.image f, ∃ v ∈ T.image g, u * v ≠ d ∧
      K < ((S.filter fun x => f x = u).card : ℝ) * (T.filter fun y => g y = v).card := by
  let V := ((S.image f).product (T.image g)).filter fun q => q.1 * q.2 ≠ d
  have hsum := kernel_pair_population_sum S T f g (fun u v => u * v ≠ d)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S.product T)
    (fun z : ℤ × ℤ => f z.1 * g z.2 = d)
  have hsplitR : (((S.product T).filter fun z => f z.1 * g z.2 = d).card : ℝ) +
      (((S.product T).filter fun z => f z.1 * g z.2 ≠ d).card : ℝ) =
      (S.card : ℝ) * T.card := by
    exact_mod_cast (hsplit.trans (Finset.card_product S T))
  have hcard : (V.card : ℝ) ≤ ((S.image f).card : ℝ) * (T.image g).card := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_product (S.image f) (T.image g))
  have hsumR : ∑ q ∈ V,
      ((S.filter fun x => f x = q.1).card : ℝ) * (T.filter fun y => g y = q.2).card =
      (((S.product T).filter fun z => f z.1 * g z.2 ≠ d).card : ℝ) := by
    exact_mod_cast hsum.symm
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
