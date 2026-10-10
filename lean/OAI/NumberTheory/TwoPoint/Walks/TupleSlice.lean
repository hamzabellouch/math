import OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! Exact splitting of a prime tuple into the removed and retained
supplies in the quantitative centering expansion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma indexed_prime_product_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    Function.Injective (fun x : (i : ι) → P i => ∏ i, (x i).val) := by
  intro x y he
  change (∏ i, (x i).val) = ∏ i, (y i).val at he
  funext i
  apply Subtype.ext
  have hp := hprime i _ (x i).property
  have hd : (x i).val ∣ ∏ j, (y j).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun j => (x j).val) (mem_univ i)
  obtain ⟨j, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun j => (y j).val)).mp hd
  have hv : (x i).val = (y j).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime j _ (y j).property)).mp hdiv
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (hdisjoint i j (Ne.symm hne)) (x i).property
      (hv.symm ▸ (y j).property)
  subst j
  exact hv

noncomputable def primeTupleSlice {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J)) :
    Finset ℕ := univ.image (fun x : (i : I) → P i => ∏ i, (x i).val)

lemma primeTupleSlice_injective {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    Function.Injective (fun x : (i : I) → P i => ∏ i, (x i).val) :=
  indexed_prime_product_injective _ (fun i => hprime i)
    (fun i j hne => hdisjoint i j (fun he => hne (Subtype.ext he)))

lemma primeTupleSlice_mass {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) :
    (∑ z ∈ primeTupleSlice P I, 1 / (z : ℝ)) = ∏ i : I, primeHarmonicMass (P i) := by
  rw [primeTupleSlice, sum_image]
  · calc
      _ = ∑ x : (i : I) → P i, ∏ i, ((x i).val : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro x _
        simp only [Nat.cast_prod, one_div, prod_inv_distrib]
      _ = _ := by
        simpa only [primeHarmonicMass] using
          (Fintype.prod_sum (fun i : I => fun p : P i => (p.val : ℝ)⁻¹)).symm
  · exact fun x _ y _ he => primeTupleSlice_injective P I hprime hdisjoint he

lemma primeTupleSlice_pos {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) {z : ℕ} (hz : z ∈ primeTupleSlice P I) :
    0 < z := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  exact prod_pos (fun i _ => (hprime i _ (x i).property).pos)

lemma primeTupleSlice_lower {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime) (H : ℝ)
    (hlarge : ∀ i, ∀ p ∈ P i, H ≤ (p : ℝ)) (hne : I.Nonempty)
    {z : ℕ} (hz : z ∈ primeTupleSlice P I) : H ≤ (z : ℝ) := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hz
  obtain ⟨i, hi⟩ := hne
  have hp : (x ⟨i, hi⟩).val ≤ ∏ j, (x j).val :=
    Nat.le_of_dvd (prod_pos (fun j _ => (hprime j _ (x j).property).pos))
      (dvd_prod_of_mem (fun j : I => (x j).val) (mem_univ (⟨i, hi⟩ : I)))
  exact (hlarge i _ (x ⟨i, hi⟩).property).trans (by exact_mod_cast hp)

lemma primeTupleSlice_split_sum {J : ℕ} (P : Fin J → Finset ℕ) (I : Finset (Fin J))
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j)) (F : ℕ → ℕ → ℂ) :
    (∑ x : (j : Fin J) → P j,
      F (∏ j : {j // j ∉ I}, (x j).val) (∏ i : I, (x i).val)) =
      ∑ y : (j : {j // j ∉ I}) → P j, ∑ z ∈ primeTupleSlice P I,
        F (∏ j, (y j).val) z := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : Fin J => j ∈ I) (fun j => P j)
  calc
    _ = ∑ xy : ((i : I) → P i) × ((j : {j // j ∉ I}) → P j),
        F (∏ j, (xy.2 j).val) (∏ i, (xy.1 i).val) := by
      simpa only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk] using
        (e.sum_comp (fun xy => F (∏ j, (xy.2 j).val) (∏ i, (xy.1 i).val)))
    _ = ∑ y : (j : {j // j ∉ I}) → P j, ∑ x : (i : I) → P i,
        F (∏ j, (y j).val) (∏ i, (x i).val) := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro y _
      rw [primeTupleSlice, sum_image]
      exact fun x _ y _ he => primeTupleSlice_injective P I hprime hdisjoint he

end TwoPointCorrelations

end OAI
