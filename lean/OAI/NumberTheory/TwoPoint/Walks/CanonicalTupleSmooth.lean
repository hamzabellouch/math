import OAI.NumberTheory.TwoPoint.Walks.TupleSmoothCost
import OAI.NumberTheory.TwoPoint.Walks.CanonicalTupleSlices
import OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale

namespace OAI

/-! Uniformly bounded smooth-dilation cost for every retained subtuple of
the actual canonical prime bands. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma retained_tuple_factor_subset {J : ℕ} (P : Fin J → Finset ℕ)
    (hp : ∀ i, ∀ p ∈ P i, p.Prime) (I : Finset (Fin J))
    (y : (i : {i // i ∉ I}) → P i) :
    (∏ i, (y i).val).primeFactors ⊆ univ.image (fun i => (y i).val) := by
  intro p hp'
  have hpprime := Nat.prime_of_mem_primeFactors hp'
  have hdiv := Nat.dvd_of_mem_primeFactors hp'
  obtain ⟨i, _, hi⟩ := (hpprime.prime.dvd_finsetProd_iff (fun i => (y i).val)).mp hdiv
  have he : p = (y i).val := (Nat.prime_dvd_prime_iff_eq hpprime
    (hp i _ (y i).property)).mp hi
  exact mem_image.mpr ⟨i, mem_univ _, he.symm⟩

lemma retained_tuple_factor_card {J : ℕ} (P : Fin J → Finset ℕ)
    (hp : ∀ i, ∀ p ∈ P i, p.Prime) (I : Finset (Fin J))
    (y : (i : {i // i ∉ I}) → P i) : (∏ i, (y i).val).primeFactors.card ≤ J := by
  calc
    _ ≤ (univ.image (fun i => (y i).val)).card := card_le_card (retained_tuple_factor_subset P hp I y)
    _ ≤ (univ : Finset {i : Fin J // i ∉ I}).card := card_image_le
    _ ≤ J := by simpa only [card_univ, Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin J => i ∉ I)

theorem eventually_canonical_retained_smooth_cost (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ∀ I : Finset (Fin J), ∀ y : (i : {i // i ∉ I}) → P i,
        smoothReciprocalProduct (∏ i, (y i).val).primeFactors (1 / 2 : ℝ) ≤ 2 := by
  filter_upwards [eventually_canonical_smooth_half_cost, eventually_ge_atTop (1 : ℝ)] with L hcost hL
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime E A W J
  intro I y
  apply hcost
  · exact (show ((∏ i, (y i).val).primeFactors.card : ℝ) ≤ J by
      exact_mod_cast retained_tuple_factor_card P hp I y).trans
        ((primeSupplyCount_le_log W L hW hL).trans
          ((Real.log_le_sub_one_of_pos hLp).trans (by linarith)))
  · intro p hpmem
    obtain ⟨i, _, hi⟩ := mem_image.mp (retained_tuple_factor_subset P hp I y hpmem)
    subst p
    exact (centeredPrimeSupply_global_bounds (Real.rpow_nonneg hLp.le _) (zero_le_one.trans hW) i.val.isLt
      (primeSupplyScale_endpoint W L (by linarith) hL) (y i).property).1.le

end TwoPointCorrelations

end OAI
