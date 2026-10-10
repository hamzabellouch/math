import Mathlib.Combinatorics.Additive.VerySmallDoubling
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace OAI

/-!
# A bounded number of sums in a dense generating set

The good-cell construction needs a uniform covering length in a finite cyclic group.
The elementary small-doubling theorem already in Mathlib supplies this without any
additional published-input hypothesis. Constants need not be optimal here.
-/

namespace Ostmann

open scoped Pointwise

private theorem small_doubling_cover {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : 1 ∈ A) (hgen : Subgroup.closure (A : Set G) = ⊤)
    (hsmall : ((A * A).card : ℝ) < (3 / 2 : ℝ) * A.card) :
    A * A = Finset.univ := by
  have hq : ((A * A).card : ℚ) < (3 / 2 : ℚ) * A.card := by
    have h : (2 : ℝ) * (A * A).card < 3 * A.card := by linarith
    have h' : (2 : ℚ) * (A * A).card < 3 * A.card := by exact_mod_cast h
    linarith
  let H := Finset.invMulSubgroup A hq
  have hAH : (A : Set G) ⊆ H := by
    intro a ha
    change a ∈ (Finset.invMulSubgroup A hq : Set G)
    rw [Finset.invMulSubgroup_eq_inv_mul]
    rw [← Finset.coe_mul]
    change a ∈ (A⁻¹ * A : Finset G)
    exact Finset.mem_mul.mpr ⟨1, by simpa using h1, a, ha, one_mul a⟩
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (Subgroup.closure_le H).mpr hAH
  have hdiff : A⁻¹ * A = Finset.univ := by
    ext a
    have ha : a ∈ H := by rw [hH]; trivial
    change a ∈ (Finset.invMulSubgroup A hq : Set G) at ha
    rw [Finset.invMulSubgroup_eq_inv_mul, ← Finset.coe_mul] at ha
    norm_cast at ha
    simpa using ha
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [← Finset.card_inv_mul_of_doubling_lt_three_halves hq, hdiff]

private theorem product_growth_or_cover {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : 1 ∈ A) (hgen : Subgroup.closure (A : Set G) = ⊤) :
    A * A = Finset.univ ∨ (3 / 2 : ℝ) * A.card ≤ (A * A).card := by
  by_cases h : ((A * A).card : ℝ) < (3 / 2 : ℝ) * A.card
  · exact Or.inl (small_doubling_cover A h1 hgen h)
  · exact Or.inr (le_of_not_gt h)

private theorem dyadic_product_growth {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : 1 ∈ A) (hgen : Subgroup.closure (A : Set G) = ⊤) (j : ℕ) :
    A ^ (2 ^ j) = Finset.univ ∨
      (3 / 2 : ℝ) ^ j * A.card ≤ (A ^ (2 ^ j)).card := by
  induction j with
  | zero => exact Or.inr (by simp)
  | succ j ih =>
    have hj : 1 ∈ A ^ (2 ^ j) := Finset.one_mem_pow h1
    have hAj : A ⊆ A ^ (2 ^ j) := Finset.subset_pow h1 (by positivity)
    have hgj : Subgroup.closure ((A ^ (2 ^ j) : Finset G) : Set G) = ⊤ := by
      apply top_unique
      rw [← hgen]
      exact Subgroup.closure_mono (show ((A : Finset G) : Set G) ⊆
        ((A ^ (2 ^ j) : Finset G) : Set G) from hAj)
    have hsq : A ^ (2 ^ (j + 1)) = A ^ (2 ^ j) * A ^ (2 ^ j) := by
      rw [pow_succ, Nat.mul_two, pow_add]
    rcases product_growth_or_cover (A ^ (2 ^ j)) hj hgj with hc | hg
    · exact Or.inl (hsq.trans hc)
    · rcases ih with hi | hi
      · exact Or.inl (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
          have hsub := Finset.pow_subset_pow_right h1 (show 2 ^ j ≤ 2 ^ (j + 1) by
            rw [pow_succ]; omega)
          rw [hi] at hsub
          exact Finset.card_le_card hsub))
      · right
        rw [hsq, pow_succ]
        calc
          (3 / 2 : ℝ) ^ j * (3 / 2) * A.card =
              (3 / 2) * ((3 / 2 : ℝ) ^ j * A.card) := by ring
          _ ≤ (3 / 2 : ℝ) * (A ^ (2 ^ j)).card := by gcongr
          _ ≤ _ := hg

/-- A positive-density generating set containing the identity covers its finite group
in a number of products depending only on the density. -/
private theorem exists_uniform_product_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
      (A : Finset G), 1 ∈ A → Subgroup.closure (A : Set G) = ⊤ →
      δ * Fintype.card G ≤ A.card → A ^ r = Finset.univ := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (δ⁻¹) (by norm_num : (1 : ℝ) < 3 / 2)
  refine ⟨2 ^ j, by positivity, ?_⟩
  intro G _ _ _ A h1 hgen hdensity
  rcases dyadic_product_growth A h1 hgen j with hcover | hgrowth
  · exact hcover
  · have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hδj : 1 < (3 / 2 : ℝ) ^ j * δ := by
      have := (mul_lt_mul_iff_left₀ hδ).mpr hj
      rw [inv_mul_cancel₀ hδ.ne'] at this
      simpa only [mul_comm] using this
    have hupper : ((A ^ (2 ^ j)).card : ℝ) ≤ Fintype.card G := by
      exact Nat.cast_le.mpr (Finset.card_le_univ (A ^ (2 ^ j : ℕ)))
    have hlower : (3 / 2 : ℝ) ^ j * (δ * Fintype.card G) ≤
        (A ^ (2 ^ j)).card := (mul_le_mul_of_nonneg_left hdensity (by positivity)).trans hgrowth
    nlinarith

/-- Uniform cyclic covering, expressed as an ordered tuple of summands. -/
theorem exists_uniform_cyclic_sum_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (q : ℕ) [NeZero q] (S : Finset (ZMod q)),
      0 ∈ S → AddSubgroup.closure (S : Set (ZMod q)) = ⊤ →
      δ * q ≤ S.card → ∀ x : ZMod q,
      ∃ f : Fin r → ZMod q, (∀ i, f i ∈ S) ∧ ∑ i, f i = x := by
  obtain ⟨r, hr, hcover⟩ := exists_uniform_product_cover δ hδ
  refine ⟨r, hr, ?_⟩
  intro q _ S h0 hgen hdensity x
  let A : Finset (Multiplicative (ZMod q)) := S.image Multiplicative.ofAdd
  have hset : (A : Set (Multiplicative (ZMod q))) =
      Multiplicative.toAdd ⁻¹' (S : Set (ZMod q)) := by
    ext a
    simp [A]
  have hgenA : Subgroup.closure (A : Set (Multiplicative (ZMod q))) = ⊤ := by
    rw [hset, ← AddSubgroup.toSubgroup_closure, hgen]
    rfl
  have hcard : A.card = S.card := Finset.card_image_of_injective _
    (fun _ _ h => congrArg Multiplicative.toAdd h)
  have h1 : 1 ∈ A := by
    exact Finset.mem_image.mpr ⟨0, h0, rfl⟩
  have hd : δ * Fintype.card (Multiplicative (ZMod q)) ≤ A.card := by
    simpa [hcard, Fintype.card_multiplicative, ZMod.card] using hdensity
  have hx : Multiplicative.ofAdd x ∈ A ^ r := by
    rw [hcover (Multiplicative (ZMod q)) A h1 hgenA hd]
    exact Finset.mem_univ _
  obtain ⟨f, hf⟩ := Finset.mem_pow.mp hx
  refine ⟨fun i => Multiplicative.toAdd (f i), ?_, ?_⟩
  · intro i
    have hi := (f i).property
    change (f i).val ∈ (A : Set (Multiplicative (ZMod q))) at hi
    rwa [hset] at hi
  · have hh := congrArg Multiplicative.toAdd hf
    simpa only [List.prod_ofFn, toAdd_prod, toAdd_ofAdd] using hh

end Ostmann

end OAI
