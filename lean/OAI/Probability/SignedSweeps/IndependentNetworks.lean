import OAI.Probability.SignedSweeps.EncounterGraph
import OAI.Probability.SignedSweeps.SubsetLaw

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]

def subsetFiber (S : Finset (J × A)) (j : J) : Finset A :=
  Finset.univ.filter (fun x => (j,x) ∈ S)

omit [Fintype J] in
@[simp]
lemma mem_subsetFiber (S : Finset (J × A)) (j : J) (x : A) :
    x ∈ subsetFiber S j ↔ (j,x) ∈ S := by simp [subsetFiber]

def subsetFiberEquiv : Finset (J × A) ≃ (J → Finset A) where
  toFun := subsetFiber
  invFun S := Finset.univ.filter (fun v => v.2 ∈ S v.1)
  left_inv S := by ext v; simp
  right_inv S := by ext j x; simp

omit [Fintype J] in
lemma subset_iff_fibers {S T : Finset (J × A)} :
    S ⊆ T ↔ ∀ j, subsetFiber S j ⊆ subsetFiber T j := by
  constructor
  · intro h j x hx
    exact (mem_subsetFiber T j x).mpr (h ((mem_subsetFiber S j x).mp hx))
  · intro h v hv
    exact (mem_subsetFiber T v.1 v.2).mp (h v.1 ((mem_subsetFiber S v.1 v.2).mpr hv))

lemma card_subset_fibers (S : Finset (J × A)) : S.card = ∑ j, (subsetFiber S j).card := by
  calc
    S.card = ∑ v : J × A, if v ∈ S then 1 else 0 := by simp
    _ = ∑ j, ∑ x : A, if (j,x) ∈ S then 1 else 0 := Fintype.sum_prod_type _
    _ = _ := by simp only [subsetFiber, Finset.card_filter]

def independentSubsetLaw (μ : J → Finset A → ℝ) (S : Finset (J × A)) : ℝ :=
  ∏ j, μ j (subsetFiber S j)

lemma independentSubsetLaw_nonneg (μ : J → Finset A → ℝ) (hμ : ∀ j S, 0 ≤ μ j S)
    (T : Finset (J × A)) : 0 ≤ independentSubsetLaw μ T :=
  Finset.prod_nonneg (fun j _ => hμ j _)

lemma independentSubsetLaw_mass (μ : J → Finset A → ℝ) :
    (∑ S, independentSubsetLaw μ S) = ∏ j, ∑ T, μ j T := by
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv subsetFiberEquiv _ _ (fun S => rfl)

lemma independentSubsetLaw_card_support (μ : J → Finset A → ℝ) (k : J → ℕ)
    (hμ : ∀ j S, S.card ≠ k j → μ j S = 0) (T : Finset (J × A))
    (hT : T.card ≠ ∑ j, k j) : independentSubsetLaw μ T = 0 := by
  have hex : ∃ j, (subsetFiber T j).card ≠ k j := by
    by_contra h
    push Not at h
    exact hT ((card_subset_fibers T).trans (Finset.sum_congr rfl (fun j _ => h j)))
  obtain ⟨j, hj⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ j) (hμ j _ hj)

lemma independentSubsetLaw_upper_inclusion (μ : J → Finset A → ℝ) (T : Finset (J × A)) :
    (∑ U : Finset (J × A), if T ⊆ U then independentSubsetLaw μ U else 0) =
      ∏ j, ∑ U : Finset A, if subsetFiber T j ⊆ U then μ j U else 0 := by
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv subsetFiberEquiv
  intro S
  simp only [Finset.prod_ite_zero, Finset.mem_univ, forall_true_left]
  change (if T ⊆ S then independentSubsetLaw μ S else 0) =
    if ∀ j, subsetFiber T j ⊆ subsetFiber S j then (∏ j, μ j (subsetFiber S j)) else 0
  simp only [subset_iff_fibers, independentSubsetLaw]

lemma network_weight_product (T : Finset (J × A)) (p : J → ℝ) :
    (∏ v ∈ T, p v.1) = ∏ j, p j ^ (subsetFiber T j).card := by
  calc
    (∏ v ∈ T, p v.1) = ∏ v : J × A, if v ∈ T then p v.1 else 1 := by simp
    _ = ∏ j, ∏ x : A, if (j,x) ∈ T then p j else 1 := Fintype.prod_prod_type _
    _ = ∏ j, ∏ _ ∈ subsetFiber T j, p j := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [subsetFiber, Finset.prod_filter]
    _ = _ := by simp

lemma independentSubsetLaw_inclusion_bound (μ : J → Finset A → ℝ) (p : J → ℝ)
    (hμ : ∀ j S, 0 ≤ μ j S) (_hp : ∀ j, 0 ≤ p j)
    (hinc : ∀ j T, (∑ U : Finset A, if T ⊆ U then μ j U else 0) ≤ (p j) ^ T.card)
    (T : Finset (J × A)) :
    (∑ U : Finset (J × A), if T ⊆ U then independentSubsetLaw μ U else 0) ≤
      ∏ v ∈ T, p v.1 := by
  rw [independentSubsetLaw_upper_inclusion, network_weight_product]
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.sum_nonneg (fun U _ => by split_ifs; exact hμ j U; exact le_rfl)
  · intro j _; exact hinc j _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}

def independentSweptLaw (S : J → Finset (Fin (2 ^ d))) : Finset (J × Fin (2 ^ d)) → ℝ :=
  independentSubsetLaw (fun j => sweptSubsetLaw d (S j))

lemma independentSweptLaw_nonneg (S : J → Finset (Fin (2 ^ d))) (T : Finset (J × Fin (2 ^ d))) :
    0 ≤ independentSweptLaw S T :=
  independentSubsetLaw_nonneg _ (fun j U => sweptSubsetLaw_nonneg d (S j) U) T

lemma independentSweptLaw_mass (S : J → Finset (Fin (2 ^ d))) :
    (∑ T, independentSweptLaw S T) = 1 := by
  unfold independentSweptLaw
  rw [independentSubsetLaw_mass]
  simp only [sweptSubsetLaw_mass, Finset.prod_const_one]

lemma independentSweptLaw_card_support (S : J → Finset (Fin (2 ^ d)))
    (T : Finset (J × Fin (2 ^ d))) (hT : T.card ≠ ∑ j, (S j).card) :
    independentSweptLaw S T = 0 :=
  independentSubsetLaw_card_support _ (fun j => (S j).card)
    (fun j U => sweptSubsetLaw_card_support d (S j) U) T hT

lemma independentSweptLaw_upper_inclusion (S : J → Finset (Fin (2 ^ d))) (T : Finset (J × Fin (2 ^ d))) :
    (∑ U : Finset (J × Fin (2 ^ d)), if T ⊆ U then independentSweptLaw S U else 0) ≤
      ∏ w ∈ T, ((S w.1).card : ℝ) / (2 ^ d : ℕ) :=
  independentSubsetLaw_inclusion_bound _ _ (fun j U => sweptSubsetLaw_nonneg d (S j) U)
    (fun index => div_nonneg (Nat.cast_nonneg (S index).card) (Nat.cast_nonneg _))
    (fun j T => sweptSubsetLaw_upper_inclusion d (S j) T) T

theorem swept_network_noIsolates_bound
    (state : J → Fin d → SymmetricGroup (2 ^ d)) (S : J → Finset (Fin (2 ^ d)))
    (k : ℕ) (hk : k = ∑ j, (S j).card)
    (hΔ : 0 < 2 * (d : ℝ) * k / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤ 1) :
    (∑ T : {T : Finset (J × Fin (2 ^ d)) // NoIsolatedVertex (encounterGraph state) T}, independentSweptLaw S T.1) ≤
      (Real.sqrt (2 * (d : ℝ) * k / (2 ^ d : ℕ))) ^ k * Real.exp (Real.exp 2 * k) := by
  have hn : (2 ^ d : ℕ) ≠ 0 := ne_of_gt (pow_pos (by omega : 0 < (2 : ℕ)) _)
  have hnR : ((2 ^ d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn
  apply network_noIsolates_probability_bound state (fun j => (S j).card / (2 ^ d : ℕ))
    (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) k _
    (independentSweptLaw S) (independentSweptLaw_nonneg S)
    (fun T hT => independentSweptLaw_card_support S T (hk ▸ hT))
    (independentSweptLaw_upper_inclusion S) hΔ hΔ1
  rw [← Finset.sum_div, mul_div_cancel₀ _ hnR, hk, Nat.cast_sum]

end SignedSweeps
end

end OAI
