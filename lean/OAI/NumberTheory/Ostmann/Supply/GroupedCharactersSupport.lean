import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersTransform

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset Ostmann.FiniteField
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
local instance (i : ι) : Fintype (MulChar (F i) ℂ) := Fintype.ofFinite _

def characterSupport (ρ : ∀ i, MulChar (F i) ℂ) : Finset ι := univ.filter (fun i => ρ i ≠ 1)

omit [DecidableEq ι] [∀ index, DecidableEq (F index)] in
@[simp] theorem mem_characterSupport (ρ : ∀ i, MulChar (F i) ℂ) (i : ι) :
    i ∈ characterSupport F ρ ↔ ρ i ≠ 1 := by simp [characterSupport]

theorem mellin_one_eq_zero {G : Type*} [Field G] [Fintype G] [DecidableEq G]
    (χ : MulChar G ℂ) (hχ : χ ≠ 1) : mellin (fun _ => 1) χ = 0 := by
  unfold Ostmann.FiniteField.mellin
  simp only [one_mul, ← map_sum, sum_units_mulChar, ite_eq_right hχ, map_zero, mul_zero]

theorem coefficient_subsetPair (b : ∀ i, F i → ℂ) (s t : Finset ι)
    (ρ : ∀ i, MulChar (F i) ℂ) :
    coefficient F (fun x => (∏ i ∈ s, b i (x i)) * (∏ i ∈ t, b i (x i))) ρ =
      ∏ i, mellin (fun u : (F i)ˣ =>
        (if i ∈ s then b i u else 1) * (if i ∈ t then b i u else 1)) (ρ i) := by
  rw [← coefficient_prod]
  congr 1
  funext x
  simp only [prod_mul_distrib, Fintype.prod_ite_mem]

theorem coefficient_subsetPair_eq_zero (b : ∀ i, F i → ℂ) (s t : Finset ι)
    (ρ : ∀ i, MulChar (F i) ℂ) (h : ¬characterSupport F ρ ⊆ s ∪ t) :
    coefficient F (fun x => (∏ i ∈ s, b i (x i)) * (∏ i ∈ t, b i (x i))) ρ = 0 := by
  rw [coefficient_subsetPair]
  obtain ⟨i, hi, hit⟩ := not_subset.mp h
  have his : i ∉ s := fun hs => hit (mem_union_left t hs)
  have hit' : i ∉ t := fun ht => hit (mem_union_right s ht)
  apply prod_eq_zero (mem_univ i)
  simp only [ite_eq_right his, ite_eq_right hit', one_mul]
  exact mellin_one_eq_zero (ρ i) ((mem_characterSupport F ρ i).mp hi)

theorem weightCoefficient_eq_sum (b : ∀ i, F i → ℝ) (K : ℕ)
    (ρ : ∀ i, MulChar (F i) ℂ) :
    weightCoefficient F b K ρ =
      ∑ s ∈ univ.powerset.filter (fun s : Finset ι => s.card ≤ K),
        ∑ t ∈ univ.powerset.filter (fun t : Finset ι => t.card ≤ K),
          coefficient F (fun x => (∏ i ∈ s, (b i (x i) : ℂ)) *
            (∏ i ∈ t, (b i (x i) : ℂ))) ρ := by
  unfold weightCoefficient truncatedWeight truncatedSubsetSum
  simp only [Complex.ofReal_sum, Complex.ofReal_prod,
    pow_two, sum_mul, mul_sum, coefficient_sum, Complex.ofReal_mul]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro t ht
  congr 1
  funext x
  exact mul_comm _ _

theorem weightCoefficient_eq_zero_of_card (b : ∀ i, F i → ℝ) (K : ℕ)
    (ρ : ∀ i, MulChar (F i) ℂ) (hcard : 2*K < (characterSupport F ρ).card) :
    weightCoefficient F b K ρ = 0 := by
  rw [weightCoefficient_eq_sum]
  apply sum_eq_zero
  intro s hs
  apply sum_eq_zero
  intro t ht
  apply coefficient_subsetPair_eq_zero F (fun i x => (b i x : ℂ)) s t ρ
  intro hsub
  have hc := (card_le_card hsub).trans (card_union_le s t)
  have hsK := (mem_filter.mp hs).2
  have htK := (mem_filter.mp ht).2
  omega

theorem characterSupport_card_le (b : ∀ i, F i → ℝ) (K : ℕ)
    (ρ : ∀ i, MulChar (F i) ℂ) (h : weightCoefficient F b K ρ ≠ 0) :
    (characterSupport F ρ).card ≤ 2*K := by
  by_contra! hn
  exact h (weightCoefficient_eq_zero_of_card F b K ρ hn)

theorem characterSupport_product_le (b : ∀ i, F i → ℝ) (K : ℕ)
    (ρ : ∀ i, MulChar (F i) ℂ) (h : weightCoefficient F b K ρ ≠ 0)
    (p : ι → ℕ) {pmax : ℕ} (hpmax : 1 ≤ pmax) (hp : ∀ i, p i ≤ pmax) :
    (∏ i ∈ characterSupport F ρ, p i) ≤ pmax^(2*K) := by
  calc
    _ ≤ ∏ i ∈ characterSupport F ρ, pmax := prod_le_prod (fun i hi => hp i)
    _ = pmax^((characterSupport F ρ).card) := prod_const _
    _ ≤ _ := pow_le_pow_right' hpmax (characterSupport_card_le F b K ρ h)

end Ostmann.Supply.GroupedCharacters

end

end OAI
