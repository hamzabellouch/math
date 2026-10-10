import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentNaturals

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def primeProductSamples (P : Finset ℕ) (k : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.univ : Finset P).powersetCard k).image primeSubsetProduct

theorem primeProductSamples_card {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) (k : ℕ) :
    (primeProductSamples P k).card = Nat.choose P.card k := by
  classical
  rw [primeProductSamples, Finset.card_image_of_injective _ (primeSubsetProduct_injective hP)]
  simp

theorem primeProductSamples_nonempty {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {k : ℕ} (hk : k ≤ P.card) : (primeProductSamples P k).Nonempty := by
  rw [← Finset.card_pos, primeProductSamples_card hP]
  exact Nat.choose_pos hk

theorem primeProductSamples_properties {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H k m : ℕ} (hH : ∀ p ∈ P, p ≤ H) (hm : m ∈ primeProductSamples P k) :
    Squarefree m ∧ Odd m ∧ m ≤ H ^ k ∧ m.primeFactors.card = k := by
  classical
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hm
  have hcard : U.card = k := (Finset.mem_powersetCard.mp hU).2
  refine ⟨primeSubsetProduct_squarefree hP U, ?_, ?_, ?_⟩
  · have hodd (V : Finset P) : Odd (∏ p ∈ V, p.val) := by
      induction V using Finset.induction_on with
      | empty => simp
      | @insert p V hp ih =>
        rw [Finset.prod_insert hp]
        exact (ho p p.property).mul ih
    exact hodd U
  · calc
      primeSubsetProduct U = ∏ p ∈ U, p.val := rfl
      _ ≤ ∏ _p ∈ U, H := Finset.prod_le_prod (fun p hp => hH p p.property)
      _ = H ^ k := by rw [Finset.prod_const, hcard]
  · rw [primeSubsetProduct_primeFactors_card hP, hcard]

theorem primeProductSamples_subset_odd_range {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H k : ℕ} (hH : ∀ p ∈ P, p ≤ H) :
    primeProductSamples P k ⊆ (Finset.range (H ^ k + 1)).filter Odd := by
  intro m hm
  have hh := primeProductSamples_properties hP ho hH hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hh.2.2.1), hh.2.1⟩

def primeProductMean (P : Finset ℕ) (k : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ primeProductSamples P k, f m) / (Nat.choose P.card k : ℝ)

theorem primeProductMean_le_odd_sum {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H k : ℕ} (hH : ∀ p ∈ P, p ≤ H) (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) :
    primeProductMean P k f ≤
      (∑ m ∈ (Finset.range (H ^ k + 1)).filter Odd, f m) / (Nat.choose P.card k : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (primeProductSamples_subset_odd_range hP ho hH)
    (fun m hm hnot => hf m)

theorem half_card_pow_le_choose {J k : ℕ} (hk : 2 * k ≤ J) :
    ((J : ℝ) / 2) ^ k / k.factorial ≤ Nat.choose J k := by
  have hjk : (J : ℝ) / 2 ≤ (J + 1 - k : ℕ) := by
    have hn : J ≤ (J + 1 - k) * 2 := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by exact_mod_cast hn)
  apply (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hjk k) (Nat.cast_nonneg _)).trans
  exact Nat.pow_le_choose k J

end Ostmann.QuadraticCenter

end

end OAI
