import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacementUniform

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators

theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    {ε B : ℝ} (hε : 0 ≤ ε) (hB : 1 ≤ B)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ B) (hg : ∀ i ∈ s, ‖g i‖ ≤ B)
    (he : ∀ i ∈ s, ‖f i - g i‖ ≤ ε) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ s.card * ε * B ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hB0 : 0 ≤ B := by linarith
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ B := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hes : ∀ i ∈ s, ‖f i - g i‖ ≤ ε := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hi := ih hfs hgs hes
    have hpf : ‖∏ i ∈ s, f i‖ ≤ B ^ s.card := by
      rw [norm_prod]
      calc
        (∏ i ∈ s, ‖f i‖) ≤ ∏ _i ∈ s, B :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg (f i)) hfs
        _ = B ^ s.card := by simp
    have hfa := he a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hid : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hid, Finset.card_insert_of_notMem ha]
    calc
      _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ +
          ‖g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)‖ := norm_add_le _ _
      _ ≤ ε * B ^ s.card + B * (s.card * ε * B ^ s.card) := by
        rw [norm_mul, norm_mul]
        exact add_le_add
          (mul_le_mul hfa hpf (norm_nonneg _) hε)
          (mul_le_mul hga hi (norm_nonneg _) hB0)
      _ ≤ ε * B ^ (s.card + 1) + B * (s.card * ε * B ^ s.card) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hB (Nat.le_succ _)) hε) le_rfl
      _ = _ := by rw [pow_succ]; push_cast; ring

theorem joint_product_test_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (μ ν : ∀ i, κ i → ℂ) (F : (∀ i, κ i) → ℂ) {ε B : ℝ}
    (hε : 0 ≤ ε) (hB : 1 ≤ B)
    (hμ : ∀ i a, ‖μ i a‖ ≤ B) (hν : ∀ i a, ‖ν i a‖ ≤ B)
    (he : ∀ i a, ‖μ i a - ν i a‖ ≤ ε) :
    ‖(∑ a : ∀ i, κ i, (∏ i, μ i (a i)) * F a) -
      ∑ a : ∀ i, κ i, (∏ i, ν i (a i)) * F a‖ ≤
      Fintype.card ι * ε * B ^ Fintype.card ι * ∑ a : ∀ i, κ i, ‖F a‖ := by
  classical
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ a : ∀ i, κ i, ‖((∏ i, μ i (a i)) - ∏ i, ν i (a i)) * F a‖ := norm_sum_le _ _
    _ ≤ ∑ a : ∀ i, κ i, (Fintype.card ι * ε * B ^ Fintype.card ι) * ‖F a‖ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [Finset.card_univ] using norm_prod_sub_prod_le Finset.univ
        (fun i => μ i (a i)) (fun i => ν i (a i)) hε hB
        (fun i _ => hμ i (a i)) (fun i _ => hν i (a i)) (fun i _ => he i (a i))
    _ = _ := by rw [Finset.mul_sum]

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
