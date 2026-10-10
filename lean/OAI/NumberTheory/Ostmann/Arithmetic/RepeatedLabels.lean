import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.RepeatedLabels
open scoped BigOperators

def multiplicity {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (label : ι → κ)
    (b : κ) : ℕ := (s.filter fun i => label i = b).card

theorem product_by_multiplicity {ι κ M : Type*} [DecidableEq κ] [Fintype κ]
    [CommMonoid M] (s : Finset ι) (label : ι → κ) (p : κ → M) :
    (∏ i ∈ s, p (label i)) = ∏ b, p b ^ multiplicity s label b := by
  rw [← Finset.prod_fiberwise' s label p]
  simp only [multiplicity, Finset.prod_const]

theorem occurrence_product_by_labels {ι κ M : Type*} [DecidableEq κ] [Fintype κ]
    [CommMonoid M] (s : Finset ι) (label : ι → κ) (w : ι → M) :
    (∏ i ∈ s, w i) = ∏ b, ∏ i ∈ s with label i = b, w i :=
  (Finset.prod_fiberwise s label w).symm

theorem representative_identity {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (b : ℝ) (μ : ι → ℝ) :
    ((∏ i ∈ s, μ i) * b ^ s.card) / (b-1) =
      (b/(b-1)) * μ i₀ * ∏ i ∈ s.erase i₀, b * μ i := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase s (fun i => μ i * b) hi₀]
  simp_rw [mul_comm (μ _) b]
  ring

theorem representative_domination {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {i₀ : ι} (hi₀ : i₀ ∈ s) {b K : ℝ} (hb : 2 ≤ b) (_hK : 0 ≤ K)
    (μ : ι → ℝ) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hbound : ∀ i ∈ s, b * μ i ≤ K) :
    ((∏ i ∈ s, μ i) * b ^ s.card) / (b-1) ≤
      2 * μ i₀ * K ^ (s.card-1) := by
  rw [representative_identity s hi₀]
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hratio : b / (b-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hratio0 : 0 ≤ b / (b-1) := div_nonneg hb0 (by linarith)
  have hprod0 : 0 ≤ ∏ i ∈ s.erase i₀, b * μ i :=
    Finset.prod_nonneg fun i hi => mul_nonneg hb0 (hμ i (Finset.mem_of_mem_erase hi))
  have hprod : (∏ i ∈ s.erase i₀, b * μ i) ≤ K ^ (s.card-1) := by
    calc
      _ ≤ ∏ _i ∈ s.erase i₀, K := Finset.prod_le_prod₀
        (fun i hi => mul_nonneg hb0 (hμ i (Finset.mem_of_mem_erase hi)))
        (fun i hi => hbound i (Finset.mem_of_mem_erase hi))
      _ = _ := by simp [Finset.card_erase_of_mem hi₀]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hratio (hμ i₀ hi₀)) hprod hprod0
    (mul_nonneg (by norm_num) (hμ i₀ hi₀))

theorem representative_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : κ → Finset ℕ) (μ : κ → ℕ → ℝ)
    (hμ : ∀ b, ∑ p ∈ S b, μ b p = 1) :
    ∑ x ∈ Fintype.piFinset S, ∏ b, μ b (x b) = 1 := by
  rw [← Finset.prod_univ_sum]
  simp only [hμ, Finset.prod_const_one]

end Ostmann.Arithmetic.RepeatedLabels

end

end OAI
