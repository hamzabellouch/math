import OAI.NumberTheory.Ostmann.Construction.LogCellFinitePartition
import OAI.NumberTheory.Ostmann.Construction.PrimeSources

namespace OAI

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

theorem dependentProductPrior_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : ∀ i, FinitePrior (κ i))
    (f : ∀ i, κ i → ℝ) :
    (dependentProductPrior μ).mean (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).mean (f i) := by
  simp only [FinitePrior.mean, dependentProductPrior, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).mass x*f i x)).symm

theorem dependentProductPrior_mean_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : ∀ i, FinitePrior (κ i))
    (f : ∀ i, κ i → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hf : ∀ i, a ≤ (μ i).mean (f i)) :
    a^(Fintype.card ι) ≤ (dependentProductPrior μ).mean (fun x => ∏ i, f i (x i)) := by
  rw [dependentProductPrior_mean]
  simpa only [Finset.prod_const, Finset.card_univ] using
    (Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : ι => a)
      (g := fun i => (μ i).mean (f i)) (fun _ _ => ha) (fun i _ => hf i))

theorem finitePrior_logCell_partition {ι : Type*} [Fintype ι]
    (μ : FinitePrior ι) (x F : ι → ℝ) (lo hi : ℝ)
    (hx : ∀ i, lo ≤ x i ∧ x i ≤ hi) :
    (∑ c∈logBlockCenters lo (hi-lo),
      μ.mean (fun i => Ostmann.smoothPartition (x i-c)*F i)) = μ.mean F := by
  classical
  simp only [FinitePrior.mean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi'
  simp_rw [← mul_assoc, mul_comm (μ.mass i) (Ostmann.smoothPartition _), mul_assoc]
  rw [← Finset.sum_mul, logBlockCenters_partition lo (hi-lo) (x i) (by
    constructor
    · exact (hx i).1
    · linarith [(hx i).2]), one_mul]

theorem exists_finitePrior_logCell {ι : Type*} [Fintype ι]
    (μ : FinitePrior ι) (x F : ι → ℝ) (lo hi : ℝ)
    (hlo : lo ≤ hi) (hx : ∀ i, lo ≤ x i ∧ x i ≤ hi)
    (hF : 0 < μ.mean F) :
    ∃ c∈logBlockCenters lo (hi-lo),
      μ.mean F/(2*(hi-lo+5)) <
        μ.mean (fun i => Ostmann.smoothPartition (x i-c)*F i) := by
  classical
  by_contra hn
  push Not at hn
  have hd : 0 < hi-lo+5 := by linarith
  have hratio : 0 ≤ μ.mean F/(2*(hi-lo+5)) :=
    div_nonneg hF.le (by positivity)
  have hs := Finset.sum_le_sum hn
  rw [finitePrior_logCell_partition μ x F lo hi hx] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hc := logBlockCenters_card_le lo (hi-lo) (sub_nonneg.mpr hlo)
  have ht := mul_le_mul_of_nonneg_right hc hratio
  have he : (hi-lo+5)*(μ.mean F/(2*(hi-lo+5)))=μ.mean F/2 := by
    field_simp
  rw [he] at ht
  linarith

end Ostmann.Construction

end

end OAI
