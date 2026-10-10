import OAI.NumberTheory.CubicMoment.Estimates.LogNormCells

namespace OAI

/-! Summing arbitrary cell pairs costs the square roots of their counts.
These bounds also apply to the far-cell subset. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cell_mass_sum_le {ι : Type*} (I : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ I, a i) ≤ Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2) := by
  have hh := cell_mass_sum_sq I a
  have hcard : 0 ≤ (I.card:ℝ) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ i ∈ I, (a i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : (Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2))^2 =
      (I.card:ℝ)*(∑ i ∈ I, (a i)^2) := by
    rw [mul_pow,Real.sq_sqrt hcard,Real.sq_sqrt hsum]
  rw [←hs] at hh
  have hn : 0 ≤ Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2) := by positivity
  nlinarith only [hh,hn]

lemma cell_pair_mass_sum_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (E : Finset (ι × κ))
    (hE : E ⊆ I.product J) (a : ι → ℝ) (b : κ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ j ∈ J, 0 ≤ b j) :
    (∑ e ∈ E, a e.1*b e.2) ≤
      Real.sqrt (I.card:ℝ)*Real.sqrt (J.card:ℝ)*
        Real.sqrt (∑ i ∈ I, (a i)^2)*Real.sqrt (∑ j ∈ J, (b j)^2) := by
  calc
    _ ≤ ∑ e ∈ I.product J, a e.1*b e.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun e he _ =>
        mul_nonneg (ha e.1 (Finset.mem_product.mp he).1)
          (hb e.2 (Finset.mem_product.mp he).2))
    _ = (∑ i ∈ I, a i)*(∑ j ∈ J, b j) := by
      calc
        _ = ∑ i ∈ I, ∑ j ∈ J, a i*b j := Finset.sum_product I J _
        _ = _ := by
          simp only [Finset.mul_sum,Finset.sum_mul]
          exact Finset.sum_comm
    _ ≤ (Real.sqrt (I.card:ℝ)*Real.sqrt (∑ i ∈ I, (a i)^2))*
        (Real.sqrt (J.card:ℝ)*Real.sqrt (∑ j ∈ J, (b j)^2)) :=
      mul_le_mul (cell_mass_sum_le I a) (cell_mass_sum_le J b)
        (Finset.sum_nonneg hb) (by positivity)
    _ = _ := by ring

lemma logCell_pair_mass_sum_le (P S : Finset Eisenstein) (J A B : ℝ)
    (E : Finset (ℤ × ℤ))
    (hE : E ⊆ (P.image (logNormCell J A)).product (S.image (logNormCell J B)))
    (α β : Eisenstein → ℂ) :
    (∑ e ∈ E, Real.sqrt (∑ a ∈ logNormCellSupport P J A e.1, ‖α a‖^2)*
      Real.sqrt (∑ b ∈ logNormCellSupport S J B e.2, ‖β b‖^2)) ≤
      Real.sqrt ((P.image (logNormCell J A)).card:ℝ)*
        Real.sqrt ((S.image (logNormCell J B)).card:ℝ)*
          Real.sqrt (∑ a ∈ P, ‖α a‖^2)*Real.sqrt (∑ b ∈ S, ‖β b‖^2) := by
  have hh := cell_pair_mass_sum_le (P.image (logNormCell J A)) (S.image (logNormCell J B))
    E hE (fun i => Real.sqrt (∑ a ∈ logNormCellSupport P J A i, ‖α a‖^2))
    (fun j => Real.sqrt (∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2))
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
  simpa only [logNormCell_energy] using hh

end CubicFirstMoment

end

end OAI
