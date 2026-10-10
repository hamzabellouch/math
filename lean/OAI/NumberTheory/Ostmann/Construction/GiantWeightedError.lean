import OAI.NumberTheory.Ostmann.Construction.GiantEmpirical

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Preliminaries
open scoped BigOperators

lemma finite_weighted_absolute_error_sq (P : Finset ℕ) (w e : ℕ → ℝ)
    (hw : ∀p∈P,0≤w p) :
    (∑p∈P,w p*|e p|)^2≤(∑p∈P,w p)*(∑p∈P,w p*(e p)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun p => Real.sqrt (w p)) (fun p => Real.sqrt (w p)*|e p|)
  have ht₁ : (∑p∈P,Real.sqrt (w p)*(Real.sqrt (w p)*|e p|))=∑p∈P,w p*|e p| := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [← mul_assoc,Real.mul_self_sqrt (hw p hp)]
  have ht₂ : (∑p∈P,(Real.sqrt (w p))^2)=∑p∈P,w p := by
    exact Finset.sum_congr rfl (fun p hp => Real.sq_sqrt (hw p hp))
  have ht₃ : (∑p∈P,(Real.sqrt (w p)*|e p|)^2)=∑p∈P,w p*(e p)^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_pow,Real.sq_sqrt (hw p hp),sq_abs]
  rwa [ht₁,ht₂,ht₃] at h

theorem eventually_giant_weighted_error (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ P : Finset ℕ, P⊆(collisionScale 4 X).primesLE →
      (∑p∈P,(Real.log p/(p:ℝ))*|giantEmpiricalMean d X p-giantSupportMean d p|)^2≤
      (∑p∈P,Real.log p/(p:ℝ))*(collisionConstant 4*Real.log (Real.log (X:ℝ))) := by
  filter_upwards [eventually_giant_mean_square_error d] with X hX
  intro P hP
  have hw (p : ℕ) : 0≤Real.log p/(p:ℝ) :=
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hc := finite_weighted_absolute_error_sq P (fun p => Real.log p/(p:ℝ))
    (fun p => giantEmpiricalMean d X p-giantSupportMean d p) (fun p _ => hw p)
  have hsub : (∑p∈P,(Real.log p/(p:ℝ))*(giantEmpiricalMean d X p-giantSupportMean d p)^2)≤
      collisionConstant 4*Real.log (Real.log (X:ℝ)) := by
    apply le_trans _ hX
    apply Finset.sum_le_sum_of_subset_of_nonneg hP
    intro p hp _
    exact mul_nonneg (hw p) (sq_nonneg _)
  exact hc.trans (mul_le_mul_of_nonneg_left hsub (Finset.sum_nonneg (fun p _ => hw p)))

theorem giant_weighted_mean_lower (d : Decomposition) (X : ℕ) (P : Finset ℕ)
    {δ : ℝ} (hδ : 0≤δ)
    (hP : ∀p∈P,p.Prime ∧ (1/3:ℝ)≤Supply.residueDensityTotal d p ∧
      Supply.residueDensityTotal d p≤(2/3:ℝ) ∧ δ≤Supply.residueGamma d p) :
    (δ/Real.sqrt 2)*(∑p∈P,Real.log p/(p:ℝ))-
      (∑p∈P,(Real.log p/(p:ℝ))*|giantEmpiricalMean d X p-giantSupportMean d p|)≤
      ∑p∈P,(Real.log p/(p:ℝ))*giantEmpiricalMean d X p := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hprime,hlo,hhi,hγ⟩ := hP p hp
  have hl := giantSupportMean_lower d hprime hδ hlo hhi hγ
  have ha := le_abs_self (giantSupportMean d p-giantEmpiricalMean d X p)
  rw [abs_sub_comm] at ha
  have hw : 0≤Real.log p/(p:ℝ) := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hm := mul_le_mul_of_nonneg_left (show δ/Real.sqrt 2-
    |giantEmpiricalMean d X p-giantSupportMean d p|≤giantEmpiricalMean d X p by linarith) hw
  nlinarith

end Ostmann.Construction

end

end OAI
