import OAI.NumberTheory.CubicMoment.Estimates.SmallBStoppedAlphaEnergy

namespace OAI

/-! The squarefree product coefficient of the literal stopped sides.
Its divisor bound is proved before collecting equal norms. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_pair_coefficient_bound (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hP : ∀ a ∈ P, primary a)
    (hα : ∀ a ∈ P, Squarefree a → ‖α a‖ ≤ L*(2:ℝ)^(primaryPrimeFactors a).card)
    (hβ : ∀ b ∈ B, ‖β b‖ ≤ M)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ‖primaryPairCoefficient P B (fun p => α p.1*β p.2) n‖ ≤
      (L*M)*(4:ℝ)^(primaryPrimeFactors n).card := by
  have hf : ∀ p ∈ primaryPairFiber P B n,
      ‖α p.1*β p.2‖ ≤ (L*M)*(2:ℝ)^(primaryPrimeFactors n).card := by
    intro p hp
    have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have he := (Finset.mem_filter.mp hp).2
    have hd : p.1 ∣ n := ⟨p.2,he.symm⟩
    have hsf : Squarefree p.1 := fun x hx => hs x (hx.trans hd)
    have hcard := Finset.card_le_card
      (primaryPrimeFactors_subset_of_dvd (hP p.1 hmem.1) hn hd)
    have ha : ‖α p.1‖ ≤ L*(2:ℝ)^(primaryPrimeFactors n).card :=
      (hα p.1 hmem.1 hsf).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hcard) hL)
    rw [norm_mul]
    calc
      _ ≤ (L*(2:ℝ)^(primaryPrimeFactors n).card)*M :=
        mul_le_mul ha (hβ p.2 hmem.2) (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hb := primaryPairCoefficient_norm_le P B hP n _
    (show 0 ≤ (L*M)*(2:ℝ)^(primaryPrimeFactors n).card by positivity) hf
  have hc : ((P.filter (fun a => a ∣ n)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors n).card := by
    exact_mod_cast primary_squarefree_divisor_card P hP hn hs
  apply hb.trans
  calc
    _ ≤ (2:ℝ)^(primaryPrimeFactors n).card*((L*M)*(2:ℝ)^(primaryPrimeFactors n).card) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (L*M)*((2:ℝ)^(primaryPrimeFactors n).card)^2 := by ring
    _ = _ := by
      rw [←pow_mul, Nat.mul_comm, pow_mul]
      norm_num

lemma stopped_pair_coefficient_bound (E U P B : Finset Eisenstein)
    (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
    (β : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hE : ∀ e ∈ E, primary e) (hP : ∀ a ∈ P, primary a)
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (hβ : ∀ b ∈ B, ‖β b‖ ≤ M)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ‖primaryPairCoefficient P B
      (fun p => stoppedAlpha E U ψ w remaining p.1*β p.2) n‖ ≤
      M*(4:ℝ)^(primaryPrimeFactors n).card := by
  apply (squarefree_pair_coefficient_bound P B _ β zero_le_one hM hP
    (fun a ha hsf => ?_) hβ hn hs).trans_eq (by rw [one_mul])
  simpa only [one_mul] using (stoppedAlpha_divisor_bound E U hE hψ w remaining a).trans
    (show ((E.filter (fun e => e ∣ a)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors a).card by
        exact_mod_cast primary_squarefree_divisor_card E hE (hP a ha) hsf)

/-- The true squarefree product support, without a coprimality replacement. -/
def squarefreePairSupport (P B : Finset Eisenstein) : Finset Eisenstein :=
  (primaryPairSupport P B).filter Squarefree

lemma squarefreePairSupport_primary (P B : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) (hB : ∀ b ∈ B, primary b)
    {n : Eisenstein} (hn : n ∈ squarefreePairSupport P B) :
    primary n ∧ Squarefree n := by
  obtain ⟨hn,hns⟩ := Finset.mem_filter.mp hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hm := Finset.mem_product.mp hp
  exact ⟨primary_mul (hP p.1 hm.1) (hB p.2 hm.2),hns⟩

lemma squarefree_pair_sum (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (F : Eisenstein → ℂ) :
    (∑ n ∈ squarefreePairSupport P B,
      primaryPairCoefficient P B (fun p => α p.1*β p.2) n*F n) =
    ∑ a ∈ P, ∑ b ∈ B, if Squarefree (a*b) then α a*β b*F (a*b) else 0 := by
  calc
    _ = ∑ n ∈ primaryPairSupport P B,
        primaryPairCoefficient P B (fun p => α p.1*β p.2) n*
          (if Squarefree n then F n else 0) := by
      rw [squarefreePairSupport,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ p ∈ P ×ˢ B, α p.1*β p.2*
        (if Squarefree (p.1*p.2) then F (p.1*p.2) else 0) :=
      primaryPairCoefficient_sum P B _ _
    _ = _ := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp

end CubicFirstMoment

end

end OAI
