import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeDivisorMoment
import OAI.NumberTheory.CubicMoment.Estimates.PrimeNormFibers
import OAI.NumberTheory.CubicMoment.Estimates.PolynomialMeanValue

namespace OAI

/-! Squarefree norm fibers have a divisor weight attached to each actual
member. Summing this weight retains logarithmic rather than small-power loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_primeFactors_norm_subset {b c : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) (hc : primary c)
    (hn : normNat c = normNat b) :
    primaryPrimeFactors c ⊆ primaryPrimeFactors b ∪ (primaryPrimeFactors b).image conjugate := by
  intro p hp
  have hpc := primaryPrimeFactor_spec hc hp
  have he : c*conjugate c = b*conjugate b := by
    rw [←normNat_cast_eq_mul_conjugate,←normNat_cast_eq_mul_conjugate,hn]
  have hd : p ∣ b*conjugate b := he ▸ dvd_mul_of_dvd_left hpc.2 _
  rcases hpc.1.2.dvd_or_dvd hd with hd | hd
  · have hprod := primaryPrimeFactors_prod hb hsb
    rw [←hprod] at hd
    obtain ⟨q,hq,hpq⟩ := (hpc.1.2.dvd_finsetProd_iff (fun q : Eisenstein => q)).mp hd
    have hqprime := (primaryPrimeFactor_spec hb hq).1
    have heq := primary_associated_eq hpc.1.1 hqprime.1
      ((hpc.1.2.dvd_prime_iff_associated hqprime.2).mp hpq)
    exact Finset.mem_union_left _ (heq ▸ hq)
  · rw [←primaryPrimeFactors_prod hb hsb,map_prod] at hd
    obtain ⟨q,hq,hpq⟩ := (hpc.1.2.dvd_finsetProd_iff conjugate).mp hd
    have hqprime := primaryPrime_conjugate (primaryPrimeFactor_spec hb hq).1
    have heq := primary_associated_eq hpc.1.1 hqprime.1
      ((hpc.1.2.dvd_prime_iff_associated hqprime.2).mp hpq)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,hq,heq.symm⟩)

lemma squarefree_norm_fiber_card (S : Finset Eisenstein)
    (hS : ∀ c ∈ S, primary c ∧ Squarefree c) {b : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) :
    (S.filter (fun c => normNat c = normNat b)).card ≤
      4^(primaryPrimeFactors b).card := by
  let U := primaryPrimeFactors b ∪ (primaryPrimeFactors b).image conjugate
  have hcard : (S.filter (fun c => normNat c = normNat b)).card ≤ U.powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro c hc
      apply Finset.mem_powerset.mpr
      exact squarefree_primeFactors_norm_subset hb hsb (hS c (Finset.mem_filter.mp hc).1).1
        (Finset.mem_filter.mp hc).2
    · intro c hc d hd he
      calc
        c = ∏ p ∈ primaryPrimeFactors c, p :=
          (primaryPrimeFactors_prod (hS c (Finset.mem_filter.mp hc).1).1
            (hS c (Finset.mem_filter.mp hc).1).2).symm
        _ = ∏ p ∈ primaryPrimeFactors d, p := by rw [he]
        _ = d := primaryPrimeFactors_prod (hS d (Finset.mem_filter.mp hd).1).1
          (hS d (Finset.mem_filter.mp hd).1).2
  have hU : U.card ≤ 2*(primaryPrimeFactors b).card := by
    exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add_left Finset.card_image_le _).trans_eq (by omega))
  calc
    _ ≤ 2^U.card := by simpa only [Finset.card_powerset] using hcard
    _ ≤ 2^(2*(primaryPrimeFactors b).card) := Nat.pow_le_pow_right (by decide) hU
    _ = _ := by rw [pow_mul]; norm_num

lemma normCollectedCoeff_squarefree_energy (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (v : Eisenstein → ℂ)
    {M : ℝ} (_hM : 0 ≤ M) (hv : ∀ b ∈ S, ‖v b‖ ≤ M) (Z : ℕ)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    (∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff S v n‖^2) ≤
      M^2*∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card := by
  have hf (n : ℕ) : ‖normCollectedCoeff S v n‖^2 ≤
      ∑ b ∈ S.filter (fun b => normNat b = n), M^2*(4:ℝ)^(primaryPrimeFactors b).card := by
    apply (norm_sum_sq_le_card_mul _ v).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hbs := (Finset.mem_filter.mp hb).1
    have he : S.filter (fun c => normNat c = n) = S.filter (fun c => normNat c = normNat b) := by
      rw [(Finset.mem_filter.mp hb).2]
    have hcard : ((S.filter (fun c => normNat c = n)).card:ℝ) ≤
        (4:ℝ)^(primaryPrimeFactors b).card := by
      rw [he]
      exact_mod_cast squarefree_norm_fiber_card S hS (hS b hbs).1 (hS b hbs).2
    exact (mul_le_mul hcard (pow_le_pow_left₀ (_root_.norm_nonneg _) (hv b hbs) 2)
      (sq_nonneg _) (by positivity)).trans_eq (by ring)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Z, ∑ b ∈ S.filter (fun b => normNat b = n),
        M^2*(4:ℝ)^(primaryPrimeFactors b).card := Finset.sum_le_sum (fun n _ => hf n)
    _ = _ := by rw [Finset.sum_fiberwise_of_maps_to hZ,Finset.mul_sum]

end CubicFirstMoment

end

end OAI
