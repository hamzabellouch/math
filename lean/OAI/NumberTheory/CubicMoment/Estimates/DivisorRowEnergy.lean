import OAI.NumberTheory.CubicMoment.Estimates.IdealDivisorPower
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! The total energy of all rows in the genuine coprimality expansion.
Every coefficient occurs once per squarefree primary divisor, so the
loss is bounded by an arbitrarily small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_subset_divisor_count (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {a : Eisenstein} (ha : primary a) :
    (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card ≤
      2^(primaryPrimeFactors a).card := by
  rw [← Finset.card_powerset]
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsU,hd⟩ := Finset.mem_filter.mp hs
  apply Finset.mem_powerset.mpr
  intro p hp
  apply (primaryPrime_mem_factors_iff ha).mpr
  exact ⟨hU p (Finset.mem_powerset.mp hsU hp),
    dvd_trans (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) hd⟩

theorem divisor_row_energy_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S U : Finset Eisenstein) (β : Eisenstein → ℂ) (N : ℝ),
      (∀ p ∈ U, primaryPrime p) →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖β a‖^2) ≤
        C*N^ε*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := primary_divisor_card_small_power hε
  refine ⟨C,hC,?_⟩
  intro S U β N hU hS
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hcount : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card : ℝ) ≤ C*N^ε := by
    let P := U.powerset.image (fun d => ∏ p ∈ d, p)
    have hP : ∀ d ∈ P, primary d := by
      intro d hd
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hd
      exact primary_finset_prod s (fun p : Eisenstein => p)
        (fun p hp => (hU p (Finset.mem_powerset.mp hs hp)).1)
    have hc : (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card ≤
        (P.filter (fun d => d ∣ a)).card := by
      apply Finset.card_le_card_of_injOn (fun d : Finset Eisenstein => ∏ p ∈ d, p)
      · intro d hd
        obtain ⟨hd,hda⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d,hd,rfl⟩,hda⟩
      · intro d hd e he hde
        exact primaryPrimeFactors_prod_injective hU
          (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp he).1 hde
    have hc' : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card : ℝ) ≤
        ((P.filter (fun d => d ∣ a)).card : ℝ) := by exact_mod_cast hc
    exact hc'.trans ((hdiv P hP a (primary_ne_zero (hS a ha).1)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg a) (hS a ha).2.2 hε.le) hC.le))
  calc
    _ = ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card : ℝ)*‖β a‖^2 := by
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)

end CubicFirstMoment

end

end OAI
