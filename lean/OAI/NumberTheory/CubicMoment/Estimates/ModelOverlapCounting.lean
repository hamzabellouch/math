import OAI.NumberTheory.CubicMoment.Estimates.PrimeCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.CubeExclusions

namespace OAI

/-! Counting the shared-prime pairs discarded in the coprime cube model. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisible_row_card_le (S : Finset Eisenstein) {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ Y) (d : Eisenstein) (hd : d ≠ 0) :
    ((S.filter (fun b => d ∣ b)).card:ℝ) ≤ 18*Y/norm d := by
  have hdN := norm_pos_of_ne_zero hd
  have hs : S.filter (fun b => d ∣ b) ⊆ (nonzeroNormBall (Y/norm d)).image (fun b => d*b) := by
    intro b hb
    obtain ⟨hb,hdiv⟩ := Finset.mem_filter.mp hb
    obtain ⟨k,rfl⟩ := hdiv
    have hk : k ≠ 0 := fun hk => (hS (d*k) hb).1 (by rw [hk,mul_zero])
    have hn : norm k ≤ Y/norm d := by
      apply (le_div_iff₀ hdN).mpr
      simpa only [norm_mul_eq,mul_comm] using (hS (d*k) hb).2
    exact Finset.mem_image.mpr ⟨k,mem_nonzeroNormBall.mpr ⟨hn,hk⟩,rfl⟩
  calc
    _ ≤ ((nonzeroNormBall (Y/norm d)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hs).trans Finset.card_image_le
    _ ≤ 18*(Y/norm d) := nonzeroNormBall_card_le (by positivity)
    _ = _ := by ring

lemma noncoprime_row_card_le (S : Finset Eisenstein) {Y D : ℝ}
    (hY : 0 ≤ Y) (hD : 0 < D) (hS : ∀ b ∈ S, b ≠ 0 ∧ norm b ≤ Y)
    {a : Eisenstein} (ha : primary a) (hsa : Squarefree a)
    (hrough : ∀ p ∈ primaryPrimeFactors a, D ≤ norm p) :
    ((S.filter (fun b => ¬IsCoprime a b)).card:ℝ) ≤
      (primaryPrimeFactors a).card*(18*Y/D) := by
  have hs : S.filter (fun b => ¬IsCoprime a b) ⊆
      (primaryPrimeFactors a).biUnion (fun p => S.filter (fun b => p ∣ b)) := by
    intro b hb
    obtain ⟨hb,hcop⟩ := Finset.mem_filter.mp hb
    obtain ⟨p,hp,hpb⟩ := not_coprime_prime_cover ha hsa hcop
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hb,hpb⟩⟩
  calc
    _ ≤ ∑ p ∈ primaryPrimeFactors a, ((S.filter (fun b => p ∣ b)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
    _ ≤ ∑ _p ∈ primaryPrimeFactors a, 18*Y/D := by
      apply Finset.sum_le_sum
      intro p hp
      exact (divisible_row_card_le S hY hS p (primaryPrimeFactor_spec ha hp).1.2.ne_zero).trans
        (div_le_div_of_nonneg_left (by positivity) hD (hrough p hp))
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
