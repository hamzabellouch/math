import OAI.NumberTheory.CubicMoment.Estimates.NormCoprimeWindow
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDivisorSubsets

namespace OAI

/-! The coarse Mellin envelope costs only the bounded number of prime
factors in a coefficient, not the size of the ambient set of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisor_subset_l1_square (S U : Finset Eisenstein) (w : Eisenstein → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (D : ℕ)
    (hD : ∀ a ∈ S, (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card ≤ D) :
    (∑ s ∈ U.powerset, (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a)^2) ≤
      (D:ℝ)*(∑ a ∈ S, w a)^2 := by
  let W := ∑ a ∈ S, w a
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hsub (s : Finset Eisenstein) :
      0 ≤ ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a :=
    Finset.sum_nonneg (fun a ha => hw a (Finset.mem_filter.mp ha).1)
  have hle (s : Finset Eisenstein) :
      (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a) ≤ W :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a ha _ => hw a ha)
  have hsum : (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a) ≤ (D:ℝ)*W := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hD a ha)) (hw a ha)
  calc
    _ ≤ ∑ s ∈ U.powerset, W*(∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hle s) (hsub s)
    _ = W*(∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ W*((D:ℝ)*W) := mul_le_mul_of_nonneg_left hsum hW
    _ = _ := by dsimp [W]; ring

theorem coprimeMellinEnvelope_of_divisor_count (S H U : Finset Eisenstein)
    (v w : Eisenstein → ℂ) (D : ℕ)
    (hD : ∀ a ∈ S, (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card ≤ D) :
    coprimeMellinEnvelope S H U v w ≤
      (H.card:ℝ)*(D:ℝ)*((∑ a ∈ S, ‖v a‖)^2+(∑ a ∈ S, ‖w a‖)^2)/2 := by
  have hv := divisor_subset_l1_square S U (fun a => ‖v a‖) (fun _ _ => _root_.norm_nonneg _) D hD
  have hw := divisor_subset_l1_square S U (fun a => ‖w a‖) (fun _ _ => _root_.norm_nonneg _) D hD
  have he : coprimeMellinEnvelope S H U v w = (H.card:ℝ)/2*
      ((∑ s ∈ U.powerset, (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖)^2)+
       (∑ s ∈ U.powerset, (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖)^2)) := by
    unfold coprimeMellinEnvelope
    rw [mul_add,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [he]
  calc
    _ ≤ (H.card:ℝ)/2*((D:ℝ)*(∑ a ∈ S, ‖v a‖)^2+(D:ℝ)*(∑ a ∈ S, ‖w a‖)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hv hw) (by positivity)
    _ = _ := by ring

theorem fullPrime_coprimeMellinEnvelope {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (v w : Eisenstein → ℂ) :
    coprimeMellinEnvelope (fullSquarefreePrimeSupport R W X e) H U v w ≤
      (H.card:ℝ)*(2^(Fintype.card ι):ℝ)*
        ((∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖v a‖)^2+
         (∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖w a‖)^2)/2 := by
  have h := coprimeMellinEnvelope_of_divisor_count (fullSquarefreePrimeSupport R W X e) H U v w
    (2^Fintype.card ι) (fun a ha => fullPrime_divisor_subsets_card R W X e U hU ha)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

end CubicFirstMoment

end

end OAI
