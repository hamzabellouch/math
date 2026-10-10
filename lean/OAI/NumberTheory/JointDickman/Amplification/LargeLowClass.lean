import OAI.NumberTheory.JointDickman.Amplification.LargeLowAdditionAvailability
import OAI.NumberTheory.JointDickman.Amplification.LargeHighClass
import OAI.NumberTheory.JointDickman.Counting.LargeAdditionWindow

namespace OAI

/-! # Active low-addition classes at the actual coefficient ratio -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def activeLowAdditionClass (B L k : ℕ) (τ C Δ : ℝ)
    (A : Finset ℕ) (e j b d : ℕ) : Finset (Finset ℕ) :=
  if (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ))/4 ≤ highAdditionWindow e b then
    availableLowNumericAdditionClass B L k τ C A e j b d (highAdditionWindow e b)
  else ∅

theorem active_low_addition_class_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ τ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (C : ℝ) (A : Finset ℕ) (e j b d : ℕ),
        A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        tiltedRegularSubsetCount B L τ C A (activeLowAdditionClass B L k τ C Δ A e j b d) ≤
          K/(j : ℝ)*Real.exp
            (largeAvailabilityExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  obtain ⟨K,hK,hbound⟩ := large_low_addition_availability_bound hFord hM hk hkg hg hg1
    (by norm_num : (0 : ℝ) < 32/5) hΔ hgap hδ hδ1 hτ hτ1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,large_addition_window_lag (by linarith : 0 < g-Δ)] with B hB hwindow
  intro C A e j b d hA hAsize he hb hj hcut hej hesize hjB
  unfold activeLowAdditionClass
  split_ifs with hactive
  · have hbsize := hactive.1
    have hW := hactive.2
    rw [hkg] at hW
    have hsize : (e*b : ℕ) ≤ Real.exp ((32/5 : ℝ)*B) := by
      push_cast
      calc
        _ ≤ Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B) :=
          mul_le_mul hesize hbsize (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact hB C A e j b d (highAdditionWindow e b) hA hAsize he hb hj hcut hej hsize hjB
      (hwindow j _ hjB hW) hW
  · simp only [tiltedRegularSubsetCount,filter_empty,card_empty,Nat.cast_zero,ite_self,mul_zero,sum_const_zero]
    exact mul_nonneg (div_nonneg hK.le (Nat.cast_nonneg _)) (Real.exp_pos _).le

end JointDickman

end OAI
