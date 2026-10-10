import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CutRectangle

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothRough
open Finset OrdinarySelbergWeights

def capUpper (N A B : ℕ) : ℕ := min (2*N/B) (4*(N/(2*A)))

lemma quarter_floor_comparison (N A : ℕ) (hA : 0<A) :
    2*N/A ≤ 4*(N/(2*A))+4 := by
  have hN := Nat.lt_mul_div_succ N (show 0<2*A by omega)
  have hdiv := Nat.div_mul_le_self (2*N) A
  nlinarith

lemma capUpper_error (N A B : ℕ) (hA : 0<A) (hAB : A≤B) :
    2*N/B ≤ capUpper N A B + 4 := by
  have h1 := quarter_floor_comparison N A hA
  have h2 := Nat.div_le_div_left (a:=2*N) hAB hA
  unfold capUpper
  omega

lemma floor_boundary_width (N A B : ℕ) (hA : 0<A) (hAB : A≤B) :
    (((N/A:ℕ):ℝ)-((N/B:ℕ):ℝ)) +
      (((2*N/A:ℕ):ℝ)-(capUpper N A B:ℝ)) ≤
      3*(N:ℝ)*((B:ℝ)-(A:ℝ))/((A:ℝ)*(B:ℝ)) + 8 := by
  have hAr : (0:ℝ)<A := by exact_mod_cast hA
  have hBr : (0:ℝ)<B := by exact_mod_cast hA.trans_le hAB
  have h1 := nat_div_real_error N A hA
  have h2 := nat_div_real_error N B (hA.trans_le hAB)
  have h3 := nat_div_real_error (2*N) A hA
  have h4 := nat_div_real_error (2*N) B (hA.trans_le hAB)
  have hc : ((2*N/B:ℕ):ℝ) ≤ (capUpper N A B:ℝ)+4 := by
    exact_mod_cast capUpper_error N A B hA hAB
  have he : (N:ℝ)/A-(N:ℝ)/B + (2*(N:ℝ))/A-(2*(N:ℝ))/B =
      3*(N:ℝ)*((B:ℝ)-(A:ℝ))/((A:ℝ)*(B:ℝ)) := by
    field_simp
    ring
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have h4' := abs_le.mp h4
  push_cast at h3' h4'
  linarith

lemma capped_rough_scale (S : Finset ℕ) (N A B : ℕ) (hA : 0<A) :
    roughBlock S (N/A) (capUpper N A B) ⊆
      Icc (2*(N/(2*A))) (4*(N/(2*A))) := by
  intro b hb
  obtain ⟨hbI,hcop⟩ := mem_filter.mp hb
  obtain ⟨hL,hU⟩ := mem_Ioc.mp hbI
  have hlo : 2*(N/(2*A)) ≤ N/A := by
    apply (Nat.le_div_iff_mul_le hA).mpr
    have hh := Nat.div_mul_le_self N (2*A)
    nlinarith
  exact mem_Icc.mpr ⟨by omega, hU.trans (min_le_right _ _)⟩

theorem capped_slice_defect_sieve (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N A B z : ℕ) (hA : 0<A) (hAB : A≤B) (hz : 1≤z)
    (hprime : Squarefree (∏ p ∈ S, p)) :
    (((smoothSlice S N A B) \ (cutRectangle S N A B (capUpper N A B))).card:ℝ) ≤
      ((B:ℝ)-(A:ℝ)) *
        ((3*(N:ℝ)*((B:ℝ)-(A:ℝ))/((A:ℝ)*(B:ℝ)) + 8) *
          (actualMass (∏ p ∈ S, p) z hprime)⁻¹ + 4*(z:ℝ)^4) := by
  have hc := slice_defect_card_cut S hS N A B (capUpper N A B) hA hAB
  have hc' : (((smoothSlice S N A B) \ (cutRectangle S N A B (capUpper N A B))).card:ℝ) ≤
      ((B:ℝ)-(A:ℝ)) * (((roughBlock S (N/B) (N/A)).card:ℝ) +
        ((roughBlock S (capUpper N A B) (2*N/A)).card:ℝ)) := by
    rw [← Nat.cast_sub hAB]
    exact_mod_cast hc
  have h1 := rough_interval_count (∏ p ∈ S, p) z (N/B) (N/A) hprime hz
    (Nat.div_le_div_left hAB hA)
  have h2 := rough_interval_count (∏ p ∈ S, p) z (capUpper N A B) (2*N/A) hprime hz
    ((min_le_left _ _).trans (Nat.div_le_div_left hAB hA))
  have hw := floor_boundary_width N A B hA hAB
  have hMass : 0 ≤ (actualMass (∏ p ∈ S, p) z hprime)⁻¹ :=
    inv_nonneg.mpr (mass_pos _ hz).le
  have habr : (0:ℝ) ≤ (B:ℝ)-(A:ℝ) := sub_nonneg.mpr (by exact_mod_cast hAB)
  apply hc'.trans
  apply mul_le_mul_of_nonneg_left _ habr
  change _ ≤ _ at h1 h2
  unfold roughBlock
  nlinarith [mul_le_mul_of_nonneg_right hw hMass]

end OrdinarySmoothRough

end

end OAI
