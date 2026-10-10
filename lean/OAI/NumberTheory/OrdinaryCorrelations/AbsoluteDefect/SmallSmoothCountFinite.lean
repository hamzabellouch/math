import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothPart
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NatDivRealError

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

lemma small_smooth_count_finite (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N A : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => smoothPart S n ≤ A)).card ≤
      ∑ a ∈ Icc 1 A, ((Finset.Icc 1 (N/a)).filter (fun b => b.Coprime (∏ p ∈ S, p))).card := by
  let B : Finset (Σ _ : ℕ, ℕ) := (Finset.Icc 1 A).sigma
    (fun a => (Finset.Icc 1 (N/a)).filter (fun b => b.Coprime (∏ p ∈ S, p)))
  have hc : ((Finset.Icc 1 N).filter (fun n => smoothPart S n ≤ A)).card ≤ B.card := by
    apply card_le_card_of_injOn (fun n => (⟨smoothPart S n, roughPart S n⟩ : Σ _ : ℕ, ℕ))
    · intro n hn
      obtain ⟨hnI, hnA⟩ := mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
      have hp := parts_pos S (by omega : 0<n)
      have he := parts_mul S (by omega : n≠0)
      apply mem_sigma.mpr
      refine ⟨mem_Icc.mpr ⟨hp.1, hnA⟩, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.2, ?_⟩,
        roughPart_coprime_product S n hS⟩⟩
      apply (Nat.le_div_iff_mul_le hp.1).mpr
      rw [Nat.mul_comm, he]
      exact hnN
    · intro n hn m hm he
      have he1 := congrArg Sigma.fst he
      have he2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) he
      change smoothPart S n = smoothPart S m at he1
      change roughPart S n = roughPart S m at he2
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hn).1).1; omega
      have hm0 : m ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hm).1).1; omega
      calc
        n = smoothPart S n * roughPart S n := (parts_mul S hn0).symm
        _ = smoothPart S m * roughPart S m := by rw [he1,he2]
        _ = m := parts_mul S hm0
  simpa only [B, Finset.card_sigma] using hc

theorem small_smooth_count (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (N A z : ℕ) (hP : Squarefree (∏ p ∈ S, p)) (hz : 1 ≤ z) :
    (((Finset.Icc 1 N).filter (fun n => smoothPart S n ≤ A)).card:ℝ) ≤
      (N:ℝ)*(actualMass (∏ p ∈ S, p) z hP)⁻¹ * (1+Real.log A) + (A:ℝ)*(z:ℝ)^4 := by
  let P := ∏ p ∈ S, p
  have hM : 0 < actualMass P z hP := mass_pos _ hz
  have hc : (((Finset.Icc 1 N).filter (fun n => smoothPart S n ≤ A)).card:ℝ) ≤
      ∑ a ∈ Icc 1 A, (((Finset.Icc 1 (N/a)).filter (fun b => b.Coprime P)).card:ℝ) := by
    exact_mod_cast small_smooth_count_finite S hS N A
  apply hc.trans
  calc
    _ ≤ ∑ a ∈ Icc 1 A, ((N:ℝ)/(a:ℝ)*(actualMass P z hP)⁻¹ + (z:ℝ)^4) := by
      apply sum_le_sum
      intro a ha
      apply (rough_count_bound P z (N/a) hP hz).trans
      apply _root_.add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hM.le)
      have ha0 : (0:ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
      apply (le_div_iff₀ ha0).mpr
      exact_mod_cast Nat.div_mul_le_self N a
    _ = (N:ℝ)*(actualMass P z hP)⁻¹*(∑ a ∈ Icc 1 A, (a:ℝ)⁻¹) + (A:ℝ)*(z:ℝ)^4 := by
      rw [sum_add_distrib]
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      ring
    _ ≤ _ := by
      apply _root_.add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg N) (inv_nonneg.mpr hM.le))
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
        harmonic_le_one_add_log A

end OrdinarySmoothRough

end

end OAI
