import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MobiusInverse

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

lemma interval_width_sum {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A B : ι → ℕ) (U : ℕ)
    (hAB : ∀ i∈I, A i≤B i) (hBU : ∀ i∈I, B i≤U)
    (hd : (I : Set ι).PairwiseDisjoint (fun i => Finset.Ioc (A i) (B i))) :
    ∑ i∈I, ((B i:ℝ)-(A i:ℝ)) ≤ U := by
  have hc : (I.biUnion (fun i => Finset.Ioc (A i) (B i))).card ≤ (Finset.Icc 1 U).card := by
    apply Finset.card_le_card
    intro n hn
    obtain ⟨i,hi,hn⟩ := mem_biUnion.mp hn
    obtain ⟨ha,hb⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,hb.trans (hBU i hi)⟩
  rw [card_biUnion hd] at hc
  have hc' : ∑ i∈I, (B i-A i) ≤ U := by simpa only [Nat.card_Ioc, Nat.card_Icc, Nat.add_sub_cancel] using hc
  have he : ((∑ i∈I, (B i-A i):ℕ):ℝ) = ∑ i∈I, ((B i:ℝ)-(A i:ℝ)) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    exact Nat.cast_sub (R:=ℝ) (hAB i hi)
  rw [← he]
  exact_mod_cast hc'

lemma boundary_sum_bound {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A B : ι → ℕ) (N U z : ℕ) (G δ : ℝ)
    (hG : 0<G) (hδ : 0≤δ) (hAB : ∀ i∈I, A i≤B i)
    (hBU : ∀ i∈I, B i≤U)
    (hd : (I : Set ι).PairwiseDisjoint (fun i => Finset.Ioc (A i) (B i)))
    (hw : ∀ i∈I, ((B i:ℝ)-(A i:ℝ))^2/((A i:ℝ)*(B i:ℝ)) ≤ δ) :
    (∑ i∈I, ((B i:ℝ)-(A i:ℝ)) *
        ((3*(N:ℝ)*((B i:ℝ)-(A i:ℝ))/((A i:ℝ)*(B i:ℝ)) + 8) * G⁻¹ + 4*(z:ℝ)^4)) ≤
      3*(N:ℝ)*G⁻¹*(I.card:ℝ)*δ + (8*G⁻¹+4*(z:ℝ)^4)*U := by
  have he (i : ι) : ((B i:ℝ)-(A i:ℝ)) *
        ((3*(N:ℝ)*((B i:ℝ)-(A i:ℝ))/((A i:ℝ)*(B i:ℝ)) + 8) * G⁻¹ + 4*(z:ℝ)^4) =
      (3*(N:ℝ)*G⁻¹)*(((B i:ℝ)-(A i:ℝ))^2/((A i:ℝ)*(B i:ℝ))) +
      (8*G⁻¹+4*(z:ℝ)^4)*((B i:ℝ)-(A i:ℝ)) := by ring
  simp_rw [he]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hwSum : (∑ i∈I, ((B i:ℝ)-(A i:ℝ))^2/((A i:ℝ)*(B i:ℝ))) ≤ (I.card:ℝ)*δ := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum hw
  have hwidth := interval_width_sum I A B U hAB hBU hd
  have h1 := mul_le_mul hwSum (le_refl (3*(N:ℝ)*G⁻¹)) (by positivity)
    (mul_nonneg (Nat.cast_nonneg I.card) hδ)
  have h2 := mul_le_mul_of_nonneg_left hwidth (show 0≤8*G⁻¹+4*(z:ℝ)^4 by positivity)
  nlinarith

end OrdinarySmoothRough

end

end OAI
