import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DualSmoothZeroLeft
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GlobalPacket

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryCorrelations.SourcePrimeFactor
open OrdinaryAdditiveBilinear OrdinaryShortDual Finset

theorem rough_support_global (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    {X : ℕ} (hX : 0<X) :
    (((Finset.Ioc 0 X).filter (fun n => primeCount P n=0)).card:ℝ) ≤
      (X:ℝ)*Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card := by
  have hic : Finset.Icc 1 X=Finset.Ioc 0 X := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hz (n : ℕ) : (0:ℝ)^OrdinaryCofactorWeight.count
      (OrdinaryCofactorWeight.primeBits P n)=if primeCount P n=0 then 1 else 0 := by
    rw [OrdinaryCofactorWeight.count_primeBits]
    change (0:ℝ)^primeCount P n=_
    split_ifs with h
    · simp [h]
    · exact zero_pow h
  have hi : OrdinaryCofactorWeight.arithmeticGenerating P X 0=
      (X:ℝ)⁻¹*(((Finset.Ioc 0 X).filter (fun n => primeCount P n=0)).card:ℝ) := by
    simp only [OrdinaryCofactorWeight.arithmeticGenerating,←mul_sum,hz,hic]
    congr 1
    rw [←sum_filter]
    simp
  have hh := OrdinaryCofactorWeight.arithmetic_generating_upper P hP hX
    (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by constructor <;> norm_num)
  rw [hi] at hh
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hm := mul_le_mul_of_nonneg_left hh hXr.le
  simpa only [sub_zero,neg_mul,one_mul,mul_add,←mul_assoc,mul_inv_cancel₀ hXr.ne',
    one_mul,mul_div_cancel₀ _ hXr.ne'] using hm

theorem actual_bilinear_minor_arc (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X A K : ℕ) (hA : 0<A) (hN : 0<X/A) (α : ℝ)
    (hlo : ∀p∈P,A≤p) (hhi : ∀p∈P,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖bilinearPart P f (fun m => smooth u D m*phase (α*m)) 0 X‖ ≤
      Real.sqrt (additiveBudget P D X A K κ)+(X:ℝ)*∑p∈P,(p:ℝ)⁻¹^2 := by
  rw [←global_coprime_is_bilinear]
  have hb := Real.le_sqrt_of_sq_le (global_packet_minor_arc P hP f u hf hu
    D X A K hA hN α hlo hhi hL hκ hgap)
  have he := global_coprime_error P hP f u hf hu D X α
  calc
    _ ≤ ‖globalPacket P f u D X α‖+
        ‖globalPacket P f u D X α-globalCoprimePacket P f u D X α‖ := by
      have hh := norm_sub_le (globalPacket P f u D X α)
        (globalPacket P f u D X α-globalCoprimePacket P f u D X α)
      simpa only [sub_sub_cancel] using hh
    _ ≤ _ := add_le_add hb he

theorem actual_short_minor_arc (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f : ℕ → ℂ) (hf : OneBounded f) (hm : Multiplicative f)
    (D U A K : ℕ) (hA : 0<A) (hN : 0<(U+D)/A) (α : ℝ)
    (hlo : ∀p∈P,A≤p) (hhi : ∀p∈P,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    (D:ℝ)⁻¹*(∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖) ≤
      ((U+D:ℕ):ℝ)*Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card+
        Real.sqrt (additiveBudget P D (U+D) A K κ)+
        2*((U+D:ℕ):ℝ)*(∑p∈P,(p:ℝ)⁻¹^2)+P.card := by
  let u := actualDual (fun m => f m*phase (α*m)) D U
  let g := dualTwist f D U α
  have hg : OneBounded g := dualTwist_bound f D U α
  have hX : 0<U+D := lt_of_lt_of_le hN (Nat.div_le_self _ _)
  have hr := (norm_roughPart_le P f g 0 (U+D) hf hg).trans
    (by simpa only [zero_add] using rough_support_global P hP hX)
  have hb : ‖bilinearPart P f g 0 (U+D)‖ ≤
      Real.sqrt (additiveBudget P D (U+D) A K κ)+
        ((U+D:ℕ):ℝ)*∑p∈P,(p:ℝ)⁻¹^2 := by
    exact actual_bilinear_minor_arc P hP f u hf (actualDual_bound _ D U)
      D (U+D) A K hA hN α hlo hhi hL hκ hgap
  have hd := norm_diagonalPart_le_reciprocal P hP f g 0 (U+D) hf hg
  have he : (∑p∈P,1/(p:ℝ)^2)=∑p∈P,(p:ℝ)⁻¹^2 := by
    simp only [one_div,inv_pow]
  rw [he] at hd
  rw [actual_short_prime_decomposition P hP f hm D U α]
  change ‖roughPart P f g 0 (U+D)+bilinearPart P f g 0 (U+D)+
    diagonalPart P f g 0 (U+D)‖≤_
  have ht := (norm_add_le (roughPart P f g 0 (U+D)+bilinearPart P f g 0 (U+D))
    (diagonalPart P f g 0 (U+D))).trans
      (add_le_add (norm_add_le (roughPart P f g 0 (U+D))
        (bilinearPart P f g 0 (U+D))) le_rfl)
  linarith

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
