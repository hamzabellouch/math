import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RoughSupportGlobal

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

def primeBlockPacket (P Q : Finset ℕ) (f u : ℕ → ℂ) (D X : ℕ) (α : ℝ) : ℂ :=
  ∑p∈Q,f p*∑n∈range (X/p),
    (f (1+n)/((primeCount P (1+n):ℂ)+1))*smooth u D (p*(1+n))*
      phase (α*(p:ℝ)*(1+n))

def primeBlockBudget (P Q : Finset ℕ) (D X A K : ℕ) (κ : ℝ) : ℝ :=
  (((X/A:ℕ):ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card)*
    (((X/A:ℕ):ℝ)*Q.card+(Q.card:ℝ)^2*((2+4*((X/A:ℕ):ℝ)*K/D)/κ))

theorem prime_block_minor_arc (P Q : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X A K : ℕ) (hA : 0<A) (hN : 0<X/A) (α : ℝ)
    (hlo : ∀p∈Q,A≤p) (hhi : ∀p∈Q,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈Q,∀q∈Q,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖primeBlockPacket P Q f u D X α‖^2 ≤ primeBlockBudget P Q D X A K κ := by
  let N := X/A
  let w := fun n => f n/((primeCount P n:ℂ)+1)
  have ha := OrdinaryCofactorWeight.arithmetic_cofactor_second_moment P hP hN hL f hf
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hw : (∑n∈range N,‖w (1+n)‖^2)≤
      (N:ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card := by
    rw [sum_range_succ_eq_Icc N (fun n => ‖w n‖^2)]
    have hh := mul_le_mul_of_nonneg_left ha hNr.le
    simpa only [N,w,primeCount,←mul_assoc,mul_inv_cancel₀ hNr.ne',
      one_mul,mul_add,mul_div_cancel₀ _ hNr.ne'] using hh
  have hT (p : ℕ) (hp : p∈Q) : X/p≤N := Nat.div_le_div_left (hlo p hp) hA
  have hb := truncated_weighted_packet Q u w f hu hf (fun p => X/p)
    D 1 N K hT α hhi hκ hgap
  have hh : ‖primeBlockPacket P Q f u D X α‖^2 ≤ (∑n∈range N,‖w (1+n)‖^2)*
      ((N:ℝ)*Q.card+(Q.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
    simpa only [primeBlockPacket,w,Nat.cast_one] using hb
  exact hh.trans (mul_le_mul_of_nonneg_right hw (by positivity))

theorem global_packet_partition {ι : Type*} (S : Finset ι) (Q : ι → Finset ℕ)
    (P : Finset ℕ) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f u : ℕ → ℂ) (D X : ℕ) (α : ℝ) :
    globalPacket P f u D X α=∑i∈S,primeBlockPacket P (Q i) f u D X α := by
  let F := fun p => f p*∑n∈range (X/p),
    (f (1+n)/((primeCount P (1+n):ℂ)+1))*smooth u D (p*(1+n))*
      phase (α*(p:ℝ)*(1+n))
  change (∑p∈P,F p)=∑i∈S,∑p∈Q i,F p
  rw [hcov,sum_biUnion hdisj]

theorem global_packet_minor_arc_blocks {ι : Type*} (S : Finset ι) (Q : ι → Finset ℕ)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X : ℕ) (A K : ι → ℕ) (κ : ι → ℝ) (α : ℝ)
    (hA : ∀i∈S,0<A i) (hN : ∀i∈S,0<X/A i)
    (hlo : ∀i∈S,∀p∈Q i,A i≤p) (hhi : ∀i∈S,∀p∈Q i,p≤K i)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (hκ : ∀i∈S,0<κ i)
    (hgap : ∀i∈S,∀p∈Q i,∀q∈Q i,p≠q → κ i≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖globalPacket P f u D X α‖ ≤
      ∑i∈S,Real.sqrt (primeBlockBudget P (Q i) D X (A i) (K i) (κ i)) := by
  rw [global_packet_partition S Q P hcov hdisj f u D X α]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  exact Real.le_sqrt_of_sq_le (prime_block_minor_arc P (Q i) hP f u hf hu
    D X (A i) (K i) (hA i hi) (hN i hi) α (hlo i hi) (hhi i hi) hL
      (hκ i hi) (hgap i hi))

theorem actual_short_minor_arc_blocks {ι : Type*} (S : Finset ι) (Q : ι → Finset ℕ)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f : ℕ → ℂ) (hf : OneBounded f) (hm : Multiplicative f)
    (D U : ℕ) (hX : 0<U+D) (A K : ι → ℕ) (κ : ι → ℝ) (α : ℝ)
    (hA : ∀i∈S,0<A i) (hN : ∀i∈S,0<(U+D)/A i)
    (hlo : ∀i∈S,∀p∈Q i,A i≤p) (hhi : ∀i∈S,∀p∈Q i,p≤K i)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (hκ : ∀i∈S,0<κ i)
    (hgap : ∀i∈S,∀p∈Q i,∀q∈Q i,p≠q → κ i≤‖1-phase (α*((p:ℝ)-q))‖) :
    (D:ℝ)⁻¹*(∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖) ≤
      ((U+D:ℕ):ℝ)*Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card+
        (∑i∈S,Real.sqrt (primeBlockBudget P (Q i) D (U+D) (A i) (K i) (κ i)))+
        2*((U+D:ℕ):ℝ)*(∑p∈P,(p:ℝ)⁻¹^2)+P.card := by
  let u := actualDual (fun m => f m*phase (α*m)) D U
  let g := dualTwist f D U α
  have hg : OneBounded g := dualTwist_bound f D U α
  have hr := (norm_roughPart_le P f g 0 (U+D) hf hg).trans
    (by simpa only [zero_add] using rough_support_global P hP hX)
  have hb := global_packet_minor_arc_blocks S Q P hP hcov hdisj f u hf
    (actualDual_bound _ D U) D (U+D) A K κ α hA hN hlo hhi hL hκ hgap
  have he := global_coprime_error P hP f u hf (actualDual_bound _ D U) D (U+D) α
  have ht := norm_sub_le (globalPacket P f u D (U+D) α)
      (globalPacket P f u D (U+D) α-globalCoprimePacket P f u D (U+D) α)
  rw [sub_sub_cancel,global_coprime_is_bilinear] at ht
  rw [global_coprime_is_bilinear] at he
  have hbb : ‖bilinearPart P f g 0 (U+D)‖ ≤
      (∑i∈S,Real.sqrt (primeBlockBudget P (Q i) D (U+D) (A i) (K i) (κ i)))+
        ((U+D:ℕ):ℝ)*∑p∈P,(p:ℝ)⁻¹^2 := ht.trans (add_le_add hb he)
  have hd := norm_diagonalPart_le_reciprocal P hP f g 0 (U+D) hf hg
  have hei : (∑p∈P,1/(p:ℝ)^2)=∑p∈P,(p:ℝ)⁻¹^2 := by
    simp only [one_div,inv_pow]
  rw [hei] at hd
  rw [actual_short_prime_decomposition P hP f hm D U α]
  change ‖roughPart P f g 0 (U+D)+bilinearPart P f g 0 (U+D)+
    diagonalPart P f g 0 (U+D)‖≤_
  have hnorm := (norm_add_le (roughPart P f g 0 (U+D)+bilinearPart P f g 0 (U+D))
    (diagonalPart P f g 0 (U+D))).trans
      (add_le_add (norm_add_le (roughPart P f g 0 (U+D))
        (bilinearPart P f g 0 (U+D))) le_rfl)
  linarith

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
