import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeBlockPacket
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseSubInt

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

def rationalPrimeBlockBudget (P Q : Finset ℕ) (D X A K q : ℕ) : ℝ :=
  (((X/A:ℕ):ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card)*
    (((X/A:ℕ):ℝ)*Q.card*(K/q+1:ℕ)+(Q.card:ℝ)^2*(q:ℝ)*(2+4*((X/A:ℕ):ℝ)*K/D))

theorem prime_block_near_rational (P Q : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X A K : ℕ) (hA : 0<A) (hN : 0<X/A) (hK : 0<K) (α : ℝ)
    (a : ℤ) (q : ℕ) (hq : 0<q) (haq : Int.gcd a q=1)
    (hlo : ∀p∈Q,A≤p) (hhi : ∀p∈Q,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹)
    (hα : |α-(a:ℝ)/q|≤1/(2*(q:ℝ)*K)) :
    ‖primeBlockPacket P Q f u D X α‖^2 ≤ rationalPrimeBlockBudget P Q D X A K q := by
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
  have hb := near_rational_weighted_packet Q u w f hu hf (fun p => X/p)
    D 1 N K hK hT α a q hq haq hhi hα
  have hh : ‖primeBlockPacket P Q f u D X α‖^2 ≤ (∑n∈range N,‖w (1+n)‖^2)*
      ((N:ℝ)*Q.card*(K/q+1:ℕ)+(Q.card:ℝ)^2*(q:ℝ)*(2+4*(N:ℝ)*K/D)) := by
    simpa only [primeBlockPacket,w,Nat.cast_one] using hb
  exact hh.trans (mul_le_mul_of_nonneg_right hw (by positivity))

theorem global_packet_near_rational_blocks {ι : Type*} (S : Finset ι) (Q : ι → Finset ℕ)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X : ℕ) (A K : ι → ℕ) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0<q) (haq : Int.gcd a q=1)
    (hA : ∀i∈S,0<A i) (hN : ∀i∈S,0<X/A i)
    (hlo : ∀i∈S,∀p∈Q i,A i≤p) (hhi : ∀i∈S,∀p∈Q i,p≤K i)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (hK : ∀i∈S,0<K i)
    (hα : ∀i∈S,|α-(a:ℝ)/q|≤1/(2*(q:ℝ)*K i)) :
    ‖globalPacket P f u D X α‖ ≤
      ∑i∈S,Real.sqrt (rationalPrimeBlockBudget P (Q i) D X (A i) (K i) q) := by
  rw [global_packet_partition S Q P hcov hdisj f u D X α]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  exact Real.le_sqrt_of_sq_le (prime_block_near_rational P (Q i) hP f u hf hu
    D X (A i) (K i) (hA i hi) (hN i hi) (hK i hi) α a q hq haq (hlo i hi) (hhi i hi) hL
      (hα i hi))

theorem actual_short_near_rational_blocks {ι : Type*} (S : Finset ι) (Q : ι → Finset ℕ)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f : ℕ → ℂ) (hf : OneBounded f) (hm : Multiplicative f)
    (D U : ℕ) (hX : 0<U+D) (A K : ι → ℕ) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0<q) (haq : Int.gcd a q=1)
    (hA : ∀i∈S,0<A i) (hN : ∀i∈S,0<(U+D)/A i)
    (hlo : ∀i∈S,∀p∈Q i,A i≤p) (hhi : ∀i∈S,∀p∈Q i,p≤K i)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (hK : ∀i∈S,0<K i)
    (hα : ∀i∈S,|α-(a:ℝ)/q|≤1/(2*(q:ℝ)*K i)) :
    (D:ℝ)⁻¹*(∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖) ≤
      ((U+D:ℕ):ℝ)*Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card+
        (∑i∈S,Real.sqrt (rationalPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) q))+
        2*((U+D:ℕ):ℝ)*(∑p∈P,(p:ℝ)⁻¹^2)+P.card := by
  let u := actualDual (fun m => f m*phase (α*m)) D U
  let g := dualTwist f D U α
  have hg : OneBounded g := dualTwist_bound f D U α
  have hr := (norm_roughPart_le P f g 0 (U+D) hf hg).trans
    (by simpa only [zero_add] using rough_support_global P hP hX)
  have hb := global_packet_near_rational_blocks S Q P hP hcov hdisj f u hf
    (actualDual_bound _ D U) D (U+D) A K α a q hq haq hA hN hlo hhi hL hK hα
  have he := global_coprime_error P hP f u hf (actualDual_bound _ D U) D (U+D) α
  have ht := norm_sub_le (globalPacket P f u D (U+D) α)
      (globalPacket P f u D (U+D) α-globalCoprimePacket P f u D (U+D) α)
  rw [sub_sub_cancel,global_coprime_is_bilinear] at ht
  rw [global_coprime_is_bilinear] at he
  have hbb : ‖bilinearPart P f g 0 (U+D)‖ ≤
      (∑i∈S,Real.sqrt (rationalPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) q))+
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

def normalizedRationalPrimeBlockBudget (P Q : Finset ℕ) (D X A K q : ℕ) : ℝ :=
  ((A:ℝ)⁻¹*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card/(X:ℝ))*
    ((A:ℝ)⁻¹*Q.card*(K/q+1:ℕ)+(Q.card:ℝ)^2*(q:ℝ)*
      (2/(X:ℝ)+4*(A:ℝ)⁻¹*K/D))

lemma prime_block_normalized_rational_budget (P Q : Finset ℕ) (D X A K q : ℕ)
    (hX : 0<X) (hA : 0<A) :
    Real.sqrt (rationalPrimeBlockBudget P Q D X A K q)/(X:ℝ) ≤
      Real.sqrt (normalizedRationalPrimeBlockBudget P Q D X A K q) := by
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hAr : (0:ℝ)<A := by exact_mod_cast hA
  have hr : (((X/A:ℕ):ℝ)/(X:ℝ))≤(A:ℝ)⁻¹ := by
    apply (div_le_iff₀ hXr).mpr
    simpa only [div_eq_mul_inv,mul_comm] using
      (Nat.cast_div_le (α:=ℝ) (m:=X) (n:=A))
  have he : rationalPrimeBlockBudget P Q D X A K q/(X:ℝ)^2=
      ((((X/A:ℕ):ℝ)/(X:ℝ))*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card/(X:ℝ))*
      (((((X/A:ℕ):ℝ)/(X:ℝ)))*Q.card*(K/q+1:ℕ)+(Q.card:ℝ)^2*(q:ℝ)*
        (2/(X:ℝ)+4*((((X/A:ℕ):ℝ)/(X:ℝ)))*K/D)) := by
    simp only [rationalPrimeBlockBudget,div_eq_mul_inv]
    ring
  have hb : rationalPrimeBlockBudget P Q D X A K q/(X:ℝ)^2 ≤
      normalizedRationalPrimeBlockBudget P Q D X A K q := by
    rw [he]
    unfold normalizedRationalPrimeBlockBudget
    gcongr
  have hs := Real.sqrt_le_sqrt hb
  simpa only [Real.sqrt_div' _ (sq_nonneg (X:ℝ)),Real.sqrt_sq hXr.le] using hs

theorem actual_short_near_rational_blocks_normalized {ι : Type*}
    (S : Finset ι) (Q : ι → Finset ℕ) (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f : ℕ → ℂ) (hf : OneBounded f) (hm : Multiplicative f)
    (D U : ℕ) (hX : 0<U+D) (A K : ι → ℕ) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0<q) (haq : Int.gcd a q=1)
    (hA : ∀i∈S,0<A i) (hN : ∀i∈S,0<(U+D)/A i)
    (hlo : ∀i∈S,∀p∈Q i,A i≤p) (hhi : ∀i∈S,∀p∈Q i,p≤K i)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (hK : ∀i∈S,0<K i)
    (hα : ∀i∈S,|α-(a:ℝ)/q|≤1/(2*(q:ℝ)*K i)) :
    ((D:ℝ)⁻¹*(∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖))/
        ((U+D:ℕ):ℝ) ≤
      Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card/((U+D:ℕ):ℝ)+
        (∑i∈S,Real.sqrt (normalizedRationalPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) q))+
        2*(∑p∈P,(p:ℝ)⁻¹^2)+P.card/((U+D:ℕ):ℝ) := by
  have hXr : (0:ℝ)<(U+D:ℕ) := by exact_mod_cast hX
  have ht := div_le_div_of_nonneg_right
    (actual_short_near_rational_blocks S Q P hP hcov hdisj f hf hm D U hX A K α a q hq haq
      hA hN hlo hhi hL hK hα) hXr.le
  have hs : (∑i∈S,Real.sqrt (rationalPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) q))/
        ((U+D:ℕ):ℝ) ≤
      ∑i∈S,Real.sqrt (normalizedRationalPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) q) := by
    rw [sum_div]
    exact sum_le_sum (fun i hi => prime_block_normalized_rational_budget P (Q i) D (U+D)
      (A i) (K i) q hX (hA i hi))
  simp only [add_div] at ht
  have he (r : ℝ) : (2*((U+D:ℕ):ℝ)*r)/((U+D:ℕ):ℝ)=2*r := by
    field_simp
  have he' (r : ℝ) : ((U+D:ℕ):ℝ)*r/((U+D:ℕ):ℝ)=r := by
    exact mul_div_cancel_left₀ r hXr.ne'
  
  simp only [he,he'] at ht
  linarith

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
