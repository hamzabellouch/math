import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeBlockPacket

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

def normalizedPrimeBlockBudget (P Q : Finset ℕ) (D X A K : ℕ) (κ : ℝ) : ℝ :=
  ((A:ℝ)⁻¹*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card/(X:ℝ))*
    ((A:ℝ)⁻¹*Q.card+(Q.card:ℝ)^2*
      ((2/(X:ℝ)+4*(A:ℝ)⁻¹*K/D)/κ))

lemma prime_block_normalized_budget (P Q : Finset ℕ) (D X A K : ℕ)
    (hX : 0<X) (hA : 0<A) {κ : ℝ} (hκ : 0<κ) :
    Real.sqrt (primeBlockBudget P Q D X A K κ)/(X:ℝ) ≤
      Real.sqrt (normalizedPrimeBlockBudget P Q D X A K κ) := by
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hAr : (0:ℝ)<A := by exact_mod_cast hA
  have hr : (((X/A:ℕ):ℝ)/(X:ℝ))≤(A:ℝ)⁻¹ := by
    apply (div_le_iff₀ hXr).mpr
    simpa only [div_eq_mul_inv,mul_comm] using
      (Nat.cast_div_le (α:=ℝ) (m:=X) (n:=A))
  have he : primeBlockBudget P Q D X A K κ/(X:ℝ)^2=
      ((((X/A:ℕ):ℝ)/(X:ℝ))*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card/(X:ℝ))*
      (((((X/A:ℕ):ℝ)/(X:ℝ)))*Q.card+(Q.card:ℝ)^2*
        ((2/(X:ℝ)+4*((((X/A:ℕ):ℝ)/(X:ℝ)))*K/D)/κ)) := by
    simp only [primeBlockBudget,div_eq_mul_inv]
    ring
  have hb : primeBlockBudget P Q D X A K κ/(X:ℝ)^2 ≤
      normalizedPrimeBlockBudget P Q D X A K κ := by
    rw [he]
    unfold normalizedPrimeBlockBudget
    gcongr
  have hs := Real.sqrt_le_sqrt hb
  simpa only [Real.sqrt_div' _ (sq_nonneg (X:ℝ)),Real.sqrt_sq hXr.le] using hs

theorem actual_short_minor_arc_blocks_normalized {ι : Type*}
    (S : Finset ι) (Q : ι → Finset ℕ) (P : Finset ℕ)
    (hP : ∀p∈P,Nat.Prime p) (hcov : P=S.biUnion Q)
    (hdisj : Set.PairwiseDisjoint (S:Set ι) Q)
    (f : ℕ → ℂ) (hf : OneBounded f) (hm : Multiplicative f)
    (D U : ℕ) (hX : 0<U+D) (A K : ι → ℕ) (κ : ι → ℝ) (α : ℝ)
    (hA : ∀i∈S,0<A i) (hN : ∀i∈S,0<(U+D)/A i)
    (hlo : ∀i∈S,∀p∈Q i,A i≤p) (hhi : ∀i∈S,∀p∈Q i,p≤K i)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) (hκ : ∀i∈S,0<κ i)
    (hgap : ∀i∈S,∀p∈Q i,∀q∈Q i,p≠q → κ i≤‖1-phase (α*((p:ℝ)-q))‖) :
    ((D:ℝ)⁻¹*(∑y∈range U,‖∑k∈range D,f (y+1+k)*phase (α*(y+1+k))‖))/
        ((U+D:ℕ):ℝ) ≤
      Real.exp (-(∑p∈P,(p:ℝ)⁻¹))+2^P.card/((U+D:ℕ):ℝ)+
        (∑i∈S,Real.sqrt (normalizedPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) (κ i)))+
        2*(∑p∈P,(p:ℝ)⁻¹^2)+P.card/((U+D:ℕ):ℝ) := by
  have hXr : (0:ℝ)<(U+D:ℕ) := by exact_mod_cast hX
  have ht := div_le_div_of_nonneg_right
    (actual_short_minor_arc_blocks S Q P hP hcov hdisj f hf hm D U hX A K κ α
      hA hN hlo hhi hL hκ hgap) hXr.le
  have hs : (∑i∈S,Real.sqrt (primeBlockBudget P (Q i) D (U+D) (A i) (K i) (κ i)))/
        ((U+D:ℕ):ℝ) ≤
      ∑i∈S,Real.sqrt (normalizedPrimeBlockBudget P (Q i) D (U+D) (A i) (K i) (κ i)) := by
    rw [sum_div]
    exact sum_le_sum (fun i hi => prime_block_normalized_budget P (Q i) D (U+D)
      (A i) (K i) hX (hA i hi) (hκ i hi))
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
