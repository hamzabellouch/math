import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CylinderBudget
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessSlotCount

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical

noncomputable def witnessEntropyBase (S : PrimeSystem) (M ℓ L J t : ℕ) : ℝ :=
  2+A+M+ℓ+L+t+witnessSlotCount ℓ L J t + max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)

noncomputable def witnessEntropyDegree (M ℓ L J t : ℕ) : ℕ :=
  2*M+ℓ*J+3*witnessSlotCount ℓ L J t+ℓ+2*t*(L+10)+4

lemma add_one_le_pow_succ {Q x : ℝ} {n : ℕ} (hQ : 2 ≤ Q) (hx : x ≤ Q^n) :
    x+1 ≤ Q^(n+1) := by
  have hpow : 1 ≤ Q^n := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith

lemma witness_polynomial_bound (S : PrimeSystem) (M ℓ L J t : ℕ) :
    cylinderBudget M * (A^(ℓ*J)*2^(witnessSlotCount ℓ L J t)) *
      (witnessTemplateBudget ℓ L J t:ℝ) *
        (max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(witnessSlotCount ℓ L J t) ≤
    witnessEntropyBase S M ℓ L J t ^ witnessEntropyDegree M ℓ L J t := by
  let N := witnessSlotCount ℓ L J t
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  let Q := witnessEntropyBase S M ℓ L J t
  have hH : 1 ≤ H := le_max_left _ _
  have hA := A_pos
  have hM := Nat.cast_nonneg (α:=ℝ) M
  have hℓ := Nat.cast_nonneg (α:=ℝ) ℓ
  have hL := Nat.cast_nonneg (α:=ℝ) L
  have ht := Nat.cast_nonneg (α:=ℝ) t
  have hN := Nat.cast_nonneg (α:=ℝ) N
  have hQ : 2 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQA : A ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQM : (M:ℝ) ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQℓ : (ℓ:ℝ)+1 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQL : (L:ℝ)+1 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQt : (t:ℝ)+1 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQN : (N:ℝ)+1 ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQH : H ≤ Q := by dsimp [Q,witnessEntropyBase]; dsimp only [H,N] at *; linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hcyl : cylinderBudget M ≤ Q^(2*M+1) := by
    unfold cylinderBudget
    push_cast
    calc
      _ ≤ Q^M * Q^(M+1) := by
        apply mul_le_mul (pow_le_pow_left₀ (by norm_num) hQ _) _ (by positivity) (pow_nonneg hQ0 _)
        apply max_le
        · exact one_le_pow₀ (by linarith)
        · exact pow_le_pow_left₀ hM hQM _
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hcore : ((ℓ:ℝ)+1)*(((L:ℝ)+1)^2*2^L) ≤ Q^(L+3) := by
    calc
      _ ≤ Q*(Q^2*Q^L) := by gcongr
      _ = _ := by rw [show L+3=L+2+1 by omega,pow_succ,pow_add]; ring
  have hcore1 : 1+((ℓ:ℝ)+1)*(((L:ℝ)+1)^2*2^L) ≤ Q^(L+4) := by
    simpa only [show L+4=(L+3)+1 by omega,add_comm (1:ℝ)] using add_one_le_pow_succ hQ hcore
  have hmeta : (Fintype.card (WitnessMetadata ℓ L t):ℝ) ≤ Q^(ℓ+1+2*t*(L+4)) := by
    rw [WitnessConfiguration.metadata_card]
    push_cast
    calc
      _ ≤ Q^ℓ*(Q*(Q^(L+4))^t)*(Q^(L+4))^t := by
        apply mul_le_mul
        · apply mul_le_mul (pow_le_pow_left₀ (by norm_num) hQ _) _ (by positivity) (pow_nonneg hQ0 _)
          exact mul_le_mul hQt (pow_le_pow_left₀ (by positivity) hcore1 _) (by positivity) hQ0
        · exact pow_le_pow_left₀ (by positivity) (hcore.trans (pow_le_pow_right₀ (by linarith) (by omega))) _
        · positivity
        · positivity
      _ = _ := by ring
  have hdesc : (Fintype.card (WitnessTestDescriptor ℓ L t N):ℝ) ≤ Q^11 := by
    rw [WitnessTemplateCode.descriptor_card]
    push_cast
    calc
      _ ≤ (Q^2*Q*Q^3*Q^2)*Q^2*Q := by
        gcongr <;> linarith
      _ = _ := by ring
  have hdesc1 : (Fintype.card (WitnessTestDescriptor ℓ L t N):ℝ)+1 ≤ Q^12 :=
    add_one_le_pow_succ hQ hdesc
  have hbudget : (witnessTemplateBudget ℓ L J t:ℝ) ≤
      Q^(N+ℓ+2*t*(L+10)+3) := by
    unfold witnessTemplateBudget
    change (((N+1)*Fintype.card (WitnessMetadata ℓ L t)*(N+1)^N*
      ((t+1)*(Fintype.card (WitnessTestDescriptor ℓ L t N)+1)^t):ℕ):ℝ) ≤ _
    push_cast
    calc
      _ ≤ Q*Q^(ℓ+1+2*t*(L+4))*Q^N*(Q*(Q^12)^t) := by
        gcongr
      _ = _ := by ring
  apply (mul_le_mul (mul_le_mul (mul_le_mul hcyl
    (mul_le_mul (pow_le_pow_left₀ hA.le hQA _) (pow_le_pow_left₀ (by norm_num) hQ _)
      (by positivity) (pow_nonneg hQ0 _)) (by positivity) (pow_nonneg hQ0 _))
    hbudget (Nat.cast_nonneg _) (by positivity))
    (pow_le_pow_left₀ (zero_le_one.trans hH) hQH _) (by positivity) (by positivity)).trans_eq
  unfold witnessEntropyDegree
  change Q^(2*M+1)*(Q^(ℓ*J)*Q^N)*Q^(N+ℓ+2*t*(L+10)+3)*Q^N = _
  simp only [←pow_add]
  congr 1
  dsimp only [N]
  omega

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
