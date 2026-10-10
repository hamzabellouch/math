import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalCodeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FactorialTotal

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B C₀ : ℝ} {ℓ L n N : ℕ}

namespace RecordPacket
noncomputable def codeEntropyMass (S : PrimeSystem) : ℝ := ∑ p : S.Index, (p:ℝ)⁻¹
noncomputable def codeEntropyBase (S : PrimeSystem) (ℓ L n N : ℕ) (C₀ B : ℝ) : ℝ :=
  Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N) +
    (ℓ:ℝ)+(L:ℝ)+(n:ℝ)+codeEntropyMass S+3
noncomputable def codeEntropyDegree (L n m N : ℕ) : ℕ := 1+n*(L+4)+m+3*N

lemma codeEntropyMass_nonneg (S : PrimeSystem) : 0 ≤ codeEntropyMass S := by
  exact sum_nonneg (fun p _ => by positivity)

lemma codeEntropyBase_ge_two (S : PrimeSystem) (ℓ L n N : ℕ) (C₀ B : ℝ) :
    2 ≤ codeEntropyBase S ℓ L n N C₀ B := by
  unfold codeEntropyBase
  have hm := codeEntropyMass_nonneg S
  have hℓ : 0 ≤ (ℓ:ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ (L:ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N):ℝ) := Nat.cast_nonneg _
  linarith

lemma metadata_polynomial_bound (Q : ℝ) (hQ : 2 ≤ Q)
    (hℓ : (ℓ:ℝ)+1 ≤ Q) (hL : (L:ℝ)+1 ≤ Q) (hn : (n:ℝ)+1 ≤ Q) :
    (Fintype.card (ListMetadata ℓ L n):ℝ) ≤ Q^(1+n*(L+4)) := by
  have hQ0 : 0 ≤ Q := le_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hQ)
  have hp : (1:ℝ) ≤ Q^(L+3) := one_le_pow₀ (by linarith : (1:ℝ) ≤ Q)
  have hA : ((ℓ:ℝ)+1)*(((L:ℝ)+1)*((2:ℝ)^L*((L:ℝ)+1))) ≤ Q^(L+3) := by
    have htwo := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hQ L
    have hprod := mul_le_mul hℓ (mul_le_mul hL (mul_le_mul htwo hL
      (by positivity) (pow_nonneg hQ0 L)) (by positivity) hQ0) (by positivity) hQ0
    exact hprod.trans_eq (by rw [pow_add]; ring)
  have hinner : (1:ℝ)+((ℓ:ℝ)+1)*(((L:ℝ)+1)*((2:ℝ)^L*((L:ℝ)+1))) ≤ Q^(L+4) := by
    calc
      _ ≤ 2*Q^(L+3) := by linarith
      _ ≤ Q*Q^(L+3) := mul_le_mul_of_nonneg_right hQ (pow_nonneg hQ0 _)
      _ = Q^(L+4) := by rw [← pow_succ']
  have hinner' : (1:ℝ)+((ℓ:ℝ)+1)*(((L:ℝ)+1)^2*(2:ℝ)^L) ≤ Q^(L+4) := by
    convert hinner using 1
    ring
  rw [listMetadata_card]
  push_cast
  calc
    _ ≤ Q*(Q^(L+4))^n := mul_le_mul hn
      (pow_le_pow_left₀ (by positivity) hinner' n) (by positivity) hQ0
    _ = _ := by rw [← pow_mul, mul_comm (L+4) n]; simp only [Nat.add_comm 1, pow_succ']

lemma exceptional_polynomial_bound (Q : ℝ) (hQ : 2 ≤ Q)
    (hm : (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N):ℝ)+codeEntropyMass S ≤ Q)
    (hℓ : (ℓ:ℝ) ≤ Q) :
    exceptionalCost S ℓ L n N C₀ B ≤
      Q^(Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)+3*N) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hshape : 3*(ℓ:ℝ)+1 ≤ Q^3 := by
    have hq2 : 4 ≤ Q^2 := by nlinarith
    nlinarith
  unfold exceptionalCost
  have hp : (∏ i ∈ range (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)),
      ((i:ℝ)+1+∑ p : S.Index, (p:ℝ)⁻¹)) ≤
      Q^(Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) := by
    calc
      _ ≤ ∏ _i ∈ range (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)), Q := by
        apply Finset.prod_le_prod₀
        · intro i _; positivity
        · intro i hi
          have hi' : (i:ℝ)+1 ≤ Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N) := by
            exact_mod_cast (mem_range.mp hi)
          dsimp only [codeEntropyMass] at hm
          linarith
      _ = _ := by simp
  calc
    _ ≤ Q^(Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) * (Q^3)^N :=
      mul_le_mul hp (pow_le_pow_left₀ (by positivity) hshape N) (by positivity) (pow_nonneg hQ0 _)
    _ = _ := by rw [← pow_mul,← pow_add]

theorem packet_entropy_polynomial :
    (Fintype.card (ListMetadata ℓ L n):ℝ)*exceptionalCost S ℓ L n N C₀ B ≤
      (codeEntropyBase S ℓ L n N C₀ B)^(
        codeEntropyDegree L n (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) N) := by
  let Q := codeEntropyBase S ℓ L n N C₀ B
  have hQ := codeEntropyBase_ge_two S ℓ L n N C₀ B
  have hmass := codeEntropyMass_nonneg S
  have hs : 0 ≤ (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N):ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ (L:ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hℓ : 0 ≤ (ℓ:ℝ) := Nat.cast_nonneg _
  have hM := metadata_polynomial_bound (ℓ := ℓ) (L := L) (n := n) Q hQ (by dsimp [Q,codeEntropyBase]; linarith)
    (by dsimp [Q,codeEntropyBase]; linarith) (by dsimp [Q,codeEntropyBase]; linarith)
  have hE := exceptional_polynomial_bound (S := S) (C₀ := C₀) (B := B)
    (ℓ := ℓ) (L := L) (n := n) (N := N) Q hQ
    (by dsimp [Q,codeEntropyBase]; linarith) (by dsimp [Q,codeEntropyBase]; linarith)
  calc
    _ ≤ Q^(1+n*(L+4))*Q^(Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)+3*N) :=
      mul_le_mul hM hE (exceptionalCost_nonneg ..) (pow_nonneg (by linarith) _)
    _ = _ := by rw [← pow_add]; simp only [codeEntropyDegree,Q,Nat.add_assoc]

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
