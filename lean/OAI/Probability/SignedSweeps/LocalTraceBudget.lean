import OAI.Probability.SignedSweeps.LocalStabilizerTrace
import OAI.Probability.SignedSweeps.PartitionCount
import OAI.Probability.SignedSweeps.OccupiedCounts

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma nat_pow_le_exp_log {a B : ℕ} (hB : 0 < B) (ha : a ≤ B) (k : ℕ) :
    (a : ℝ)^k ≤ Real.exp ((k : ℝ)*Real.log B) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hB)]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ha) k

lemma partitionCount_le_exp {n B : ℕ} (hB : n+1 ≤ B) :
    (Fintype.card (Partition n) : ℝ) ≤
      Real.exp (2*(Nat.sqrt n : ℝ)*Real.log B) := by
  have hc : (Fintype.card (Partition n) : ℝ) ≤ (n+1 : ℕ)^(2*Nat.sqrt n) := by
    exact_mod_cast partitionCount_le n
  have hh := nat_pow_le_exp_log (by omega : 0 < B) hB (2*Nat.sqrt n)
  exact hc.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh)

lemma pairTypeCount_le_exp {p t B : ℕ} (hpt : p ≤ t) (hB : t+1 ≤ B) :
    (Fintype.card (PairType p) : ℝ) ≤
      Real.exp ((4*(Nat.sqrt t : ℝ)+1)*Real.log B) := by
  have hc : (Fintype.card (PairType p) : ℝ) ≤ (p+1 : ℕ)^(4*Nat.sqrt p+1) := by
    exact_mod_cast pairTypeCount_le p
  apply hc.trans
  apply (nat_pow_le_exp_log (by omega : 0 < B) (by omega : p+1 ≤ B) _).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega)))
  have hh : (Nat.sqrt p : ℝ) ≤ Nat.sqrt t := by exact_mod_cast Nat.sqrt_le_sqrt hpt
  push_cast
  linarith

def localTraceError (t q B : ℕ) : ℝ :=
  (2*(Nat.sqrt t : ℝ)+26*(q:ℝ)^2+8*q+1)*Real.log B+8*q+1

lemma localTraceError_nonneg {t q B : ℕ} (hB : 1 ≤ B) :
    0 ≤ localTraceError t q B := by
  unfold localTraceError
  have hl : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  positivity

lemma signed_local_stabilizer_trace_exp {u v p l t q : ℕ}
    (h : u+v=p) (ht : u+v+l=t) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ q) (hb : b.1.colLen 0 ≤ q)
    (i : Fin p ↪ Fin t) (f : SymmetricGroup t → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (η G : ℝ)
    (hamb : ∀ (lam : Partition t) (c : Partition l), SignedOccurrence ht a b c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤
          Real.exp (η*signedEntropy a b+G))
    (B : ℕ) (hB : 2*t+2*q+1 ≤ B) :
    (LinearMap.trace ℂ (WordSpace p (Fin q ⊕ Fin q))
      (pairTypeProjection h a b (Fin q) * coefficientAction (signedWordRepresentation p (Fin q))
        (fun g => f (g.viaEmbedding i)))).re ≤
      ((p.factorial : ℝ) / t.factorial) *
        Real.exp ((η-1)*signedEntropy a b+G+localTraceError t q B) := by
  have hraw := signed_local_stabilizer_trace h ht a b
    (C := Fin q) (by simpa using ha) (by simpa using hb) i f hf η G hamb B
    (by simp only [Fintype.card_fin]; omega)
  simp only [Fintype.card_fin] at hraw
  apply hraw.trans
  have hpc : p+1 ≤ B := by omega
  have hl : Real.log (p+1 : ℕ) ≤ Real.log B :=
    Real.log_le_log (by positivity) (by exact_mod_cast hpc)
  have hc := partitionCount_le_exp (by omega : t+1 ≤ B)
  have hp := nat_pow_le_exp_log (by omega : 0 < B) hpc (2*(q*q))
  have hp' : (p+1:ℝ)^(2*(q*q)) ≤ Real.exp (2*(q:ℝ)^2*Real.log B) := by
    convert hp using 1 <;> push_cast <;> ring_nf
  calc
    _ ≤ ((p.factorial : ℝ)/t.factorial) * Real.exp (2*(Nat.sqrt t:ℝ)*Real.log B) *
        Real.exp (2*(q:ℝ)^2*Real.log B) *
        Real.exp ((η-1)*signedEntropy a b+G+Real.log (p+1:ℕ)+1+
          8*(q:ℝ)*(Real.log (p+1:ℕ)+1)+24*(q:ℝ)^2*Real.log B) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) hp' (by positivity) (by positivity)
    _ = ((p.factorial : ℝ)/t.factorial) *
        Real.exp (2*(Nat.sqrt t:ℝ)*Real.log B + 2*(q:ℝ)^2*Real.log B +
        ((η-1)*signedEntropy a b+G+Real.log (p+1:ℕ)+1+
          8*(q:ℝ)*(Real.log (p+1:ℕ)+1)+24*(q:ℝ)^2*Real.log B)) := by
      simp only [Real.exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by positivity)
      have hq : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
      dsimp [localTraceError]
      nlinarith

lemma pairCarrierCost_le_exp {u v t q B : ℕ} (a : Partition u) (b : Partition v)
    (ht : u+v ≤ t) (hB : t+1 ≤ B) :
    pairCarrierCost (Fin q) a b ≤
      Real.exp (signedEntropy a b+2*(q:ℝ)^2*Real.log B) := by
  have ha := nat_pow_le_exp_log (by omega : 0 < B) (by omega : u+1 ≤ B) (q*q)
  have hb := nat_pow_le_exp_log (by omega : 0 < B) (by omega : v+1 ≤ B) (q*q)
  unfold pairCarrierCost
  simp only [Fintype.card_fin]
  calc
    _ ≤ Real.exp (signedEntropy a b) *
        (Real.exp (((q*q:ℕ):ℝ)*Real.log B) * Real.exp (((q*q:ℕ):ℝ)*Real.log B)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply mul_le_mul _ _ (by positivity) (Real.exp_nonneg _)
      · simpa only [Nat.cast_add, Nat.cast_one] using ha
      · simpa only [Nat.cast_add, Nat.cast_one] using hb
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring

end SignedSweeps
end

end OAI
