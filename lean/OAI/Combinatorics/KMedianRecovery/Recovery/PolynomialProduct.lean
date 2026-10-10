import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CompletionCoefficient
import OAI.Combinatorics.KMedianRecovery.Recovery.AffineLogBound
import OAI.Combinatorics.KMedianRecovery.Machines.SizeBitLength

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly

private lemma polynomial_product (A B R Q T b d : ℕ) :
    (A*b)*(B*b^3)*(R*b^d)*Q*(T*b^2)^13 = (A*B*R*Q*T^13)*b^(d+30) := by
  rw [mul_pow, ← pow_mul]
  have he : d+30 = 4+d+26 := by omega
  rw [he, pow_add, pow_add]
  ring
open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies RoundedAssembly

lemma cap_polynomial (n N : ℕ) (h : n ≤ N) :
    Rounding.cap n (gamma/16) ≤ (⌈20/(gamma/16)⌉₊+2)*(N+2)^2 := by
  have he : 0 < gamma/16 := div_pos gamma_pos (by norm_num)
  have hn : (n:ℝ)^2 ≤ ((N:ℝ)+2)^2 := by
    have h' : (n:ℝ) ≤ N := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) N]
  have hc : ⌈20*(n:ℝ)^2/(gamma/16)⌉₊ ≤ ⌈20/(gamma/16)⌉₊*(N+2)^2 := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = (20/(gamma/16))*(n:ℝ)^2 := by ring
      _ ≤ (20/(gamma/16))*((N:ℝ)+2)^2 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _)
  have hb : 1 ≤ (N+2)^2 := one_le_pow₀ (by omega)
  unfold Rounding.cap
  nlinarith

lemma input_size_pos (I : RationalMetricInput) : 1 ≤ I.size := by
  have := I.facilities_nonempty.card_pos
  unfold RationalMetricInput.size
  omega

lemma input_points_le_size (I : RationalMetricInput) : I.pointCount ≤ I.size := by
  calc
    _ = (I.clients ∪ I.facilities).card := by rw [I.covered]; simp
    _ ≤ I.size := Finset.card_union_le _ _

lemma supplied_count_log (v : ℚ) (Nstar : ℕ) (hv : 0 < v) :
    ∃ A : ℝ, 0 < A ∧ ∀ I : RationalMetricInput,
      (countBound (commonL v Nstar I.clients.card (Rounding.cap I.clients.card (gamma/16))):ℝ) ≤
        A*Real.log ((I.size:ℝ)+2) := by
  let C : ℕ := ⌈20/(gamma/16)⌉₊+2
  let B : ℝ := Nstar+3*Real.log (9*C)/Real.log (1+(v:ℝ)^2)+9
  let D : ℝ := 9/Real.log (1+(v:ℝ)^2)
  obtain ⟨A1,hA1,hfirst⟩ := LogPolynomial.affine_log_bound B D
  let R : ℝ := 2+4*Anchoring.countConstant (1/100)/(gamma/16)
  have hR : 0 ≤ R := by
    have := PhaseSurplusProducer.countConstant_ge_ten
    have := gamma_pos
    dsimp [R]
    positivity
  obtain ⟨A,hA,hsecond⟩ := LogPolynomial.affine_log_bound 1 (R*A1)
  refine ⟨A,hA,?_⟩
  intro I
  have hN : 1 ≤ I.size := input_size_pos I
  have hn : I.clients.card ≤ I.size := by unfold RationalMetricInput.size; omega
  have hCap := cap_polynomial I.clients.card I.size hn
  have hbound := commonL_bound v C Nstar I.clients.card
    (Rounding.cap I.clients.card (gamma/16)) I.size 2
    (by exact_mod_cast hv) hN hn (by dsimp [C]; exact_mod_cast (by omega : 1 ≤ ⌈20/(gamma/16)⌉₊+2))
    (Rounding.cap_pos _ _) (by exact_mod_cast hCap)
  have hL : (commonL v Nstar I.clients.card (Rounding.cap I.clients.card (gamma/16)):ℝ) ≤
      A1*Real.log ((I.size:ℝ)+2) := by
    apply le_trans hbound.le
    have ht := hfirst ((I.size:ℝ)+2) (by linarith [Nat.cast_nonneg (α := ℝ) I.size])
    calc
      _ = B+D*Real.log ((I.size:ℝ)+2) := by dsimp only [B,D]; ring
      _ ≤ _ := ht
  have hC := countBound_bound (commonL v Nstar I.clients.card (Rounding.cap I.clients.card (gamma/16)))
  calc
    _ ≤ R*(commonL v Nstar I.clients.card (Rounding.cap I.clients.card (gamma/16)):ℝ)+1 := hC
    _ ≤ R*(A1*Real.log ((I.size:ℝ)+2))+1 := by gcongr
    _ = 1+(R*A1)*Real.log ((I.size:ℝ)+2) := by ring
    _ ≤ _ := hsecond _ (by linarith [Nat.cast_nonneg (α := ℝ) I.size])

theorem bitCount_polynomial (v : ℚ) (Nstar : ℕ) (c a : ℝ) (hv : 0 < v) (hc : 0 ≤ c) :
    ∃ P : Polynomial ℕ, ∀ I : RationalMetricInput,
      bitCount v Nstar c a I ≤ P.eval I.bits.length := by
  obtain ⟨A,hA,hL⟩ := supplied_count_log v Nstar hv
  obtain ⟨KR,d,hrep⟩ := LogPolynomial.amplification_polynomial c A gamma ⌈a⌉₊ hc gamma_pos
  let KC : ℕ := ⌈20/(gamma/16)⌉₊+2
  let KL : ℕ := ⌈A⌉₊
  let K : ℕ := (KL+1)*(KC+1)*KR*recoveryCoefficient*(KC+KL+3)^13
  refine ⟨Polynomial.C K * (Polynomial.X+Polynomial.C 2)^(d+30),?_⟩
  intro I
  let b := I.size+2
  let C := Rounding.cap I.clients.card (gamma/16)
  let L := countBound (commonL v Nstar I.clients.card C)
  let n := repetitions c L (FailureBudget.failure gamma ⌈a⌉₊ I.size)
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hclients : I.clients.card ≤ b := by dsimp [b,RationalMetricInput.size]; omega
  have hpoints : I.pointCount ≤ b := (input_points_le_size I).trans (by dsimp [b]; omega)
  have hC : C ≤ KC*b^2 := cap_polynomial _ _ (by unfold RationalMetricInput.size; omega)
  have hLC : L ≤ KL*b := by
    have ht : (L:ℝ) ≤ A*((I.size:ℝ)+2) :=
      (hL I).trans (mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity)) hA.le)
    have ht' := ht.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil A) (by positivity : 0 ≤ (I.size:ℝ)+2))
    exact_mod_cast ht'
  have hn : n ≤ KR*b^d := hrep I.size L (hL I)
  have hLp : L+1 ≤ (KL+1)*b := by nlinarith
  have hU : I.clients.card*C+1 ≤ (KC+1)*b^3 := by
    have hmul := Nat.mul_le_mul hclients hC
    have hpow : 1 ≤ b^3 := one_le_pow₀ hb
    nlinarith
  have hT : 2*I.pointCount+C+L+1 ≤ (KC+KL+3)*b^2 := by
    have hb2 : b ≤ b^2 := by nlinarith
    have hpt : 2*I.pointCount ≤ 2*b^2 := by omega
    have hl2 := hLC.trans (Nat.mul_le_mul_left KL hb2)
    have hpow : 1 ≤ b^2 := one_le_pow₀ hb
    nlinarith
  have hB := recoveryBitCount_polynomial (marked false I.clients) (marked true I.facilities) C L
    (I.clients.card*C) n
  have hB' : bitCount v Nstar c a I ≤ (L+1)*(I.clients.card*C+1)*n*recoveryCoefficient*
      (2*I.pointCount+C+L+1)^13 := by
    simpa only [bitCount,C,L,n,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.ceil_natCast,Nat.mul_comm]
      using hB
  have hfinal : bitCount v Nstar c a I ≤ K*b^(d+30) := by
    apply hB'.trans
    calc
      _ ≤ ((KL+1)*b)*((KC+1)*b^3)*(KR*b^d)*recoveryCoefficient*((KC+KL+3)*b^2)^13 := by gcongr
      _ = K*b^(d+30) := polynomial_product _ _ _ _ _ _ _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X]
  exact hfinal.trans (Nat.mul_le_mul_left K
    (Nat.pow_le_pow_left (Nat.add_le_add_right I.size_le_bitLength 2) (d+30)))

end MetricKMedianRecovery.GlobalAssembly

end OAI
