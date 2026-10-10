import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicControls
import OAI.Combinatorics.ContingencyTables.Counting.CountingWordsBound

namespace OAI

/-! # The complete counting word is polynomial in the original input -/

namespace ContingencyTables.CountingPublicWordBound
open CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def controlPolynomial : Polynomial ℕ :=
  CountingPublicControls.inputPolynomial+CountingPublicControls.observationPolynomial+
    CountingPublicControls.returnPolynomial+CountingPublicControls.precisionPolynomial+
    CountingTerminalBounds.gridPolynomial+2048*(CountingTerminalBounds.phasePolynomial+1)+X+1

def wordPolynomial : Polynomial ℕ := CountingWordsBound.wordPolynomial.comp controlPolynomial

def amplifiedPolynomial : Polynomial ℕ := 64*X*wordPolynomial

lemma reciprocal_controls (k M : ℕ) (hk : 0 < k) (hM : k ≤ M) :
    0 < (1/(k:ℚ)) ∧ 1/(1/(k:ℚ)) ≤ (M:ℚ) ∧
      CommonBasesFPRAS.repetitionCount (1/(k:ℚ)) ≤ 64*(M+1) := by
  have hkq : (0:ℚ) < k := by exact_mod_cast hk
  refine ⟨one_div_pos.mpr hkq,?_,?_⟩
  · simpa only [one_div_one_div] using (show (k:ℚ) ≤ M by exact_mod_cast hM)
  · unfold CommonBasesFPRAS.repetitionCount
    rw [one_div,Rat.inv_natCast_den_of_pos hk,Nat.size_eq_bits_len]
    exact Nat.mul_le_mul_left 64 (Nat.add_le_add_right
      ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hM) 1)

lemma bitCount_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    RootedCountingWords.bitCount A s ≤ wordPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let S := size r c b epsilon delta
  let M := controlPolynomial.eval S
  have hm0 : CountingPublicControls.inputPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hmN : CountingPublicControls.observationPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hmn : CountingPublicControls.returnPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hmk : CountingPublicControls.precisionPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hmK : CountingTerminalBounds.gridPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hmh : 2048*(CountingTerminalBounds.phasePolynomial.eval S+1) ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hSM : S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hsc : ∀ x∈[Fintype.card (Labels A),A.W,s.H,
      CompanionTargetMixing.restartTime A s.H s.L,s.L],
      x ≤ CountingPublicControls.inputPolynomial.eval S :=
    CountingPublicControls.scalar_bound hEK r c b hne epsilon delta he
  have hp : Fintype.card (Labels A) ≤ M :=
    (hsc _ (by simp only [List.mem_cons,eq_self,true_or])).trans hm0
  have hW : A.W ≤ M :=
    (hsc _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hm0
  have hH : s.H ≤ M :=
    (hsc _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hm0
  have ht : CompanionTargetMixing.restartTime A s.H s.L ≤ M :=
    (hsc _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hm0
  have hcontrols := CountingPublicControls.settings_bounds hEK r c b hne epsilon delta he
  have hN : s.N ≤ M := hcontrols.1.trans hmN
  have hn : s.n ≤ M := hcontrols.2.1.trans hmn
  have hk : s.k ≤ M := hcontrols.2.2.trans hmk
  have hterminal := CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he
  have hK : s.K ≤ M := hterminal.1.trans hmK
  have hh : s.h ≤ M :=
    (Nat.mul_le_mul_left 2048 (Nat.add_le_add_right hterminal.2.2 1)).trans hmh
  have hd : A.d ≤ M := (dimension_le r c b epsilon delta).trans hSM
  have hcapacity : CountingTerminalSchedule.capacityBits A ≤ M :=
    (capacityBits_le hEK r c b hne epsilon delta).trans hSM
  have hkpos : 0 < s.k := CountingPhaseSchedule.precision_pos _ _ _ _ _
  have hrec := reciprocal_controls s.k M hkpos hk
  have hb := CountingWordsBound.bitCount_bound A s M hd hW hK hH hk hn hN hh
    hH hcapacity hp ht hrec.1 hrec.2.1 hrec.2.2
  simpa only [wordPolynomial,Polynomial.eval_comp] using hb

lemma amplified_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    RootedCountingAmplification.bitCount A s delta ≤ amplifiedPolynomial.eval (size r c b epsilon delta) := by
  have hw := bitCount_public hEK r c b hne epsilon delta he
  have hr := repeats_le r c b epsilon delta
  dsimp only
  simp only [RootedCountingAmplification.bitCount,CommonBasesFPRAS.repetitionCount,
    amplifiedPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  exact Nat.mul_le_mul hr hw

end
end ContingencyTables.CountingPublicWordBound

end OAI
