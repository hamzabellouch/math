import OAI.Combinatorics.ParityLifts.RaceLoop

namespace OAI

namespace ParityWL.Complexity

lemma race_budget_numeric (A q B L : ℕ) :
    (1000*(B+L+2)^2*(A*(20*(B+L+2)+1)^q+1) : ℝ) ≤
      (1000*(A*21^q+1))*(B+L+2)^(q+2) := by
  let X : ℝ := B+L+2
  have hX : 1 ≤ X := by dsimp only [X]; have := Nat.cast_nonneg (α:=ℝ) B; have := Nat.cast_nonneg (α:=ℝ) L; linarith
  have hpow : (20*X+1)^q ≤ (21*X)^q := by gcongr; linarith
  have h1 : 1 ≤ X^q := one_le_pow₀ hX
  rw [mul_pow] at hpow
  have hsecond : (A : ℝ)*(20*X+1)^q+1 ≤ (A*21^q+1)*X^q := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α:=ℝ) A)]
  have hh := mul_le_mul_of_nonneg_left hsecond (by positivity : 0 ≤ 1000*X^2)
  calc
    _ ≤ 1000*X^2*((A*21^q+1)*X^q) := hh
    _ = _ := by rw [pow_add]; dsimp only [X]; ring

lemma race_machine_numeric (D E : ℝ) (q B L t : ℕ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ht : (t : ℝ) ≤ D*(E*(B+L+2 : ℝ)^q+1)^2+44*L+20) :
    (t : ℝ) ≤ (D*(E+2)^2+64)*(B+L+2 : ℝ)^(2*q+2) := by
  have hcost : (t : ℝ) ≤ D*(E*(B+L+2 : ℝ)^q+0+2)^2+44*(B+L+1 : ℕ)+20 := by
    apply ht.trans
    push_cast
    have h1 : 0 ≤ E*(B+L+2 : ℝ)^q := by positivity
    have hh : (E*(B+L+2 : ℝ)^q+1)^2 ≤ (E*(B+L+2 : ℝ)^q+0+2)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hD, Nat.cast_nonneg (α:=ℝ) B]
  have hT : E*(B+L+2 : ℝ)^q ≤ E*((B+L+1 : ℕ)+1 : ℝ)^q := by
    push_cast
    ring_nf
    exact le_rfl
  have hh := decision_numeric_bound D E 0 0 q (B+L+1) 0
    (E*(B+L+2 : ℝ)^q) 0 t hD hE (by norm_num) (by norm_num)
    (by positivity) (by norm_num) hT (by norm_num) hcost
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,
    add_zero,add_assoc,one_add_one_eq_two] using hh

/-- One fixed finite machine enumerates all parameter pairs and bounded simulations.
The exponent and multiplier do not depend on the pair which eventually halts. -/
lemma raceDecision_bound (M : Machine) : ∃ A : ℝ, 0<A ∧ ∃ d : ℕ, 0<d ∧
    ∀ bs : List Bool, ∀ P : Bool → Prop,
    (∀ j : ℕ, 0<j → ∀ k : ℕ, 4 ≤ k → ∃ s b, Emits M (trialInput j k bs) s b ∧ P b) →
    ∀ j k s : ℕ, 0<j → 4 ≤ k → ∀ b : Bool, Emits M (trialInput j k bs) s b →
    ∃ t a, Emits (raceCode M).decision bs t a ∧ P a ∧
      (t : ℝ) ≤ A*(s+j+k+bs.length+2 : ℝ)^d := by
  let q := (PolyProgram.raceStep M).degree
  let C := (PolyProgram.raceStep M).coefficient
  let E : ℝ := 1000*(C*21^q+1)
  let D : ℝ := 500*((raceCode M).factor+2 : ℝ)*((raceCode M).depth+2 : ℝ)
  have hE : 0<E := by dsimp only [E]; positivity
  have hD : 0<D := by
    dsimp only [D]
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast (show 0<(raceCode M).factor+2 by omega)))
      (by exact_mod_cast (show 0<(raceCode M).depth+2 by omega))
  refine ⟨D*(E+2)^2+64,by positivity,2*(q+2)+2,by omega,?_⟩
  intro bs P hM j k s hj hk b hb
  let B := s+j+k
  have hB : (raceStage M B bs).1=true := raceStage_complete M bs j k s B b hj hk
    (by dsimp only [B]; omega) (by dsimp only [B]; omega) (by dsimp only [B]; omega) hb
  obtain ⟨a,ha,hP⟩ := raceCode_run M bs P hM B hB
  have hr : RBEval (raceCode M) (treeEncode bs) (E*(B+bs.length+2 : ℝ)^(q+2)) (treeEncode a) := by
    apply ha.real.mono
    simp only [raceStepBudget,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    exact race_budget_numeric C q B bs.length
  obtain ⟨t,ht,hcost⟩ := hr.decision
  refine ⟨t,a,ht,hP,?_⟩
  have hn := race_machine_numeric D E (q+2) B bs.length t hD.le hE.le hcost
  simpa only [B,Nat.cast_add] using hn

end ParityWL.Complexity

end OAI
