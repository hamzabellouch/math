import OAI.MathematicalPhysics.NavierStokes.Material.Decoding

namespace OAI

namespace Alternating.Memory
open scoped BigOperators

noncomputable def tapeUpdate (b a ell : ℕ) (i : Instruction) (A B : ℝ) : ℝ × ℝ :=
  let R := (b : ℝ) * B - 2 * a
  if i.2.2 = 2 then (((2 * i.2.1 : ℝ) + A) / b, R)
  else if i.2.2 = 1 then (A, ((2 * i.2.1 : ℝ) + R) / b)
  else ((b : ℝ) * A - 2 * ell,
    ((2 * ell : ℝ) + ((2 * i.2.1 : ℝ) + R) / b) / b)

noncomputable def branchCode (b K a ell : ℕ) (i : Instruction) (A B : ℝ) : ℝ :=
  ((2 * i.1 : ℝ) + (tapeUpdate b a ell i A B).1 +
    (b : ℝ)⁻¹ ^ K * (tapeUpdate b a ell i A B).2) / b

theorem branchCode_smooth (b K a ell : ℕ) (i : Instruction) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => branchCode b K a ell i p.1 p.2) := by
  unfold branchCode tapeUpdate
  split_ifs <;> fun_prop

noncomputable def localBranchCode (M : Machine) (K q a : ℕ) (A B : ℝ) : ℝ :=
  let i := M.normalizedInstruction q a
  if i.2.2 = 0 then
    ∑ ell ∈ Finset.range M.symbolCount,
      digitSelector (alphabetBase M) ell A * branchCode (alphabetBase M) K a ell i A B
  else branchCode (alphabetBase M) K a 0 i A B

theorem localBranchCode_smooth (M : Machine) (K q a : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => localBranchCode M K q a p.1 p.2) := by
  dsimp only [localBranchCode]

  split_ifs
  · apply ContDiff.sum
    intro ell _
    exact ((digitSelector_smooth _ _).comp contDiff_fst).mul (branchCode_smooth _ _ _ _ _)
  · exact branchCode_smooth _ _ _ _ _

noncomputable def localWrite (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  let b := alphabetBase M
  let C := readState b N n D
  let A := readLeft b N n D
  let B := readRight b N n D
  epsilon b N (n + 1) *
    ∑ q ∈ Finset.range (M.stateCount + 1), ∑ a ∈ Finset.range M.symbolCount,
      digitSelector b q C * digitSelector b a B *
        localBranchCode M (width N (n + 1)) q a A B

theorem localWrite_smooth (M : Machine) (N n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (localWrite M N n) := by
  have hb : 2 ≤ alphabetBase M := by have := alphabetBase_ge_four M; omega
  apply contDiff_const.mul
  apply ContDiff.sum
  intro q _
  apply ContDiff.sum
  intro a _
  apply ContDiff.mul
  · exact ((digitSelector_smooth _ _).comp (readState_smooth hb N n)).mul
      ((digitSelector_smooth _ _).comp (readRight_smooth hb N n))
  · exact (localBranchCode_smooth M _ q a).comp
      ((readLeft_smooth hb N n).prodMk (readRight_smooth hb N n))

end Alternating.Memory

namespace Alternating.Memory

noncomputable def sequenceCode (b K : ℕ) (a : ℕ → ℕ) : ℝ :=
  fraction b ((List.range K).map a)

theorem sequenceCode_head (b K : ℕ) (a : ℕ → ℕ) :
    sequenceCode b (K + 1) a =
      ((a 0 : ℝ) + sequenceCode b K (fun j => a (j + 1))) / b := by
  simp [sequenceCode, List.range_succ_eq_map, Function.comp_def, Nat.succ_eq_add_one]

theorem sequenceCode_agree (b K : ℕ) {a c : ℕ → ℕ} (hac : ∀ j < K, a j = c j) :
    sequenceCode b K a = sequenceCode b K c := by
  unfold sequenceCode
  congr 1
  apply List.map_congr_left
  intro j hj
  exact hac j (List.mem_range.1 hj)

theorem sequenceCode_extend {b K : ℕ} (hb : 0 < b) {a : ℕ → ℕ} (ha : a K = 0) :
    sequenceCode b (K + 1) a = sequenceCode b K a := by
  simp [sequenceCode, List.range_succ, List.map_append, fraction_append hb, ha]

theorem sequenceCode_widen {b K L : ℕ} (hb : 0 < b) (hKL : K ≤ L)
    {a : ℕ → ℕ} (ha : ∀ j, K ≤ j → a j = 0) : sequenceCode b L a = sequenceCode b K a := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hKL
  clear hKL
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← Nat.add_assoc, sequenceCode_extend hb (ha _ (by omega)), ih]

theorem sequenceCode_pop {b K L : ℕ} (hb : 0 < b) (hKL : K ≤ L + 1)
    {a : ℕ → ℕ} (ha : ∀ j, K ≤ j → a j = 0) :
    sequenceCode b L (fun j => a (j + 1)) = (b : ℝ) * sequenceCode b K a - a 0 := by
  have h := sequenceCode_head b L a
  rw [sequenceCode_widen hb hKL ha] at h
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp at h
  linarith

def leftSequence (c : Configuration) (j : ℕ) : ℕ :=
  2 * c.tape (c.head - 1 - (j : ℤ))

def rightSequence (c : Configuration) (j : ℕ) : ℕ :=
  2 * c.tape (c.head + (j : ℤ))

theorem actualSequences_vanish (I : MachineInput) (n : ℕ) {j : ℕ}
    (hj : width I.2.length n ≤ j) :
    leftSequence (configurationAt I n) j = 0 ∧ rightSequence (configurationAt I n) j = 0 := by
  have h := actualBlock_full_tape I n hj
  simp only [leftSequence, rightSequence, h.1, h.2, mul_zero, and_self]

theorem leftSequence_moveRight_zero (c : Configuration) (p w : ℕ) :
    leftSequence (applyInstruction c (p, w, 2)) 0 = 2 * w := by
  have he : c.head + 2 - 1 - 1 = c.head := by omega
  simp [leftSequence, applyInstruction, he]

theorem leftSequence_moveRight_succ (c : Configuration) (p w j : ℕ) :
    leftSequence (applyInstruction c (p, w, 2)) (j + 1) = leftSequence c j := by
  change 2 * (Function.update c.tape c.head w) (c.head + 2 - 1 - 1 - ((j + 1 : ℕ) : ℤ)) = _
  have he : c.head + 2 - 1 - 1 - ((j + 1 : ℕ) : ℤ) = c.head - 1 - (j : ℤ) := by omega
  rw [he, Function.update_of_ne (by omega)]
  rfl

theorem rightSequence_moveRight (c : Configuration) (p w j : ℕ) :
    rightSequence (applyInstruction c (p, w, 2)) j = rightSequence c (j + 1) := by
  change 2 * (Function.update c.tape c.head w) (c.head + 2 - 1 + (j : ℤ)) = _
  rw [Function.update_of_ne (by omega)]
  congr 2
  dsimp [rightSequence]
  omega

theorem leftSequence_stay (c : Configuration) (p w j : ℕ) :
    leftSequence (applyInstruction c (p, w, 1)) j = leftSequence c j := by
  dsimp [leftSequence, applyInstruction]
  rw [Function.update_of_ne (by omega)]
  congr 2
  omega

theorem rightSequence_stay_zero (c : Configuration) (p w : ℕ) :
    rightSequence (applyInstruction c (p, w, 1)) 0 = 2 * w := by
  simp [rightSequence, applyInstruction]

theorem rightSequence_stay_succ (c : Configuration) (p w j : ℕ) :
    rightSequence (applyInstruction c (p, w, 1)) (j + 1) = rightSequence c (j + 1) := by
  dsimp [rightSequence, applyInstruction]
  rw [Function.update_of_ne (by omega)]
  congr 2
  omega

theorem leftSequence_moveLeft (c : Configuration) (p w j : ℕ) :
    leftSequence (applyInstruction c (p, w, 0)) j = leftSequence c (j + 1) := by
  dsimp [leftSequence, applyInstruction]
  rw [Function.update_of_ne (by omega)]
  congr 2
  omega

theorem rightSequence_moveLeft_zero (c : Configuration) (p w : ℕ) :
    rightSequence (applyInstruction c (p, w, 0)) 0 = leftSequence c 0 := by
  dsimp [rightSequence, leftSequence, applyInstruction]
  rw [Function.update_of_ne (by omega)]
  congr 2
  omega

theorem rightSequence_moveLeft_one (c : Configuration) (p w : ℕ) :
    rightSequence (applyInstruction c (p, w, 0)) 1 = 2 * w := by
  simp [rightSequence, applyInstruction]

theorem rightSequence_moveLeft_add_two (c : Configuration) (p w j : ℕ) :
    rightSequence (applyInstruction c (p, w, 0)) (j + 2) = rightSequence c (j + 1) := by
  dsimp [rightSequence, applyInstruction]
  rw [Function.update_of_ne (by omega)]
  congr 2
  omega


theorem tapeUpdate_correct {b K : ℕ} (hb : 0 < b) (c : Configuration) (i : Instruction)
    (hl : ∀ j, K ≤ j → leftSequence c j = 0)
    (hr : ∀ j, K ≤ j → rightSequence c j = 0) :
    tapeUpdate b (c.tape c.head) (c.tape (c.head - 1)) i
      (sequenceCode b K (leftSequence c)) (sequenceCode b K (rightSequence c)) =
    (sequenceCode b (K + 2) (leftSequence (applyInstruction c i)),
      sequenceCode b (K + 2) (rightSequence (applyInstruction c i))) := by
  rcases i with ⟨p, w, d⟩
  fin_cases d
  · change tapeUpdate b (c.tape c.head) (c.tape (c.head - 1)) (p, w, 0)
      (sequenceCode b K (leftSequence c)) (sequenceCode b K (rightSequence c)) =
        (sequenceCode b (K + 2) (leftSequence (applyInstruction c (p, w, 0))),
          sequenceCode b (K + 2) (rightSequence (applyInstruction c (p, w, 0))))
    have hA : sequenceCode b (K + 2) (leftSequence (applyInstruction c (p, w, 0))) =
        (b : ℝ) * sequenceCode b K (leftSequence c) - (leftSequence c 0 : ℝ) := by
      rw [show leftSequence (applyInstruction c (p, w, 0)) =
        (fun j => leftSequence c (j + 1)) from funext (leftSequence_moveLeft c p w)]
      exact sequenceCode_pop hb (by omega) hl
    have hB : sequenceCode b (K + 2) (rightSequence (applyInstruction c (p, w, 0))) =
        ((leftSequence c 0 : ℝ) + ((2 * w : ℝ) +
          ((b : ℝ) * sequenceCode b K (rightSequence c) - rightSequence c 0)) / b) / b := by
      rw [show K + 2 = (K + 1) + 1 by omega, sequenceCode_head,
        rightSequence_moveLeft_zero, sequenceCode_head]
      simp only [zero_add, Nat.add_assoc]
      rw [rightSequence_moveLeft_one]
      simp_rw [rightSequence_moveLeft_add_two]
      rw [sequenceCode_pop hb (by omega) hr]
      push_cast
      rfl
    rw [hA, hB]
    simp [tapeUpdate, leftSequence, rightSequence]
  · change tapeUpdate b (c.tape c.head) (c.tape (c.head - 1)) (p, w, 1)
      (sequenceCode b K (leftSequence c)) (sequenceCode b K (rightSequence c)) =
        (sequenceCode b (K + 2) (leftSequence (applyInstruction c (p, w, 1))),
          sequenceCode b (K + 2) (rightSequence (applyInstruction c (p, w, 1))))
    have hA : sequenceCode b (K + 2) (leftSequence (applyInstruction c (p, w, 1))) =
        sequenceCode b K (leftSequence c) := by
      rw [funext (leftSequence_stay c p w)]
      exact sequenceCode_widen hb (by omega) hl
    have hB : sequenceCode b (K + 2) (rightSequence (applyInstruction c (p, w, 1))) =
        ((2 * w : ℝ) + ((b : ℝ) * sequenceCode b K (rightSequence c) - rightSequence c 0)) / b := by
      rw [show K + 2 = (K + 1) + 1 by omega, sequenceCode_head, rightSequence_stay_zero]
      simp_rw [rightSequence_stay_succ]
      rw [sequenceCode_pop hb (by omega) hr]
      push_cast
      rfl
    rw [hA, hB]
    simp [tapeUpdate, rightSequence]
  · change tapeUpdate b (c.tape c.head) (c.tape (c.head - 1)) (p, w, 2)
      (sequenceCode b K (leftSequence c)) (sequenceCode b K (rightSequence c)) =
        (sequenceCode b (K + 2) (leftSequence (applyInstruction c (p, w, 2))),
          sequenceCode b (K + 2) (rightSequence (applyInstruction c (p, w, 2))))
    have hA : sequenceCode b (K + 2) (leftSequence (applyInstruction c (p, w, 2))) =
        ((2 * w : ℝ) + sequenceCode b K (leftSequence c)) / b := by
      rw [show K + 2 = (K + 1) + 1 by omega, sequenceCode_head, leftSequence_moveRight_zero]
      simp_rw [leftSequence_moveRight_succ]
      rw [sequenceCode_widen hb (by omega) hl]
      push_cast
      rfl
    have hB : sequenceCode b (K + 2) (rightSequence (applyInstruction c (p, w, 2))) =
        (b : ℝ) * sequenceCode b K (rightSequence c) - rightSequence c 0 := by
      rw [show rightSequence (applyInstruction c (p, w, 2)) =
        (fun j => rightSequence c (j + 1)) from funext (rightSequence_moveRight c p w)]
      exact sequenceCode_pop hb (by omega) hr
    rw [hA, hB]
    simp [tapeUpdate, rightSequence]


open scoped BigOperators

theorem width_succ (N n : ℕ) : width N (n + 1) = width N n + 2 := by
  dsimp [width]
  omega

@[simp] theorem actualBlock_leftCode_eq (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    (actualBlock I hI n).leftCode =
      sequenceCode (alphabetBase I.1) (width I.2.length n) (leftSequence (configurationAt I n)) := rfl

@[simp] theorem actualBlock_rightCode_eq (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    (actualBlock I hI n).rightCode =
      sequenceCode (alphabetBase I.1) (width I.2.length n) (rightSequence (configurationAt I n)) := rfl

theorem tapeUpdate_actual (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    let c := configurationAt I n
    tapeUpdate (alphabetBase I.1) (c.tape c.head) (c.tape (c.head - 1))
      (I.1.normalizedInstruction c.state (c.tape c.head))
      (actualBlock I hI n).leftCode (actualBlock I hI n).rightCode =
      ((actualBlock I hI (n + 1)).leftCode, (actualBlock I hI (n + 1)).rightCode) := by
  have hb : 0 < alphabetBase I.1 := by have := alphabetBase_ge_four I.1; omega
  have h := tapeUpdate_correct hb (configurationAt I n)
    (I.1.normalizedInstruction (configurationAt I n).state
      ((configurationAt I n).tape (configurationAt I n).head))
    (fun j hj => (actualSequences_vanish I n hj).1)
    (fun j hj => (actualSequences_vanish I n hj).2)
  rw [← I.1.step_eq_normalized, ← configurationAt_succ, ← width_succ] at h
  exact h

theorem branchCode_actual (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    let c := configurationAt I n
    branchCode (alphabetBase I.1) (width I.2.length (n + 1))
      (c.tape c.head) (c.tape (c.head - 1))
      (I.1.normalizedInstruction c.state (c.tape c.head))
      (actualBlock I hI n).leftCode (actualBlock I hI n).rightCode =
      (actualBlock I hI (n + 1)).code := by
  have hb : 0 < alphabetBase I.1 := by have := alphabetBase_ge_four I.1; omega
  dsimp only
  rw [branchCode, tapeUpdate_actual, (actualBlock I hI (n + 1)).code_formula hb]
  simp only [actualBlock, configurationAt_succ, Machine.step_eq_normalized, applyInstruction,
    Nat.cast_mul, Nat.cast_ofNat]

theorem sequenceCode_digit_cylinder {b K d : ℕ} (hb : 2 ≤ b) (hK : 0 < K)
    {f : ℕ → ℕ} (hf : ∀ j < K, Even (f j) ∧ f j + 2 ≤ b) (hd : f 0 = 2 * d) :
    (b : ℝ) * sequenceCode b K f ∈ Set.Icc (2 * (d : ℝ)) (2 * d + 1) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hallowed : AllowedDigits b ((List.range L).map (fun j => f (j + 1))) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hj' := List.mem_range.1 hj
    exact hf _ (by omega)
  have hrest0 := fraction_nonneg b ((List.range L).map (fun j => f (j + 1)))
  have hrest1 := fraction_lt_one hb hallowed
  change 0 ≤ sequenceCode b L (fun j => f (j + 1)) at hrest0
  change sequenceCode b L (fun j => f (j + 1)) < 1 at hrest1
  rw [sequenceCode_head, hd]
  have he : (b : ℝ) * (((2 * d : ℕ) : ℝ) + sequenceCode b L (fun j => f (j + 1))) / b =
      2 * d + sequenceCode b L (fun j => f (j + 1)) := by
    push_cast
    field_simp
  rw [← mul_div_assoc, he]
  exact ⟨by linarith, by linarith⟩

theorem actualBlock_left_cylinder (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    let c := configurationAt I n
    (alphabetBase I.1 : ℝ) * (actualBlock I hI n).leftCode ∈
      Set.Icc (2 * (c.tape (c.head - 1) : ℝ)) (2 * c.tape (c.head - 1) + 1) := by
  apply sequenceCode_digit_cylinder (by have := alphabetBase_ge_four I.1; omega)
    (by dsimp [width]; omega)
  · intro j _
    exact symbol_digit_allowed ((configurationAt_valid hI n).2 _)
  · simp

theorem actualBlock_right_cylinder (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    let c := configurationAt I n
    (alphabetBase I.1 : ℝ) * (actualBlock I hI n).rightCode ∈
      Set.Icc (2 * (c.tape c.head : ℝ)) (2 * c.tape c.head + 1) := by
  apply sequenceCode_digit_cylinder (by have := alphabetBase_ge_four I.1; omega)
    (by dsimp [width]; omega)
  · intro j _
    exact symbol_digit_allowed ((configurationAt_valid hI n).2 _)
  · simp

theorem branchCode_nonleft {b K a e : ℕ} {i : Instruction} (hi : i.2.2 ≠ 0) (A B : ℝ) :
    branchCode b K a e i A B = branchCode b K a 0 i A B := by
  dsimp [branchCode, tapeUpdate]
  split_ifs with h2 h1
  · rfl
  · rfl
  · have hd := i.2.2.isLt
    have hne2 : i.2.2.val ≠ 2 := fun h => h2 (Fin.ext h)
    have hne1 : i.2.2.val ≠ 1 := fun h => h1 (Fin.ext h)
    have hne0 : i.2.2.val ≠ 0 := fun h => hi (Fin.ext h)
    omega

theorem localBranchCode_exact {M : Machine} {K q a ell : ℕ} (hell : ell < M.symbolCount)
    {A B : ℝ} (hA : (alphabetBase M : ℝ) * A ∈ Set.Icc (2 * (ell : ℝ)) (2 * ell + 1)) :
    localBranchCode M K q a A B =
      branchCode (alphabetBase M) K a ell (M.normalizedInstruction q a) A B := by
  dsimp only [localBranchCode]
  split_ifs with hd
  · exact selector_sum hell hA _
  · exact (branchCode_nonleft hd A B).symm

theorem localWrite_at_cylinders {M : Machine} {N n q a ell : ℕ} {D : ℝ}
    (hq : q ≤ M.stateCount) (ha : a < M.symbolCount) (hell : ell < M.symbolCount)
    (hC : (alphabetBase M : ℝ) * readState (alphabetBase M) N n D ∈
      Set.Icc (2 * (q : ℝ)) (2 * q + 1))
    (hA : (alphabetBase M : ℝ) * readLeft (alphabetBase M) N n D ∈
      Set.Icc (2 * (ell : ℝ)) (2 * ell + 1))
    (hB : (alphabetBase M : ℝ) * readRight (alphabetBase M) N n D ∈
      Set.Icc (2 * (a : ℝ)) (2 * a + 1)) :
    localWrite M N n D = epsilon (alphabetBase M) N (n + 1) *
      branchCode (alphabetBase M) (width N (n + 1)) a ell (M.normalizedInstruction q a)
        (readLeft (alphabetBase M) N n D) (readRight (alphabetBase M) N n D) := by
  dsimp only [localWrite]
  simp_rw [digitSelector_selects hC, digitSelector_selects hB]
  have hq' : q < M.stateCount + 1 := by omega
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_range, ite_eq_left ha, ite_eq_left hq']
  rw [localBranchCode_exact hell hA]

theorem localWrite_exact (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    localWrite I.1 I.2.length n (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) =
      epsilon (alphabetBase I.1) I.2.length (n + 1) * (actualBlock I hI (n + 1)).code := by
  let c := configurationAt I n
  have hv := configurationAt_valid hI n
  rcases actualBlock_read I hI n with ⟨hC, hB, hA⟩
  change readState (alphabetBase I.1) I.2.length n
    (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) = (actualBlock I hI n).code at hC
  change readLeft (alphabetBase I.1) I.2.length n
    (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) = (actualBlock I hI n).leftCode at hA
  change readRight (alphabetBase I.1) I.2.length n
    (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) = (actualBlock I hI n).rightCode at hB
  have hb : 2 ≤ alphabetBase I.1 := by have := alphabetBase_ge_four I.1; omega
  rw [localWrite_at_cylinders hv.1 (hv.2 c.head) (hv.2 (c.head - 1))
      (by rw [hC]; exact (actualBlock I hI n).code_state_cylinder hb rfl)
      (by rw [hA]; exact actualBlock_left_cylinder I hI n)
      (by rw [hB]; exact actualBlock_right_cylinder I hI n), hA, hB, branchCode_actual]

end Alternating.Memory

end OAI
