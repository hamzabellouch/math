import OAI.Computability.MeanPayoff.Potential

namespace OAI

section

namespace MeanPayoff

def auxiliaryCalls (n Bmax : ℕ) : ℕ :=
  (16 * n * globalS Bmax + 2) * globalJ n Bmax +
  globalJ n Bmax * ((globalG Bmax + 1) * (globalS Bmax * (2 * globalJ n Bmax))) +
  globalListBound n Bmax * globalJ n Bmax

def chainBound (Bmax : ℕ) : ℕ := 8 * globalS Bmax * (Nat.log 2 Bmax + 2) + 1

def callBase (n Bmax : ℕ) : ℕ := chainBound Bmax * (auxiliaryCalls n Bmax + 1) + 1

def callBound (n Bmax d : ℕ) : ℕ := callBase n Bmax ^ (d + 1)

namespace CountedAlgorithm

theorem bounded_solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).Bounded
      ((widthPotential (globalS Bmax) I.width + 1) * (1 + auxiliaryCalls G.n Bmax * N)) := by
  rw [solveWidth]
  split_ifs with hB
  · apply Counted.bounded_mono (Counted.bounded_charge 1 (Counted.bounded_pure _ (N := 0)))
    exact Nat.mul_le_mul (by omega : 1 ≤ widthPotential (globalS Bmax) I.width + 1)
      (by omega : 1 ≤ 1 + auxiliaryCalls G.n Bmax * N)
  · have hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    have htight := bounded_tighten_global P hR lower hN I hb
    have hafter : ∀ T : InnerBox I,
        ((orientPlus (orient G P hR lower T.box) (globalJ G.n Bmax)).bind fun O =>
          (finishChoice G P hR lower T.box (by rw [T.width_eq]; exact hb) O
            (solveWidth G P hR lower
              (T.box.capHigh T.box.C T.box.C_positive
                (T.box.C_smaller (by rw [T.width_eq]; exact hb)).le))
            (solveWidth G P hR lower
              (T.box.capLow T.box.C T.box.C_positive
                (T.box.C_smaller (by rw [T.width_eq]; exact hb)).le))).map T.include).Bounded
        (globalJ G.n Bmax * ((globalG Bmax + 1) * (globalS Bmax * (2 * globalJ G.n Bmax * N))) +
          (globalListBound G.n Bmax * (globalJ G.n Bmax * N) +
            widthPotential (globalS Bmax) I.width * (1 + auxiliaryCalls G.n Bmax * N))) := by
      intro T
      have hK : 128 * globalS Bmax < T.box.width := by rw [T.width_eq]; exact hb
      have hpot : widthPotential (globalS Bmax) T.box.C + 1 ≤
          widthPotential (globalS Bmax) I.width := by
        have hp := T.box.C_potential hK
        rw [T.width_eq] at hp
        omega
      have hup := bounded_solveWidth G P hR lower hN
        (T.box.capHigh T.box.C T.box.C_positive (T.box.C_smaller hK).le)
      have hlo := bounded_solveWidth G P hR lower hN
        (T.box.capLow T.box.C T.box.C_positive (T.box.C_smaller hK).le)
      have hmul := Nat.mul_le_mul_right (1 + auxiliaryCalls G.n Bmax * N) hpot
      have hu := Counted.bounded_mono hup hmul
      have hl := Counted.bounded_mono hlo hmul
      have horient := bounded_orientPlus (bounded_orient_global G P hR lower hN T.box) (globalJ G.n Bmax)
      have hlen : (orientPlus (orient G P hR lower T.box) (globalJ G.n Bmax)).erase.All
          (fun O => O.exceptions.length ≤ globalListBound G.n Bmax) := by
        rw [erase_orientPlus, erase_orient]
        exact MeanPayoff.orientPlus_length G P hR (eraseLower lower) T.box
      apply Counted.bounded_bind_qualified _ _ horient hlen
      intro O hO
      apply Counted.bounded_map
      apply Counted.bounded_mono (bounded_finishChoice G P hR lower hN T.box hK O _ _ hu hl)
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hO) _
    have hbind := Counted.bounded_bind _ htight hafter
    apply Counted.bounded_mono (Counted.bounded_charge 1 hbind)
    unfold auxiliaryCalls
    ring_nf
    omega
termination_by I.width
 decreasing_by
  all_goals
    change T.box.C < I.width
    rw [← T.width_eq]
    exact T.box.C_smaller hK

theorem bounded_solveWidth_global (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) {N : ℕ} (hN : LowerBound lower N)
    (I : SolveBox G.n Bmax) :
    (solveWidth G P hR lower I).Bounded (chainBound Bmax * (1 + auxiliaryCalls G.n Bmax * N)) := by
  apply Counted.bounded_mono (bounded_solveWidth G P hR lower hN I)
  apply Nat.mul_le_mul_right
  have hp := widthPotential_bound (globalS Bmax) I.width (by have hs := globalS_large Bmax; omega)
  have hm := Nat.log_mono_right (b := 2) I.bounded
  have hh := Nat.mul_le_mul_left (8 * globalS Bmax) (Nat.add_le_add_right hm 2)
  unfold chainBound
  omega

theorem bounded_solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    (solve G P I).Bounded (callBound G.n Bmax (parameterRank P.parameter)) := by
  rw [solve]
  have hb : 1 ≤ callBase G.n Bmax := by unfold callBase; omega
  split_ifs with hR
  · apply Counted.bounded_mono (Counted.bounded_charge 1 (Counted.bounded_pure _ (N := 0)))
    have hh := Nat.one_le_pow (parameterRank P.parameter + 1) _ hb
    simpa only [callBound, Nat.add_zero] using hh
  · have hlow : LowerBound (P := P) (Bmax := Bmax) (fun Q _ K => solve G Q K)
        (callBase G.n Bmax ^ parameterRank P.parameter) := by
      intro Q hq K
      apply Counted.bounded_mono (bounded_solve G Q K)
      apply Nat.pow_le_pow_right hb
      omega
    apply Counted.bounded_mono
      (bounded_solveWidth_global G P (le_of_not_gt hR) _ hlow I)
    have hp : 1 ≤ callBase G.n Bmax ^ parameterRank P.parameter :=
      Nat.one_le_pow _ _ hb
    unfold callBound
    rw [pow_succ]
    have hkp := Nat.mul_le_mul_left (chainBound Bmax) hp
    have hf : chainBound Bmax * (auxiliaryCalls G.n Bmax + 1) ≤ callBase G.n Bmax := by
      unfold callBase
      omega
    calc
      _ ≤ (chainBound Bmax * (auxiliaryCalls G.n Bmax + 1)) *
          callBase G.n Bmax ^ parameterRank P.parameter := by nlinarith only [hkp]
      _ ≤ _ := by
        simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left (callBase G.n Bmax ^ parameterRank P.parameter) hf
termination_by parameterRank P.parameter

end CountedAlgorithm


theorem parameterRank_nat_bound (r : ℕ) :
    parameterRank (r : ℚ) ≤ 8 * Nat.clog 2 (r + 1) := by
  apply Nat.find_min' (parameter_rank_exists (r : ℚ))
  have hpow : (9 / 10 : ℚ) ^ 8 ≤ 1 / 2 := by norm_num
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ (9 / 10) ^ 8) hpow
    (Nat.clog 2 (r + 1))
  rw [← pow_mul] at hh
  have hr : (r : ℚ) < (2 : ℚ) ^ Nat.clog 2 (r + 1) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self r) (Nat.le_pow_clog (by norm_num : 1 < 2) (r + 1)))
  have hp := mul_lt_mul_of_pos_left hr
    (by positivity : (0 : ℚ) < (1 / 2 : ℚ) ^ Nat.clog 2 (r + 1))
  have he : (1 / 2 : ℚ) ^ Nat.clog 2 (r + 1) * (2 : ℚ) ^ Nat.clog 2 (r + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [he] at hp
  exact (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg r)).trans_lt hp

theorem rootRank_bound (G : Game) :
    parameterRank (rootBudgets G).parameter ≤ 24 * Nat.clog 2 (G.n + 1) := by
  rw [rootBudgets_parameter]
  have hr := parameterRank_nat_bound (G.n ^ 3)
  have hc : Nat.clog 2 (G.n ^ 3 + 1) ≤ 3 * Nat.clog 2 (G.n + 1) := by
    apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr
    have hn := Nat.le_pow_clog (by norm_num : 1 < 2) (G.n + 1)
    have hp := Nat.pow_le_pow_left hn 3
    rw [← pow_mul, Nat.mul_comm (Nat.clog 2 (G.n + 1)) 3] at hp
    exact (by nlinarith : G.n ^ 3 + 1 ≤ (G.n + 1) ^ 3).trans hp
  have h := Nat.mul_le_mul_left 8 hc
  norm_num only [Nat.cast_pow] at hr
  omega


namespace SolveBox

def SafeEndpoints {n Bmax : ℕ} (I : SolveBox n Bmax) : Prop :=
  ∀ i, -(Bmax : ℤ) + I.width ≤ 6 * I.a i ∧
    6 * I.b i + I.width ≤ 7 * Bmax

theorem safe_of_inside {n Bmax : ℕ} {I K : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (ha : I.a ≤ K.a) (hb : K.b ≤ I.b)
    (hw : K.width ≤ I.width) : K.SafeEndpoints := by
  intro i
  have hi := hI i
  have hai : I.a i ≤ K.a i := ha i
  have hbi : K.b i ≤ I.b i := hb i
  have hw' : (K.width : ℤ) ≤ I.width := by exact_mod_cast hw
  omega

theorem safe_centered {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (q : BoxVector I) (A : ℕ) (hA : 0 < A)
    (hmax : 2 * A ≤ Bmax) (hr : 8 * A ≤ I.width) :
    (centered q.val A hA hmax).SafeEndpoints := by
  intro i
  have hi := hI i
  have hqa : I.a i ≤ q.val i := q.property.1 i
  have hqb : q.val i ≤ I.b i := q.property.2 i
  have hr' : (8 : ℤ) * A ≤ I.width := by exact_mod_cast hr
  dsimp only [centered]
  push_cast
  omega

theorem safe_withFloor {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (q : BoxVector I) : (I.withFloor q).SafeEndpoints :=
  safe_of_inside hI q.property.1 (le_refl _) (le_refl _)

theorem safe_withCeiling {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (q : BoxVector I) : (I.withCeiling q).SafeEndpoints :=
  safe_of_inside hI (le_refl _) q.property.2 (le_refl _)

theorem safe_capLow {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (C : ℕ) (hC : 0 < C) (hle : C ≤ I.width) :
    (I.capLow C hC hle).SafeEndpoints :=
  safe_of_inside hI (le_refl _) (fun _ => min_le_left _ _) hle

theorem safe_capHigh {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (C : ℕ) (hC : 0 < C) (hle : C ≤ I.width) :
    (I.capHigh C hC hle).SafeEndpoints :=
  safe_of_inside hI (fun _ => le_max_left _ _) (le_refl _) hle

theorem eight_D_le {n Bmax : ℕ} (I : SolveBox n Bmax) : 8 * I.D ≤ I.width := by
  have hd := Nat.div_mul_le_self I.width (32 * globalS Bmax)
  have hs := globalS_large Bmax
  change 8 * (I.width / (32 * globalS Bmax)) ≤ I.width
  nlinarith

theorem safe_narrowCentered {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (I.narrowCentered hB q.val).SafeEndpoints :=
  safe_centered hI q I.D _ _ I.eight_D_le

theorem safe_wideCentered {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) :
    (I.wideCentered hB q.val).SafeEndpoints := by
  apply safe_centered hI q I.E
  exact Nat.mul_div_le I.width 8

theorem safe_vector_bound {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (q : BoxVector I) (i : Fin n) :
    -(Bmax : ℤ) ≤ 6 * q.val i ∧ 6 * q.val i ≤ 7 * Bmax := by
  have hi := hI i
  have ha : I.a i ≤ q.val i := q.property.1 i
  have hb : q.val i ≤ I.b i := q.property.2 i
  omega

theorem safe_vector_abs {n Bmax : ℕ} {I : SolveBox n Bmax}
    (hI : I.SafeEndpoints) (q : BoxVector I) (i : Fin n) :
    |q.val i| ≤ 2 * (Bmax : ℤ) := by
  have h := safe_vector_bound hI q i
  rw [abs_le]
  omega

end SolveBox

theorem rootBox_safe (G : Game) : (rootBox G).SafeEndpoints := by
  intro i
  dsimp only [rootBox]
  rw [Int.toNat_of_nonneg (topWidth_positive G).le]
  constructor <;> omega

inductive ReachableBox (G : Game) : SolveBox G.n (topWidth G).toNat → Prop
  | root : ReachableBox G (rootBox G)
  | inside {I K} : ReachableBox G I → I.a ≤ K.a → K.b ≤ I.b → K.width ≤ I.width →
      ReachableBox G K
  | centered {I} (q : BoxVector I) (A : ℕ) (hA : 0 < A)
      (hm : 2 * A ≤ (topWidth G).toNat) : ReachableBox G I → 8 * A ≤ I.width →
      ReachableBox G (SolveBox.centered q.val A hA hm)

theorem ReachableBox.safe {G : Game} {I} (h : ReachableBox G I) : I.SafeEndpoints := by
  induction h with
  | root => exact rootBox_safe G
  | inside _ ha hb hw ih => exact SolveBox.safe_of_inside ih ha hb hw
  | centered q A hA hm _ hr ih => exact SolveBox.safe_centered ih q A hA hm hr

end MeanPayoff
end

end OAI
