import OAI.LinearAlgebra.MatrixMultiplication.Numerical.AllFieldCertificates

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

inductive Op where
  | constant (q : ℚ)
  | add (i j : ℕ)
  | neg (i : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  | log (i : ℕ)
  deriving DecidableEq, Repr

instance : Hashable Op where
  hash
    | .constant q => hash ((0 : ℕ), q.num, q.den)
    | .add i j => hash ((1 : ℕ), i, j)
    | .neg i => hash ((2 : ℕ), i)
    | .mul i j => hash ((3 : ℕ), i, j)
    | .inv i => hash ((4 : ℕ), i)
    | .log i => hash ((5 : ℕ), i)

abbrev Program := Array Op

noncomputable def Op.value (v : ℕ → ℝ) : Op → ℝ
  | .constant q => q
  | .add i j => v i + v j
  | .neg i => -v i
  | .mul i j => v i * v j
  | .inv i => (v i)⁻¹
  | .log i => Real.log (v i)

noncomputable def Program.eval (p : Program) : Array ℝ :=
  p.foldl (fun v op => v.push (op.value (fun i => v[i]?.getD 0))) #[]

def contains (a b : Ball) : Bool :=
  decide (|a.center - b.center| + a.radius ≤ b.radius)

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

noncomputable def polynomial (t : ℝ) : List ℚ → ℝ
  | [] => 0
  | a :: as => (a : ℝ) + t * polynomial t as

def traceHead (trace : List Ball) : Ball := trace.headD (.exact 0)

def checkPolynomial (t : Ball) : List ℚ → List Ball → Bool
  | [], [] => true
  | a :: as, b :: bs =>
      contains (Ball.add (.exact a) (Ball.mul t (traceHead bs))) b &&
        checkPolynomial t as bs
  | _, _ => false

theorem checkPolynomial_sound {t : Ball} {x : ℝ} (hx : t.Encloses x)
    (as : List ℚ) (trace : List Ball)
    (h : checkPolynomial t as trace = true) :
    (traceHead trace).Encloses (polynomial x as) := by
  induction as generalizing trace with
  | nil =>
      cases trace with
      | nil => simpa [traceHead, polynomial] using Ball.exact_sound 0
      | cons b bs => simp [checkPolynomial] at h
  | cons a as ih =>
      cases trace with
      | nil => simp [checkPolynomial] at h
      | cons b bs =>
          simp only [checkPolynomial, Bool.and_eq_true] at h
          exact contains_sound
            (Ball.add_sound (Ball.exact_sound a) (Ball.mul_sound hx (ih bs h.2))) h.1

def logCoefficients : List ℚ :=
  (List.range 24).map (fun i => 1 / (2 * (i : ℚ) + 1))

theorem realApprox_eq_polynomial (x : ℝ) :
    realApprox 48 x =
      2 * ((x - 1) / (x + 1)) *
        polynomial (((x - 1) / (x + 1)) ^ 2) logCoefficients := by
  simp only [realApprox, sumPower]
  norm_num [Finset.sum_range_succ, logCoefficients, List.range_succ,
    polynomial, List.map_append, List.foldr_append]
  ring

theorem normalized_log_error_48 (x : ℝ) (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    |Real.log x - realApprox 48 x| < 1 / (2 : ℝ) ^ 72 := by
  obtain ⟨ht0, ht3⟩ := normalized_variable_bounds x hlo hhi
  apply lt_of_le_of_lt (normalized_log_error x hlo hhi 48)
  calc
    _ ≤ 2 * (((1 : ℝ) / 3) ^ 49 / (1 - 1 / 3)) := by gcongr
    _ < 1 / (2 : ℝ) ^ 72 := by norm_num

def pad (b : Ball) (error : ℚ) : Ball := ⟨b.center, b.radius + error⟩

theorem pad_sound {b : Ball} {x y : ℝ} {error : ℚ}
    (hx : b.Encloses x) (hxy : |y - x| ≤ (error : ℝ)) :
    (pad b error).Encloses y := by
  unfold Ball.Encloses pad at *
  simp only [Rat.cast_add]
  calc
    _ = |(y - x) + (x - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |y - x| + |x - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (error : ℝ) + (b.radius : ℝ) := add_le_add hxy hx
    _ = _ := by ring

def logVariable (m : ℚ) : ℚ := (m - 1) / (m + 1)

def normalizedLogBall (m : ℚ) (trace : List Ball) : Ball :=
  pad (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)) (1 / 2 ^ 72)

theorem normalizedLogBall_sound {m : ℚ} {trace : List Ball}
    (hlo : 1 ≤ m) (hhi : m ≤ 2)
    (hc : checkPolynomial (.exact (logVariable m ^ 2)) logCoefficients trace = true) :
    (normalizedLogBall m trace).Encloses (Real.log (m : ℝ)) := by
  have hp := checkPolynomial_sound (Ball.exact_sound (logVariable m ^ 2))
    logCoefficients trace hc
  have hv : (logVariable m : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) + 1) := by
    simp [logVariable]
  have ha : (Ball.mul (.exact (2 * logVariable m)) (traceHead trace)).Encloses
      (realApprox 48 (m : ℝ)) := by
    rw [realApprox_eq_polynomial]
    convert Ball.mul_sound (Ball.exact_sound (2 * logVariable m)) hp using 1
    simp [hv]
  apply pad_sound ha
  have h := (normalized_log_error_48 (m : ℝ)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)).le
  simpa using h

structure LogWitness where
  exponent : ℤ
  mantissa : ℚ
  trace : List Ball
  deriving DecidableEq

def logResult (two a : Ball) (w : LogWitness) : Ball :=
  pad (Ball.add (normalizedLogBall w.mantissa w.trace)
    (Ball.mul (.exact w.exponent) two)) (a.radius / a.lower)

def checkLog (two a b : Ball) (w : LogWitness) : Bool :=
  decide (0 < a.lower ∧ 1 ≤ w.mantissa ∧ w.mantissa ≤ 2 ∧
    a.center = w.mantissa * (2 : ℚ) ^ w.exponent) &&
  checkPolynomial (.exact (logVariable w.mantissa ^ 2)) logCoefficients w.trace &&
  contains (logResult two a w) b

theorem checkLog_sound {two a b : Ball} {w : LogWitness} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) := by
  simp only [checkLog, Bool.and_eq_true] at h
  obtain ⟨hpos, hlo, hhi, heq⟩ := of_decide_eq_true h.1.1
  have hm : (0 : ℝ) < w.mantissa := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hlo)
  have heq' : (a.center : ℝ) = (w.mantissa : ℝ) * (2 : ℝ) ^ w.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) heq
  have hlog : Real.log (a.center : ℝ) =
      Real.log (w.mantissa : ℝ) + (w.exponent : ℝ) * Real.log 2 := by
    rw [heq', Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have hcenter : (Ball.add (normalizedLogBall w.mantissa w.trace)
      (Ball.mul (.exact w.exponent) two)).Encloses (Real.log (a.center : ℝ)) := by
    rw [hlog]
    exact Ball.add_sound (normalizedLogBall_sound hlo hhi h.1.2)
      (by simpa using Ball.mul_sound (Ball.exact_sound (w.exponent : ℚ)) htwo)
  exact contains_sound (pad_sound hcenter (log_center_lipschitz hx hpos)) h.2

structure Witness where
  ball : Ball
  logarithm : Option LogWitness := none
  deriving DecidableEq

def ballAt (v : Array Ball) (i : ℕ) : Ball := v[i]?.getD (.exact 0)

def checkStep (two : Ball) (v : Array Ball) (op : Op) (w : Witness) : Bool :=
  match op with
  | .constant q => contains (.exact q) w.ball
  | .add i j => contains (Ball.add (ballAt v i) (ballAt v j)) w.ball
  | .neg i => contains (Ball.neg (ballAt v i)) w.ball
  | .mul i j => contains (Ball.mul (ballAt v i) (ballAt v j)) w.ball
  | .inv i => decide (0 < (ballAt v i).lower) && contains (Ball.inv (ballAt v i)) w.ball
  | .log i => match w.logarithm with
    | none => false
    | some lw => checkLog two (ballAt v i) w.ball lw

def Related (bs : Array Ball) (vs : Array ℝ) : Prop :=
  bs.size = vs.size ∧ ∀ i, (ballAt bs i).Encloses (vs[i]?.getD 0)

theorem checkStep_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {bs : Array Ball} {vs : Array ℝ} (hr : Related bs vs)
    {op : Op} {w : Witness} (hc : checkStep two bs op w = true) :
    w.ball.Encloses (op.value (fun i => vs[i]?.getD 0)) := by
  cases op with
  | constant q => exact contains_sound (Ball.exact_sound q) hc
  | add i j => exact contains_sound (Ball.add_sound (hr.2 i) (hr.2 j)) hc
  | neg i => exact contains_sound (Ball.neg_sound (hr.2 i)) hc
  | mul i j => exact contains_sound (Ball.mul_sound (hr.2 i) (hr.2 j)) hc
  | inv i =>
      simp only [checkStep, Bool.and_eq_true] at hc
      exact contains_sound (Ball.inv_sound (hr.2 i) (of_decide_eq_true hc.1)) hc.2
  | log i =>
      cases hw : w.logarithm with
      | none => simp [checkStep, hw] at hc
      | some lw =>
          simp only [checkStep, hw] at hc
          exact checkLog_sound htwo (hr.2 i) hc

theorem Related.push {bs : Array Ball} {vs : Array ℝ} (hr : Related bs vs)
    {b : Ball} {v : ℝ} (hv : b.Encloses v) : Related (bs.push b) (vs.push v) := by
  constructor
  · simpa using hr.1
  · intro i
    simp only [ballAt, Array.getElem?_push, ← hr.1]
    split_ifs with hi
    · exact hv
    · exact hr.2 i

theorem Related.empty : Related #[] #[] := by
  constructor
  · rfl
  · intro i
    simpa [ballAt] using Ball.exact_sound 0

noncomputable def evalFrom (ops : List Op) (vs : Array ℝ) : Array ℝ :=
  ops.foldl (fun v op => v.push (op.value (fun i => v[i]?.getD 0))) vs

def ballsFrom (ws : List Witness) (bs : Array Ball) : Array Ball :=
  ws.foldl (fun b w => b.push w.ball) bs

def checkFrom (two : Ball) : List Op → List Witness → Array Ball → Bool
  | [], [], _ => true
  | op :: ops, w :: ws, bs =>
      checkStep two bs op w && checkFrom two ops ws (bs.push w.ball)
  | _, _, _ => false

theorem checkFrom_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    (ops : List Op) (ws : List Witness) {bs : Array Ball} {vs : Array ℝ}
    (hr : Related bs vs) (hc : checkFrom two ops ws bs = true) :
    Related (ballsFrom ws bs) (evalFrom ops vs) := by
  induction ops generalizing ws bs vs with
  | nil =>
      cases ws with
      | nil => exact hr
      | cons w ws => simp [checkFrom] at hc
  | cons op ops ih =>
      cases ws with
      | nil => simp [checkFrom] at hc
      | cons w ws =>
          simp only [checkFrom, Bool.and_eq_true] at hc
          exact ih ws (hr.push (checkStep_sound htwo hr hc.1)) hc.2

def checkProgram (two : Ball) (p : Program) (ws : List Witness) : Bool :=
  checkFrom two p.toList ws #[]

theorem checkProgram_sound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {p : Program} {ws : List Witness} (hc : checkProgram two p ws = true) :
    Related (ballsFrom ws #[]) p.eval := by
  have h := checkFrom_sound htwo p.toList ws Related.empty hc
  simpa only [evalFrom, Array.foldl_toList, Program.eval] using h

theorem evalFrom_append (as bs : List Op) (v : Array ℝ) :
    evalFrom (as ++ bs) v = evalFrom bs (evalFrom as v) := by
  simp [evalFrom, List.foldl_append]

theorem ballsFrom_append (as bs : List Witness) (v : Array Ball) :
    ballsFrom (as ++ bs) v = ballsFrom bs (ballsFrom as v) := by
  simp [ballsFrom, List.foldl_append]

theorem checkFrom_append (two : Ball) (as bs : List Op) (aw bw : List Witness)
    (v : Array Ball) (hlen : as.length = aw.length) :
    checkFrom two (as ++ bs) (aw ++ bw) v =
      (checkFrom two as aw v && checkFrom two bs bw (ballsFrom aw v)) := by
  induction as generalizing aw v with
  | nil =>
      cases aw with
      | nil => simp [checkFrom, ballsFrom]
      | cons w ws => simp at hlen
  | cons a as ih =>
      cases aw with
      | nil => simp at hlen
      | cons w ws =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simp only [List.cons_append, checkFrom, ballsFrom, List.foldl_cons]
          rw [ih ws (v.push w.ball) hlen]
          exact (Bool.and_assoc _ _ _).symm

theorem checked_upper_bound {two : Ball} (htwo : two.Encloses (Real.log 2))
    {p : Program} {ws : List Witness} (hc : checkProgram two p ws = true)
    (i : ℕ) (bound : ℚ) (hb : (ballAt (ballsFrom ws #[]) i).upper ≤ bound) :
    p.eval[i]?.getD 0 ≤ (bound : ℝ) := by
  have hv := (Ball.bounds ((checkProgram_sound htwo hc).2 i)).2
  exact hv.trans (by exact_mod_cast hb)

theorem checked_below_target {two : Ball} (htwo : two.Encloses (Real.log 2))
    {p : Program} {ws : List Witness} (hc : checkProgram two p ws = true)
    (i : ℕ) (hb : (ballAt (ballsFrom ws #[]) i).upper < (2371054887 : ℚ) / 10 ^ 9) :
    p.eval[i]?.getD 0 < (2371054887 : ℝ) / 10 ^ 9 := by
  have hv := (Ball.bounds ((checkProgram_sound htwo hc).2 i)).2
  apply lt_of_le_of_lt hv
  have hcast : ((ballAt (ballsFrom ws #[]) i).upper : ℝ) <
      (((2371054887 : ℚ) / 10 ^ 9 : ℚ) : ℝ) := Rat.cast_lt.mpr hb
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast

end MatrixMultiplication.AllFieldCertificates.Replay

end OAI
