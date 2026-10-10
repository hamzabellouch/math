import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowForceBalls

namespace OAI

/-! Interval evaluation of every derivative of the actual initialized slow
force, from the finite program and fast names for viscosity and the query. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

theorem slowClockTime_pos {y : SpaceTime} (hy : -(1 / 2 : ℝ) < y.1) :
    0 < 1 + y.1 := by linarith

def slowEvaluationBalls {y : SpaceTime} (loader body : Input)
    (hl : ValidInput loader) (hb : ValidInput body) (a : ℕ → ℚ)
    (b : ℕ → RationalSpaceTime) (hy : -(1 / (2 : ℕ) : ℝ) < y.1)
    (hname : IsFastName b y) (α : List (Fin 4)) (N : ℕ) (j : Fin 3) : QBall :=
  letI := ShearFlows.twoAtLeastTwo
  let c := clockPointName b (slowClockTime_pos hy) hname
  let n := (timeSpaceWord α).1
  let β := (timeSpaceWord α).2
  let speed := realNameBall (reciprocalClockName b) N
  let q := phaseBalls 2 (quadraticPhaseBalls loader body hl hb c β) n 0 N j
  let d := phaseBalls 1 (viscousPhaseBalls loader body hl hb c β) n 0 N j
  ((speed.pow (2 + n)).mul q).add
    ((QBall.exact (-1)).mul
      ((realNameBall a N).mul ((speed.pow (1 + n)).mul d)))

theorem slowEvaluationBalls_contains {y : SpaceTime} {loader body : Input}
    (hl : ValidInput loader) (hb : ValidInput body) {ν : ℝ} {a : ℕ → ℚ}
    (ha : IsFastRealName a ν) (b : ℕ → RationalSpaceTime)
    (hy : -(1 / 2 : ℝ) < y.1) (hname : IsFastName b y)
    (α : List (Fin 4)) (N : ℕ) (j : Fin 3) :
    (slowEvaluationBalls loader body hl hb a b hy hname α N j).Contains
      (mixedDerivative (force ν (slowFromRest (initializedProgram loader body))) α y j) := by
  let V := initializedProgram loader body
  let n := (timeSpaceWord α).1
  let β := (timeSpaceWord α).2
  let c := clockPointName b (by linarith : 0 < 1 + y.1) hname
  have hc : IsFastName c (logClock y.1, y.2) := clockPointName_spec b _ hname
  have hs : ContDiff ℝ ∞ V := initializedProgram_smooth hl hb
  have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0 :=
    fun _ ht x => initializedProgram_zero_extend loader body ht x
  have hQ := (spatialPhase_smooth (quadraticPhase_smooth hs) β).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => y.2)))
  have hD := (spatialPhase_smooth (viscousPhase_smooth hs) β).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => y.2)))
  have hq := phaseBalls_contains 2 hQ (logClock y.1)
    (quadraticPhaseBalls_contains hl hb hc β) n 0 N j
  have hd := phaseBalls_contains 1 hD (logClock y.1)
    (viscousPhaseBalls_contains hl hb hc β) n 0 N j
  have hv := realNameBall_contains (reciprocalClockName_spec b (by linarith) hname) N
  have h := QBall.contains_add (QBall.contains_mul (QBall.contains_pow hv (2 + n)) hq)
    (QBall.contains_mul (QBall.contains_exact (-1))
      (QBall.contains_mul (realNameBall_contains ha N)
        (QBall.contains_mul (QBall.contains_pow hv (1 + n)) hd)))
  rw [mixedDerivative_perm (force_smooth (slowFromRest_smooth hs hz) ν)
    (timeSpaceWord_perm α)]
  rw [slowFromRest_mixed_formula hs hz (initializedProgram_zero_advection hl hb) ν _ _ hy]
  simpa only [slowEvaluationBalls, iteratedDeriv_zero, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_neg, Rat.cast_one, neg_one_mul, sub_eq_add_neg,
    n, β, c, Function.comp_def, id_eq] using h

theorem slowEvaluationBalls_converges {y : SpaceTime} {loader body : Input}
    (hl : ValidInput loader) (hb : ValidInput body) {ν : ℝ} {a : ℕ → ℚ}
    (ha : IsFastRealName a ν) (b : ℕ → RationalSpaceTime)
    (hy : -(1 / 2 : ℝ) < y.1) (hname : IsFastName b y)
    (α : List (Fin 4)) (j : Fin 3) :
    QBall.Converges (fun N => slowEvaluationBalls loader body hl hb a b hy hname α N j)
      (mixedDerivative (force ν (slowFromRest (initializedProgram loader body))) α y j) := by
  let V := initializedProgram loader body
  let n := (timeSpaceWord α).1
  let β := (timeSpaceWord α).2
  let c := clockPointName b (by linarith : 0 < 1 + y.1) hname
  have hc : IsFastName c (logClock y.1, y.2) := clockPointName_spec b _ hname
  have hs : ContDiff ℝ ∞ V := initializedProgram_smooth hl hb
  have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0 :=
    fun _ ht x => initializedProgram_zero_extend loader body ht x
  have hQ := (spatialPhase_smooth (quadraticPhase_smooth hs) β).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => y.2)))
  have hD := (spatialPhase_smooth (viscousPhase_smooth hs) β).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => y.2)))
  have hq := phaseBalls_converges 2 hQ (logClock y.1)
    (quadraticPhaseBalls_converges hl hb hc β) n 0 j
  have hd := phaseBalls_converges 1 hD (logClock y.1)
    (viscousPhaseBalls_converges hl hb hc β) n 0 j
  have hv := realNameBall_converges (reciprocalClockName_spec b (by linarith) hname)
  have h := ((hv.pow (2 + n)).mul hq).add
    ((QBall.converges_exact (-1)).mul
      ((realNameBall_converges ha).mul ((hv.pow (1 + n)).mul hd)))
  rw [mixedDerivative_perm (force_smooth (slowFromRest_smooth hs hz) ν)
    (timeSpaceWord_perm α)]
  rw [slowFromRest_mixed_formula hs hz (initializedProgram_zero_advection hl hb) ν _ _ hy]
  simpa only [slowEvaluationBalls, iteratedDeriv_zero, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_neg, Rat.cast_one, neg_one_mul, sub_eq_add_neg,
    n, β, c, Function.comp_def, id_eq] using h

end ForcedComputation

end OAI
