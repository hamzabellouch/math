import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

/-! A terminating rational search for the logarithm of a positive named real.
The search compares certified exponential balls with the input name; it never
uses a test of equality or ordering on real numbers. -/

open Filter
open scoped Topology
open ShearFlows

namespace ForcedComputation

def logSearchData (n : ℕ) : ℚ × ℚ × ℕ :=
  (Encodable.decode (α := ℚ × ℚ × ℕ) n).getD (0, 0, 0)

def logReady (a : ℕ → ℚ) (ε : ℚ) (n : ℕ) : Prop :=
  let d := logSearchData n
  d.1 < d.2.1 ∧ d.2.1 - d.1 < 2 * ε ∧
    (expBall d.1 d.2.2).center + (expBall d.1 d.2.2).radius <
      a d.2.2 - (2 : ℚ) ^ (-(d.2.2 : ℤ)) ∧
    a d.2.2 + (2 : ℚ) ^ (-(d.2.2 : ℤ)) <
      (expBall d.2.1 d.2.2).center - (expBall d.2.1 d.2.2).radius

instance (a : ℕ → ℚ) (ε : ℚ) (n : ℕ) : Decidable (logReady a ε n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

noncomputable section

theorem errorTolerance_tendsto : Tendsto errorTolerance atTop (𝓝 (0 : ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  change Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0)
  simpa only [one_div, inv_pow] using h

theorem fastRealName_tendsto {x : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a x) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 x) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg)
    (fun n => by simpa only [Real.dist_eq, abs_sub_comm] using ha n)
    errorTolerance_tendsto

theorem logReady_exists {x : ℝ} (hx : 0 < x) {a : ℕ → ℚ}
    (ha : IsFastRealName a x) {ε : ℚ} (hε : 0 < ε) : ∃ n, logReady a ε n := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨l, hl₁, hl₂⟩ := exists_rat_btwn (show Real.log x - ε < Real.log x by linarith)
  obtain ⟨u, hu₁, hu₂⟩ := exists_rat_btwn (show Real.log x < Real.log x + ε by linarith)
  have hlx : Real.exp l < x := (Real.exp_lt_exp.mpr hl₂).trans_eq (Real.exp_log hx)
  have hux : x < Real.exp u := (Real.exp_log hx).symm.trans_lt (Real.exp_lt_exp.mpr hu₁)
  have hleft := ((expBall_converges l).1.add (expBall_converges l).2).eventually_lt
    ((fastRealName_tendsto ha).sub errorTolerance_tendsto) (by simpa using hlx)
  have hright := ((fastRealName_tendsto ha).add errorTolerance_tendsto).eventually_lt
    ((expBall_converges u).1.sub (expBall_converges u).2) (by simpa using hux)
  obtain ⟨k, hkL, hkU⟩ := (hleft.and hright).exists
  refine ⟨Encodable.encode (l, u, k), ?_⟩
  have hd : logSearchData (Encodable.encode (l, u, k)) = (l, u, k) := by
    simp only [logSearchData, Encodable.encodek, Option.getD_some]
  rw [logReady, hd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast hl₂.trans hu₁
  · exact_mod_cast (show (u : ℝ) - l < 2 * (ε : ℝ) by linarith)
  · have he : (((2 : ℚ) ^ (-(k : ℤ))) : ℝ) = errorTolerance k := by
      simp [errorTolerance, zpow_neg, zpow_natCast]
    exact_mod_cast (show (expBall l k).center + (expBall l k).radius <
        (a k : ℝ) - ((2 : ℚ) ^ (-(k : ℤ)) : ℝ) by simpa only [he] using hkL)
  · have he : (((2 : ℚ) ^ (-(k : ℤ))) : ℝ) = errorTolerance k := by
      simp [errorTolerance, zpow_neg, zpow_natCast]
    exact_mod_cast (show (a k : ℝ) + ((2 : ℚ) ^ (-(k : ℤ)) : ℝ) <
        (expBall u k).center - (expBall u k).radius by simpa only [he] using hkU)

end

/-- Rational bisection is not required: an exhaustive finite search of strict
certified brackets terminates for every positive input. -/
def logApprox {x : ℝ} (a : ℕ → ℚ) (hx : 0 < x) (ha : IsFastRealName a x)
    (ε : ℚ) (hε : 0 < ε) : ℚ :=
  let d := logSearchData (Nat.find (logReady_exists hx ha hε))
  (d.1 + d.2.1) / 2

noncomputable section

theorem logApprox_spec {x : ℝ} (a : ℕ → ℚ) (hx : 0 < x) (ha : IsFastRealName a x)
    (ε : ℚ) (hε : 0 < ε) : |Real.log x - (logApprox a hx ha ε hε : ℝ)| ≤ ε := by
  let n := Nat.find (logReady_exists hx ha hε)
  let d := logSearchData n
  obtain ⟨hlu, hwidth, hl, hu⟩ := Nat.find_spec (logReady_exists hx ha hε)
  change d.1 < d.2.1 at hlu
  change d.2.1 - d.1 < 2 * ε at hwidth
  change (expBall d.1 d.2.2).center + (expBall d.1 d.2.2).radius <
    a d.2.2 - (2 : ℚ) ^ (-(d.2.2 : ℤ)) at hl
  change a d.2.2 + (2 : ℚ) ^ (-(d.2.2 : ℤ)) <
    (expBall d.2.1 d.2.2).center - (expBall d.2.1 d.2.2).radius at hu
  have hlow := expBall_contains d.1 d.2.2
  have hhigh := expBall_contains d.2.1 d.2.2
  have hname := ha d.2.2
  have htol : (2 : ℝ) ^ (-(d.2.2 : ℤ)) = errorTolerance d.2.2 := by
    simp [errorTolerance, zpow_neg, zpow_natCast]
  have hlR := (Rat.cast_lt (K := ℝ)).mpr hl
  have huR := (Rat.cast_lt (K := ℝ)).mpr hu
  push_cast at hlR huR
  rw [htol] at hlR huR
  have heL : Real.exp (d.1 : ℝ) < x := by
    dsimp only [QBall.Contains] at hlow
    linarith [(abs_le.mp hlow).2, (abs_le.mp hname).1]
  have heU : x < Real.exp (d.2.1 : ℝ) := by
    dsimp only [QBall.Contains] at hhigh
    linarith [(abs_le.mp hhigh).1, (abs_le.mp hname).2]
  have hlLog : (d.1 : ℝ) < Real.log x := (Real.lt_log_iff_exp_lt hx).mpr heL
  have huLog : Real.log x < (d.2.1 : ℝ) := (Real.log_lt_iff_lt_exp hx).mpr heU
  have hw : (d.2.1 : ℝ) - d.1 < 2 * (ε : ℝ) := by exact_mod_cast hwidth
  change |Real.log x - (((d.1 + d.2.1) / 2 : ℚ) : ℝ)| ≤ ε
  push_cast
  rw [abs_le]
  constructor <;> linarith

end

def logFastName {x : ℝ} (a : ℕ → ℚ) (hx : 0 < x) (ha : IsFastRealName a x) : ℕ → ℚ :=
  fun n => logApprox a hx ha ((2 : ℚ) ^ (-(n : ℤ))) (by positivity)

theorem logFastName_spec {x : ℝ} (a : ℕ → ℚ) (hx : 0 < x) (ha : IsFastRealName a x) :
    IsFastRealName (logFastName a hx ha) (Real.log x) := by
  intro n
  have h := logApprox_spec a hx ha ((2 : ℚ) ^ (-(n : ℤ))) (by positivity)
  simpa [logFastName, errorTolerance] using h

end ForcedComputation

end OAI
