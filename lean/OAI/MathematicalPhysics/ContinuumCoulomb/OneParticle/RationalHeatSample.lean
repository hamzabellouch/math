import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalExponentialProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PiProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PlanarForcingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatKernel

namespace OAI

/-! Actual rational evaluation of the heat-resolvent integrand. Both π and
the exponential are computed by rational approximation programs.
Clamping the computed π below by one keeps every denominator quantitative. -/

namespace ContinuumCoulomb.RationalHeatSample
open ExactQuantumFactoring.BitStackProgram

def safePi (N : ℕ) : ℚ := max 1 (PiProgram.approximate N)

theorem safePi_ge_one (N : ℕ) : (1 : ℝ) ≤ (safePi N : ℝ) := by
  exact_mod_cast le_max_left (1 : ℚ) (PiProgram.approximate N)

theorem safePi_error (N : ℕ) (hN : 0 < N) :
    |(safePi N : ℝ) - Real.pi| ≤ 8 / (N : ℝ) := by
  have h := PiProgram.error N hN
  have hp : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  by_cases hq : (1 : ℚ) ≤ PiProgram.approximate N
  · simpa only [safePi, max_eq_right hq] using h
  · have hq' : (PiProgram.approximate N : ℝ) ≤ 1 := by exact_mod_cast le_of_not_ge hq
    rw [safePi, max_eq_left (le_of_not_ge hq), Rat.cast_one,
      abs_of_nonpos (by linarith)]
    rw [abs_of_nonpos (by linarith)] at h
    linarith

noncomputable def safePiProgram : Procedure unaryCode ratCode safePi := by
  let q := PiProgram.program
  let one := Procedure.constant unaryCode ratCode (1 : ℚ)
  let difference := Procedure.ratSub.comp (q.pair one)
  let negative := Procedure.intSign.comp (Procedure.ratNum.comp difference)
  exact (Procedure.conditional negative one q).congrFun (by
    intro N
    simp only [Function.comp_apply, Rat.num_neg, decide_eq_true_eq]
    unfold safePi
    split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith)])

abbrev Point := ℚ × ℚ
abbrev Arguments := ℚ × (Point × Point)
abbrev Settings := ℕ × (ℕ × ℕ)
abbrev Input := Settings × Arguments

def pointCode : Point → List Bool := prodCode ratCode ratCode
def argumentsCode : Arguments → List Bool := prodCode ratCode (prodCode pointCode pointCode)
def settingsCode : Settings → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)
def inputCode : Input → List Bool := prodCode settingsCode argumentsCode

def exponent (a : Arguments) : ℚ :=
  -a.1 - ((a.2.1.1 - a.2.2.1) ^ 2 + (a.2.1.2 - a.2.2.2) ^ 2) / (4 * a.1)

def value (x : Input) : ℚ :=
  RationalExponential.approximate x.1.1 x.1.2.1 (exponent x.2) *
    PlanarForcingProgram.value x.2.2.2 / (4 * safePi x.1.2.2 * x.2.1)

noncomputable def exponentProgram : Procedure argumentsCode ratCode exponent := by
  let t := Procedure.first ratCode (prodCode pointCode pointCode)
  let xy := Procedure.second ratCode (prodCode pointCode pointCode)
  let x := (Procedure.first pointCode pointCode).comp xy
  let y := (Procedure.second pointCode pointCode).comp xy
  let dx := Procedure.ratSub.comp
    (((Procedure.first ratCode ratCode).comp x).pair ((Procedure.first ratCode ratCode).comp y))
  let dy := Procedure.ratSub.comp
    (((Procedure.second ratCode ratCode).comp x).pair ((Procedure.second ratCode ratCode).comp y))
  let normSq := Procedure.ratAdd.comp
    ((Procedure.ratMul.comp (dx.pair dx)).pair (Procedure.ratMul.comp (dy.pair dy)))
  let four := Procedure.constant argumentsCode ratCode (4 : ℚ)
  let denom := Procedure.ratMul.comp (four.pair t)
  let gaussian := Procedure.ratDiv.comp (normSq.pair denom)
  exact (Procedure.ratSub.comp ((Procedure.ratNeg.comp t).pair gaussian)).congrFun
    (by intro a; simp only [exponent, pow_two]; rfl)

noncomputable def program : Procedure inputCode ratCode value := by
  let settings := Procedure.first settingsCode argumentsCode
  let args := Procedure.second settingsCode argumentsCode
  let M := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp settings
  let pn := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp settings
  let p := (Procedure.first unaryCode unaryCode).comp pn
  let N := (Procedure.second unaryCode unaryCode).comp pn
  let expArg := M.pair (p.pair (exponentProgram.comp args))
  let exponential := RationalExponentialProgram.program.comp expArg
  let xy := (Procedure.second ratCode (prodCode pointCode pointCode)).comp args
  let y := (Procedure.second pointCode pointCode).comp xy
  let forcing := PlanarForcingProgram.program.comp y
  let numerator := Procedure.ratMul.comp (exponential.pair forcing)
  let t := (Procedure.first ratCode (prodCode pointCode pointCode)).comp args
  let pi := safePiProgram.comp N
  let four := Procedure.constant inputCode ratCode (4 : ℚ)
  let denominator := Procedure.ratMul.comp ((Procedure.ratMul.comp (four.pair pi)).pair t)
  exact (Procedure.ratDiv.comp (numerator.pair denominator)).congrFun (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode ratCode value := program.toTM2

theorem ratio_error {E e P Q dE dP : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hE : |E - e| ≤ dE) (hPQ : |P - Q| ≤ dP) :
    |E / P - e / Q| ≤ dE + dP := by
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hdE : 0 ≤ dE := (abs_nonneg _).trans hE
  have hdP : 0 ≤ dP := (abs_nonneg _).trans hPQ
  have hid : E / P - e / Q = (E - e) / P + e * (Q - P) / (P * Q) := by
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(E - e) / P| + |e * (Q - P) / (P * Q)| := abs_add_le _ _
    _ ≤ dE + dP := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hP0]
        apply (div_le_iff₀ hP0).mpr
        exact hE.trans (by nlinarith)
      · rw [abs_div, abs_mul, abs_of_nonneg he, abs_of_pos (mul_pos hP0 hQ0), abs_sub_comm Q P]
        apply (div_le_iff₀ (mul_pos hP0 hQ0)).mpr
        have hmul : 1 ≤ P * Q := by nlinarith
        have hnum := mul_le_mul_of_nonneg_left hPQ he
        nlinarith

theorem exponent_nonpos (a : Arguments) (ht : 0 < (a.1 : ℝ)) :
    (exponent a : ℝ) ≤ 0 := by
  simp only [exponent, Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_add, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_ofNat]
  have hpos : 0 ≤ (((a.2.1.1 : ℝ) - a.2.2.1) ^ 2 +
      ((a.2.1.2 : ℝ) - a.2.2.2) ^ 2) / (4 * (a.1 : ℝ)) := by positivity
  linarith

theorem position_sub_norm_sq (x y : Point) :
    ‖PlanarForcingProgram.position x - PlanarForcingProgram.position y‖ ^ 2 =
      ((x.1 : ℝ) - y.1) ^ 2 + ((x.2 : ℝ) - y.2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, PlanarForcingProgram.position, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]

theorem exact_density (a : Arguments) :
    Real.exp (exponent a : ℝ) * planarForcing (PlanarForcingProgram.position a.2.2) /
      (4 * Real.pi * (a.1 : ℝ)) =
    Real.exp (-(a.1 : ℝ)) * planarHeatKernel a.1
      (PlanarForcingProgram.position a.2.1 - PlanarForcingProgram.position a.2.2) *
      planarForcing (PlanarForcingProgram.position a.2.2) := by
  simp only [exponent, Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_add,
    Rat.cast_pow, Rat.cast_mul, Rat.cast_ofNat, planarHeatKernel, position_sub_norm_sq]
  rw [show -(a.1 : ℝ) - (((a.2.1.1 : ℝ) - a.2.2.1) ^ 2 +
      ((a.2.1.2 : ℝ) - a.2.2.2) ^ 2) / (4 * (a.1 : ℝ)) =
      -(a.1 : ℝ) + (-((((a.2.1.1 : ℝ) - a.2.2.1) ^ 2 +
      ((a.2.1.2 : ℝ) - a.2.2.2) ^ 2) / (4 * (a.1 : ℝ)))) by ring,
    Real.exp_add]
  simp only [neg_div]
  ring

theorem error (x : Input) (ht : 0 < (x.2.1 : ℝ)) (hN : 0 < x.1.2.2)
    (hM : |(exponent x.2 : ℝ)| ≤ x.1.1) :
    |(value x : ℝ) - Real.exp (exponent x.2 : ℝ) *
      planarForcing (PlanarForcingProgram.position x.2.2.2) /
      (4 * Real.pi * (x.2.1 : ℝ))| ≤
      ((2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ)) / (4 * (x.2.1 : ℝ)) := by
  let F := planarForcing (PlanarForcingProgram.position x.2.2.2)
  have hF : 0 ≤ F := planarForcing_nonnegative _
  have hF1 : F ≤ 1 := planarForcing_le_one _
  have he := RationalExponential.error x.1.1 x.1.2.1 (exponent x.2) hM
  have hr := ratio_error
    (E := (RationalExponential.approximate x.1.1 x.1.2.1 (exponent x.2) : ℝ))
    (e := Real.exp (exponent x.2 : ℝ)) (dE := (2 ^ x.1.2.1 : ℝ)⁻¹)
    (dP := 8 / (x.1.2.2 : ℝ))
    (safePi_ge_one x.1.2.2) (by linarith [Real.two_le_pi])
    (Real.exp_pos _).le ((Real.exp_le_one_iff).mpr (exponent_nonpos x.2 ht))
    (by simpa only [abs_sub_comm] using he) (safePi_error x.1.2.2 hN)
  have hd : 0 < 4 * (x.2.1 : ℝ) := by positivity
  have hv : (value x : ℝ) - Real.exp (exponent x.2 : ℝ) * F /
      (4 * Real.pi * (x.2.1 : ℝ)) =
      (((RationalExponential.approximate x.1.1 x.1.2.1 (exponent x.2) : ℝ) /
        (safePi x.1.2.2 : ℝ) - Real.exp (exponent x.2 : ℝ) / Real.pi) * F) /
        (4 * (x.2.1 : ℝ)) := by
    simp only [value, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, PlanarForcingProgram.value_cast]
    dsimp only [F]
    ring
  rw [hv, abs_div, abs_mul, abs_of_nonneg hF, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  have hn := mul_le_mul_of_nonneg_right hr hF
  have hb : 0 ≤ (2 ^ x.1.2.1 : ℝ)⁻¹ + 8 / (x.1.2.2 : ℝ) := by positivity
  exact hn.trans (by nlinarith)

end ContinuumCoulomb.RationalHeatSample

end OAI
