import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.HoppingProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactQuotientBounds

namespace OAI

/-! The actual normalized hopping coefficient has a polynomial TM2
approximation. The sole fixed guard is chosen from the already proved
positive normalization integral; it is independent of every input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.ComputableHopping
open ExactQuantumFactoring.BitStackProgram

abbrev Input := HoppingSchedule.Input

def precision (P : ℕ) : ℕ := 16 * contactNormalizationGuard ^ 2 * (P + 1)

def argument (x : Input) : HoppingSchedule.Input := ((x.1.1, precision x.1.2), x.2)

def approximate (x : Input) : ℚ :=
  HoppingSchedule.approximate (argument x) /
    (2 * NormalizationSchedule.approximate (precision x.1.2))

theorem precision_cast (P : ℕ) :
    (precision P : ℝ) = 16 * (contactNormalizationGuard : ℝ) ^ 2 * ((P : ℝ) + 1) := by
  simp only [precision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

theorem precision_budget (P : ℕ) :
    (contactNormalizationGuard : ℝ) * ((precision P : ℝ) + 1)⁻¹ ≤ 1 ∧
    3 * (contactNormalizationGuard : ℝ) ^ 2 * ((precision P : ℝ) + 1)⁻¹ ≤
      ((P : ℝ) + 1)⁻¹ := by
  let C := (contactNormalizationGuard : ℝ)
  let S := (P : ℝ) + 1
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hc : (1 : ℕ) ≤ contactNormalizationGuard := contactNormalizationGuard_positive
    exact_mod_cast hc
  have hS : 1 ≤ S := by
    dsimp only [S]
    linarith [show (0 : ℝ) ≤ (P : ℝ) from Nat.cast_nonneg _]
  have hC0 : 0 < C := by linarith
  have hS0 : 0 < S := by linarith
  have hC2 : C ≤ C ^ 2 := by nlinarith
  have hCs : C ^ 2 ≤ C ^ 2 * S := by nlinarith [sq_nonneg C]
  rw [precision_cast]
  change C * (16 * C ^ 2 * S + 1)⁻¹ ≤ 1 ∧
    3 * C ^ 2 * (16 * C ^ 2 * S + 1)⁻¹ ≤ S⁻¹
  constructor
  · exact (mul_inv_le_iff₀ (by positivity)).mpr (by nlinarith)
  · apply (mul_inv_le_iff₀ (by positivity)).mpr
    rw [show S⁻¹ * (16 * C ^ 2 * S + 1) = (16 * C ^ 2 * S + 1) / S by ring]
    exact (le_div_iff₀ hS0).mpr (by nlinarith)

theorem approximation_error (x : Input) (hd : |(x.2 : ℝ)| ≤ (x.1.1 : ℝ)) :
    |(approximate x : ℝ) - planarHopping (x.2 : ℝ)| ≤ ((x.1.2 : ℝ) + 1)⁻¹ := by
  let A := ∫ r, planarResolventMode r ^ 2
  let ε := ((precision x.1.2 : ℝ) + 1)⁻¹
  have ha : 0 < A := planarResolventMode_square_integral_positive
  have hC : (1 : ℝ) ≤ contactNormalizationGuard := by
    have hc : (1 : ℕ) ≤ contactNormalizationGuard := contactNormalizationGuard_positive
    exact_mod_cast hc
  have hn := NormalizationSchedule.approximation_error (precision x.1.2)
  have hb := HoppingSchedule.approximation_error (argument x) hd
  have hq := contact_quotient_error hC ha contactNormalizationGuard_bound
    (show 0 ≤ ε by dsimp [ε]; positivity) (precision_budget x.1.2).1
    (planarHoppingNumerator_abs_le_four (x.2 : ℝ)) hn hb
  have hq' : |(approximate x : ℝ) - planarHopping (x.2 : ℝ)| ≤
      3 * (contactNormalizationGuard : ℝ) ^ 2 * ε := by
    simpa only [approximate, argument, planarHopping_eq_numerator,
      Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, A, ε] using hq
  exact hq'.trans (precision_budget x.1.2).2

noncomputable opaque precisionFactorsProgram :
    Procedure unaryCode (prodCode unaryCode unaryCode)
      (fun P => (16 * contactNormalizationGuard ^ 2, P + 1)) :=
  (Procedure.constant unaryCode unaryCode (16 * contactNormalizationGuard ^ 2)).pair
    Procedure.unarySuccessor

noncomputable opaque precisionRawProgram : Procedure unaryCode unaryCode
    (fun P => (16 * contactNormalizationGuard ^ 2) * (P + 1)) :=
  ResolventSchedule.mulProgram.comp precisionFactorsProgram

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  precisionRawProgram.congrFun (by intro P; rfl)

noncomputable opaque argumentProgram :
    Procedure HoppingSchedule.inputCode HoppingSchedule.inputCode argument := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) ratCode
  let r := (Procedure.first unaryCode unaryCode).comp rp
  let p := (Procedure.second unaryCode unaryCode).comp rp
  let d := Procedure.second (prodCode unaryCode unaryCode) ratCode
  exact ((r.pair (precisionProgram.comp p)).pair d).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure HoppingSchedule.inputCode ratCode approximate := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) ratCode
  let p := (Procedure.second unaryCode unaryCode).comp rp
  let n := HoppingSchedule.program.comp argumentProgram
  let a := NormalizationSchedule.program.comp (precisionProgram.comp p)
  let two := Procedure.constant HoppingSchedule.inputCode ratCode (2 : ℚ)
  let den := Procedure.ratMul.comp (two.pair a)
  exact (Procedure.ratDiv.comp (n.pair den)).congrFun (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime HoppingSchedule.inputCode ratCode approximate := program.toTM2

end ContinuumCoulomb.ComputableHopping

end

end OAI
