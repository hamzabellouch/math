import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombKernel
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.BisectionProgram

namespace OAI

/-! A literal rational approximation of the bounded three-dimensional
Coulomb kernel. Only a dyadic square root and rational arithmetic occur. -/

noncomputable section
namespace ContinuumCoulomb.CappedKernelProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Triple := ℚ × (ℚ × ℚ)
abbrev Input := (ℕ × ℚ) × Triple

def position (q : Triple) : Position := WithLp.toLp 2 ![(q.1 : ℝ), (q.2.1 : ℝ), (q.2.2 : ℝ)]
def normSquare (q : Triple) : ℚ := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2

def approximate (x : Input) : ℚ :=
  (max x.1.2 (RationalSquareRoot.value (x.1.1, normSquare x.2)))⁻¹

theorem normSquare_nonnegative (q : Triple) : 0 ≤ normSquare q := by
  unfold normSquare
  positivity

theorem position_norm_sq (q : Triple) : ‖position q‖ ^ 2 = (normSquare q : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [position, normSquare, Fin.sum_univ_succ]
  ring

theorem position_norm (q : Triple) : ‖position q‖ = Real.sqrt (normSquare q : ℝ) := by
  rw [← position_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem approximation_error (x : Input) (hε : 0 < x.1.2) :
    |(approximate x : ℝ) - cappedCoulombKernel (x.1.2 : ℝ) (position x.2)| ≤
      ((x.1.2 : ℝ)⁻¹ ^ 2) * (2 : ℝ)⁻¹ ^ x.1.1 := by
  let a : ℝ := max (x.1.2 : ℝ) (RationalSquareRoot.value (x.1.1, normSquare x.2) : ℝ)
  let b : ℝ := max (x.1.2 : ℝ) ‖position x.2‖
  have hεr : (0 : ℝ) < x.1.2 := by exact_mod_cast hε
  have ha : 0 < a := hεr.trans_le (le_max_left _ _)
  have hb : 0 < b := hεr.trans_le (le_max_left _ _)
  have hroot := RationalSquareRoot.value_error x.1.1 (normSquare_nonnegative x.2)
  rw [← position_norm] at hroot
  have hdiff : |a - b| ≤ (2 : ℝ)⁻¹ ^ x.1.1 := by
    have h := abs_max_sub_max_le_abs
      (RationalSquareRoot.value (x.1.1, normSquare x.2) : ℝ) ‖position x.2‖ (x.1.2 : ℝ)
    rw [max_comm _ (x.1.2 : ℝ), max_comm _ (x.1.2 : ℝ)] at h
    exact h.trans hroot
  have hai : a⁻¹ ≤ (x.1.2 : ℝ)⁻¹ := inv_anti₀ hεr (le_max_left _ _)
  have hbi : b⁻¹ ≤ (x.1.2 : ℝ)⁻¹ := inv_anti₀ hεr (le_max_left _ _)
  have he : (approximate x : ℝ) - cappedCoulombKernel (x.1.2 : ℝ) (position x.2) =
      (b - a) * a⁻¹ * b⁻¹ := by
    have hcast : (approximate x : ℝ) = a⁻¹ := by
      simp only [approximate, Rat.cast_inv, Rat.cast_max, a]
    rw [hcast]
    change a⁻¹ - b⁻¹ = _
    field_simp [ha.ne', hb.ne']
  rw [he, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha),
    abs_of_pos (inv_pos.mpr hb), abs_sub_comm b a]
  calc
    _ ≤ ((2 : ℝ)⁻¹ ^ x.1.1) * (x.1.2 : ℝ)⁻¹ * (x.1.2 : ℝ)⁻¹ := by gcongr
    _ = _ := by ring

def tripleCode : Triple → List Bool := prodCode ratCode (prodCode ratCode ratCode)
def inputCode : Input → List Bool := prodCode (prodCode unaryCode ratCode) tripleCode

noncomputable opaque maximumProgram : Procedure (prodCode ratCode ratCode) ratCode
    (fun q => max q.1 q.2) := by
  exact (Procedure.conditional BisectionProgram.rationalLess
    (Procedure.second ratCode ratCode) (Procedure.first ratCode ratCode)).congrFun (by
      intro q
      simp only [decide_eq_true_eq]
      split_ifs with h
      · exact (max_eq_right h.le).symm
      · exact (max_eq_left (le_of_not_gt h)).symm)

noncomputable opaque normSquareProgram : Procedure tripleCode ratCode normSquare := by
  let x := Procedure.first ratCode (prodCode ratCode ratCode)
  let yz := Procedure.second ratCode (prodCode ratCode ratCode)
  let y := (Procedure.first ratCode ratCode).comp yz
  let z := (Procedure.second ratCode ratCode).comp yz
  let sx := Procedure.ratMul.comp (x.pair x)
  let sy := Procedure.ratMul.comp (y.pair y)
  let sz := Procedure.ratMul.comp (z.pair z)
  exact (Procedure.ratAdd.comp ((Procedure.ratAdd.comp (sx.pair sy)).pair sz)).congrFun
    (by intro q; simp only [normSquare, Function.comp_apply, pow_two])

noncomputable opaque program : Procedure inputCode ratCode approximate := by
  let params := Procedure.first (prodCode unaryCode ratCode) tripleCode
  let precision := (Procedure.first unaryCode ratCode).comp params
  let epsilon := (Procedure.second unaryCode ratCode).comp params
  let coords := Procedure.second (prodCode unaryCode ratCode) tripleCode
  let square := normSquareProgram.comp coords
  let root := RationalSquareRoot.program.comp (precision.pair square)
  let den := maximumProgram.comp (epsilon.pair root)
  exact (Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode (1 : ℚ)).pair den)).congrFun
    (by intro x; simp only [approximate, Function.comp_apply, one_div])

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode ratCode approximate :=
  program.toTM2

end ContinuumCoulomb.CappedKernelProgram

end

end OAI
