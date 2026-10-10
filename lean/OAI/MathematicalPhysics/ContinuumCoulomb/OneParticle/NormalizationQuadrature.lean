import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableResolvent
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalRectangleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolventModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.NumericalSquare

namespace OAI

/-! Literal quadrature of the actual squared resolvent. Each sample is
computed by the fixed Taylor/heat program, with its proved error. -/

namespace ContinuumCoulomb.NormalizationQuadrature
open ExactQuantumFactoring.BitStackProgram

abbrev Settings := ℕ × ℕ
abbrev Input := RationalRectangleProgram.Input Settings

def settingsCode : Settings → List Bool := prodCode unaryCode unaryCode

def sample (e : Settings) (a b : ℚ) : ℚ :=
  ResolventSchedule.approximate (e, (a, b)) ^ 2

def value (x : Input) : ℚ := RationalRectangleProgram.value sample x

noncomputable opaque sampleProgram :
    Procedure (prodCode (prodCode settingsCode ratCode) ratCode) ratCode
      (fun x => sample x.1.1 x.1.2 x.2) := by
  let ax := Procedure.first (prodCode settingsCode ratCode) ratCode
  let e := (Procedure.first settingsCode ratCode).comp ax
  let a := (Procedure.second settingsCode ratCode).comp ax
  let b := Procedure.second (prodCode settingsCode ratCode) ratCode
  let point := a.pair b
  let q := ResolventSchedule.program.comp (e.pair point)
  exact (Procedure.ratMul.comp (q.pair q)).congrFun (by
    intro x
    simp only [sample, pow_two]
    rfl)

noncomputable opaque program :
    Procedure (RationalRectangleProgram.inputCode settingsCode) ratCode value :=
  RationalRectangleProgram.program settingsCode sample sampleProgram

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime (RationalRectangleProgram.inputCode settingsCode) ratCode value :=
  program.toTM2

theorem sample_error (e : Settings) (a b : ℚ)
    (hR : ‖PlanarForcingProgram.position (a, b)‖ ≤ (e.1 : ℝ)) :
    |(sample e a b : ℝ) - planarResolventMode (PlanarForcingProgram.position (a, b)) ^ 2| ≤
      3 * ((e.2 : ℝ) + 1)⁻¹ := by
  rw [sample, Rat.cast_pow]
  apply unitInterval_square_error (planarResolventMode_positive _).le (planarResolventMode_le_one _)
  · exact (inv_le_one₀ (show (0 : ℝ) < (e.2 : ℝ) + 1 by positivity)).mpr
      (show (1 : ℝ) ≤ (e.2 : ℝ) + 1 by
        linarith [show (0 : ℝ) ≤ (e.2 : ℝ) from Nat.cast_nonneg _])
  · exact ResolventSchedule.approximation_error (e, (a, b)) hR

theorem error (x : Input) (hh : 0 ≤ (x.2.2.2 : ℝ))
    (hR : ∀ i < x.1, ∀ j < x.1,
      ‖PlanarForcingProgram.position
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i,
         RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j)‖ ≤ (x.2.1.1 : ℝ)) :
    |(value x : ℝ) -
      ∫ a in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
        ∫ b in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
          planarResolventMode (planarPairEquiv.symm (a, b)) ^ 2| ≤
      ((x.1 : ℝ) * (x.2.2.2 : ℝ)) ^ 2 *
        (128 * (x.2.2.2 : ℝ) + 3 * ((x.2.1.2 : ℝ) + 1)⁻¹) := by
  let f := fun a b => planarResolventMode (planarPairEquiv.symm (a, b)) ^ 2
  let v := fun i j => (sample x.2.1
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j) : ℝ)
  have hx : ∀ a a' b, |f a b - f a' b| ≤ 64 * |a - a'| := by
    intro a a' b
    simpa only [f, planarPair_distance_first] using
      planarResolventMode_square_norm_sub (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a', b))
  have hy : ∀ a b b', |f a b - f a b'| ≤ 64 * |b - b'| := by
    intro a b b'
    simpa only [f, planarPair_distance_second] using
      planarResolventMode_square_norm_sub (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a, b'))
  have hs : ∀ i < x.1, ∀ j < x.1,
      |v i j - f (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) i)
        (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) j)| ≤
        3 * ((x.2.1.2 : ℝ) + 1)⁻¹ := by
    intro i hi j hj
    have h := sample_error x.2.1 _ _ (hR i hi j hj)
    simpa only [v, f, rationalPosition_eq_pair, RationalQuadratureProgram.node_cast] using h
  have h := UniformQuadrature.rectangle_error f v _ _ x.1 _ _ x.1 hh hh
    (by norm_num : (0 : ℝ) ≤ 64) (by norm_num : (0 : ℝ) ≤ 64)
    (fun a _ a' _ b _ => hx a a' b) (fun a _ b _ b' _ => hy a b b') hs
  rw [value, RationalRectangleProgram.value_cast]
  simp only [RationalQuadratureProgram.node_cast]
  convert h using 1
  ring

end ContinuumCoulomb.NormalizationQuadrature

end OAI
