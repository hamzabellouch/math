import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HoppingBox
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.ComputableResolvent
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalRectangleProgram

namespace OAI

/-! Literal compact contact quadrature, using the already certified
resolvent program at each translated rational point. -/

namespace ContinuumCoulomb.HoppingQuadrature
open ExactQuantumFactoring.BitStackProgram

abbrev Settings := (ℕ × ℕ) × ℚ
abbrev Input := RationalRectangleProgram.Input Settings

def settingsCode : Settings → List Bool :=
  prodCode (prodCode unaryCode unaryCode) ratCode

def sample (e : Settings) (a b : ℚ) : ℚ :=
  PlanarForcingProgram.value (a, b) *
    ResolventSchedule.approximate (e.1, (a - e.2, b))

def value (x : Input) : ℚ := RationalRectangleProgram.value sample x

noncomputable opaque sampleProgram :
    Procedure (prodCode (prodCode settingsCode ratCode) ratCode) ratCode
      (fun x => sample x.1.1 x.1.2 x.2) := by
  let ax := Procedure.first (prodCode settingsCode ratCode) ratCode
  let e := (Procedure.first settingsCode ratCode).comp ax
  let a := (Procedure.second settingsCode ratCode).comp ax
  let b := Procedure.second (prodCode settingsCode ratCode) ratCode
  let par := (Procedure.first (prodCode unaryCode unaryCode) ratCode).comp e
  let d := (Procedure.second (prodCode unaryCode unaryCode) ratCode).comp e
  let shift := Procedure.ratSub.comp (a.pair d)
  let phi := ResolventSchedule.program.comp (par.pair (shift.pair b))
  let forcing := PlanarForcingProgram.program.comp (a.pair b)
  exact (Procedure.ratMul.comp (forcing.pair phi)).congrFun (by intro x; rfl)

noncomputable opaque program :
    Procedure (RationalRectangleProgram.inputCode settingsCode) ratCode value :=
  RationalRectangleProgram.program settingsCode sample sampleProgram

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime (RationalRectangleProgram.inputCode settingsCode) ratCode value :=
  program.toTM2

theorem sample_error (e : Settings) (a b : ℚ)
    (hR : ‖PlanarForcingProgram.position (a - e.2, b)‖ ≤ (e.1.1 : ℝ)) :
    |(sample e a b : ℝ) -
      planarHoppingIntegrand (e.2 : ℝ) (PlanarForcingProgram.position (a, b))| ≤
        ((e.1.2 : ℝ) + 1)⁻¹ := by
  rw [sample, Rat.cast_mul, PlanarForcingProgram.value_cast, planarHoppingIntegrand,
    ← rationalPosition_shift_first, ← mul_sub, abs_mul,
    abs_of_nonneg (planarForcing_nonnegative _)]
  exact (mul_le_mul_of_nonneg_left
    (ResolventSchedule.approximation_error (e.1, (a - e.2, b)) hR)
    (planarForcing_nonnegative _)).trans
      (mul_le_of_le_one_left (by positivity) (planarForcing_le_one _))

theorem error (x : Input) (hh : 0 ≤ (x.2.2.2 : ℝ))
    (hR : ∀ i < x.1, ∀ j < x.1,
      ‖PlanarForcingProgram.position
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i - x.2.1.2,
         RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j)‖ ≤ (x.2.1.1.1 : ℝ)) :
    |(value x : ℝ) -
      ∫ a in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
        ∫ b in (x.2.2.1 : ℝ)..(RationalQuadratureProgram.node x.2.2.1 x.2.2.2 x.1 : ℝ),
          planarHoppingIntegrand (x.2.1.2 : ℝ) (planarPairEquiv.symm (a, b))| ≤
      ((x.1 : ℝ) * (x.2.2.2 : ℝ)) ^ 2 *
        (128 * (x.2.2.2 : ℝ) + ((x.2.1.1.2 : ℝ) + 1)⁻¹) := by
  let f := fun a b => planarHoppingIntegrand (x.2.1.2 : ℝ) (planarPairEquiv.symm (a, b))
  let v := fun i j => (sample x.2.1
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
    (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j) : ℝ)
  have hx : ∀ a a' b, |f a b - f a' b| ≤ 64 * |a - a'| := by
    intro a a' b
    simpa only [f, planarPair_distance_first] using
      planarHoppingIntegrand_norm_sub_explicit (x.2.1.2 : ℝ)
        (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a', b))
  have hy : ∀ a b b', |f a b - f a b'| ≤ 64 * |b - b'| := by
    intro a b b'
    simpa only [f, planarPair_distance_second] using
      planarHoppingIntegrand_norm_sub_explicit (x.2.1.2 : ℝ)
        (planarPairEquiv.symm (a, b)) (planarPairEquiv.symm (a, b'))
  have hs : ∀ i < x.1, ∀ j < x.1,
      |v i j - f (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) i)
        (UniformQuadrature.node (x.2.2.1 : ℝ) (x.2.2.2 : ℝ) j)| ≤
        ((x.2.1.1.2 : ℝ) + 1)⁻¹ := by
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

end ContinuumCoulomb.HoppingQuadrature

end OAI
