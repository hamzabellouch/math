import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorExclusion
import OAI.NumberTheory.CubicMoment.Estimates.DivisorCharacterMass

namespace OAI

/-! The two actual coprime Poisson rows are the literal stopped rows at
the shifted norm heights. Divisibility filters and the original interval
support remain in the statement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedRowCoefficient_phase (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) :
    stoppedRowCoefficient X w z u W selected n =
      stoppedRowCoefficient X w z 0 W selected n*mellinPhase u (norm n) := by
  have hz : mellinPhase 0 (norm n) = 1 := by simp [mellinPhase]
  simp only [stoppedRowCoefficient,normTwist_eq_mellinPhase,hz,mul_one]

def stoppedDivisorMass (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H U : Finset Eisenstein) : ℝ :=
  ∑ d ∈ U.powerset, ∑ h ∈ H,
    ‖∑ n ∈ (stoppedIntervalSupport ι X a b e).filter (fun n => (∏ p ∈ d,p) ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n h‖^2

lemma stoppedDivisorMass_eq (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H U : Finset Eisenstein) :
    stoppedDivisorMass X w z a b u W selected e H U =
      divisorCharacterMass (stoppedIntervalSupport ι X a b e) H U
        (stoppedRowCoefficient X w z 0 W selected) u := by
  unfold stoppedDivisorMass divisorCharacterMass finiteCharacterMass
  simp_rw [stoppedRowCoefficient_phase X w z u W selected]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro h _
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem stopped_coprime_mellin_mass (X w z a b u t : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H U : Finset Eisenstein) {N : ℝ} (hN : 0 < N) :
    coprimeMellinMass (stoppedIntervalSupport ι X a b e) H U
      (fun n => star (stoppedRowCoefficient X w z u W selected n))
      (fun n => star (stoppedRowCoefficient X w z u W selected n))
      (fun n => norm n/N) t =
        (stoppedDivisorMass X w z a b (u+2*Real.pi*t) W selected e H U+
         stoppedDivisorMass X w z a b (u-2*Real.pi*t) W selected e H U)/2 := by
  rw [stoppedDivisorMass_eq,stoppedDivisorMass_eq]
  have he := twistedCoprimeMellinMass_eq_divisor_mass
    (stoppedIntervalSupport ι X a b e) H U
    (stoppedRowCoefficient X w z 0 W selected)
    (fun n hn => (stoppedIntervalSupport_spec X a b e hn).1) u t hN
  simpa only [twistedCoprimeMellinMass,←stoppedRowCoefficient_phase] using he

end CubicFirstMoment

end

end OAI
