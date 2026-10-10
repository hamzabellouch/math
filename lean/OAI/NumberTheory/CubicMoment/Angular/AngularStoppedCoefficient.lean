import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughRows

namespace OAI

/-! Phase and active roughness of the literal angular stopped coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angularStoppedRowCoefficient_phase (ℓ : ℤ) (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) :
    angularStoppedRowCoefficient ℓ X w z u W selected n =
      angularStoppedRowCoefficient ℓ X w z 0 W selected n*mellinPhase u (norm n) := by
  unfold angularStoppedRowCoefficient
  rw [stoppedRowCoefficient_phase]
  ring

lemma angularStoppedRowCoefficient_ne_zero (ℓ : ℤ) (X w z u : ℝ)
    (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop) {n : Eisenstein}
    (hn : angularStoppedRowCoefficient ℓ X w z u W selected n ≠ 0) :
    stoppedRowCoefficient X w z u W selected n ≠ 0 :=
  (mul_ne_zero_iff.mp hn).1

lemma angularStoppedRowCoefficient_early_roughness (ℓ : ℤ)
    (X w z u ρ Z Q : ℝ) (W : ι → ℝ → ℂ)
    (hw : 0 < w) (hwz : w ≤ z) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {n p : Eisenstein}
    (hn : angularStoppedRowCoefficient ℓ X w z u W
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) n ≠ 0)
    (hp : primaryPrime p) (hpn : p ∣ n) :
    min w (geometricBinLower ρ X h) ≤ norm p :=
  stoppedRowCoefficient_early_roughness X w z u ρ Z Q W hw hwz hρ hρ₂
    j k h early hj (angularStoppedRowCoefficient_ne_zero ℓ X w z u W _ hn) hp hpn

end CubicFirstMoment

end

end OAI
