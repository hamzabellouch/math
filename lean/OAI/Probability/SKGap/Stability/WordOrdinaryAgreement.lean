import Mathlib
import OAI.Probability.SKGap.Stability.WordStableAgreement
import OAI.Probability.SKGap.Matrix.MarkedWordIBP

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actualWord_agrees_no_inverse (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R)
    (j : ℝ) (a : ι→ℝ) (M : Matrix ι ι ℝ) (hM : Mᵀ=M) (hMR : opNorm M≤R)
    (F : List (WordLetter ι)) (hF : inverseCount F=0) :
    actualWord f R hR j a 1 F M=exactWord j a F M := by
  induction F with
  | nil => rfl
  | cons l F ih =>
    cases l with
    | inverse => simp [inverseCount] at hF
    | diag d =>
      have ht : inverseCount F=0 := by simpa [inverseCount] using hF
      change diagonal d*actualWord f R hR j a 1 F M=diagonal d*exactWord j a F M
      rw [ih ht]
    | noise =>
      have ht : inverseCount F=0 := by simpa [inverseCount] using hF
      change realProject R hR M*actualWord f R hR j a 1 F M=M*exactWord j a F M
      rw [realProject_eq_self hR M hM hMR,ih ht]
end SKGap
end
end

end OAI
