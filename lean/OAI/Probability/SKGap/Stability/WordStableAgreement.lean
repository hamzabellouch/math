import Mathlib
import OAI.Probability.SKGap.Brownian.PathAgreement
import OAI.Probability.SKGap.Matrix.Word

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def WordLetter.exactEval (j : ℝ) (a : ι→ℝ) : WordLetter ι→Matrix ι ι ℝ→Matrix ι ι ℝ
  | .diag d,_ => diagonal d
  | .noise,M => M
  | .inverse,M => (1-diagonal a*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1))⁻¹

def exactWord (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  matrixFactorProduct (F.map (WordLetter.exactEval j a)) M

theorem actualWord_agrees [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0<lo)
    (hf : ∀ x∈Icc lo hi,f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0≤R)
    (j : ℝ) {a : ι→ℝ} (ha : ∀ i,0≤a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M≤R)
    (hl : lo≤ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi≤ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (F : List (WordLetter ι)) : actualWord f R hR j a 1 F M=exactWord j a F M := by
  have he (l : WordLetter ι) : l.eval f R hR j a 1 M=l.exactEval j a M := by
    cases l with
    | diag d => rfl
    | noise => exact realProject_eq_self hR M hM hMR
    | inverse => exact pathK_agrees f hlo hf hR j ha M hM hMR hl hu
  induction F with
  | nil => rfl
  | cons l F ih =>
    change l.eval f R hR j a 1 M*actualWord f R hR j a 1 F M=l.exactEval j a M*exactWord j a F M
    rw [he,ih]
end SKGap
end
end

end OAI
