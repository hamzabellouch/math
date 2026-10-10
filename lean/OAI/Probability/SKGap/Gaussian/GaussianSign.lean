import Mathlib
import OAI.Probability.SKGap.Localization.Conjugation

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def gaussianSignEquiv {κ : Type*} (q : κ → ℝ) (hq : ∀ b, q b^2=1) :
    (κ → ℝ) ≃ᵐ (κ → ℝ) where
  toFun g b := q b*g b
  invFun g b := q b*g b
  left_inv g := by ext b; dsimp; rw [← mul_assoc,← sq,hq b,one_mul]
  right_inv g := by ext b; dsimp; rw [← mul_assoc,← sq,hq b,one_mul]
  measurable_toFun := by change Measurable (fun g : κ → ℝ => fun b => q b*g b); fun_prop
  measurable_invFun := by change Measurable (fun g : κ → ℝ => fun b => q b*g b); fun_prop

lemma gaussianSign_map {κ : Type*} [Fintype κ] (q : κ → ℝ) (hq : ∀ b, q b^2=1) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (gaussianSignEquiv q hq) =
      Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  have he (b : κ) : (gaussianReal 0 1).map (fun x => q b*x) = gaussianReal 0 1 := by
    rcases sq_eq_one_iff.mp (hq b) with h|h
    · simp [h]
    · simpa only [h,neg_one_mul,neg_zero] using (gaussianReal_map_neg (μ := (0:ℝ)) (v := 1))
  change (Measure.pi (fun _ : κ => gaussianReal 0 1)).map (fun g b => q b*g b) = _
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  simp only [he]

lemma gaussianSign_integral {κ : Type*} [Fintype κ] (q : κ → ℝ) (hq : ∀ b, q b^2=1)
    (F : (κ → ℝ) → ℝ) :
    (∫ g, F (gaussianSignEquiv q hq g) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ g, F g ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  rw [← integral_map_equiv,gaussianSign_map]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def goeSign (s : ι → ℝ) : MatrixCoordinates ι → ℝ :=
  Sum.elim (fun p => s p.1*s p.2) (fun _ => 1)

omit [Fintype ι] [DecidableEq ι] in
lemma goeSign_sq (s : ι → ℝ) (hs : ∀ i, s i^2=1) (b : MatrixCoordinates ι) :
    goeSign s b^2=1 := by
  rcases b with ⟨i,k⟩|i
  · simp only [goeSign,Sum.elim_inl,mul_pow,hs,one_mul]
  · norm_num [goeSign]

omit [Fintype ι] [DecidableEq ι] in
lemma goeMatrix_sign (r : ℝ) (s : ι → ℝ) (hs : ∀ i, s i^2=1)
    (g : MatrixCoordinates ι → ℝ) :
    goeMatrix r (gaussianSignEquiv (goeSign s) (goeSign_sq s hs) g) =
      signConjugate s (goeMatrix r g) := by
  ext i k
  dsimp [goeMatrix,gaussianSignEquiv,goeSign,signConjugate]
  ring

lemma goe_equivariant_offdiag (r : ℝ) (F : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hF : ∀ (s : ι → ℝ), (∀ i, s i^2=1) → ∀ M,
      F (signConjugate s M)=signConjugate s (F M)) (i k : ι) (hik : i ≠ k) :
    (∫ g, F (goeMatrix r g) i k ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))=0 := by
  let s : ι → ℝ := fun b => if b=i then -1 else 1
  have hs : ∀ b, s b^2=1 := by intro b; dsimp [s]; split <;> norm_num
  have hi := gaussianSign_integral (goeSign s) (goeSign_sq s hs) (fun g => F (goeMatrix r g) i k)
  have hsi : s i = -1 := by simp [s]
  have hsk : s k = 1 := by simp [s,Ne.symm hik]
  have heq : (fun g => F (goeMatrix r (gaussianSignEquiv (goeSign s) (goeSign_sq s hs) g)) i k) =
      (fun g => -F (goeMatrix r g) i k) := by
    funext g
    rw [goeMatrix_sign r s hs g,hF s hs]
    change s i*s k*F (goeMatrix r g) i k = _
    rw [hsi,hsk,neg_one_mul,neg_mul,one_mul]
  rw [heq,integral_neg] at hi
  linarith
end SKGap
end
end

end OAI
