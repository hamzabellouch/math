import OAI.NumberTheory.JointDickman.Amplification.SmallArcModel
import OAI.NumberTheory.JointDickman.Amplification.WeightedFourierTruncation
import OAI.NumberTheory.JointDickman.Amplification.MajorArcErrorSum

namespace OAI

/-! # The retained arc model with its full Fourier integral -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

noncomputable def fullSmallMajorArcModel (B j : ℕ) [NeZero j] (X : ℝ) (Q : ℕ)
    (F W : ℝ → ℂ) (a : ℕ+ → ℂ) : ℂ :=
  (1/(j : ℂ))*∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
    ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then a q*
      ∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ
    else 0 else 0

theorem smallArcModel_full_error {B j : ℕ} [NeZero j] (hB : 0 < B)
    (X : ℝ) (Q : ℕ) (F : ℝ → ℂ) (hF : Continuous F)
    (w : 𝓢(ℝ,ℝ)) (a : ℕ+ → ℂ) (ha : ∀ q, ‖a q‖ ≤ 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ M) (k : ℕ) :
    ‖fullSmallMajorArcModel B j X Q F (testFourierTransform w) a-
      smallMajorArcModel B j X Q F (testFourierTransform w) a‖ ≤
      ((B^12 : ℕ) : ℝ)*((B^12 : ℕ)+1)*
        (M*(((B : ℝ)^13)^k)⁻¹*(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖)) := by
  classical
  let E := M*(((B : ℝ)^13)^k)⁻¹*(∫ ξ : ℝ, |ξ|^k*‖testFourierTransform w ξ‖)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let I := fun q : ℕ+ => fun h : ZMod (j*(q : ℕ)) =>
    ∫ ξ : ℝ, F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*testFourierTransform w ξ
  let J := fun q : ℕ+ => fun h : ZMod (j*(q : ℕ)) =>
    ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
      F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*testFourierTransform w ξ
  have hlocal (q : ℕ+) (h : ZMod (j*(q : ℕ))) : ‖I q h-J q h‖ ≤ E := by
    have hh := schwartz_weighted_truncation w
      (fun ξ : ℝ => F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X)))
      (hF.comp (continuous_const.add (continuous_id.div_const _))) hM
      (pow_pos (show (0 : ℝ) < B by exact_mod_cast hB) 13) (fun ξ => hbound _) k
    simpa only [I,J,E,mul_comm] using hh
  have hsum := reducedArc_sum_error (B^12) j
    (fun q h => if (q : ℕ) ≤ Q then a q*I q h else 0)
    (fun q h => if (q : ℕ) ≤ Q then a q*J q h else 0) hE (by
      intro q _ h _
      by_cases hq : (q : ℕ) ≤ Q
      · simp only [hq,ite_true,← mul_sub,norm_mul]
        exact (mul_le_mul (ha q) (hlocal q h) (norm_nonneg _) (by norm_num)).trans_eq (one_mul E)
      · simp only [hq,ite_false,sub_self,norm_zero]
        exact hE)
  have hnormalize (V : (q : ℕ+) → ZMod (j*(q : ℕ)) → ℂ) :
      (∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
        ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then a q*V q h else 0 else 0) =
      ∑ q ∈ positiveDenominators (B^12),
        ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
          (if (q : ℕ) ≤ Q then a q*V q h else 0) else 0 := by
    apply sum_congr rfl
    intro q _
    by_cases hq : (q : ℕ) ≤ Q <;> simp [hq]
  change ‖(1/(j : ℂ))*(∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
      ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then a q*I q h else 0 else 0)-
    (1/(j : ℂ))*(∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
      ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then a q*J q h else 0 else 0)‖ ≤ _
  rw [hnormalize I,hnormalize J,← mul_sub,norm_mul,norm_div,norm_one,Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  dsimp [E]
  field_simp

end JointDickman

end OAI
