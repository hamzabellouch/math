import OAI.NumberTheory.JointDickman.Amplification.RescaledMajorIntegral
import OAI.NumberTheory.JointDickman.Amplification.MajorArcErrorSum

namespace OAI

/-! # Integrating a uniform local coefficient approximation on the major arcs -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

noncomputable def majorArcModel (B j : ℕ) [NeZero j] (X : ℝ) (F W : ℝ → ℂ) (a : ℕ+ → ℂ) : ℂ :=
  (1/(j : ℂ))*∑ q ∈ positiveDenominators (B^12), ∑ h : ZMod (j*(q : ℕ)),
    if h.val.Coprime (q : ℕ) then a q*
      ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
        F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ
    else 0

theorem majorArc_uniform_approximation :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ F G W : ℝ → ℂ,
      Continuous F → Continuous G → Continuous W → Periodic (fun x => F x*G x) 1 →
      ∀ a : ℕ+ → ℂ, ∀ L E : ℝ, 0 ≤ L → 0 ≤ E → (∀ x, ‖F x‖ ≤ L) →
      (∀ q ∈ positiveDenominators (B^12), ∀ h : ZMod (j*(q : ℕ)),
        h.val.Coprime (q : ℕ) → ∀ ξ : ℝ, |ξ| ≤ (B : ℝ)^13 →
        ‖G ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))-(X : ℂ)*a q*W ξ‖ ≤ E) →
      ‖(∫ x in majorArcRegion B j X, F x*G x)-majorArcModel B j X F W a‖ ≤
        (B : ℝ)^12*((B : ℝ)^12+1)*(2*(B : ℝ)^13)*L*E/X := by
  filter_upwards [majorArc_rescaled_integral] with B hB
  intro X hX hlog j hj F G W hF hG hW hp a L E hL hE hFb herror
  let : NeZero j := hj
  let A : (q : ℕ+) → ZMod (j*(q : ℕ)) → ℂ := fun q h =>
    ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
      F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*
        G ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))
  let C : (q : ℕ+) → ZMod (j*(q : ℕ)) → ℂ := fun q h => (X : ℂ)*a q*
    ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
      F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ
  have hR : 0 ≤ (B : ℝ)^13 := pow_nonneg (Nat.cast_nonneg B) _
  have hs := reducedArc_sum_error (B^12) j A C (E := (2*(B : ℝ)^13)*L*E)
    (by positivity) (by
      intro q hq h hh
      have hθ : Continuous (fun ξ : ℝ => (h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X)) :=
        continuous_const.add (continuous_id.div_const _)
      have hi := weighted_interval_error (a := -(B : ℝ)^13) (b := (B : ℝ)^13)
        (by linarith) hL (hF.comp hθ) (hG.comp hθ) (continuous_const.mul hW)
        (fun ξ _ => hFb _) (fun ξ hξ => herror q hq h hh ξ (abs_le.mpr hξ))
      dsimp only [Function.comp_def,Pi.mul_apply] at hi
      have heq : (fun ξ : ℝ => F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*
          ((X : ℂ)*a q*W ξ)) = fun ξ => ((X : ℂ)*a q)*
            (F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ) := by
        funext ξ
        ring
      rw [heq,intervalIntegral.integral_const_mul] at hi
      simpa only [A,C,sub_neg_eq_add,← two_mul] using hi)
  have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hmodel : (1/((j : ℂ)*X))*(∑ q ∈ positiveDenominators (B^12),
      ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then C q h else 0) =
      majorArcModel B j X F W a := by
    unfold majorArcModel
    simp only [mul_sum]
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro h _
    split_ifs
    · dsimp [C]
      field_simp
    · simp
  rw [hB X hX hlog j hj (fun x => F x*G x) (hF.mul hG) hp,← hmodel]
  change ‖(1/((j : ℂ)*X))*(∑ q ∈ positiveDenominators (B^12),
      ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then A q h else 0)-_‖ ≤ _
  rw [← mul_sub,norm_mul,norm_div,norm_one,norm_mul,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  refine (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1/((j : ℝ)*X))).trans_eq ?_
  push_cast
  field_simp

end JointDickman

end OAI
