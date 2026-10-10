import OAI.NumberTheory.JointDickman.Amplification.MajorArcFiniteSum
import OAI.NumberTheory.JointDickman.Amplification.LocalArcIntegral

namespace OAI

/-! # The exact rescaled frequency integral on all major arcs -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

theorem smoothCoefficientAdditiveSum_continuous (B : ℕ) {a b X : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X) {w : ℝ → ℝ}
    (hsupp : ∀ s, s ≤ a ∨ b < s → w s = 0) :
    Continuous (fun θ => smoothCoefficientAdditiveSum B X θ w) := by
  have heq : (fun θ => smoothCoefficientAdditiveSum B X θ w) =
      fun θ => ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
        (coefficientWeight B n : ℂ)*(w (n/X) : ℂ)*additivePhase ((n : ℝ)*θ) := by
    funext θ
    exact tsum_eq_Ioc_of_scaled_support ha hab hX hsupp _ (by intro n hn; simp [hn])
  rw [heq]
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))

theorem smoothCoefficientAdditiveSum_periodic (B j : ℕ) (X : ℝ) (w : ℝ → ℝ) :
    Periodic (fun θ => smoothCoefficientAdditiveSum B X (-(j : ℝ)*θ) w) 1 := by
  intro θ
  dsimp only
  have he : -(j : ℝ)*(θ+1) = -(j : ℝ)*θ+(-(j : ℤ) : ℤ) := by push_cast; ring
  rw [he,smoothCoefficientAdditiveSum_add_int]

theorem majorArc_rescaled_integral :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ F : ℝ → ℂ, Continuous F → Periodic F 1 →
      (∫ x in majorArcRegion B j X, F x) =
        (1/((j : ℂ)*X))*
          ∑ q ∈ positiveDenominators (B^12), ∑ h : ZMod (j*(q : ℕ)),
            if h.val.Coprime (q : ℕ) then
              ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
                F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))
            else 0 := by
  filter_upwards [majorArc_finite_sum] with B hB
  intro X hX hlog j hj F hF hp
  let : NeZero j := hj
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  rw [hB X hX hlog j hj F hF hp,mul_sum]
  apply sum_congr rfl
  intro q _
  rw [mul_sum]
  apply sum_congr rfl
  intro h _
  split_ifs with hh
  · rw [local_arc_change_variables hjR hX.ne']
    push_cast
    field_simp
  · simp

end JointDickman

end OAI
