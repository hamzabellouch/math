import OAI.NumberTheory.JointDickman.Amplification.SmallMajorArcFiniteSum
import OAI.NumberTheory.JointDickman.Amplification.LocalArcIntegral

namespace OAI

/-! # Rescaling the retained small-denominator arcs -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

theorem smallMajorArc_rescaled_integral :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ F : ℝ → ℂ, Continuous F → Periodic F 1 →
      (∫ x in smallMajorArcRegion B j X Q, F x) =
        (1/((j : ℂ)*X))*
          ∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
            ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
              ∫ ξ in -(B : ℝ)^13..(B : ℝ)^13,
                F ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))
            else 0 else 0 := by
  filter_upwards [smallMajorArc_finite_sum] with B hB
  intro X hX hlog j hj Q F hF hp
  let : NeZero j := hj
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hjC : (j : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  rw [hB X hX hlog j hj Q F hF hp,mul_sum]
  apply sum_congr rfl
  intro q _
  split_ifs with hq
  · rw [mul_sum]
    apply sum_congr rfl
    intro h _
    split_ifs
    · rw [local_arc_change_variables hjR hX.ne']
      push_cast
      field_simp
    · simp
  · simp

end JointDickman

end OAI
