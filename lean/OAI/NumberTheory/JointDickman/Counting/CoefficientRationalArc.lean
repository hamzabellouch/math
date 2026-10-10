import OAI.NumberTheory.JointDickman.Counting.LargeMajorCoefficient
import OAI.NumberTheory.JointDickman.Amplification.RationalUnitRepresentatives
import OAI.NumberTheory.JointDickman.Counting.ArcCoefficientIdentity

namespace OAI

/-! # The large-denominator coefficient estimate on an arbitrary rational arc -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficient_on_large_rational_arc
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ a b ε : ℝ, 0 < a → a ≤ b → 0 < ε →
      ∀ᶠ B : ℕ in atTop, ∀ X θ : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ r : ℚ, r.den ≤ B^15 → (B : ℝ)^(2/5 : ℝ) ≤ r.den →
      |θ-(r : ℝ)| ≤ (B : ℝ)^13/X →
      ∀ (w w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) →
      ‖smoothCoefficientAdditiveSum B X θ w‖ ≤
        (D*M*(b-a)+K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*X*(B : ℝ)^(-2/5+ε) := by
  obtain ⟨D,K,hD,hK,hbound⟩ := coefficient_large_majorArc_bound hSD hSW hM hMP
  refine ⟨D,K,hD,hK,?_⟩
  intro a b ε ha hab hε
  filter_upwards [hbound a b ε ha hab hε,eventually_ge_atTop 1] with B hboundB hB
  intro X θ hX hlog r hq hqlo hnear w w' M N hM0 hN hw hw' hwb hw'b hsupp
  let : NeZero r.den := ⟨r.pos.ne'⟩
  obtain ⟨u,k,hr⟩ := rational_eq_unit_fraction_add_int r
  let ξ : ℝ := X*(θ-r)
  have hθ : θ = (((u : ZMod r.den).val : ℝ)/r.den+ξ/X)+(k : ℝ) := by
    dsimp [ξ]
    rw [hr]
    field_simp
    ring
  have hξ : |ξ| ≤ (B : ℝ)^(14 : ℝ) := by
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    dsimp [ξ]
    rw [abs_mul,abs_of_pos hX,Real.rpow_ofNat]
    calc
      _ ≤ X*((B : ℝ)^13/X) := mul_le_mul_of_nonneg_left hnear hX.le
      _ = (B : ℝ)^13 := by field_simp
      _ ≤ (B : ℝ)^14 := pow_le_pow_right₀ hB1 (by norm_num)
  rw [hθ,smoothCoefficientAdditiveSum_add_int,← coefficientExponentialSum_eq_smooth]
  exact hboundB X hX hlog r.den hq hqlo u w w' M N ξ hM0 hN hw hw' hwb hw'b hsupp hξ

end JointDickman

end OAI
