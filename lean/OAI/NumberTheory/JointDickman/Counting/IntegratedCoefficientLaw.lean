import OAI.NumberTheory.JointDickman.Amplification.MajorArcApproximation
import OAI.NumberTheory.JointDickman.Counting.CoefficientFourierContinuity

namespace OAI

/-! # The integrated major-arc coefficient law from the published arithmetic inputs -/

namespace JointDickman
open Filter MeasureTheory Function
open scoped Topology ArithmeticFunction.Moebius

theorem majorArc_error_power {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) :
    B^12*(B^12+1)*(2*B^13)*C*B^(-50 : ℝ) ≤ 4*C*B^(-13 : ℝ) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hp12 : 1 ≤ B^12 := one_le_pow₀ hB
  have hpow : B^12*B^12*B^13*B^(-50 : ℝ) = B^(-13 : ℝ) := by
    rw [← pow_add,← pow_add]
    rw [← Real.rpow_natCast,← Real.rpow_add hB0]
    norm_num
  calc
    _ ≤ B^12*(2*B^12)*(2*B^13)*C*B^(-50 : ℝ) := by gcongr; linarith
    _ = 4*C*(B^12*B^12*B^13*B^(-50 : ℝ)) := by ring
    _ = _ := by rw [hpow]

/-- The coefficient is replaced inside the full major-arc integral, with a
uniform O(B^-13) error. The three hypotheses are exactly the published
Selberg--Delange, squarefree-character and reciprocal-Mertens inputs. -/
theorem coefficient_majorArc_integral_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ j : ℕ, ∀ (_ : NeZero j),
      ∀ (w w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
      (∀ x, x ≤ a ∨ b < x → w x = 0) →
      ∀ (F : ℝ → ℂ) (L : ℝ), Continuous F → Periodic F 1 → 0 ≤ L →
      (∀ x, ‖F x‖ ≤ L) →
      ‖(∫ x in majorArcRegion B j X,
          F x*smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)-
        majorArcModel B j X F (coefficientFourierTransform c H B X w)
          (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))‖ ≤
        4*K*b*(2*M+(N+2*Real.pi*M)*(b-a))*L*(B : ℝ)^(-13 : ℝ) := by
  obtain ⟨c,hc,hcpos,H,K,hK,hcoeff⟩ := coefficient_lifted_majorArc_law hSD hSW hM
  refine ⟨c,hc,hcpos,H,K,hK,?_⟩
  intro a b ha hab
  filter_upwards [hcoeff a b ha hab,majorArc_uniform_approximation,
    coefficient_support_window ha,eventually_ge_atTop 1] with B hcoeffB happrox hwindow hB
  intro X hX hlog j hj w w' M N hM0 hN0 hw hw' hwb hw'b hsupp F L hF hp hL hFb
  let : NeZero j := hj
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : 0 < B := lt_of_lt_of_le Nat.zero_lt_one hB
  have haX : 1 < a*X := lt_of_lt_of_le (by norm_num) (hwindow X hX hlog.1).1
  have hwc : Continuous w := continuous_iff_continuousAt.mpr (fun x => (hw x).continuousAt)
  have hG : Continuous (fun x => smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w) :=
    (smoothCoefficientAdditiveSum_continuous B ha.le hab hX hsupp).comp
      (continuous_const.mul continuous_id)
  have hW := coefficientFourierTransform_continuous c H B hB0 hX haX hwc hsupp
  let D : ℝ := K*b*(2*M+(N+2*Real.pi*M)*(b-a))
  have hD : 0 ≤ D := by dsimp [D]; have hb := ha.trans_le hab; positivity
  have hbound := happrox X hX hlog.1 j hj F
    (fun x => smoothCoefficientAdditiveSum B X (-(j : ℝ)*x) w)
    (coefficientFourierTransform c H B X w) hF hG hW
    (hp.mul (smoothCoefficientAdditiveSum_periodic B j X w))
    (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ)) L
    (D*X*(B : ℝ)^(-50 : ℝ)) hL (by positivity) hFb (by
      intro q hq h hh ξ hξ
      have hq12 : (q : ℝ) ≤ (B : ℝ)^12 := by
        exact_mod_cast (mem_positiveDenominators (B^12) q).mp hq
      have hq15 : (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) := by
        rw [Real.rpow_ofNat]
        exact hq12.trans (pow_le_pow_right₀ hB1 (by norm_num : 12 ≤ 15))
      have hξ14 : |ξ| ≤ (B : ℝ)^(14 : ℝ) := by
        rw [Real.rpow_ofNat]
        exact hξ.trans (pow_le_pow_right₀ hB1 (by norm_num : 13 ≤ 14))
      let p := (arcLiftEquiv j (q : ℕ)).symm h
      have he : arcLiftEquiv j (q : ℕ) p = h := (arcLiftEquiv j (q : ℕ)).apply_symm_apply h
      have hr : p.2.val.Coprime (q : ℕ) :=
        (arcLiftEquiv_coprime p.1 p.2).mp (by rw [he]; exact hh)
      have ht := hcoeffB X hX hlog j (q : ℕ) hq15 p.1 p.2 hr
        w w' M N ξ hM0 hN0 hw hw' hwb hw'b hsupp hξ14
      rw [he] at ht
      exact ht)
  have hfactor : (B : ℝ)^12*((B : ℝ)^12+1)*(2*(B : ℝ)^13)*L*
      (D*X*(B : ℝ)^(-50 : ℝ))/X =
      (B : ℝ)^12*((B : ℝ)^12+1)*(2*(B : ℝ)^13)*(D*L)*(B : ℝ)^(-50 : ℝ) := by
    field_simp
  rw [hfactor] at hbound
  refine hbound.trans ((majorArc_error_power hB1 (mul_nonneg hD hL)).trans_eq ?_)
  dsimp [D]
  ring

end JointDickman

end OAI
