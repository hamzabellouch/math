import OAI.NumberTheory.JointDickman.Counting.ArcCoefficientIdentity

namespace OAI

/-! # The published coefficient expansion on the actual lifted arcs -/

namespace JointDickman
open Filter MeasureTheory
open scoped Topology ArithmeticFunction.Moebius

noncomputable def coefficientFourierTransform (c : ℕ → ℝ) (H B : ℕ)
    (X : ℝ) (w : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)*
    additivePhase (-ξ*s)

theorem coefficient_lifted_majorArc_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ (j q : ℕ) [NeZero j] [NeZero q] [NeZero (j*q)],
      (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) → ∀ (t : Fin j) (r : Fin q), r.val.Coprime q →
      ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ x, HasDerivAt w (w' x) x) → Continuous w' →
      (∀ x, |w x| ≤ M) → (∀ x, |w' x| ≤ N) →
      (∀ x, x ≤ a ∨ b < x → w x = 0) → |ξ| ≤ (B : ℝ)^(14 : ℝ) →
      ‖smoothCoefficientAdditiveSum B X (-(j : ℝ)*
          (((arcLiftEquiv j q (t,r)).val : ℝ)/(j*q : ℕ)+ξ/((j : ℝ)*X))) w -
        (X : ℂ)*((μ q : ℂ)/(q.totient : ℂ))*coefficientFourierTransform c H B X w ξ‖ ≤
        (K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*X*(B : ℝ)^(-50 : ℝ) := by
  obtain ⟨c,hc,hcpos,H,K,hK,hbound⟩ := coefficient_oscillatory_law hSD hSW hM
  refine ⟨c,hc,hcpos,H,K,hK,?_⟩
  intro a b ha hab
  filter_upwards [hbound a b ha hab] with B hB
  intro X hX hlog j q _ _ _ hq t r hr w w' M N ξ hM0 hN0 hw hw' hwb hw'b hsupp hξ
  rw [lifted_arc_smooth_coefficient B t r hr hX.ne']
  exact hB X hX hlog q hq (-(ZMod.unitOfCoprime r.val hr)) w w' M N (-ξ)
    hM0 hN0 hw hw' hwb hw'b hsupp (by simpa only [abs_neg] using hξ)

end JointDickman

end OAI
