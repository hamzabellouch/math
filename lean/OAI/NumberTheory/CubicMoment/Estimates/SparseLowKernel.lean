import OAI.NumberTheory.CubicMoment.Estimates.SparseKernelTwists
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductHeight
import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductEnvelope

namespace OAI

/-! Actual low-height sparse late-stop cancellation. The common angular
and norm twists are placed on the two independent coefficient sides. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem ordinary_sparse_low_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hpnt : PrimaryPrimePNT) {C ξ D : ℝ} (hC : 0 < C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hD : 1 ≤ D) (Ct : ℕ) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (A B ρ H : ℝ) (ℓ : ℤ), 0 < A → Real.exp 1 ≤ 2*A →
      X^(35/100:ℝ) ≤ B → B ≤ X^(40/100:ℝ) → 2*A ≤ D*X/B →
      1 < ρ → ρ ≤ 2 → 0 < H →
      ∀ (j k h : ℕ), ρ*geometricBinLower ρ X h ≤ (Real.log X)^C →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R F E U P Q : Finset Eisenstein) (remaining : Eisenstein → Prop),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ F, primary d ∧ norm d ≤ X) →
      (∀ e ∈ E, primary e) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A) →
      (∀ b ∈ Q, primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B) →
      let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
      let β := stoppedBeta R F
        (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
        primeDetectorCutoff (X^ξ)
        (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
      ‖∑ a ∈ P, ∑ b ∈ Q, α a*β b*
        centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-τ) := by
  obtain ⟨τ,K,hτ,hK,hbound⟩ := ordinary_sparse_centered_bilinear (ι := ι)
    hpnt hC hξ hξz hD primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨τ,(8/3)*Real.log 2*K,hτ,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hbound hX
  intro A B ρ H ℓ hA h2A hBlo hBhi hAB hρ hρ₂ hH j k h hboundary
    S W R F E U P Q remaining hS hW hR hF hE hP hQ
  dsimp only
  let α := stoppedAlpha E U primeDetectorCutoff (X^ξ) remaining
  let β := stoppedBeta R F
    (distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
    primeDetectorCutoff (X^ξ)
    (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h (X^(38/100:ℝ)) (X^(36/100:ℝ)) false)
  let T := (1+Real.log X)^Ct
  have hT : 0 < T := by dsimp [T]; positivity [Real.log_nonneg hX]
  have hM : 0 ≤ K*X^(5/6-τ) := by positivity
  have hb (t : ℝ) : ‖centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t‖ ≤
      K*X^(5/6-τ) := by
    have he := hbound A B ρ hA h2A hBlo hBhi hAB hρ hρ₂ j k h hboundary
      S W R F E U P Q remaining (fun a => theta ℓ a*normTwist t a)
      (fun b => theta ℓ b*normTwist t b) hS hW hR hF hE hP hQ
      (fun a ha => (sparse_common_twist_norm (hP a ha).1 ℓ t).le)
      (fun b hb => (sparse_common_twist_norm (hQ b hb).1 ℓ t).le)
    rw [←sparse_common_twist_identity P Q (fun a ha => (hP a ha).1)
      (fun b hb => (hQ b hb).1) α β centeredGauss
      (fun n => primeProductEnvelope (norm n/X)) ℓ t] at he
    convert he using 1
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [centered_product_low_integral P Q α β ℓ primeProductEnvelope X X T hH]
  have heint : (fun t => (lowHeightWeight H T t*Complex.exp ((-Real.log X*t:ℝ)*Complex.I))*
      centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t) =
      (fun t => lowHeightWeight H T t*(Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
        centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t)) := by funext t; ring
  rw [heint]
  have hi := lowHeightWeight_integral_bound H hT hM
    (fun t => Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
      centeredProductSmoothed P Q α β ℓ primeProductEnvelope X t) (by
        intro t _
        rw [norm_mul]
        have hephase : ‖Complex.exp ((-Real.log X*t:ℝ)*Complex.I)‖ = 1 := by
          simp only [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
            Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,Real.exp_zero]
        rw [hephase,one_mul]
        exact hb t)
  exact hi.trans_eq (by dsimp [T]; ring)

end CubicFirstMoment

end

end OAI
