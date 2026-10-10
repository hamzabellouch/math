import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePrimeStatisticBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

/-! # Exact giant-prior normalization for the data-dependent template statistic -/
namespace Ostmann
open scoped Classical BigOperators

local instance templateStatisticSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

theorem movingTemplatePrimeAmplitude_smooth_average
    (P : Finset ℕ) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (H : ℝ) :
    movingTemplatePrimeAmplitude Subtype.val outside μ childBound pivotBound V F φ G n r m
      (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) φ H) ν
      greg ggiant favorable =
    smoothGiantExternalAverage ν (V n) φ H H (fun s y XL XR =>
      movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y XL XR *
        movingTaggedTransform (Sum.elim (fun b : Bool => if b then XL else XR) (Subtype.val ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s) := by
  unfold movingTemplatePrimeAmplitude smoothGiantExternalAverage
  simp only [finite_univ_canonical, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext XL
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext s
    arg 2
    ext XL
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr (by ext; simp only [Finset.mem_univ])
  intro y _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro XR _
  apply Finset.sum_congr rfl
  intro XL _
  ring

theorem movingTemplatePrimeAmplitude_statistic_eq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (H : ℝ) :
    movingTemplatePrimeAmplitude Subtype.val outside μ childBound pivotBound V F φ G n r m
      (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) φ H) ν
      greg ggiant favorable =
    (Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      movingTemplatePrimeStatistic P outside μ childBound pivotBound V F φ G n r m ν
        greg ggiant favorable H (H - 1) (H + 1) (H - 1) (H + 1) := by
  rw [movingTemplatePrimeAmplitude_smooth_average, smoothGiantExternalAverage_eq _ _ _ _ _ hout]
  rw [show smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H +
    smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H =
    2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H by ring]
  apply congrArg (fun z : ℂ =>
    (Real.exp (2 * smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) * z)
  unfold movingTemplatePrimeStatistic
  refine primeExternalAverage_congr_primes ν (V n) (H - 1) (H + 1) (H - 1) (H + 1) _ _ ?_
  intro s y XL XR hXL hXR
  let q := fun b : Bool => if b then XL else XR
  let _ : ∀ b, Fact (q b).Prime := fun b => ⟨by cases b <;> assumption⟩
  let _ : ∀ i, Fact ((Subtype.val ∘ y) i).Prime := fun i => ⟨hP _ (y i).property⟩
  have ht : movingTaggedTransform (Sum.elim q (Subtype.val ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
      movingRegularTransform (Sum.elim q (Subtype.val ∘ y))
        (fun i => match i with
          | .inl b => fun t => if favorable (q b) then complexUnitPhase (ggiant (q b) t) else 0
          | .inr j => greg (y j)) outside.prod s := by
    unfold movingTaggedTransform movingRegularTransform
    apply Finset.prod_congr rfl
    intro i _
    cases i <;> rfl
  have hf := movingTemplateCoefficient_full_transform Subtype.val outside μ childBound pivotBound V F
    φ G n r m s y q (fun i => hP _ (y i).property) greg ggiant favorable
  have hcore : movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F
      φ G n r m s y XL XR * movingTaggedTransform (Sum.elim q (Subtype.val ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
      (giantPairPhase ggiant favorable outside.prod (∏ i, (y i : ℕ)) XL XR s *
        primeProductTransform greg (outside.prod * XL * XR) (∏ i, (y i : ℕ)) s) *
        movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G n r m s y XL XR := by
    rw [mul_comm, ht]
    exact hf
  have hp : (0 : ℝ) < XL := Nat.cast_pos.mpr hXL.pos
  have hr : (0 : ℝ) < XR := Nat.cast_pos.mpr hXR.pos
  simp only [Real.exp_log hp, Real.exp_log hr, Nat.floor_natCast]
  rw [show (fun b : Bool => if b then XL else XR) = q from rfl, hcore]
  simp only [movingGiantPhase, movingExternalRegularFactor, movingTemplate_product,
    Real.exp_log hp, Real.exp_log hr, Nat.floor_natCast, giantOuterWeight,
    Bool.false_eq_true, ite_false, mul_one, positiveLogCutoff, hp, hr, ite_true]
  ring

end Ostmann

end OAI
