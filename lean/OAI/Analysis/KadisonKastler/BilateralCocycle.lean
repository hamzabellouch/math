import OAI.Analysis.KadisonKastler.BilateralBoundaryTransport

namespace OAI

/-! Finite random-walk cocycles and the iterated coefficient transport. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralIncrementProduct : ℕ → BilateralWalkPath G → G
  | 0, _ => 1
  | n + 1, ω => (ω (n : ℤ))⁻¹ * bilateralIncrementProduct n ω

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
@[simp] theorem bilateralIncrementProduct_zero (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G 0 ω = 1 := rfl

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
@[simp] theorem bilateralIncrementProduct_succ (n : ℕ) (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G (n + 1) ω = (ω (n : ℤ))⁻¹ * bilateralIncrementProduct G n ω := rfl

omit [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
@[simp] theorem bilateralTranslate_add (a b : ℤ) (ω : BilateralWalkPath G) :
    bilateralTranslate G a (bilateralTranslate G b ω) = bilateralTranslate G (a + b) ω := by
  funext j
  simp [bilateralTranslate, add_assoc]

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
theorem bilateralIncrementProduct_add (n m : ℕ) (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G (n + m) ω =
      bilateralIncrementProduct G m (bilateralTranslate G n ω) * bilateralIncrementProduct G n ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, bilateralIncrementProduct_succ, ih, bilateralIncrementProduct_succ]
    simp [bilateralTranslate, mul_assoc, add_comm]

theorem bilateralIncrementProduct_measurable (n : ℕ) : Measurable (bilateralIncrementProduct G n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : G × G => p.1⁻¹ * p.2)).comp
      ((measurable_pi_apply (n : ℤ)).prodMk ih)

variable {G} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem bilateral_transport_iterate (σ : G →* unitary (K →L[ℂ] K))
    {f : BilateralWalkPath G → K}
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) (n : ℕ) :
    ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G n ω) = (σ (bilateralIncrementProduct G n ω) : K →L[ℂ] K) (f ω) := by
  induction n with
  | zero =>
    apply Filter.Eventually.of_forall
    intro ω
    have hzero : bilateralTranslate G 0 ω = ω := by funext j; simp [bilateralTranslate]
    simp [hzero, bilateralIncrementProduct]
  | succ n ih =>
    have hs := (bilateralTranslate_measurePreserving G n).quasiMeasurePreserving.ae ht
    filter_upwards [hs, ih] with ω hs hω
    have hn : (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by omega
    rw [bilateralTranslate_add, hn] at hs
    rw [hs, hω, bilateralIncrementProduct_succ, map_mul]
    simp only [bilateralTranslate, zero_add]
    rfl

end

end KadisonKastler

end OAI
