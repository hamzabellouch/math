import OAI.NumberTheory.JointDickman.Arithmetic.PrimePhaseRepulsion

namespace OAI

/-! # A uniform qualitative form of the minimizing-twist separation -/
namespace JointDickman
open Complex Filter Finset PublishedInputs
open scoped Topology

lemma primeDistanceSquared_continuous (f : ArithmeticFunction ℂ) (X : ℝ) :
    Continuous (primeDistanceSquared f X) := by
  unfold primeDistanceSquared
  fun_prop

lemma primeDistance_minimizing_twist (f : ArithmeticFunction ℂ) {X : ℝ} (hX : 0 ≤ X) :
    ∃ t₀ : ℝ, |t₀| ≤ X ∧ ∀ t : ℝ, |t| ≤ X →
      primeDistanceSquared f X t₀ ≤ primeDistanceSquared f X t := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (show -X ≤ X by linarith))
    (primeDistanceSquared_continuous f X).continuousOn
  exact ⟨t₀, abs_le.mpr ht₀, fun t ht => hmin (abs_le.mp ht)⟩

/-- Outside a unit neighborhood of a minimizing twist, the distance tends
to infinity uniformly in all bounded coefficient functions. This asserts
qualitative separation only, not the numerical rate of MRT Lemma A.4. -/
theorem primeDistance_separated_from_minimizer (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∃ t₀ : ℝ, |t₀| ≤ X ∧
        (∀ t : ℝ, |t| ≤ X → primeDistanceSquared f X t₀ ≤ primeDistanceSquared f X t) ∧
        ∀ t : ℝ, |t| ≤ X → 1 ≤ |t-t₀| → R ≤ primeDistanceSquared f X t := by
  filter_upwards [two_twist_distance_diverges R, eventually_ge_atTop (0 : ℝ)] with X hsep hX
  intro f hf
  obtain ⟨t₀, ht₀, hmin⟩ := primeDistance_minimizing_twist f hX
  refine ⟨t₀, ht₀, hmin, ?_⟩
  intro t ht hdist
  have hh := hsep f hf t t₀ ht ht₀ hdist
  have hm := hmin t ht
  linarith

end JointDickman

end OAI
