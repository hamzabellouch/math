import OAI.NumberTheory.JointDickman.Probability.SitePairTestSum
import OAI.NumberTheory.JointDickman.Counting.LagEnvelopeMoments

namespace OAI

/-! # A singular-factor pair bound gives the sampling fixed-test bound -/
namespace JointDickman
open Finset PublishedInputs

variable {M T : ℕ} {A : Type*} [Fintype A]

theorem siteTestMean_le_lag_envelope (hT : 0 < T) {r : ℝ} (hr : 0 ≤ r)
    (p : Fin M → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (E : Fin M → Fin M → A → A → ℝ) (hdiag : ∀ i a, E i i a a = 0)
    (hpair : ∀ i j, i ≠ j → ∀ g h : A → ℝ,
      (∀ a, |g a| ≤ 1) → (∀ b, |h b| ≤ 1) →
      |finiteExpectation (p i) (fun a => finiteExpectation (p j)
        (fun b => E i j a b*g a*h b))| ≤ lagEnvelope T r i j)
    (g h : Fin M → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean p E g h ≤ (M : ℝ)*(2*r*Real.exp 24) := by
  simpa only [Fintype.card_fin] using siteTestMean_le_of_pair_rows p hpone E hdiag (lagEnvelope T r)
    (fun i => lagEnvelope_nonneg T hr i i)
    (fun i j hij g h hg hh => (le_abs_self _).trans (hpair i j hij g h hg hh))
    (fun i => lagEnvelope_row_sum hT hr i) g h hg hh

end JointDickman

end OAI
