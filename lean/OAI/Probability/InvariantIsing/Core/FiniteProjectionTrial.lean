import OAI.Probability.InvariantIsing.Fields.SpinProjectionEntropy

namespace OAI

/-! A trial measure obtained by pushing canonical spins through a finite
map. The log-partition loss consists of the expected energy loss and the
entropy of the projection. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem log_sum_exp_projection_bound {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [DecidableEq Y]
    (f : X → Y) (H : X → ℝ) (K : Y → ℝ) (C : X → ℝ)
    (Z : ℝ) (hZ : 0 < Z)
    (hkernel : ∀ y, (∑ x ∈ Finset.univ.filter (fun x => f x = y),
      Real.exp (-C x)) ≤ Z) :
    Real.log (∑ x, Real.exp (H x)) ≤ Real.log (∑ y, Real.exp (K y)) +
      (∑ x, finiteCanonicalWeights H x * (H x - K (f x))) +
      (∑ x, finiteCanonicalWeights H x * C x) + Real.log Z := by
  let p := finiteCanonicalWeights H
  let q := finitePushforwardWeights f p
  have htrial := log_sum_exp_ge_trial K q
    (finitePushforwardWeights_nonneg f p (fun x => (finiteCanonicalWeights_pos H x).le))
    ((finitePushforwardWeights_sum f p).trans (finiteCanonicalWeights_sum H))
  have he := finite_pushforward_entropy_bound f p C
    (finiteCanonicalWeights_pos H) (finiteCanonicalWeights_sum H) Z hZ hkernel
  have hcan := log_sum_exp_eq_canonical H
  have hav := finitePushforwardWeights_average f p K
  have hsub : (∑ x, p x * (H x - K (f x))) =
      (∑ x, p x * H x) - ∑ x, p x * K (f x) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  change Real.log (∑ x, Real.exp (H x)) ≤ _
  change Real.log (∑ x, Real.exp (H x)) = (∑ x, p x * H x) + finiteShannonEntropy p at hcan
  change (∑ y, q y * K y) = ∑ x, p x * K (f x) at hav
  change finiteShannonEntropy p - finiteShannonEntropy q ≤ _ at he
  change _ ≤ Real.log (∑ y, Real.exp (K y)) at htrial
  change Real.log (∑ x, Real.exp (H x)) ≤ Real.log (∑ y, Real.exp (K y)) +
    (∑ x, p x * (H x - K (f x))) + (∑ x, p x * C x) + Real.log Z
  rw [hsub]
  linarith

end InvariantIsing

end

end OAI
