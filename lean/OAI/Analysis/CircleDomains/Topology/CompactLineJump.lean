import OAI.Analysis.CircleDomains.Topology.DiskLineIntegration
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! Compactly supported tests turn the finite-interval jump estimate into
an estimate over the entire line. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem filled_line_integration_through_disks_univ
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f F ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hρ : Integrable ρ)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hF : EqOn F (clipScalar ∘ f) (diskLineDomain c r y))
    (hfill : ∀ i x, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i) → F x = clipScalar (value i))
    (hcluster : ∀ i p u, (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f → |u - value i| ≤ A i)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo a b)
    (hint : Integrable (fun x => F x * deriv φ x))
    (hdint : Integrable (fun x => deriv F x * φ x))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |φ x| ≤ C) :
    |(∫ x, F x * deriv φ x) + (∫ x, deriv F x * φ x)| ≤
      2 * C * ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  have hzero : φ a = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; exact (lt_irrefl a) (hsupp h).1)
  have hone : φ b = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h; exact (lt_irrefl b) (hsupp h).2)
  have hs₁ : support (fun x => F x * deriv φ x) ⊆ Ioc a b := by
    intro x hx
    have hder : x ∈ support (deriv φ) := by
      intro h
      exact hx (by simp [h])
    exact Ioo_subset_Ioc_self (hsupp (support_deriv_subset hder))
  have hs₂ : support (fun x => deriv F x * φ x) ⊆ Ioc a b := by
    intro x hx
    have hφx : x ∈ support φ := by
      intro h
      exact hx (by simp [h])
    exact Ioo_subset_Ioc_self (hsupp (subset_tsupport φ hφx))
  have h := filled_line_integration_through_disks c r value A hr hA hdisj hab ha hb
    hf hρ hmajor hF hfill hcluster hφ hzero hone hint hdint hC hbound
  simpa only [intervalIntegral.integral_eq_integral_of_support_subset hs₁,
    intervalIntegral.integral_eq_integral_of_support_subset hs₂] using h

end CircleDomainRigidity

end OAI
