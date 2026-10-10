import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.LocalFlatBallTransfer
import OAI.Analysis.RieszRectifiability.Limits.CompactSupportApproximants

namespace OAI

/-!
Local bilateral flatness in a compact-test limit transfers to nearby support points of the
approximating measures, contradicting an eventual lower bound on their local flatness error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_excludes_local_flat_ball {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (U : Set (Ambient d)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) (hr : 0 < r)
    (hbad : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ U → ε ≤ bilateralBeta n (μ j) b r)
    (a : Ambient d) (ha : a ∈ ν.support) (haU : a ∈ U) :
    ¬ ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      (∀ x ∈ ball a (2 * r), x ∈ ν.support → infDist x (S : Set (Ambient d)) < ε * r / 16) ∧
      (∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16) := by
  rintro ⟨S, hS, hforward, hreverse⟩
  obtain ⟨φ, b, _, hφ, hbs, hb⟩ := compactTestConvergence_support_approximants μ ν hlocal a ha
  let : ∀ j, IsFiniteMeasureOnCompacts ((μ ∘ φ) j) :=
    fun j => inferInstanceAs (IsFiniteMeasureOnCompacts (μ (φ j)))
  have hc : CompactTestConvergence (μ ∘ φ) ν := fun f => (hlocal f).comp hφ
  have ht := compactTestConvergence_local_flat_ball n (μ ∘ φ) ν hc C hC
    (fun j => hlower (φ j)) (fun t ht => hφ.eventually (hdiam t ht))
    a ha b hb r ε hr hε hε1 S hS hforward hreverse
  obtain ⟨j, hjflat, hjbad, hjU⟩ :=
    (ht.and ((hφ.eventually hbad).and (hb.eventually (hU.mem_nhds haU)))).exists
  exact (not_lt_of_ge (hjbad (b j) (hbs j) hjU)) hjflat

end

end RieszRectifiability

end OAI
