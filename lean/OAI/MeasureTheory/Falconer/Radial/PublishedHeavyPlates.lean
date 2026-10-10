import OAI.MeasureTheory.Falconer.Radial.AffineSubspaceFrostman

namespace OAI

/-! # The published heavy-hyperplane cover used by the coarse-filter construction

P. Shmerkin, *A non-linear version of Bourgain's projection theorem*,
J. Eur. Math. Soc. 25 (2023), 4155--4204, Appendix B, Lemma B.3,
printed pages 4201--4202, DOI 10.4171/JEMS/1283.
Publisher PDF: https://ems.press/content/serial-article-files/32954 .

This is only the hyperplane case k=d-1, at the single scale used in the
application, with heavy threshold delta^(a/8192). The lower-dimensional
concentration hypothesis is retained explicitly. The conclusion covers
each heavy plate in the unit ball by one of finitely many thicker plates.
The constant is allowed to depend on the dimension, a and C. No assertion
about dyadic filters, retained product mass or distance sets is assumed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def heavyPlateExponent (a : ℝ) : ℝ := a/8192

def PublishedHeavyHyperplanes : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ a C : ℝ, 1/2 < a → a < 1 → 0 < C →
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (μ : ProbabilityMeasure (Space d)) (δ : ℝ),
      0 < δ → δ ≤ 1 →
      (∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ < 1) →
      (∀ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 →
        ∀ p : Space d, (μ : Measure (Space d)) (affineSubspaceNeighborhood V p δ) ≤
          ENNReal.ofReal (C*δ^a)) →
      ∃ S : Finset (Space d × ℝ),
        (∀ p ∈ S, ‖p.1‖ = 1) ∧ (S.card:ℝ) ≤ K*δ^(-heavyPlateExponent a) ∧
        ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
          ENNReal.ofReal (δ^(heavyPlateExponent a)) ≤
            (μ : Measure (Space d)) {x | |inner ℝ w x-t| ≤ δ} →
          ∃ p ∈ S, ∀ x : Space d, ‖x‖ < 1 → |inner ℝ w x-t| ≤ δ →
            |inner ℝ p.1 x-p.2| ≤ K*δ^(a-2*heavyPlateExponent a)

theorem heavyPlateExponent_pos {a : ℝ} (ha : 0 < a) : 0 < heavyPlateExponent a := by
  unfold heavyPlateExponent
  positivity

theorem heavyPlate_cover_exponent {a : ℝ} (ha : 1/2 < a) :
    (1/4:ℝ) < a-2*heavyPlateExponent a := by
  unfold heavyPlateExponent
  linarith only [ha]

end Falconer

end OAI
