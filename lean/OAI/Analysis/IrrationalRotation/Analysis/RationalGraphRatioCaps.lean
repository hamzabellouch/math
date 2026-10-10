import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphTrimming
import OAI.Analysis.IrrationalRotation.Analysis.InfiniteRatioCaps
import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleReindex

namespace OAI

noncomputable section
open MeasureTheory Function Set
open scoped BigOperators
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem floorCocycle_ratio_le_prefix {A : ℕ} (hA : 1 ≤ A) (x y : Circle) (v : ℤ)
    (hxy : ∀ i, A ≤ i → p.coordinate i x ≤ p.coordinate i y)
    (hx : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) x + (v : ℝ) * p.alpha θ (k + 1))))
    (hy : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) y + (v : ℝ) * p.alpha θ (k + 1)))) :
    p.floorCocycle θ v y / p.floorCocycle θ v x ≤
      Real.exp (p.rationalGraphPrefixCost A) := by
  rw [hp.parameter_cocycle_eq_flattened, hp.parameter_cocycle_eq_flattened]
  apply CircleWeights.cocycle_ratio_cap_finite_exceptions
    θ p.flattenedFrequency p.flattenedCost v x y (Finset.range (A - 1))
    (fun k => (hp.flattenedCost_pos k).le)
  · intro k hk
    have hkA : A ≤ k + 1 := by simp only [Finset.mem_range] at hk; omega
    simpa only [CircleWeights.coordinate, CircleWeights.representative,
      flattenedFrequency, coordinate, rep, natCast_zsmul] using hxy (k + 1) hkA
  · simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast] using hx
  · simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast] using hy

theorem trimmed_floorCocycle_ratio_le {A j n : ℕ} (hA : 1 ≤ A) (hj : 1 ≤ j)
    (x : Circle) (hx : x ∈ p.rationalGraphGood A j) (t : ℝ)
    (ht : p.q A • (t : Circle) = 0)
    (hphase : Int.fract ((n : ℝ) * θ - t) < p.ell j)
    (hn : (n : ℝ) ≤ p.Q j) (hd : p.orbitGraphDensity θ j n x ≠ 0) (v : ℤ)
    (hfx : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) x + (v : ℝ) * p.alpha θ (k + 1))))
    (hfy : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) (x + (((n : ℝ) * θ : ℝ) : Circle)) +
        (v : ℝ) * p.alpha θ (k + 1)))) :
    p.floorCocycle θ v (x + (((n : ℝ) * θ : ℝ) : Circle)) / p.floorCocycle θ v x ≤
      Real.exp (p.rationalGraphPrefixCost A) :=
  hp.floorCocycle_ratio_le_prefix hA x _ v
    (hp.ordered_of_rationalGraphGood hA hj x hx t ht hphase hn hd) hfx hfy

theorem exists_uniform_rationalGraph_cap_set :
    ∃ s : Set Circle, MeasurableSet s ∧ (∀ᵐ x ∂circleMeasure, x ∈ s) ∧
      (∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s) ∧
      ∀ (A j n : ℕ), 1 ≤ A → 1 ≤ j → ∀ x ∈ s,
        x ∈ p.rationalGraphGood A j → ∀ t : ℝ,
        p.q A • (t : Circle) = 0 →
        Int.fract ((n : ℝ) * θ - t) < p.ell j →
        (n : ℝ) ≤ p.Q j → p.orbitGraphDensity θ j n x ≠ 0 →
        ∀ v : ℤ, p.floorCocycle θ v (x + (((n : ℝ) * θ : ℝ) : Circle)) /
          p.floorCocycle θ v x ≤ Real.exp (p.rationalGraphPrefixCost A) := by
  have hq : ∀ k, p.flattenedFrequency k ≠ 0 := by
    intro k
    change (p.q (k + 1) : ℤ) ≠ 0
    exact_mod_cast (hp.q_pos (k + 1)).ne'
  have hphase : Summable (CircleWeights.phase θ p.flattenedFrequency) := by
    change Summable (fun k : ℕ => Int.fract (((p.q (k + 1) : ℤ) : ℝ) * θ))
    simpa only [alpha, Int.cast_natCast] using hp.summable_phases
  obtain ⟨s, hs, hfull, hinv, hfinite, _⟩ := CircleWeights.exists_cocycle_set
    θ p.flattenedFrequency hq p.flattenedCost hphase
  refine ⟨s, hs, hfull, hinv, ?_⟩
  intro A j n hA hj x hx hgood t ht hph hn hd v
  apply hp.trimmed_floorCocycle_ratio_le hA hj x hgood t ht hph hn hd v
  · simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast] using hfinite x hx v
  · have hy := hfinite (CircleWeights.rotate θ (n : ℤ) x) ((hinv (n : ℤ) x).mpr hx) v
    simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, CircleWeights.rotate, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast, ← AddCircle.coe_nsmul, nsmul_eq_mul] using hy

end Invariant233.CircleParameterLaws

end

end OAI
