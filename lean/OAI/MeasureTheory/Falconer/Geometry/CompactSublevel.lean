import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem exists_positive_compact_sublevel {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsProbabilityMeasure μ] {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (f : X → ℝ≥0∞) (hf : LowerSemicontinuous f)
    {p : ℝ} (hp : 0 < p) (hI : (∫⁻ x, (f x)^p ∂μ) < ∞) :
    ∃ A : Set X, IsCompact A ∧ A ⊆ K ∧ 0 < μ A ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x ∈ A, f x ≤ C := by
  let A : ℕ → Set X := fun n => K ∩ f ⁻¹' Iic (n : ℝ≥0∞)
  have hfinite : ∀ᵐ x ∂μ, f x < ∞ := by
    filter_upwards [ae_lt_top (hf.measurable.pow_const p) hI.ne] with x hx
    by_contra h
    have ht : f x = ∞ := top_unique (not_lt.mp h)
    rw [ht, ENNReal.top_rpow_of_pos hp] at hx
    exact lt_irrefl _ hx
  have hfull : ∀ᵐ x ∂μ, x ∈ ⋃ n, A n := by
    filter_upwards [hμ, hfinite] with x hx hfx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfx.ne
    exact mem_iUnion.mpr ⟨n, hx, hn.le⟩
  obtain ⟨n, hn⟩ : ∃ n, 0 < μ (A n) := by
    by_contra h
    have hz : ∀ n, μ (A n) = 0 := fun n => le_antisymm (not_lt.mp (fun hn => h ⟨n, hn⟩)) bot_le
    have hzero : μ (⋃ n, A n) = 0 := measure_iUnion_null hz
    have hc : μ (⋃ n, A n)ᶜ = 0 := by
      change μ {x | x ∉ ⋃ n, A n} = 0
      exact (ae_iff.mp hfull)
    have hu : μ univ = 0 := by
      rw [← union_compl_self (⋃ n, A n)]
      exact measure_union_null hzero hc
    simp at hu
  refine ⟨A n, hK.inter_right (hf.isClosed_preimage n), inter_subset_left, hn,
    n, ENNReal.natCast_ne_top n, fun x hx => hx.2⟩

end PlanarFalconer

end OAI
