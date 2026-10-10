import OAI.NumberTheory.DukePrimeDegree.Entropy.ControlledCutObservation

namespace OAI

/-! # Boundary avoidance across changing finite levels

The union bound and Borel--Cantelli apply to all cuts up to a level that
changes with time. The summability hypothesis is an explicit numerical
budget; no entropy or subordinate-partition conclusion is assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace DukePrimeDegree

theorem ae_eventually_avoid_varying_cut_levels
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Measurable (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (L : ℕ → ℕ) (ε : ℕ → ℝ) (B : ℕ → ℕ → ℝ≥0∞)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) (ε k)) ≤ B m k)
    (hbudget : (∑' k, ∑ m ∈ Finset.range (L k+1), (N m:ℝ≥0∞)*B m k) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ m ≤ L k, ∀ i,
      ε k < |f m i (T^[k] x)-c m i| := by
  classical
  let S (k : ℕ) : Set Y := ⋃ m ∈ Finset.range (L k+1), ⋃ i : Fin (N m),
    (T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)
  have hpre (k m : ℕ) (i : Fin (N m)) :
      μ ((T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)) ≤ B m k := by
    rw [(hT.iterate k).measure_preimage
      (realBoundaryStrip_measurableSet (hf m i) _ _).nullMeasurableSet]
    exact hbound m i k
  have hS (k : ℕ) : μ (S k) ≤ ∑ m ∈ Finset.range (L k+1), (N m:ℝ≥0∞)*B m k := by
    calc
      _ ≤ ∑ m ∈ Finset.range (L k+1), μ (⋃ i : Fin (N m),
          (T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.range (L k+1), ∑ i : Fin (N m),
          μ ((T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)) :=
        Finset.sum_le_sum fun m _ => measure_iUnion_fintype_le _ _
      _ ≤ ∑ m ∈ Finset.range (L k+1), ∑ _i : Fin (N m), B m k :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i _ => hpre k m i
      _ = _ := by simp
  have hsum : (∑' k, μ (S k)) ≠ ∞ :=
    ne_top_of_le_ne_top hbudget (ENNReal.tsum_le_tsum hS)
  filter_upwards [ae_eventually_notMem (μ := μ) (s := S) hsum] with x hx
  filter_upwards [hx] with k hk
  intro m hm i
  apply lt_of_not_ge
  intro hbad
  apply hk
  exact mem_iUnion₂.mpr ⟨m,Finset.mem_range.mpr (by omega),
    mem_iUnion.mpr ⟨i,hbad⟩⟩

end DukePrimeDegree

end

end OAI
