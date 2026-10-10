import OAI.Geometry.SurfaceImmersion.Correction.GlobalSmoothingBounds
import OAI.Geometry.SurfaceImmersion.Correction.ShiftedSmoothingBounds

namespace OAI

/-! Fixed-atlas smoothing with an unweighted derivative prefix. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold MeasureTheory
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Localized norms whose first `q` derivatives are unweighted. -/
def ShiftedBound (q m : ℕ) (s C : ℝ) (f : M → V) : Prop :=
  ∀ i : A.centers, FiniteOrderSmoothing.ShiftedBound q m s C
    (localize (i : M) (A.weight i) f)

/-- Fixed smooth chart transitions preserve the unweighted prefix. -/
theorem restoration_shifted_bound (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, FiniteOrderSmoothing.ShiftedBound q m s C (h i)) →
      A.ShiftedBound q m s (D * C)
        (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hd using fun j : ℕ => A.restoration_bound (V := V) j
  refine ⟨∑ j ∈ Finset.range (q + m + 1), D j,
    Finset.sum_nonneg (fun j _ => hD j), ?_⟩
  intro h s C hs hs1 hC hh hb i j hj x
  have he : 0 < s ^ (j - q) := pow_pos hs _
  have ho := hd j h 1 (C / s ^ (j - q)) zero_lt_one le_rfl
    (div_nonneg hC he.le) hh (fun k => (hb k).prefix hs hs1 hC hj)
  have hi := ho i j le_rfl x (mem_univ x)
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ] at hi
  calc
    _ ≤ s ^ (j - q) * (D j * (C / s ^ (j - q))) :=
      mul_le_mul_of_nonneg_left hi he.le
    _ = D j * C := by field_simp
    _ ≤ (∑ k ∈ Finset.range (q + m + 1), D k) * C :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC

/-- Global gain of arbitrary higher derivatives uses only the fixed prefix. -/
theorem smoothing_shifted_gain (r q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ, V) ∞ f →
      A.ShiftedBound q 0 1 C f → A.ShiftedBound q m s
        (D * ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C)
        (A.smooth r s f) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_shifted_bound (V := V) q m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hg := weightedGainConstant_nonneg r m
  have h := hd (fun i => finiteSmooth r s (localize (i : M) (A.weight i) f)) s
    (((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C)
    hs hs1 (by positivity)
    (fun i => finiteSmooth_smooth r hs
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
    (fun i => finiteSmooth_shifted_gain r q m hs hC
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
      (localize_compact (i : M) (A.weight_support i) f)
      (by simpa using (hb i).prefix zero_lt_one le_rfl hC (j := q) (by omega)))
  simpa only [smooth, mul_assoc] using h

/-- The same global smoother is bounded at every original shifted order. -/
theorem smoothing_shifted_bounded (r q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : M → V) (s t C : ℝ),
      0 < s → 0 < t → t ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ, V) ∞ f →
      A.ShiftedBound q m t C f → A.ShiftedBound q m t
        (D * (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) (A.smooth r s f) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_shifted_bound (V := V) q m
  refine ⟨D, hD, ?_⟩
  intro f s t C hs ht ht1 hC hf hb
  have h := hd (fun i => finiteSmooth r s (localize (i : M) (A.weight i) f)) t
    ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) ht ht1 (by positivity)
    (fun i => finiteSmooth_smooth r hs
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
    (fun i => finiteSmooth_shifted_bounded r q m hs ht
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
      (localize_compact (i : M) (A.weight_support i) f) (hb i))
  simpa only [smooth, mul_assoc] using h

variable [CompleteSpace V]

/-- The actual global smoothing error obeys the shifted two-scale estimate. -/
theorem smoothing_shifted_tail (r q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : M → V) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel 𝓘(ℝ, V) ∞ f →
      A.ShiftedBound q r t B f → A.ShiftedBound q m t C f →
      A.ShiftedBound q m τ
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (f - A.smooth r s f) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_shifted_bound (V := V) q m
  refine ⟨D, hD, ?_⟩
  intro f s t τ B C hτ hτs hst ht1 hB hC hf hb hc
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτ1 : τ ≤ 1 := hτs.trans (hst.trans ht1)
  have hsize : 0 ≤ tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r) :=
    mul_nonneg (tailConstant_nonneg r) (by positivity)
  have h := hd (fun i => residual s r (localize (i : M) (A.weight i) f)) τ
    (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r)) hτ hτ1 hsize
    (fun i => residual_smooth hs r
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
    (fun i => by
      rw [← error_finiteSmooth]
      exact shifted_smoothing_tail r q m hτ hτs hst ht1 hB hC
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
        (localize_compact (i : M) (A.weight_support i) f) (hb i) (hc i))
  rw [A.sub_smooth_eq_error]
  simpa only [error, mul_assoc] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
