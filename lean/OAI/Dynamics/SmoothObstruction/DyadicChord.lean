import Mathlib

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators

namespace SmoothObstruction.DyadicChord

def prefixSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, f j
noncomputable def average (f : ℕ → ℝ) (n : ℕ) : ℝ := prefixSum f n / n
noncomputable def chord (f : ℕ → ℝ) (n u : ℕ) : ℝ := prefixSum f u - u * average f n
noncomputable def deviation (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' (by simp) (fun u => |chord f n u| / n)

lemma prefixSum_add (f : ℕ → ℝ) (n m : ℕ) :
    prefixSum f (n + m) = prefixSum f n + prefixSum (fun j => f (n + j)) m := by
  simp only [prefixSum, sum_range_add]

lemma deviation_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ deviation f n := by
  have h := Finset.le_sup' (fun u => |chord f n u| / n)
    (show 0 ∈ range (n + 1) by simp)
  calc
    0 = |chord f n 0| / n := by simp [chord, prefixSum]
    _ ≤ deviation f n := h

lemma abs_chord_le (f : ℕ → ℝ) {n u : ℕ} (hn : 0 < n) (hu : u ≤ n) :
    |chord f n u| ≤ n * deviation f n := by
  have h := Finset.le_sup' (fun u => |chord f n u| / n)
    (show u ∈ range (n + 1) by simpa using Nat.lt_succ_of_le hu)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have := (div_le_iff₀ hn').mp h
  simpa [deviation, mul_comm] using this

lemma deviation_le (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) {D : ℝ}
    (hD : ∀ u ≤ n, |chord f n u| ≤ n * D) : deviation f n ≤ D := by
  apply Finset.sup'_le
  intro u hu
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  simpa [mul_comm] using hD u (Nat.le_of_lt_succ (Finset.mem_range.mp hu))

@[simp] lemma deviation_one (f : ℕ → ℝ) : deviation f 1 = 0 := by
  apply le_antisymm _ (deviation_nonneg f 1)
  apply deviation_le f (by omega)
  intro u hu
  interval_cases u <;> simp [chord, average, prefixSum]

lemma average_double (f : ℕ → ℝ) {n : ℕ} (_hn : 0 < n) :
    average f (2 * n) = (average f n + average (fun j => f (n + j)) n) / 2 := by
  rw [show 2 * n = n + n by omega, average, prefixSum_add]
  simp only [Nat.cast_add, average]
  ring

lemma prefixSum_eq (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    prefixSum f n = n * average f n := by
  unfold average
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp

lemma chord_left (f : ℕ → ℝ) (n u : ℕ) :
    chord f (2 * n) u = chord f n u + u * (average f n - average f (2 * n)) := by
  unfold chord
  ring

lemma chord_right (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (u : ℕ) :
    chord f (2 * n) (n + u) = chord (fun j => f (n + j)) n u +
      ((n : ℝ) - u) * (average f n - average f (2 * n)) := by
  simp only [chord, prefixSum_add, Nat.cast_add]
  rw [prefixSum_eq f hn, average_double f hn]
  ring

/-- A deterministic midpoint recurrence for maximal deviation from the
block's own chord. No independence or average mixing hypothesis is used. -/
lemma deviation_double_le (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    deviation f (2 * n) ≤
      (|average f n - average f (2 * n)| +
        max (deviation f n) (deviation (fun j => f (n + j)) n)) / 2 := by
  apply deviation_le f (by omega)
  intro u hu
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let D := max (deviation f n) (deviation (fun j => f (n + j)) n)
  have hbound_left : ∀ u ≤ n, |chord f (2 * n) u| ≤
      n * (|average f n - average f (2 * n)| + D) := by
    intro v hv
    rw [chord_left]
    calc
      _ ≤ |chord f n v| + |(v : ℝ) * (average f n - average f (2 * n))| := abs_add_le _ _
      _ = |chord f n v| + v * |average f n - average f (2 * n)| := by
        rw [abs_mul, show |(v : ℝ)| = v from abs_of_nonneg (Nat.cast_nonneg v)]
      _ ≤ n * deviation f n + n * |average f n - average f (2 * n)| :=
        add_le_add (abs_chord_le f hn hv)
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) (abs_nonneg _))
      _ ≤ n * (|average f n - average f (2 * n)| + D) := by
        have h := mul_le_mul_of_nonneg_left (le_max_left (deviation f n)
          (deviation (fun j => f (n + j)) n)) hn0
        dsimp [D]
        linarith
  have hbound_right : ∀ v ≤ n, |chord f (2 * n) (n + v)| ≤
      n * (|average f n - average f (2 * n)| + D) := by
    intro v hv
    rw [chord_right f hn]
    calc
      _ ≤ |chord (fun j => f (n + j)) n v| +
          |((n : ℝ) - v) * (average f n - average f (2 * n))| := abs_add_le _ _
      _ = |chord (fun j => f (n + j)) n v| +
          ((n : ℝ) - v) * |average f n - average f (2 * n)| := by
        rw [abs_mul, show |(n : ℝ) - v| = (n : ℝ) - v from
          abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hv))]
      _ ≤ n * deviation (fun j => f (n + j)) n + n * |average f n - average f (2 * n)| :=
        add_le_add (abs_chord_le _ hn hv)
          (mul_le_mul_of_nonneg_right (by simp) (abs_nonneg _))
      _ ≤ n * (|average f n - average f (2 * n)| + D) := by
        have h := mul_le_mul_of_nonneg_left (le_max_right (deviation f n)
          (deviation (fun j => f (n + j)) n)) hn0
        dsimp [D]
        linarith
  have h : |chord f (2 * n) u| ≤ n * (|average f n - average f (2 * n)| + D) := by
    by_cases hun : u ≤ n
    · exact hbound_left u hun
    · simpa only [Nat.add_sub_of_le (by omega : n ≤ u)] using
        hbound_right (u - n) (by omega)
  calc
    _ ≤ n * (|average f n - average f (2 * n)| + D) := h
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, D]; ring

/-- A rational square version, more convenient for summing the L² energies. -/
lemma deviation_double_sq (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (deviation f (2 * n))^2 ≤
      (3 / 4 : ℝ) * (average f n - average f (2 * n))^2 +
      (3 / 8 : ℝ) * ((deviation f n)^2 + (deviation (fun j => f (n + j)) n)^2) := by
  have h := deviation_double_le f hn
  have h0 := deviation_nonneg f (2 * n)
  have hl := deviation_nonneg f n
  have hr := deviation_nonneg (fun j => f (n + j)) n
  have hd0 : 0 ≤ |average f n - average f (2 * n)| := abs_nonneg _
  have hsq := sq_abs (average f n - average f (2 * n))
  rcases le_total (deviation f n) (deviation (fun j => f (n + j)) n) with hh | hh
  · rw [max_eq_right hh] at h
    nlinarith [sq_nonneg (|average f n - average f (2 * n)| - deviation (fun j => f (n + j)) n / 2),
      sq_nonneg (deviation f n)]
  · rw [max_eq_left hh] at h
    nlinarith [sq_nonneg (|average f n - average f (2 * n)| - deviation f n / 2),
      sq_nonneg (deviation (fun j => f (n + j)) n)]

end SmoothObstruction.DyadicChord

namespace SmoothObstruction.DyadicChord

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma prefixSum_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n : ℕ) :
    MemLp (fun x => prefixSum (fun j => Y j x) n) 2 μ := by
  exact memLp_finsetSum _ (fun j _ => hY j)

lemma average_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n : ℕ) :
    MemLp (fun x => average (fun j => Y j x) n) 2 μ := by
  simpa only [average, div_eq_mul_inv] using (prefixSum_memLp hY n).mul_const (n : ℝ)⁻¹

lemma chord_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n u : ℕ) :
    MemLp (fun x => chord (fun j => Y j x) n u) 2 μ := by
  exact (prefixSum_memLp hY u).sub ((average_memLp hY n).const_mul u)

lemma deviation_memLp {Y : ℕ → Ω → ℝ} (hY : ∀ j, MemLp (Y j) 2 μ) (n : ℕ) :
    MemLp (fun x => deviation (fun j => Y j x) n) 2 μ := by
  have h : MemLp ((range (n + 1)).sup' (by simp)
      (fun u x => |chord (fun j => Y j x) n u| / n)) 2 μ := by
    apply Finset.sup'_induction (p := fun g : Ω → ℝ => MemLp g 2 μ) (by simp)
      (fun u x => |chord (fun j => Y j x) n u| / n)
    · intro f hf g hg
      exact hf.sup hg
    · intro u _
      simpa only [Real.norm_eq_abs, div_eq_mul_inv] using
        (chord_memLp hY n u).norm.mul_const (n : ℝ)⁻¹
  convert h using 1
  funext x
  exact (Finset.sup'_apply (s := range (n + 1)) (by simp)
    (fun u x => |chord (fun j => Y j x) n u| / n) x).symm

/-- A measure-preserving transformation gives precisely the stationarity needed
below; no independence, ergodicity, or decay of correlations enters. -/
def orbit (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) (j : ℕ) : ℝ := f (T^[j] x)

omit [MeasurableSpace Ω] in
lemma orbit_shift (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) (n : ℕ) :
    (fun j => orbit T f x (n + j)) = orbit T f (T^[n] x) := by
  funext j
  simp only [orbit, Nat.add_comm n j, Function.iterate_add_apply]

lemma integral_comp_preserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) :
    (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hgm : AEStronglyMeasurable g (Measure.map T μ) := by
    rw [hT.map_eq]
    exact hg.aestronglyMeasurable
  have h := integral_map hT.measurable.aemeasurable hgm
  rw [hT.map_eq] at h
  exact h.symm

lemma orbit_memLp {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (j : ℕ) : MemLp (fun x => orbit T f x j) 2 μ :=
  hf.comp_measurePreserving (hT.iterate j)

noncomputable def averageEnergy (T : Ω → Ω) (f : Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ x, (average (orbit T f x) n)^2 ∂μ

noncomputable def deviationEnergy (T : Ω → Ω) (f : Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  ∫ x, (deviation (orbit T f x) n)^2 ∂μ

lemma averageEnergy_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) :
    0 ≤ averageEnergy T f μ n := integral_nonneg (fun _ => sq_nonneg _)

lemma deviationEnergy_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) :
    0 ≤ deviationEnergy T f μ n := integral_nonneg (fun _ => sq_nonneg _)

@[simp] lemma deviationEnergy_one (T : Ω → Ω) (f : Ω → ℝ) :
    deviationEnergy T f μ 1 = 0 := by simp [deviationEnergy]

@[simp] lemma averageEnergy_one (T : Ω → Ω) (f : Ω → ℝ) :
    averageEnergy T f μ 1 = ∫ x, (f x)^2 ∂μ := by
  simp [averageEnergy, average, prefixSum, orbit]

lemma averageEnergy_shift {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (n m : ℕ) :
    (∫ x, (average (fun j => orbit T f x (n + j)) m)^2 ∂μ) = averageEnergy T f μ m := by
  simp only [orbit_shift]
  exact integral_comp_preserving (hT.iterate n) ((average_memLp (orbit_memLp hT hf) m).integrable_sq)

lemma deviationEnergy_shift {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (n m : ℕ) :
    (∫ x, (deviation (fun j => orbit T f x (n + j)) m)^2 ∂μ) = deviationEnergy T f μ m := by
  simp only [orbit_shift]
  exact integral_comp_preserving (hT.iterate n) ((deviation_memLp (orbit_memLp hT hf) m).integrable_sq)

/-- The midpoint square is exactly the drop in the average's second moment.
This identity uses only stationarity of the right half. -/
lemma midpoint_energy {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    (∫ x, (average (orbit T f x) n - average (orbit T f x) (2 * n))^2 ∂μ) =
      averageEnergy T f μ n - averageEnergy T f μ (2 * n) := by
  have hL : Integrable (fun x => (average (orbit T f x) n)^2) μ :=
    (average_memLp (orbit_memLp hT hf) n).integrable_sq
  have hR : Integrable (fun x => (average (fun j => orbit T f x (n + j)) n)^2) μ :=
    (average_memLp (fun j => orbit_memLp hT hf (n + j)) n).integrable_sq
  have hW : Integrable (fun x => (average (orbit T f x) (2 * n))^2) μ :=
    (average_memLp (orbit_memLp hT hf) (2 * n)).integrable_sq
  calc
    _ = ∫ x, (((average (orbit T f x) n)^2 +
        (average (fun j => orbit T f x (n + j)) n)^2) / 2 -
        (average (orbit T f x) (2 * n))^2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [average_double _ hn]
      ring
    _ = (averageEnergy T f μ n + averageEnergy T f μ n) / 2 -
        averageEnergy T f μ (2 * n) := by
      have hadd : Integrable (fun x => ((average (orbit T f x) n)^2 +
          (average (fun j => orbit T f x (n + j)) n)^2) / 2) μ := (hL.add hR).div_const 2
      rw [integral_sub hadd hW, integral_div,
        integral_add hL hR, averageEnergy_shift hT hf]
      rfl
    _ = _ := by ring

lemma averageEnergy_double_le {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    averageEnergy T f μ (2 * n) ≤ averageEnergy T f μ n := by
  have h : (0 : ℝ) ≤ ∫ x, (average (orbit T f x) n -
      average (orbit T f x) (2 * n))^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [midpoint_energy hT hf hn] at h
  linarith

lemma deviationEnergy_double {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    deviationEnergy T f μ (2 * n) ≤
      (3 / 4 : ℝ) * (averageEnergy T f μ n - averageEnergy T f μ (2 * n)) +
      (3 / 4 : ℝ) * deviationEnergy T f μ n := by
  have hL : Integrable (fun x => (deviation (orbit T f x) n)^2) μ :=
    (deviation_memLp (orbit_memLp hT hf) n).integrable_sq
  have hR : Integrable (fun x => (deviation (fun j => orbit T f x (n + j)) n)^2) μ :=
    (deviation_memLp (fun j => orbit_memLp hT hf (n + j)) n).integrable_sq
  have hM : Integrable (fun x => (average (orbit T f x) n -
      average (orbit T f x) (2 * n))^2) μ :=
    ((average_memLp (orbit_memLp hT hf) n).sub
      (average_memLp (orbit_memLp hT hf) (2 * n))).integrable_sq
  have hW : Integrable (fun x => (deviation (orbit T f x) (2 * n))^2) μ :=
    (deviation_memLp (orbit_memLp hT hf) (2 * n)).integrable_sq
  calc
    _ ≤ ∫ x, (3 / 4 : ℝ) * (average (orbit T f x) n -
          average (orbit T f x) (2 * n))^2 +
        (3 / 8 : ℝ) * ((deviation (orbit T f x) n)^2 +
          (deviation (fun j => orbit T f x (n + j)) n)^2) ∂μ :=
      integral_mono hW ((hM.const_mul _).add ((hL.add hR).const_mul _))
        (fun x => deviation_double_sq (orbit T f x) hn)
    _ = _ := by
      have hadd : Integrable (fun x => (3 / 8 : ℝ) * ((deviation (orbit T f x) n)^2 +
          (deviation (fun j => orbit T f x (n + j)) n)^2)) μ := (hL.add hR).const_mul _
      rw [integral_add (hM.const_mul (3 / 4)) hadd, integral_const_mul,
        integral_const_mul, integral_add hL hR, midpoint_energy hT hf hn,
        deviationEnergy_shift hT hf]
      change (3 / 4 : ℝ) * _ + (3 / 8 : ℝ) * (deviationEnergy T f μ n + _) = _
      ring

end SmoothObstruction.DyadicChord

namespace SmoothObstruction.DyadicChord

/-- A telescoping potential turns the midpoint recurrence into an absolute
summability bound. These constants do not depend on a process or dimension. -/
lemma energy_sum_bound (A Z : ℕ → ℝ) (hA : ∀ h, 0 ≤ A h) (hZ : ∀ h, 0 ≤ Z h)
    (hZ₀ : Z 0 = 0)
    (hrec : ∀ h, Z (h + 1) ≤ (3 / 4 : ℝ) * (A h - A (h + 1)) + (3 / 4 : ℝ) * Z h)
    (N : ℕ) : ∑ h ∈ range N, Z h ≤ 3 * A 0 := by
  have hpot : ∀ n, (∑ h ∈ range n, Z h) + 4 * Z n + 3 * A n ≤ 3 * A 0 := by
    intro n
    induction n with
    | zero => simp [hZ₀]
    | succ n ih =>
      rw [sum_range_succ]
      linarith [hrec n]
  linarith [hpot N, hZ N, hA N]

lemma energy_summable (A Z : ℕ → ℝ) (hA : ∀ h, 0 ≤ A h) (hZ : ∀ h, 0 ≤ Z h)
    (hZ₀ : Z 0 = 0)
    (hrec : ∀ h, Z (h + 1) ≤ (3 / 4 : ℝ) * (A h - A (h + 1)) + (3 / 4 : ℝ) * Z h) :
    Summable Z ∧ ∑' h, Z h ≤ 3 * A 0 := by
  exact ⟨summable_of_sum_range_le hZ (energy_sum_bound A Z hA hZ hZ₀ hrec),
    Real.tsum_le_of_sum_range_le hZ (energy_sum_bound A Z hA hZ hZ₀ hrec)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The square-summability conclusion of the source dyadic chord lemma, with
an explicit absolute constant 3. The process is recorded as an observable of
a measure-preserving transformation; in particular it covers the compact
orthogonal-frame process required by the smooth switching construction. -/
theorem dyadic_square_summable {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Summable (fun h => deviationEnergy T f μ (2^h)) ∧
      (∑' h, deviationEnergy T f μ (2^h)) ≤ 3 * ∫ x, (f x)^2 ∂μ := by
  have h := energy_summable (fun h => averageEnergy T f μ (2^h))
    (fun h => deviationEnergy T f μ (2^h))
    (fun h => averageEnergy_nonneg T f _) (fun h => deviationEnergy_nonneg T f _)
    (by simp) (fun h => by
      simpa only [pow_succ', Nat.ofNat_pos] using
        deviationEnergy_double hT hf (pow_pos (by omega : 0 < 2) h))
  simpa only [pow_zero, averageEnergy_one] using h

/-- The nonnegative drops in the second moments telescope, without any need
for an ergodic theorem or for a mixing estimate. -/
theorem average_drop_summable {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∀ h, 0 ≤ averageEnergy T f μ (2^h) - averageEnergy T f μ (2^(h + 1))) ∧
    Summable (fun h => averageEnergy T f μ (2^h) - averageEnergy T f μ (2^(h + 1))) ∧
    (∑' h, (averageEnergy T f μ (2^h) - averageEnergy T f μ (2^(h + 1)))) ≤
      ∫ x, (f x)^2 ∂μ := by
  have hnonneg : ∀ h, 0 ≤ averageEnergy T f μ (2^h) -
      averageEnergy T f μ (2^(h + 1)) := by
    intro h
    rw [sub_nonneg]
    simpa only [pow_succ'] using
      averageEnergy_double_le hT hf (pow_pos (by omega : 0 < 2) h)
  have hbound : ∀ n, (∑ h ∈ range n, (averageEnergy T f μ (2^h) -
      averageEnergy T f μ (2^(h + 1)))) ≤ ∫ x, (f x)^2 ∂μ := by
    intro n
    rw [Finset.sum_range_sub']
    simp only [pow_zero, averageEnergy_one]
    linarith [averageEnergy_nonneg (μ := μ) T f (2^n)]
  exact ⟨hnonneg, summable_of_sum_range_le hnonneg hbound,
    Real.tsum_le_of_sum_range_le hnonneg hbound⟩

end SmoothObstruction.DyadicChord

end

end OAI
