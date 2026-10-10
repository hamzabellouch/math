import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKGapCutoff.Clock

theorem scheffe_density {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hf0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hmass : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun n => ∫ x, |f n x-g x| ∂μ) atTop (𝓝 0) := by
  have hmin : Tendsto (fun n => ∫ x, min (f n x) (g x) ∂μ)
      atTop (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence g
    · intro n
      exact (hf n).aestronglyMeasurable.inf hg.aestronglyMeasurable
    · exact hg
    · intro n
      filter_upwards [hf0 n,hg0] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
      exact min_le_right _ _
    · filter_upwards [hlim] with x hx
      simpa using hx.min (tendsto_const_nhds (x := g x))
  have ht := (hmass.add (tendsto_const_nhds (x := ∫ x, g x ∂μ))).sub
    (hmin.const_mul 2)
  have hz : (∫ x, g x ∂μ)+(∫ x, g x ∂μ)-2*(∫ x, g x ∂μ)=0 := by ring
  rw [hz] at ht
  apply ht.congr
  intro n
  rw [← integral_add (hf n) hg, ← integral_const_mul]
  have hi : Integrable (fun x => f n x+g x) μ := (hf n).add hg
  have hj : Integrable (fun x => 2*min (f n x) (g x)) μ := ((hf n).inf hg).const_mul 2
  rw [← integral_sub hi hj]
  congr 1
  ext x
  rcases le_total (f n x) (g x) with h|h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem scheffe_density_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ᶠ n in l, Integrable (f n) μ) (hg : Integrable g μ)
    (hf0 : ∀ᶠ n in l, ∀ᵐ x ∂μ, 0 ≤ f n x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) l (𝓝 (g x)))
    (hmass : Tendsto (fun n => ∫ x, f n x ∂μ) l (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun n => ∫ x, |f n x-g x| ∂μ) l (𝓝 0) := by
  have hmin : Tendsto (fun n => ∫ x, min (f n x) (g x) ∂μ)
      l (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence g
    · filter_upwards [hf] with n hn
      exact hn.aestronglyMeasurable.inf hg.aestronglyMeasurable
    · filter_upwards [hf0] with n hn
      filter_upwards [hn,hg0] with x hx hy
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
      exact min_le_right _ _
    · exact hg
    · filter_upwards [hlim] with x hx
      simpa using hx.min (tendsto_const_nhds (x := g x))
  have ht := (hmass.add (tendsto_const_nhds (x := ∫ x, g x ∂μ))).sub
    (hmin.const_mul 2)
  have hz : (∫ x, g x ∂μ)+(∫ x, g x ∂μ)-2*(∫ x, g x ∂μ)=0 := by ring
  rw [hz] at ht
  apply ht.congr'
  filter_upwards [hf] with n hn
  rw [← integral_add hn hg, ← integral_const_mul]
  have hi : Integrable (fun x => f n x+g x) μ := hn.add hg
  have hj : Integrable (fun x => 2*min (f n x) (g x)) μ := (hn.inf hg).const_mul 2
  rw [← integral_sub hi hj]
  congr 1
  ext x
  rcases le_total (f n x) (g x) with h|h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

noncomputable def stepMass (p : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, (Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x

lemma stepMass_of_nonneg (p : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    stepMass p x = p ⌊x⌋₊ := by
  unfold stepMass
  rw [tsum_eq_single ⌊x⌋₊]
  · exact Set.indicator_of_mem (show x ∈ Set.Ico (⌊x⌋₊:ℝ) (⌊x⌋₊+1) from
      ⟨Nat.floor_le hx,Nat.lt_floor_add_one x⟩) _
  · intro j hj
    apply Set.indicator_of_notMem
    intro h
    exact hj ((Nat.floor_eq_iff hx).mpr h).symm

lemma stepMass_of_neg (p : ℕ → ℝ) {x : ℝ} (hx : x < 0) : stepMass p x = 0 := by
  unfold stepMass
  suffices hh : (fun j : ℕ => (Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x) = 0 by
    rw [hh]
    change (∑' _ : ℕ, (0:ℝ)) = 0
    exact tsum_zero
  ext j
  apply Set.indicator_of_notMem
  intro h
  exact (not_le.mpr hx) ((Nat.cast_nonneg j).trans h.1)

lemma stepMass_nonneg {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) (x : ℝ) : 0 ≤ stepMass p x := by
  by_cases hx : 0 ≤ x
  · rw [stepMass_of_nonneg p hx]
    exact hp _
  · rw [stepMass_of_neg p (lt_of_not_ge hx)]

lemma integral_step_interval (p : ℕ → ℝ) (j : ℕ) :
    ∫ x : ℝ, (Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x = p j := by
  rw [integral_indicator measurableSet_Ico,integral_const]
  simp [Measure.real,Real.volume_Ico]

lemma integrable_step_interval (p : ℕ → ℝ) (j : ℕ) :
    Integrable ((Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j)) :=
  (integrableOn_const (μ := volume) (C := p j) (by simp [Real.volume_Ico])).integrable_indicator
    measurableSet_Ico

lemma integral_step_interval_norm (p : ℕ → ℝ) (j : ℕ) :
    ∫ x : ℝ, ‖(Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x‖ = |p j| := by
  rw [← integral_step_interval (fun j => |p j|) j]
  congr 1
  ext x
  by_cases hx : x ∈ Set.Ico (j:ℝ) (j+1)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

lemma integral_stepMass {p : ℕ → ℝ} (hp : Summable p) :
    ∫ x, stepMass p x = ∑' j, p j := by
  unfold stepMass
  rw [← integral_tsum_of_summable_integral_norm (integrable_step_interval p)]
  · simp only [integral_step_interval]
  · simpa only [integral_step_interval_norm] using hp.abs

lemma integrable_stepMass {p : ℕ → ℝ} (hp : HasSum p 1) : Integrable (stepMass p) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_stepMass hp.summable,hp.tsum_eq]
  norm_num

noncomputable def histogram (q : ℝ) (n : ℕ) (p : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt n*stepMass p (q*n+x*Real.sqrt n)

lemma integrable_histogram {p : ℕ → ℝ} (hp : HasSum p 1) (q : ℝ) {n : ℕ}
    (hn : 0 < n) : Integrable (histogram q n p) := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  have hi := ((integrable_stepMass hp).comp_add_right (q*n)).comp_mul_right' hs
  convert! hi.const_mul (Real.sqrt (n:ℝ)) using 1
  ext x
  simp only [histogram,add_comm]

lemma integral_histogram {p : ℕ → ℝ} (hp : HasSum p 1) (q : ℝ) {n : ℕ}
    (hn : 0 < n) : ∫ x, histogram q n p x = 1 := by
  have hs : Real.sqrt (n:ℝ) ≠ 0 := by positivity
  unfold histogram
  rw [integral_const_mul]
  have hh : (fun x : ℝ => stepMass p (q*n+x*Real.sqrt n)) =
      (fun x : ℝ => (fun t => stepMass p (t+q*n)) (Real.sqrt n*x)) := by
    ext x
    congr 1
    ring
  rw [hh,Measure.integral_comp_mul_left (fun t : ℝ => stepMass p (t+q*n))
    (Real.sqrt (n:ℝ)),integral_add_right_eq_self,
    integral_stepMass hp.summable,hp.tsum_eq,smul_eq_mul,mul_one,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_inv_cancel₀ hs]

lemma histogram_nonneg {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) (q : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ histogram q n p x :=
  mul_nonneg (Real.sqrt_nonneg _) (stepMass_nonneg hp _)

end SKGapCutoff.Clock

end

end OAI
