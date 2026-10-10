import OAI.Probability.InvariantIsing.Cavity.CavityStrictLevels
import OAI.Probability.IsingPerceptron.ContactFaces

namespace OAI

/-! Uniform finite overlap paths with strictly increasing interior
levels. Their endpoint convention is fixed, and they converge to the
original quantile almost everywhere and in L1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def cavityUniformLevel (n : ℕ) (s : ℝ) : Fin (n + 1) :=
  ⟨uniformCellIndex n s, Nat.lt_succ_of_le (uniformCellIndex_le n s)⟩

lemma cavityUniformLevel_monotone (n : ℕ) : Monotone (cavityUniformLevel n) := by
  intro s t hst
  change min n ⌊(n + 1 : ℕ) * s⌋₊ ≤ min n ⌊(n + 1 : ℕ) * t⌋₊
  exact min_le_min_left n (Nat.floor_mono
    (mul_le_mul_of_nonneg_left hst (by positivity)))

lemma cavityUniformLevel_on_cell (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityUniformLevel n s = i := by
  apply Fin.ext
  change min n ⌊(n + 1 : ℕ) * s⌋₊ = i.val
  rw [floor_on_uniformCell n i hs, min_eq_right (Nat.le_of_lt_succ i.isLt)]

lemma cavity_uniform_epsilon (n : ℕ) : (1 / ((n : ℝ) + 1)) ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

def cavityStrictUniformLevels (p : OverlapPath) (n : ℕ) : Fin (n + 1) → ℝ :=
  cavityStrictLevels (fun i => uniformCellAverage p n i) (1 / ((n : ℝ) + 1))

lemma cavityStrictUniformLevels_mem (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) :
    cavityStrictUniformLevels p n i ∈ Ioo (0 : ℝ) 1 :=
  cavityStrictLevels_mem _
    (fun i => uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    (cavity_uniform_epsilon n) i

lemma cavityStrictUniformLevels_strict (p : OverlapPath) (n : ℕ) :
    StrictMono (cavityStrictUniformLevels p n) :=
  cavityStrictLevels_strict _
    (fun _i _j hij => uniformCellAverage_monotone p.monotone
      (fun s => ⟨p.nonneg s, p.le_one s⟩) n hij)
    (cavity_uniform_epsilon n)

def cavityStrictUniformPath (p : OverlapPath) (n : ℕ) : OverlapPath where
  val := fun s => cavityStrictUniformLevels p n (cavityUniformLevel n s)
  monotone := (cavityStrictUniformLevels_strict p n).monotone.comp (cavityUniformLevel_monotone n)
  nonneg := fun s => (cavityStrictUniformLevels_mem p n (cavityUniformLevel n s)).1.le
  le_one := fun s => (cavityStrictUniformLevels_mem p n (cavityUniformLevel n s)).2.le

lemma cavityStrictUniformPath_on_cell (p : OverlapPath) (n : ℕ) (i : Fin (n + 1)) {s : ℝ}
    (hs : s ∈ Ioo (uniformCut n i.castSucc) (uniformCut n i.succ)) :
    cavityStrictUniformPath p n s = cavityStrictUniformLevels p n i := by
  change cavityStrictUniformLevels p n (cavityUniformLevel n s) = _
  rw [cavityUniformLevel_on_cell n i hs]

lemma cavityStrictUniformPath_dist (p : OverlapPath) (n : ℕ) (s : ℝ) :
    |cavityStrictUniformPath p n s - uniformCellAverage p n (uniformCellIndex n s)| ≤
      1 / ((n : ℝ) + 1) :=
  cavityStrictLevels_dist _
    (fun i => uniformCellAverage_mem p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩) n i)
    (cavity_uniform_epsilon n).1.le (cavityUniformLevel n s)

lemma cavityStrictUniformPath_ae_tendsto (p : OverlapPath) :
    ∀ᵐ s ∂pathMeasure, Tendsto (fun n => cavityStrictUniformPath p n s) atTop (𝓝 (p s)) := by
  have ha := uniformCellAverage_ae_tendsto p.monotone (fun s => ⟨p.nonneg s, p.le_one s⟩)
  change ∀ᵐ s ∂pathMeasure, _ at ha
  filter_upwards [ha] with s hs
  have hd : Tendsto (fun n => cavityStrictUniformPath p n s -
      uniformCellAverage p n (uniformCellIndex n s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Real.norm_eq_abs] using cavityStrictUniformPath_dist p n s
  simpa only [sub_add_cancel, zero_add] using hd.add hs

lemma cavityStrictUniformPath_l1_tendsto (p : OverlapPath) :
    Tendsto (fun n => ∫ s, |cavityStrictUniformPath p n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  have ha := cavityStrictUniformPath_ae_tendsto p
  have hd := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := fun n s => |cavityStrictUniformPath p n s - p s|) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (((cavityStrictUniformPath p n).measurable.sub p.measurable).abs).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_abs, abs_le]
      constructor <;> linarith [(cavityStrictUniformPath p n).nonneg s,
        (cavityStrictUniformPath p n).le_one s, p.nonneg s, p.le_one s])
    (ha.mono fun s hs => by simpa only [sub_self, abs_zero] using (hs.sub_const (p s)).abs)
  simpa only [integral_zero] using hd

end InvariantIsing

end

end OAI
