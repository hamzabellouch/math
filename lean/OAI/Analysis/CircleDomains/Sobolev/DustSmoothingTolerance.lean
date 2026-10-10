import OAI.Analysis.CircleDomains.Sobolev.CircleSmoothingBands

namespace OAI

/-! The concrete smoothing tolerance is positive off the dust, uniformly
small, and tends to zero at every dust point. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 def dustSmoothingTolerance {X Y : Type*} [MetricSpace Y]
    (q : X → Y) (B : Set Y) (ε : ℝ) (x : X) : ℝ :=
  min ε (infDist (q x) B) / 2

 theorem continuous_dustSmoothingTolerance
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {q : X → Y} (hq : Continuous q) (B : Set Y) (ε : ℝ) :
    Continuous (dustSmoothingTolerance q B ε) :=
  (continuous_const.min ((continuous_infDist_pt B).comp hq)).div_const 2

 theorem dustSmoothingTolerance_pos
    {X Y : Type*} [MetricSpace Y] (q : X → Y) {B : Set Y}
    (hB : IsClosed B) (hne : B.Nonempty) {ε : ℝ} (hε : 0 < ε)
    {x : X} (hx : q x ∉ B) : 0 < dustSmoothingTolerance q B ε x :=
  div_pos (lt_min hε ((hB.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)

 theorem dustSmoothingTolerance_le_half
    {X Y : Type*} [MetricSpace Y] (q : X → Y) (B : Set Y) (ε : ℝ) (x : X) :
    dustSmoothingTolerance q B ε x ≤ ε / 2 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

 theorem dustSmoothingTolerance_tendsto_zero
    {X Y : Type*} [MetricSpace Y] {l : Filter X} (q : X → Y)
    (B : Set Y) {s : Y} (hs : s ∈ B) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : Tendsto q l (𝓝 s)) : Tendsto (dustSmoothingTolerance q B ε) l (𝓝 0) := by
  have hd : Tendsto (fun x => infDist (q x) B) l (𝓝 0) := by
    simpa only [Function.comp_def, infDist_zero_of_mem hs] using
      ((continuous_infDist_pt B).tendsto s).comp hq
  have hc : Tendsto (fun _ : X => ε) l (𝓝 ε) := tendsto_const_nhds
  have ht := (hc.min hd).div_const (2 : ℝ)
  change Tendsto (fun x => min ε (infDist (q x) B) / 2) l (𝓝 0)
  simpa only [min_eq_right hε, zero_div] using ht

end CircleDomainRigidity

end

end OAI
