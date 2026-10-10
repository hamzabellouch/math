import OAI.MeasureTheory.SelfSimilar.BallRatios

namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace System
variable {ι : Type uι} [Fintype ι]

noncomputable def component (S : System ι) (μ : Measure ℝ) (i : ι) : Measure ℝ :=
  ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

instance component_finite (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ] (i : ι) :
    IsFiniteMeasure (S.component μ i) := by
  constructor
  simp only [component,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

theorem component_le (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (i : ι) :
    S.component μ i ≤ μ := by
  calc
    S.component μ i ≤ ∑ j, S.component μ j :=
      Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
    _ = μ := hμ.symm

theorem affine_preimage_closedBall (S : System ι) (i : ι) (x r : ℝ) :
    S.affine i ⁻¹' closedBall (S.affine i x) (|S.ratio i| *r) = closedBall x r := by
  ext y
  simp only [mem_preimage,mem_closedBall,Real.dist_eq]
  have he : S.affine i y-S.affine i x = S.ratio i*(y-x) := by simp only [affine]; ring
  rw [he,abs_mul]
  exact mul_le_mul_iff_right₀ (S.ratio_pos i)

theorem component_ball (S : System ι) (μ : Measure ℝ) (i : ι) (x r : ℝ) :
    S.component μ i (closedBall (S.affine i x) (|S.ratio i| *r)) =
      ENNReal.ofReal (S.weight i) * μ (closedBall x r) := by
  rw [component,Measure.smul_apply,smul_eq_mul,Measure.map_apply
    (S.affine_continuous i).measurable isClosed_closedBall.measurableSet,
    S.affine_preimage_closedBall]

end System

namespace BallRatios
noncomputable def information (μ : Measure ℝ) (x r : ℝ) : ℝ :=
  -Real.log (μ.real (closedBall x r))

theorem massReal_pos (μ : Measure ℝ) [IsFiniteMeasure μ] {x r : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) : 0 < μ.real (closedBall x r) := by
  exact ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
    (closedBall_mem_nhds x hr))) (measure_ne_top μ _)

theorem information_component {ι : Type uι} [Fintype ι] (S : System ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : S.SelfSimilar μ) (i : ι)
    {x r : ℝ} (hx : x ∈ μ.support) (hr : 0 < r) :
    information μ (S.affine i x) (|S.ratio i| *r) =
      information μ x r - Real.log (S.weight i) -
        logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) := by
  have hbase := massReal_pos μ hx hr
  have hcomp : (S.component μ i).real (closedBall (S.affine i x) (|S.ratio i| *r)) =
      S.weight i * μ.real (closedBall x r) := by
    simp only [Measure.real,S.component_ball,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (S.weight_nonneg i)]
  have hcp : 0 < (S.component μ i).real (closedBall (S.affine i x) (|S.ratio i| *r)) := by
    rw [hcomp]; exact mul_pos (S.weight_pos i) hbase
  have htop : 0 < μ.real (closedBall (S.affine i x) (|S.ratio i| *r)) := by
    exact hcp.trans_le (ENNReal.toReal_mono (measure_ne_top μ _)
      (S.component_le μ hμ i _))
  have hl : logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) =
      Real.log (μ.real (closedBall (S.affine i x) (|S.ratio i| *r))) -
        Real.log (S.weight i) - Real.log (μ.real (closedBall x r)) := by
    unfold logRatio
    rw [ENNReal.toReal_div]
    change Real.log (μ.real _ / (S.component μ i).real _) = _
    rw [Real.log_div htop.ne' hcp.ne']
    rw [hcomp,Real.log_mul (S.weight_pos i).ne' hbase.ne']
    ring
  rw [hl]
  unfold information
  ring
end BallRatios

namespace Coding
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem slope_ne_zero (S : System ι) (ω : ℕ → ι) (n : ℕ) : slope S ω n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact abs_pos.mp (S.ratio_pos (ω j))

omit [Nonempty ι] in
theorem abs_slope_pos (S : System ι) (ω : ℕ → ι) (n : ℕ) : 0 < |slope S ω n| :=
  abs_pos.mpr (slope_ne_zero S ω n)

theorem abs_slope_lt_one (S : System ι) (ω : ℕ → ι) {n : ℕ} (hn : 0 < n) :
    |slope S ω n| < 1 := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact (abs_slope_le S ω hc.le hr n).trans_lt (pow_lt_one₀ hc.le hc1 hn.ne')

theorem slope_tendsto_zero (S : System ι) (ω : ℕ → ι) :
    Tendsto (fun n => |slope S ω n|) atTop (𝓝 0) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact squeeze_zero (fun n => abs_nonneg _) (abs_slope_le S ω hc.le hr)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1)

end Coding
end EntropyRateDimension

end

end OAI
