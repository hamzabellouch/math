import OAI.MeasureTheory.SelfSimilar.Interpolation

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
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

omit [Nonempty ι] in
theorem slope_log_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    -Real.log |slope S ω (n+1)| = -Real.log |slope S ω n| + -Real.log |S.ratio (ω n)| := by
  rw [slope_succ,abs_mul,Real.log_mul (abs_slope_pos S ω n).ne' (S.ratio_pos _).ne',neg_add]

omit [Nonempty ι] in
theorem ratio_log_pos (S : System ι) (i : ι) : 0 < -Real.log |S.ratio i| :=
  neg_pos.mpr (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i))

theorem radial_limit_of_prefix (S : System ι) (ω : ℕ → ι)
    (hx : point S ω ∈ (law S).support)
    (hlim : Tendsto (fun n => prefixInfo S n ω / -Real.log |slope S ω n|)
      atTop (𝓝 (exponent S))) :
    Tendsto (fun r => BallRatios.information (law S) (point S ω) r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  let F : ℝ → ℝ := fun t => BallRatios.information (law S) (point S ω) (Real.exp (-t))
  let t : ℕ → ℝ := fun n => -Real.log |slope S ω n|
  have hF : Monotone F := by
    intro a b hab
    exact BallRatios.information_antitone _ hx (Real.exp_pos _)
      (Real.exp_le_exp.mpr (neg_le_neg hab))
  have ht : Monotone t := monotone_nat_of_le_succ fun n => by
    dsimp only [t]
    rw [slope_log_succ]
    exact le_add_of_nonneg_right (ratio_log_pos S _).le
  have ht0 : t 0=0 := by simp [t,slope_zero]
  have hstep : ∀ n, t (n+1) ≤ t n + ∑ i, -Real.log |S.ratio i| := by
    intro n
    dsimp only [t]
    rw [slope_log_succ]
    exact add_le_add_right (Finset.single_le_sum (fun i _ => (ratio_log_pos S i).le)
      (Finset.mem_univ (ω n))) _
  have hrtop : Tendsto (fun n => |slope S ω n|) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
      Eventually.of_forall (fun n => abs_slope_pos S ω n)⟩
  have htop : Tendsto t atTop atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hrtop)
  have hlim' : Tendsto (fun n => F (t n)/t n) atTop (𝓝 (exponent S)) := by
    simpa only [F,t,neg_neg,Real.exp_log (abs_slope_pos S ω _),prefixInfo] using hlim
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF ht ht0 hstep htop hlim'
  have hlog : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply (hfull.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]

theorem ae_radial_sequence (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun n : ℕ => BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 (exponent S)) := by
  have hseq : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) :=
    Real.tendsto_exp_atBot_nhdsGT.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hm (n : ℕ) : Measurable (fun x : ℝ =>
      BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ)) := by
    have hs : MeasurableSet {z : ℝ × ℝ | dist z.2 z.1 ≤ Real.exp (-(n : ℝ))} :=
      measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
    have hmass := measurable_measure_prodMk_left (ν := law S) hs
    exact hmass.ennreal_toReal.log.neg.div_const _
  apply (ae_map_iff (point_measurable S).aemeasurable (measurableSet_tendsto _ hm)).mpr
  filter_upwards [ae_prefix_exponent S,ae_point_support S] with ω hlim hs
  have hr := (radial_limit_of_prefix S ω (by simpa using hs 0) hlim).comp hseq
  simpa only [Function.comp_def,Real.log_exp,neg_neg] using hr

end EntropyRateDimension.Coding

end

end OAI
