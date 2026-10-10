import OAI.Analysis.LipschitzHilbert.Fourier.NarrowBandCutoff
import OAI.Analysis.LipschitzHilbert.Fourier.LineProductSpectrum

namespace OAI

/-! Each nonzero frequency has a compact smooth neighborhood on which a
positive dilation of the fixed narrow multiplier is exactly one. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem narrowBandProfile_eventually_one :
    (fun y : ℝ => narrowBandProfile y) =ᶠ[𝓝 (201/200:ℝ)] 1 := by
  filter_upwards [narrowBandBump.eventuallyEq_one,
    eventually_gt_nhds (show (0:ℝ)<201/200 by norm_num)] with y hy hpos
  have hz : narrowBandPositive (-y)=0 := by
    by_contra hn
    have hh := (narrowBandPositive_support (-y) hn).1
    linarith
  simp only [narrowBandProfile_apply,narrowBandPositive_apply] at hz ⊢
  rw [hy,hz]
  simp

theorem narrowBandProfile_eventually_one_abs (x : ℝ)
    (hx : |x|=(201/200:ℝ)) :
    (fun y : ℝ => narrowBandProfile y) =ᶠ[𝓝 x] 1 := by
  by_cases hp : 0≤x
  · have he : x=(201/200:ℝ) := by simpa only [abs_of_nonneg hp] using hx
    rw [he]
    exact narrowBandProfile_eventually_one
  · have he : -x=(201/200:ℝ) := by simpa only [abs_of_neg (lt_of_not_ge hp)] using hx
    have ht : Tendsto (fun y : ℝ => -y) (𝓝 x) (𝓝 (201/200:ℝ)) := by
      rw [←he]
      exact continuous_neg.continuousAt.tendsto
    filter_upwards [ht.eventually narrowBandProfile_eventually_one] with y hy
    simpa only [narrowBandProfile_even,Pi.one_apply] using hy

theorem exists_narrow_window (x : ℝ) (hx : x≠0) :
    ∃ w : ℝ, 0<w ∧ ∃ b : ContDiffBump x,
      ∀ y : ℝ, narrowBandProfile (w*y)*(b y:ℂ)=(b y:ℂ) := by
  let w : ℝ := (201/200)/|x|
  have hw : 0<w := div_pos (by norm_num) (abs_pos.mpr hx)
  have hxw : |w*x|=(201/200:ℝ) := by
    rw [abs_mul,abs_of_pos hw]
    dsimp [w]
    exact div_mul_cancel₀ _ (abs_pos.mpr hx).ne'
  have ht : Tendsto (fun y : ℝ => w*y) (𝓝 x) (𝓝 (w*x)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto
  have hn : {y : ℝ | narrowBandProfile (w*y)=1}∈𝓝 x :=
    ht.eventually (narrowBandProfile_eventually_one_abs (w*x) hxw)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let b : ContDiffBump x :=
    { rIn := r/4
      rOut := r/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨w,hw,b,?_⟩
  intro y
  by_cases hz : b y=0
  · simp only [hz,Complex.ofReal_zero,mul_zero]
  · have hy : y∈Metric.ball x r := by
      have hm : y∈Function.support b := hz
      rw [b.support_eq] at hm
      change dist y x<r/2 at hm
      change dist y x<r
      linarith
    rw [hsub hy,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
