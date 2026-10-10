import OAI.Geometry.RCD.Sobolev.FiniteDisjointIntegral
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! # Open sets of large local averages

No null-sphere hypothesis is needed: shrink the inner integral first, then
move the center between two concentric balls.
-/

open Set Metric MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def ballAverageBad (μ : Measure X) (f : X → ℝ) (R t : ℝ) : Set X :=
  {x | ∃ r : ℝ, 0 < r ∧ r < R ∧ t*μ.real (ball x r) < ∫ y in ball x r, f y ∂μ}

theorem exists_smaller_ball_integral_gt (μ : Measure X) {f : X → ℝ} {x : X}
    {r b : ℝ} (hr : 0 < r) (hf : IntegrableOn f (ball x r) μ)
    (hb : b < ∫ y in ball x r, f y ∂μ) :
    ∃ s : ℝ, 0 < s ∧ s < r ∧ b < ∫ y in ball x s, f y ∂μ := by
  let s : ℕ → ℝ := fun k => r-1/((k:ℝ)+1)
  have hslim : Tendsto s atTop (𝓝 r) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := r) : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hslt (k : ℕ) : s k < r := by
    dsimp only [s]
    have : 0 < 1/((k:ℝ)+1) := by positivity
    linarith
  have hmono : Monotone (fun k => ball x (s k)) := by
    intro i j hij
    apply ball_subset_ball
    dsimp only [s]
    gcongr
  have hunion : (⋃ k, ball x (s k)) = ball x r := by
    apply Subset.antisymm (iUnion_subset fun k => ball_subset_ball (hslt k).le)
    intro y hy
    obtain ⟨k,hk⟩ := (hslim.eventually (Ioi_mem_nhds (show dist y x < r from hy))).exists
    exact mem_iUnion_of_mem k hk
  have hi := tendsto_setIntegral_of_monotone (fun k => measurableSet_ball) hmono
    (show IntegrableOn f (⋃ k, ball x (s k)) μ by rwa [hunion])
  rw [hunion] at hi
  obtain ⟨k,hk0,hkb⟩ := ((hslim.eventually (Ioi_mem_nhds hr)).and
    (hi.eventually (Ioi_mem_nhds hb))).exists
  exact ⟨s k,hk0,hslt k,hkb⟩

theorem isOpen_ballAverageBad (μ : Measure X) {f : X → ℝ}
    (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfin : ∀ x r, μ (ball x r) ≠ ⊤) {R t : ℝ} (ht : 0 ≤ t) :
    IsOpen (ballAverageBad μ f R t) := by
  apply Metric.isOpen_iff.mpr
  rintro x ⟨r,hr,hrR,hbig⟩
  obtain ⟨s,hs,hsr,hsmall⟩ := exists_smaller_ball_integral_gt μ hr hf.integrableOn hbig
  refine ⟨(r-s)/2,by positivity,?_⟩
  intro z hz
  have hzs : dist z x < (r-s)/2 := hz
  have hsub : ball x s ⊆ ball z ((r+s)/2) := by
    intro y hy
    have hh := dist_triangle y x z
    rw [dist_comm x z] at hh
    have hys : dist y x < s := hy
    change dist y z < (r+s)/2
    linarith
  have hsub' : ball z ((r+s)/2) ⊆ ball x r := by
    intro y hy
    have hh := dist_triangle y z x
    have hyz : dist y z < (r+s)/2 := hy
    change dist y x < r
    linarith
  refine ⟨(r+s)/2,by positivity,by linarith,?_⟩
  calc
    t*μ.real (ball z ((r+s)/2)) ≤ t*μ.real (ball x r) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub' (hfin x r)) ht
    _ < ∫ y in ball x s, f y ∂μ := hsmall
    _ ≤ ∫ y in ball z ((r+s)/2), f y ∂μ :=
      setIntegral_mono_set hf.integrableOn (ae_restrict_of_ae hf0)
        (Eventually.of_forall fun _ hy => hsub hy)

end RegularPointCoordinates

end

end OAI
