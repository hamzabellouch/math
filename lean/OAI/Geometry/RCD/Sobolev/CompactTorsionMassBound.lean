import OAI.Geometry.RCD.Sobolev.HarmonicSquareTestPositive
import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicCompactExtension

namespace OAI

/-! # A compact torsion test bounds interior square mass by an annulus -/

open Set Metric MeasureTheory Laplacian
open scoped ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_laplacian_continuous {n : ℕ} {f : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (Δ f) := by
  rw [laplacian_eq_sum_second_directional hf]
  apply continuous_finsetSum
  intro i _
  have hd : ContDiff ℝ 1 (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem compact_torsion_mass_bound {n : ℕ} {f T : Euclidean n → ℝ}
    {a b c B : ℝ} (hab : a≤b)
    (hf : ContDiff ℝ 2 f) (hT : ContDiff ℝ 2 T) (hs : HasCompactSupport T)
    (hTb : tsupport T⊆ball 0 b) (hT0 : ∀ x, 0≤T x)
    (hh : ∀ x∈tsupport T, (Δ f) x=0)
    (hcore : ∀ x∈ball (0:Euclidean n) a, (Δ T) x= -c)
    (hupper : ∀ x, (Δ T) x≤B) :
    c*(∫ x in ball (0:Euclidean n) a, (f x)^2)≤
      B*(∫ x in ball 0 b \ ball 0 a, (f x)^2) := by
  have hfc : Continuous (fun x => (f x)^2) := hf.continuous.pow 2
  have hpc : Continuous (fun x => (f x)^2*(Δ T) x) :=
    hfc.mul (euclidean_laplacian_continuous hT)
  have hfi : IntegrableOn (fun x => (f x)^2) (ball (0:Euclidean n) b) volume :=
    (hfc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hpi : IntegrableOn (fun x => (f x)^2*(Δ T) x) (ball (0:Euclidean n) b) volume :=
    (hpc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hpos : 0≤∫ x in ball (0:Euclidean n) b, (f x)^2*(Δ T) x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
    · exact harmonic_square_test_nonneg hf hT hs hT0 hh
    · rw [laplacian_eq_zero_of_notMem_tsupport T (fun ht => hx (hTb ht)),mul_zero]
  have hinner : (∫ x in ball (0:Euclidean n) a, (f x)^2*(Δ T) x)=
      -c*(∫ x in ball 0 a, (f x)^2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    change (f x)^2*(Δ T) x= -c*(f x)^2
    rw [hcore x hx]
    ring
  have hann : (∫ x in ball (0:Euclidean n) b \ ball 0 a, (f x)^2*(Δ T) x)≤
      B*(∫ x in ball 0 b \ ball 0 a, (f x)^2) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hpi.mono_set sdiff_subset) ((hfi.mono_set sdiff_subset).const_mul B)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hupper x) (sq_nonneg (f x))
  have hsplit := setIntegral_sdiff measurableSet_ball hpi (ball_subset_ball hab)
  rw [hinner] at hsplit
  linarith

end RegularPointCoordinates

end

end OAI
