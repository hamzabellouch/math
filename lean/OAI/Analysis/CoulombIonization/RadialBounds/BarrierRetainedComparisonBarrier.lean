import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNonlinearBarrier
import OAI.Analysis.CoulombIonization.Localization.BarrierConditionalBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierRetainedComparison_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

def InverseComparisonAt (d H μ κ hₗ hₕ ξ C : ℝ) : Prop :=
  d^4*H ≤ C ∧
  (∀ h ∈ Icc hₗ hₕ, κ*h^(3/2:ℝ) < d^6*μ → h-ξ ≤ d^4*H) ∧
  (∀ h ∈ Icc hₗ hₕ, d^6*μ < κ*h^(3/2:ℝ) → d^4*H ≤ h+ξ)

lemma pow_four_three_halves {d : ℝ} (hd : 0 ≤ d) :
    (d^4)^(3/2:ℝ) = d^6 := by
  rw [←Real.rpow_natCast d 4,←Real.rpow_mul hd]
  norm_num

lemma scaled_positive_reaction {d u : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u) :
    (d^4*u)^(3/2:ℝ) = d^6*u^(3/2:ℝ) := by
  rw [Real.mul_rpow (by positivity) hu,pow_four_three_halves hd]

lemma inverse_high_unscaled {d H μ κ hₗ hₕ ξ C u : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) (hh : d^4*u ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C)
    (hμ : reaction κ u < 4*Real.pi*μ) : u-ξ/d^4 ≤ H := by
  have hπ : 0 < 4*Real.pi := by positivity
  have he : reaction κ u = (4*Real.pi)*(κ*u^(3/2:ℝ)) := by
    simp only [reaction,max_eq_left hu]
    ring
  rw [he] at hμ
  have hm := (mul_lt_mul_iff_right₀ hπ).mp hμ
  have ht : κ*(d^4*u)^(3/2:ℝ) < d^6*μ := by
    rw [scaled_positive_reaction hd.le hu]
    nlinarith [mul_lt_mul_of_pos_left hm (pow_pos hd 6)]
  have hb := hi.2.1 (d^4*u) hh ht
  have hq : d^4*(ξ/d^4) = ξ := by field_simp
  have hp : 0 < d^4 := pow_pos hd 4
  nlinarith

lemma inverse_low_unscaled {d H μ κ hₗ hₕ ξ C u : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) (hh : d^4*u ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C)
    (hμ : 4*Real.pi*μ < reaction κ u) : H ≤ u+ξ/d^4 := by
  have hπ : 0 < 4*Real.pi := by positivity
  have he : reaction κ u = (4*Real.pi)*(κ*u^(3/2:ℝ)) := by
    simp only [reaction,max_eq_left hu]
    ring
  rw [he] at hμ
  have hm := (mul_lt_mul_iff_right₀ hπ).mp hμ
  have ht : d^6*μ < κ*(d^4*u)^(3/2:ℝ) := by
    rw [scaled_positive_reaction hd.le hu]
    nlinarith [mul_lt_mul_of_pos_left hm (pow_pos hd 6)]
  have hb := hi.2.2 (d^4*u) hh ht
  have hq : d^4*(ξ/d^4) = ξ := by field_simp
  have hp : 0 < d^4 := pow_pos hd 4
  nlinarith

lemma dyadic_inverse_four_bound {R d ξ : ℝ} (hR : 0 < R) (hd : R/2 ≤ d)
    (hξ : 0 ≤ ξ) : ξ/d^4 ≤ 16*ξ/R^4 := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < R/2) hd
  apply (div_le_div_iff₀ (pow_pos hd0 4) (pow_pos hR 4)).mpr
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R/2) hd 4
  have he : (R/2)^4 = R^4/16 := by ring
  rw [he] at hp
  nlinarith [mul_le_mul_of_nonneg_left hp hξ]

theorem retained_old_source {R d H μ κ hₗ hₕ ξ C u lam1 lam2 e : ℝ}
    (hR : 0 < R) (hd : R/2 ≤ d) (hξ : 0 ≤ ξ)
    (hu : 0 ≤ u) (hh : d^4*u ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C)
    (hp : 16*ξ+2*e < lam1-lam2)
    (hr : H-lam2/R^4 < (u-lam1/R^4)+2*e/R^4) :
    4*Real.pi*μ ≤ reaction κ u := by
  by_contra hn
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity : 0 < R/2) hd
  have hlo := inverse_high_unscaled hd0 hu hh hi (lt_of_not_ge hn)
  have hq := dyadic_inverse_four_bound hR hd hξ
  have hs : (16*ξ+2*e)/R^4 < (lam1-lam2)/R^4 :=
    div_lt_div_of_pos_right hp (pow_pos hR 4)
  simp only [add_div,sub_div,mul_div_assoc] at hs hq hr
  linarith

theorem retained_field_source {R d H μ κ hₗ hₕ ξ C lam2 : ℝ}
    (hR : 0 < R) (hd : R ≤ d) (hξ : 0 ≤ ξ) (hshift : ξ < lam2)
    (hu : 0 ≤ H-lam2/R^4) (hh : d^4*(H-lam2/R^4) ∈ Icc hₗ hₕ)
    (hi : InverseComparisonAt d H μ κ hₗ hₕ ξ C) :
    reaction κ (H-lam2/R^4) ≤ 4*Real.pi*μ := by
  by_contra hn
  have hd0 := hR.trans_le hd
  have hlo := inverse_low_unscaled hd0 hu hh hi (lt_of_not_ge hn)
  have hq : ξ/d^4 ≤ ξ/R^4 := div_le_div_of_nonneg_left hξ
    (pow_pos hR 4) (pow_le_pow_left₀ hR.le hd 4)
  have hs := div_lt_div_of_pos_right hshift (pow_pos hR 4)
  linarith

end Work_BarrierRetainedComparison_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis CoulombPDE CoulombAtom

lemma classical_weak_lower {U : Set TFSpace} (hU : IsOpen U)
    {u h : TFSpace → ℝ} (hu : Continuous u) (hh : LocallyIntegrable h)
    (hd : ∀ x ∈ U, ContDiffAt ℝ 2 u x) (hle : ∀ x ∈ U, h x ≤ Δ u x) :
    WeakLaplacianLowerOn U u h := by
  apply weak_lower_local hu.locallyIntegrable hh
  intro x hx
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x := ⟨r/2,3*r/4,by positivity,by linarith⟩
  let v : TFSpace → ℝ := fun y => b y*u y
  have hv : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.mul (hd y hy)
    · have hyb : y ∉ tsupport b := by
        intro hyb
        have hb : dist y x ≤ 3*r/4 := by
          simpa only [ContDiffBump.tsupport_eq,mem_closedBall] using hyb
        exact hy (hsub (mem_ball.mpr (by linarith)))
      apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyb] with z hz
      simp only [v,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have he {y : TFSpace} (hy : y ∈ ball x (r/2)) : v =ᶠ[𝓝 y] u := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp only [v,b.one_of_mem_closedBall (ball_subset_closedBall hz),one_mul]
  refine ⟨ball x (r/2),isOpen_ball,mem_ball_self (by positivity),?_⟩
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ y, Δ v y*φ y := by
      apply integral_mono (locallyIntegrable_mul_test hh hφ.continuous hc)
        (locallyIntegrable_mul_test (tfLaplacian_continuous hv).locallyIntegrable hφ.continuous hc)
      intro y
      dsimp only
      by_cases hy : φ y = 0
      · simp only [hy,mul_zero,le_refl]
      · have hym := hs (subset_tsupport φ hy)
        rw [(laplacian_congr_nhds (he hym)).eq_of_nhds]
        exact mul_le_mul_of_nonneg_right (hle y (hsub (ball_subset_ball (by linarith) hym))) (hn y)
    _ = ∫ y, v y*Δ φ y := (compact_laplacian_green hv hφ hc).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun y => by
      dsimp only
      by_cases hy : Δ φ y = 0
      · simp only [hy,mul_zero]
      · rw [(he (hs (tfLaplacian_support hφ hy))).eq_of_nhds])

end CoulombBarrier

end

end OAI
