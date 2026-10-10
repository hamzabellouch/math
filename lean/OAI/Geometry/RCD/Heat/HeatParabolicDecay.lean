import OAI.Geometry.RCD.Heat.HeatParabolicStep
import OAI.Geometry.RCD.Heat.HeatLevelMass
import OAI.Geometry.RCD.Heat.ParabolicDyadicAlgebra

namespace OAI

/-! # Dyadic decay of heat upper levels

Small normalized space-time L² mass forces the upper-level energies to
vanish on nested cylinders. The normalization is by radius squared
times volume, and all constants come from the actual RCD Sobolev bound.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_parabolic_level_decay {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    letI : (hausdorff n X).Regular := inferInstance
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : X) (R τ : ℝ), 0 < R → -1 ≤ K*R^2 → 0 < τ →
      ∀ f : Lp ℝ 2 (hausdorff n X),
      (∫ t in τ..(τ+R^2), ∫ y in ball x R, (heatAt (hausdorff n X) hX.quadratic t f y)^2
        ∂hausdorff n X) ≤ δ*(R^2*(hausdorff n X).real (ball x R)) →
      Tendsto (fun i : ℕ => ∫ t in (parabolicDyadicTime τ R i)..(τ+R^2),
        ∫ y in closedBall x (R/2+R/(4*2^i)),
          (max (heatAt (hausdorff n X) hX.quadratic t f y-(1-(2^i:ℝ)⁻¹)) 0)^2
            ∂hausdorff n X) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : (hausdorff n X).Regular := inferInstance
  obtain ⟨p,C,hp,hC,hstep⟩ := hX.heat_parabolic_level_step hn
  let α := 1-2/p
  have hα : 0 < α := by
    have hp0 : 0 < p := by linarith
    have hh : 2/p < 1 := (div_lt_one hp0).mpr hp
    dsimp only [α]
    linarith
  let C₀ := C*657*(1312:ℝ)^α
  let b₀ := 4*(16:ℝ)^α
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; positivity
  obtain ⟨δ,hδ,hdecay⟩ := exists_superlinear_decay_threshold hC₀ hb₀ hα
  refine ⟨δ,hδ,?_⟩
  intro x R τ hR hcurv hτ f hsmall
  let μ := hausdorff n X
  let V := μ.real (ball x R)
  let W := R^2
  let J (i : ℕ) := ∫ t in (parabolicDyadicTime τ R i)..(τ+R^2),
    ∫ y in closedBall x (R/2+R/(4*2^i)),
      (max (heatAt μ hX.quadratic t f y-(1-(2^i:ℝ)⁻¹)) 0)^2 ∂μ
  let Y := fun i => J i/(W*V)
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hW : 0 < W := sq_pos_of_pos hR
  have hJn (i : ℕ) : 0 ≤ J i := by
    apply intervalIntegral.integral_nonneg_of_forall
    · have ht := (parabolicDyadicTime_bounds (τ := τ) hR i).2.2.2
      dsimp only [W] at hW
      linarith
    · intro t
      exact integral_nonneg fun y => sq_nonneg _
  have hYn (i : ℕ) : 0 ≤ Y i := div_nonneg (hJn i) (mul_pos hW hV).le
  have hstart : Y 0 ≤ δ := by
    have hsub : closedBall x (R/2+R/(4*2^0)) ⊆ ball x R :=
      closedBall_subset_ball (dyadic_inner_radii hR 0).2.2
    have hJ0 : J 0 ≤ ∫ t in τ..(τ+R^2), ∫ y in ball x R,
        (heatAt μ hX.quadratic t f y)^2 ∂μ := by
      dsimp only [J,parabolicDyadicTime]
      simp only [pow_zero,inv_one,sub_self,sub_zero,mul_zero,add_zero]
      have hc : Continuous (fun t => ∫ y in closedBall x (R/2+R/(4*2^0)),
          (max (heatAt μ hX.quadratic t f y) 0)^2 ∂μ) := by
        simpa only [sub_zero] using continuous_heat_upper_level_mass μ hX.quadratic f
          (k := 0) (by norm_num) (S := closedBall x (R/2+R/(4*2^0))) measurableSet_closedBall
      apply intervalIntegral.integral_mono_on (by linarith [sq_nonneg R])
        (hc.intervalIntegrable (μ := volume) _ _)
        ((continuous_setIntegral_sq_path μ (heatAt_continuous μ hX.quadratic f)
          (S := ball x R) measurableSet_ball).intervalIntegrable (μ := volume) _ _)
      intro t _
      exact heat_zero_level_mass_le μ hX.quadratic f t hsub
    exact (div_le_iff₀ (mul_pos hW hV)).mpr (hJ0.trans hsmall)
  have hrec (i : ℕ) : Y (i+1) ≤ C₀*b₀^i*(Y i)^(1+α) := by
    have hr := dyadic_inner_radii hR i
    have hk := dyadic_level_gap_bounds hR i
    have ht := parabolicDyadicTime_bounds (τ := τ) hR i
    let Q := (parabolicDyadicTime τ R (i+1)-parabolicDyadicTime τ R i)⁻¹+
      5*(((R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))))⁻¹)^2
    have hQn : 0 ≤ Q := by
      dsimp only [Q]
      exact add_nonneg (inv_nonneg.mpr (sub_nonneg.mpr ht.2.1.le)) (by positivity)
    have hh := hstep x R hR hcurv f (R/2+R/(4*2^(i+1))) (R/2+R/(4*2^i)) hr.2.1 hr.2.2
      (parabolicDyadicTime τ R i) (parabolicDyadicTime τ R (i+1)) (τ+R^2)
      (1-(2^i:ℝ)⁻¹) (1-(2^(i+1):ℝ)⁻¹) (hτ.trans_le ht.1) ht.2.1 ht.2.2.1.le hk.1 hk.2.1
    let P : Lp ℝ 2 μ → Lp ℝ 2 μ :=
      (upperLevelPart_lipschitz (1-(2^i:ℝ)⁻¹)).compLp (upperLevelPart_zero hk.1)
    let J' := ∫ t in (parabolicDyadicTime τ R i)..(τ+R^2),
      ∫ y in closedBall x (R/2+R/(4*2^i)), (P (heatAt μ hX.quadratic t f) y)^2 ∂μ
    have hJ' : J' = J i := by
      apply intervalIntegral.integral_congr
      intro t _
      exact integral_upperLevelPart_sq μ _ hk.1 _
    change J (i+1) ≤ C*V^(2/p-1)*(2*R^2*Q+1)*J'*
      (Q*J'/((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))^2)^(1-2/p) at hh
    have hexp : 2/p-1 = -α := by dsimp only [α]; ring
    rw [hJ',hexp] at hh
    change J (i+1) ≤ C*V^(-α)*(2*R^2*Q+1)*J i*
      (Q*J i/((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))^2)^α at hh
    have hcoef := parabolic_dyadic_coefficient (τ := τ) hR i
    change W*Q ≤ 328*4^i ∧ 2*W*Q+1 ≤ 657*4^i ∧
      W*Q*(((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))⁻¹)^2 ≤ 1312*16^i at hcoef
    have hq : Q*(((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))⁻¹)^2 ≤ (1312*16^i)/W := by
      apply (le_div_iff₀ hW).mpr
      nlinarith only [hcoef.2.2]
    have harg : Q*J i/((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))^2 ≤
        (1312*16^i/W)*J i := by
      have hh := mul_le_mul_of_nonneg_right hq (hJn i)
      simpa only [div_eq_mul_inv,inv_pow,mul_assoc,mul_comm,mul_left_comm] using hh
    have hbnd : J (i+1) ≤ C*V^(-α)*(657*4^i)*J i*((1312*16^i/W)*J i)^α := by
      have hJi := hJn i
      apply hh.trans
      gcongr
      first | positivity | exact hcoef.2.1
    have hnorm := div_le_div_of_nonneg_right hbnd (mul_pos hW hV).le
    rw [parabolic_normalized_identity hW hV (hJn i) (by norm_num : (0:ℝ)<1312)
      (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)<16) hα i] at hnorm
    exact hnorm
  have hlim := hdecay Y hYn hstart hrec
  have hJlim := hlim.mul_const (W*V)
  have heq (i : ℕ) : Y i*(W*V) = J i := div_mul_cancel₀ _ (mul_pos hW hV).ne'
  simpa only [heq,zero_mul] using hJlim

end RegularPointCoordinates

end

end OAI
