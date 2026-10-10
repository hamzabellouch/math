import OAI.Geometry.RCD.Coordinates.RegularCoreRepresentative
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Coordinates.SplittingApproximation
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Compact heat data from the original first-order harmonic coordinates -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_compact_heat_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hcurv : ∀ k, -1 ≤ K*(16*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hs : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k)) (i : Fin n) :
    let m := hausdorff n X
    let q := hX.quadratic
    ∃ (g : ℕ → SobolevSpace m q) (d : ℕ → Lp ℝ 2 m)
      (V : ℕ → X → ℝ) (L A : ℕ → ℝ≥0),
      (∀ k, IsWeakLaplacian m q (g k) (d k)) ∧
      (∀ k, LipschitzWith (L k) (V k)) ∧ (∀ k, HasCompactSupport (V k)) ∧
      (∀ k, SobolevSpace.toLp m q (g k) =ᵐ[m] V k) ∧
      (∀ k, ∀ᵐ x ∂m, |SobolevSpace.toLp m q (g k) x| ≤ A k) ∧
      (∀ k, SobolevSpace.toLp m q (g k) =ᵐ[m.restrict (ball (p k) (6*r k))]
        SobolevSpace.toLp m q (u k i)) ∧
      (∀ k, d k =ᵐ[m.restrict (ball (p k) (6*r k))] fun _ => 0) ∧
      Tendsto (fun k => (∫ x in closedBall (p k) (2*r k), |localGamma m q (g k) (g k) x-1| ∂m)/
        m.real (ball (p k) (4*r k))) atTop (𝓝 0) := by
  intro m q
  let ℓ (k : ℕ) : ℝ≥0 := ⟨1+ε k,by linarith [hε k]⟩
  have hext (k : ℕ) := hX.local_poisson_regular_extension hn (u k i) 0
    (show 0 < 6*r k by linarith [hr k]) (show 2*(6*r k)<16*r k by linarith [hr k])
    ((isConstantLaplacianOn_zero_iff m q _ _).mpr ((hs k).harmonic i)) (ℓ k) ((hs k).gradient i)
  choose g d hd hrep hd0 using hext
  choose V L A hV hVc hg hA using fun k => regular_core_representative m q (g k)
  refine ⟨fun k => (g k).val,d,V,L,A,hd,hV,hVc,hg,hA,hrep,hd0,?_⟩
  have hm (k : ℕ) (a : ℝ) (ha : 0 < a) : 0 < m.real (ball (p k) (a*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos ha (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1)
  have hv (k : ℕ) : m.real (ball (p k) (16*r k)) ≤ D*m.real (ball (p k) (4*r k)) := by
    have hh := hvol (p k) (16*r k) (by linarith [hr k]) (hcurv k) (p k)
      (by simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤16) (hr k).le)
    simpa only [show (1/4:ℝ)*(16*r k)=4*r k by ring] using hh
  apply squeeze_zero (fun k => div_nonneg (integral_nonneg fun _ => abs_nonneg _) (hm k 4 (by norm_num)).le)
    (g := fun k => D*ε k) _ (by simpa only [mul_zero] using hε0.const_mul D)
  intro k
  have hfin := (hX.finiteOnBounded (ball (p k) (16*r k)) isBounded_ball).ne
  let : IsFiniteMeasure (m.restrict (ball (p k) (16*r k))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hi : IntegrableOn (fun x => |localGamma m q (u k i) (u k i) x-1|)
      (ball (p k) (16*r k)) m :=
    ((localGamma_memL1 m q (u k i) (u k i)).integrableOn.sub (integrable_const _)).abs
  have heq : localGamma m q (g k).val (g k).val
      =ᵐ[m.restrict (closedBall (p k) (2*r k))] localGamma m q (u k i) (u k i) :=
    ae_restrict_of_ae_restrict_of_subset (closedBall_subset_ball (by linarith [hr k]))
      (localGamma_pair_congr_ae m q (hrep k) (hrep k))
  have hsmall : (∫ x in closedBall (p k) (2*r k), |localGamma m q (g k).val (g k).val x-1| ∂m) ≤
      ∫ x in ball (p k) (16*r k), |localGamma m q (u k i) (u k i) x-1| ∂m := by
    have heint := integral_congr_ae (heq.fun_comp (fun z => |z-1|))
    simp only [Function.comp_apply] at heint
    rw [heint]
    exact setIntegral_mono_set hi (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall (closedBall_subset_ball (by linarith [hr k])))
  have hmean := (hs k).gram i i
  have hbound : (∫ x in ball (p k) (16*r k), |localGamma m q (u k i) (u k i) x-1| ∂m) ≤
      ε k*m.real (ball (p k) (16*r k)) := by
    rw [← div_eq_inv_mul,div_le_iff₀ (hm k 16 (by norm_num))] at hmean
    simpa only [ite_true] using hmean
  apply (div_le_iff₀ (hm k 4 (by norm_num))).mpr
  exact (hsmall.trans hbound).trans (by
    have hh := mul_le_mul_of_nonneg_left (hv k) (hε k)
    convert hh using 1; ring)

end RegularPointCoordinates

end

end OAI
