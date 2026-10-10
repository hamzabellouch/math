import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Scalar
import OAI.Geometry.IntegralFillings.Charts.LinearMass
import OAI.Geometry.IntegralFillings.Geometry.Comparison
import OAI.Geometry.IntegralFillings.Geometry.Determinant
import OAI.Geometry.IntegralFillings.Charts.CurrentAxioms
import OAI.Geometry.IntegralFillings.Currents.IntegralPush

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace SharpIntegralFillings

namespace Optimality

lemma innerSpace_CAT0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsCAT0 E := by
  let s : E → E → ℝ → E := fun x y t => (1-t) • x + t • y
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x y
    simp [s]
  · intro x y a b ha hb
    have he : s x y a - s x y b = (a-b) • (y-x) := by dsimp [s]; module
    simp only [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    rw [norm_sub_rev y x]
  · intro o x y a b ha hb
    have he : s o x a - s o y b = a • (x-o) - b • (y-o) := by dsimp [s]; module
    have hi : ‖a • (x-o) - b • (y-o)‖^2 =
        a^2 * ‖x-o‖^2 + b^2 * ‖y-o‖^2 -
          a*b*(‖x-o‖^2 + ‖y-o‖^2 - ‖(x-o)-(y-o)‖^2) := by
      simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
      ring
    have hxy : (x-o)-(y-o) = x-y := by abel
    rw [hxy] at hi
    simp only [dist_eq_norm, he]
    rw [hi, norm_sub_rev o x, norm_sub_rev o y]
    nlinarith

abbrev UnitBall (d : ℕ) := Metric.closedBall (0 : Euc d) 1

instance (d : ℕ) : Nonempty (UnitBall d) := ⟨⟨0, by simp⟩⟩

lemma unitBall_CAT0 (d : ℕ) : IsCAT0 (UnitBall d) :=
  innerSpace_CAT0.closedBall 0 (by norm_num)

noncomputable def ballChart (d : ℕ) : IntegerChart (UnitBall d) d where
  domain := Metric.ball 0 1
  borel := measurableSet_ball
  bounded := Metric.isBounded_ball
  param := fun z => ⟨z.val, show dist z.val 0 ≤ 1 from le_of_lt z.property⟩
  bilipschitz := ⟨1, 1, by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    rfl, by
    intro x y
    simp only [ENNReal.coe_one, one_mul]
    rfl⟩
  multiplicity := fun _ => 1
  integrable := by
    simp only [Int.cast_one]
    exact integrableOn_const (μ := volume) (C := (1:ℝ)) Metric.isBounded_ball.measure_lt_top.ne

lemma chart_integerRectifiable {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {d : ℕ} (C : IntegerChart X d) : IntegerRectifiable C.action := by
  classical
  let D : ℕ → IntegerChart X d := fun i => if i = 0 then C else emptyChart d
  have hD (i : ℕ) : IsMetricCurrent (D i).action := (D i).action_isMetricCurrent
  refine ⟨D, ?_, hD, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by omega
      simp [D, hj]
    · simp [D, hi]
  · apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    have hi' : i ≠ 0 := by simpa using hi
    simp [D, hi']
  · intro b π
    rw [tsum_eq_single 0]
    · simp [D]
    · intro i hi
      simp [D, hi]

lemma det_le_one_of_clm_norm {d : ℕ} (p : Fin d → Euc d →L[ℝ] ℝ)
    (hp : ∀ i, ‖p i‖ ≤ 1) :
    |Matrix.det (fun i j => p i (EuclideanSpace.single j 1))| ≤ 1 := by
  apply abs_det_le_one_of_dot_bound
  intro i v
  have hv : ∑ j, v j • EuclideanSpace.single j (1:ℝ) =
      (WithLp.toLp 2 v : Euc d) := by
    convert (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (WithLp.toLp 2 v) using 1
    simp
  have he : (fun j => p i (EuclideanSpace.single j 1)) ⬝ᵥ v =
      p i (WithLp.toLp 2 v) := by
    rw [← hv, map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  rw [he]
  exact (p i).le_opNorm _ |>.trans (by simpa using mul_le_mul_of_nonneg_right (hp i) (norm_nonneg (WithLp.toLp 2 v : Euc d)))

lemma chart_mass_le_unitLip {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X] {d : ℕ} (C : IntegerChart X d)
    (hC : LipschitzWith 1 C.param) :
    mass C.action ≤ ∫ z in C.domain, |(C.multiplicity z : ℝ)| := by
  let μ := C.majorantMeasure (fun _ => 1)
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * 1)
      (volume.restrict C.domain) := by simpa using C.integrable.abs
  have hfin : IsFiniteMeasure μ := densityPush_finite _ _ hρ
  have hctrl : Controls C.action μ := by
    apply C.majorant_controls hρ (Eventually.of_forall fun _ => zero_le_one)
    intro π hπ
    have hnorm : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
        ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ ≤ 1 := by
      apply ae_all_iff.mpr
      intro i
      have hs : LipschitzOnWith 1 (C.scalar (π i)) C.domain := by
        simpa only [one_mul] using C.scalar_lipschitzOn hC (hπ i)
      simpa using ae_norm_fderivWithin_le volume C.borel hs
    filter_upwards [hnorm] with z hz
    exact det_le_one_of_clm_norm _ hz
  apply (mass_le_measure hfin hctrl).trans_eq
  have hn : 0 ≤ᵐ[volume.restrict C.domain] fun z => |(C.multiplicity z : ℝ)| * 1 :=
    Eventually.of_forall fun z => by positivity
  have h := integral_densityPush (volume.restrict C.domain) C.measurable_paramExtended
    hρ hn (continuous_const : Continuous (fun _ : X => (1:ℝ)))
  simpa only [integral_const, smul_eq_mul, mul_one, IntegerChart.majorantMeasure, μ] using h

lemma ballChart_mass_le (d : ℕ) : mass (ballChart d).action ≤ omega d := by
  have hL : LipschitzWith 1 (ballChart d).param := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    rfl
  have h := chart_mass_le_unitLip (ballChart d) hL
  simpa [ballChart, omega, Measure.real] using h

end Optimality
end SharpIntegralFillings

end

end OAI
