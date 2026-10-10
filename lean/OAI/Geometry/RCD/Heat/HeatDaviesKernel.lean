import OAI.Geometry.RCD.Heat.HeatWeightedRows

namespace OAI

/-! # Pointwise Davies bound for the constructed kernel

Reciprocal exponential weights pair the two half-time rows. The resulting
bound has the sharp quadratic cost before optimizing the weight parameter.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

theorem radialWeight_half_sq (q : X) (a R : ℝ) (z : X) :
    (radialWeight q (a/2) R z)^2 = radialWeight q a R z := by
  simp only [radialWeight,← Real.exp_nat_mul]
  congr 1
  ring

theorem radialWeight_neg_mul (q : X) (a R : ℝ) (z : X) :
    radialWeight q (-a) R z*radialWeight q a R z = 1 := by
  simp only [radialWeight,← Real.exp_add]
  rw [show (-a)*min (dist q z) R+a*min (dist q z) R = 0 by ring,Real.exp_zero]

namespace NoncollapsedRCD

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_davies_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x y : X) (a r t : ℝ),
      0 ≤ a → 0 < r → -1 ≤ K*r^2 → r^2 < t/2 →
      hX.canonicalHeatKernel hn p t x y ≤
        C^2/(Real.sqrt ((hausdorff n X).real (ball x r))*
          Real.sqrt ((hausdorff n X).real (ball y r)))*
        Real.exp (-a*dist x y/2+a*r+a^2*t/4) := by
  obtain ⟨C,hC,hrow⟩ := hX.canonicalHeatKernel_weighted_row hn p
  refine ⟨C,hC,?_⟩
  intro x y a r t ha hr hcurv hrt
  have hs : 0 < t/2 := lt_of_le_of_lt (sq_nonneg r) hrt
  have ht : 0 < t := by linarith
  let μ := hausdorff n X
  let k := hX.canonicalHeatKernel hn p
  have hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let R := dist x y
  let f := fun z => radialWeight y (-a/2) R z*k (t/2) x z
  let g := fun z => radialWeight y (a/2) R z*k (t/2) y z
  have hfm : MemLp f 2 μ := by
    have hw := radialWeight_signed_lipschitz y (-a/2) (dist_nonneg (x := x) (y := y))
    have hm := memLp_top_of_bound (μ := μ) hw.continuous.aestronglyMeasurable
      (Real.exp (|-a/2| *R)) (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using radialWeight_signed_bound y (-a/2) dist_nonneg z)
    exact hm.mul (heatKernel_memLp μ hX.quadratic hk hs x)
  have hgm : MemLp g 2 μ := by
    have hw := radialWeight_signed_lipschitz y (a/2) (dist_nonneg (x := x) (y := y))
    have hm := memLp_top_of_bound (μ := μ) hw.continuous.aestronglyMeasurable
      (Real.exp (|a/2| *R)) (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using radialWeight_signed_bound y (a/2) dist_nonneg z)
    exact hm.mul (heatKernel_memLp μ hX.quadratic hk hs y)
  have he : (∫ z, f z*g z ∂μ) = k t x y := by
    calc
      _ = ∫ z, k (t/2) x z*k (t/2) z y ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp only [f,g]
        rw [show -a/2 = -(a/2) by ring]
        rw [show radialWeight y (-(a/2)) R z*k (t/2) x z*
            (radialWeight y (a/2) R z*k (t/2) y z) =
            (radialWeight y (-(a/2)) R z*radialWeight y (a/2) R z)*
              (k (t/2) x z*k (t/2) y z) by ring,
          radialWeight_neg_mul,one_mul]
        exact congrArg (fun v => k (t/2) x z*v) (hk.symmetric (t/2) hs y z)
      _ = k (t/2+t/2) x y := hk.convolution _ _ hs hs x y
      _ = _ := by congr 1; ring
  have hfint : (∫ z, (f z)^2 ∂μ) =
      ∫ z, radialWeight y (-a) R z*(k (t/2) x z)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [f]
    rw [mul_pow,radialWeight_half_sq]
  have hgint : (∫ z, (g z)^2 ∂μ) =
      ∫ z, radialWeight y a R z*(k (t/2) y z)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [g]
    rw [mul_pow,radialWeight_half_sq]
  have hxb := hrow y x (-a) R r (t/2) dist_nonneg hr hcurv hrt
  have hyb := hrow y y a R r (t/2) dist_nonneg hr hcurv hrt
  simp only [R,dist_comm y x,min_self,abs_neg,abs_of_nonneg ha,neg_sq,neg_mul] at hxb
  simp only [R,dist_self,min_eq_left dist_nonneg,mul_zero,zero_add,abs_of_nonneg ha] at hyb
  let A := C/Real.sqrt (μ.real (ball x r))*
    Real.exp ((-a*dist x y+a*r)/2+a^2/4*(t/2))
  let B := C/Real.sqrt (μ.real (ball y r))*
    Real.exp ((a*r)/2+a^2/4*(t/2))
  have hcs := integral_mul_sq_le_integral_sq μ f g hfm hgm
  rw [he,abs_of_nonneg (hk.nonneg t ht x y)] at hcs
  have hf0 : 0 ≤ ∫ z, (f z)^2 ∂μ := integral_nonneg fun z => sq_nonneg _
  have hg0 : 0 ≤ ∫ z, (g z)^2 ∂μ := integral_nonneg fun z => sq_nonneg _
  have hAf : (∫ z, (f z)^2 ∂μ) ≤ A^2 := by
    rw [hfint]
    simpa only [A,μ,k,R,neg_mul] using hxb
  have hBg : (∫ z, (g z)^2 ∂μ) ≤ B^2 := by
    rw [hgint]
    exact hyb
  have hsq : (k t x y)^2 ≤ (A*B)^2 :=
    hcs.trans (by rw [mul_pow]; exact mul_le_mul hAf hBg hg0 (sq_nonneg A))
  have hAB : k t x y ≤ A*B :=
    (sq_le_sq₀ (hk.nonneg t ht x y) (by dsimp only [A,B]; positivity)).mp hsq
  refine hAB.trans_eq ?_
  dsimp only [A,B]
  rw [show C/Real.sqrt (μ.real (ball x r))*
      Real.exp ((-a*dist x y+a*r)/2+a^2/4*(t/2))*
      (C/Real.sqrt (μ.real (ball y r))*Real.exp (a*r/2+a^2/4*(t/2))) =
      (C^2/(Real.sqrt (μ.real (ball x r))*Real.sqrt (μ.real (ball y r))))*
        (Real.exp ((-a*dist x y+a*r)/2+a^2/4*(t/2))*
          Real.exp (a*r/2+a^2/4*(t/2))) by ring]
  rw [← Real.exp_add]
  congr 2
  ring

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
