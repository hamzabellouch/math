import OAI.Geometry.RCD.Sobolev.RadialCutoffEnergyTransfer

namespace OAI

/-! # Exact energy normalization for a physical interior cutoff -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem nested_cutoff_integral_region (μ : Measure X) (p : X)
    {a b R r : ℝ} (hab : a<b) (hbR : b<R) (hr : 0<r) (F : X → ℝ) :
    (∫ x in ball p (R*r), (nestedBallCutoff p (a*r) (b*r) x)^2*F x ∂μ)=
      ∫ x, (nestedBallCutoff p (a*r) (b*r) x)^2*F x ∂μ := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hd : R*r≤dist p x := by simpa only [mem_ball,not_lt,dist_comm] using hx
  have hz := nestedBallCutoff_eq_zero p (mul_lt_mul_of_pos_right hab hr)
    ((mul_lt_mul_of_pos_right hbR hr).le.trans hd)
  rw [hz]
  simp

theorem NoncollapsedRCD.radial_cutoff_energy_identity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (p : X) {a b R S r ε : ℝ}
    (hab : a<b) (hbR : b<R) (hRS : R<S) (hr : 0<r)
    {V : X → Euclidean n}
    (hV : IsMeasuredEuclideanApproximation (hausdorff n X) n p r S ε V)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) :
    (∫ x in ball p (R*r), (nestedBallCutoff p (a*r) (b*r) x)^2*
      localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X)=
      (∫ x in ball p (S*r), (euclideanNestedCutoff n hab (V x))^2*
        localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X)+
      ∫ x in ball p (S*r),
        ((nestedBallCutoff p (a*r) (b*r) x)^2-(euclideanNestedCutoff n hab (V x))^2)*
        localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X := by
  let μ := hausdorff n X
  let χ := fun x => nestedBallCutoff p (a*r) (b*r) x
  let θ := fun x => euclideanNestedCutoff n hab (V x)
  have hi : IntegrableOn (fun x => (χ x)^2*localGamma μ hX.quadratic w w x)
      (ball p (S*r)) μ := by
    apply (localGamma_memL1 μ hX.quadratic w w).restrict.bdd_mul
      (((nestedBallCutoff_lipschitz p (mul_lt_mul_of_pos_right hab hr)).continuous.aestronglyMeasurable).pow 2)
    exact Eventually.of_forall fun x => by
      have hh := nestedBallCutoff_bounds p (a*r) (b*r) x
      change ‖(χ x)^2‖≤(1:ℝ)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      dsimp only [χ]
      nlinarith
  have hj : IntegrableOn (fun x => (θ x)^2*localGamma μ hX.quadratic w w x)
      (ball p (S*r)) μ := by
    apply (localGamma_memL1 μ hX.quadratic w w).restrict.bdd_mul
      ((((euclideanNestedCutoff n hab).continuous.measurable.comp hV.measurable).aestronglyMeasurable).pow 2)
    exact Eventually.of_forall fun x => by
      have hh := nestedBallCutoff_bounds (0:Euclidean n) a b (V x)
      change ‖(θ x)^2‖≤(1:ℝ)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change 0≤θ x ∧ θ x≤1 at hh
      nlinarith
  have he := nested_cutoff_integral_region μ p hab hbR hr (localGamma μ hX.quadratic w w)
  have he' := nested_cutoff_integral_region μ p hab (hbR.trans hRS) hr (localGamma μ hX.quadratic w w)
  rw [he,← he']
  have hsub := integral_sub hi hj
  have heq : (fun x => ((χ x)^2-(θ x)^2)*localGamma μ hX.quadratic w w x)=
      fun x => (χ x)^2*localGamma μ hX.quadratic w w x-(θ x)^2*localGamma μ hX.quadratic w w x := by
    funext x
    ring
  change _=(_)+∫ x in ball p (S*r), ((χ x)^2-(θ x)^2)*localGamma μ hX.quadratic w w x ∂μ
  rw [heq,hsub]
  ring

end RegularPointCoordinates

end

end OAI
