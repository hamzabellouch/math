import OAI.Geometry.RCD.Heat.CompactHeatInterpolationLaws
import OAI.Geometry.RCD.Heat.CompactHeatScalingCoupling
import OAI.Geometry.RCD.Metric.WithDensityMarginals

namespace OAI

/-! # The actual joint law of a heat-bridge point and its two endpoints -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def jointDensity (k : ℕ) (t : Ioo (0:ℝ) 1) (z : X × (S × T)) : ℝ :=
  (D.left k z.2.1 * hX.canonicalHeatKernel hn p (ε k/4*t) z.1 z.2.1)*
    (hX.canonicalHeatKernel hn p (ε k/4*(1-t)) z.1 z.2.2 * D.right k z.2.2)

theorem jointDensity_pos (k : ℕ) (t : Ioo (0:ℝ) 1) (z : X × (S × T)) :
    0 < D.jointDensity k t z :=
  mul_pos (mul_pos (D.left_pos k z.2.1)
    (hX.canonicalHeatKernel_pos hn p _
      (mul_pos (div_pos (hε k) (by norm_num)) t.property.1) _ _))
    (mul_pos (hX.canonicalHeatKernel_pos hn p _
      (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)) _ _)
      (D.right_pos k z.2.2))

theorem jointDensity_continuous (k : ℕ) (t : Ioo (0:ℝ) 1) :
    Continuous (D.jointDensity k t) := by
  let L := hX.compactHeatFactorKernel hn p S (ε k/4*t)
    (mul_pos (div_pos (hε k) (by norm_num)) t.property.1)
  let R := hX.compactHeatFactorKernel hn p T (ε k/4*(1-t))
    (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2))
  change Continuous (fun z : X × (S × T) =>
    (D.left k z.2.1*L (z.1,z.2.1))*(R (z.1,z.2.2)*D.right k z.2.2))
  fun_prop

def jointMeasure (k : ℕ) (t : Ioo (0:ℝ) 1) : Measure (X × (S × T)) :=
  ((hausdorff n X).prod (μ.prod ν)).withDensity (fun z => ENNReal.ofReal (D.jointDensity k t z))

theorem jointMeasure_fst (k : ℕ) (t : Ioo (0:ℝ) 1) :
    (D.jointMeasure k t).map Prod.fst = (D.interpolationLaw k t : Measure X) := by
  let m := hausdorff n X
  let L := hX.compactHeatFactorKernel hn p S (ε k/4*t)
    (mul_pos (div_pos (hε k) (by norm_num)) t.property.1)
  let R := hX.compactHeatFactorKernel hn p T (ε k/4*(1-t))
    (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2))
  have hL x a : 0 ≤ L (x,a) := hX.canonicalHeatKernel_nonneg hn p _ x a
  have hR x b : 0 ≤ R (x,b) := hX.canonicalHeatKernel_nonneg hn p _ x b
  rw [jointMeasure,product_density_fst _ _ _ (D.jointDensity_continuous k t).measurable.ennreal_ofReal]
  change m.withDensity _ = m.withDensity _
  congr 1
  funext x
  have he : (fun ab : S × T => ENNReal.ofReal (D.jointDensity k t (x,ab))) =
      fun ab => (ENNReal.ofReal (L (x,ab.1))*ENNReal.ofReal (D.left k ab.1))*
        (ENNReal.ofReal (R (x,ab.2))*ENNReal.ofReal (D.right k ab.2)) := by
    funext ab
    change ENNReal.ofReal ((D.left k ab.1*L (x,ab.1))*(R (x,ab.2)*D.right k ab.2)) = _
    rw [ENNReal.ofReal_mul (mul_nonneg (D.left_pos k ab.1).le (hL x ab.1)),
      ENNReal.ofReal_mul (D.left_pos k ab.1).le,ENNReal.ofReal_mul (hR x ab.2)]
    ac_rfl
  rw [he,lintegral_prod_mul
    (f := fun a : S => ENNReal.ofReal (L (x,a))*ENNReal.ofReal (D.left k a))
    (g := fun b : T => ENNReal.ofReal (R (x,b))*ENNReal.ofReal (D.right k b))]
  · rw [← compactKernelFactor_ofReal μ L (D.left k) hL (fun a => (D.left_pos k a).le) x,
      ← compactKernelFactor_ofReal ν R (D.right k) hR (fun b => (D.right_pos k b).le) x]
    exact (ENNReal.ofReal_mul (by
      exact integral_nonneg fun a => mul_nonneg (hL x a) (D.left_pos k a).le)).symm
  · exact (((L.continuous.comp (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal).mul
      (D.left k).continuous.measurable.ennreal_ofReal).aemeasurable
  · exact (((R.continuous.comp (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal).mul
      (D.right k).continuous.measurable.ennreal_ofReal).aemeasurable

theorem jointMeasure_snd (k : ℕ) (t : Ioo (0:ℝ) 1) :
    (D.jointMeasure (D.index k) t).map Prod.snd = (D.coupling k : Measure (S × T)) := by
  let m := hausdorff n X
  let i := D.index k
  let c := ε i/4
  have hc : 0 < c := div_pos (hε i) (by norm_num)
  have hs : 0 < c*(t:ℝ) := mul_pos hc t.property.1
  have ht : 0 < c*(1-(t:ℝ)) := mul_pos hc (sub_pos.mpr t.property.2)
  have htime : c*(t:ℝ)+c*(1-t)=c := by ring
  rw [jointMeasure,product_density_snd _ _ _ (D.jointDensity_continuous i t).measurable.ennreal_ofReal]
  change (μ.prod ν).withDensity _ = (μ.prod ν).withDensity _
  congr 1
  funext ab
  let L x := hX.canonicalHeatKernel hn p (c*t) x ab.1
  let R x := hX.canonicalHeatKernel hn p (c*(1-t)) x ab.2
  have hL x : 0 ≤ L x := hX.canonicalHeatKernel_nonneg hn p _ _ _
  have hR x : 0 ≤ R x := hX.canonicalHeatKernel_nonneg hn p _ _ _
  have hi : Integrable (fun x => L x*R x) m := by
    convert hX.canonicalHeatKernel_product_integrable hn p _ _ hs ht ab.1 ab.2 using 1
    funext x
    change hX.canonicalHeatKernel hn p (c*t) x ab.1 * _ = _
    rw [hX.canonicalHeatKernel_symmetric hn p (c*t) x ab.1]
  have he : (∫ x, L x*R x ∂m)=hX.canonicalHeatKernel hn p c ab.1 ab.2 := by
    calc
      _ = ∫ x, hX.canonicalHeatKernel hn p (c*t) ab.1 x*
          hX.canonicalHeatKernel hn p (c*(1-t)) x ab.2 ∂m := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [L,R]
          rw [hX.canonicalHeatKernel_symmetric hn p (c*t) x ab.1]
      _ = _ := by rw [hX.canonicalHeatKernel_convolution hn p _ _ hs ht,htime]
  let C := D.left i ab.1*D.right i ab.2
  have hC : 0 ≤ C := mul_nonneg (D.left_pos i ab.1).le (D.right_pos i ab.2).le
  have hde : (fun x => D.jointDensity i t (x,ab)) = fun x => C*(L x*R x) := by
    funext x
    dsimp only [jointDensity,C,L,R,c]
    ring
  have hde' (x : X) := congrFun hde x
  simp_rw [hde']
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul C)
    (Eventually.of_forall fun x => mul_nonneg hC (mul_nonneg (hL x) (hR x))),integral_const_mul,he]
  change ENNReal.ofReal ((D.left i ab.1*D.right i ab.2)*hX.canonicalHeatKernel hn p c ab.1 ab.2) =
    ENNReal.ofReal ((D.left i ab.1*hX.canonicalHeatKernel hn p c ab.1 ab.2)*D.right i ab.2)
  congr 1
  ring

theorem jointMeasure_probability (k : ℕ) (t : Ioo (0:ℝ) 1) :
    IsProbabilityMeasure (D.jointMeasure k t) := by
  have he := D.jointMeasure_fst k t
  let : IsProbabilityMeasure ((D.jointMeasure k t).map Prod.fst) := by rw [he]; infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

def jointLaw (k : ℕ) (t : Ioo (0:ℝ) 1) : ProbabilityMeasure (X × (S × T)) :=
  ⟨D.jointMeasure k t,D.jointMeasure_probability k t⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
