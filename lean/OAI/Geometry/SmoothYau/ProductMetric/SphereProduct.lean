import Mathlib
import OAI.Geometry.SmoothYau.ProductMetric.FourWaveThreeSmul

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
namespace YauCounterexamples
lemma four_nodal_finite (g : SmoothMetric FourModel FourManifold)
    (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
    (hr : ThreeRegular u) : nodalMeasure g 3 (u ∘ fourToThree) ≠ (∞ : ℝ≥0∞) := by
  let : RiemannianBundle (fun x : FourManifold => TangentSpace 𝓘(ℝ,FourModel) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourModel (fun x : FourManifold => TangentSpace 𝓘(ℝ,FourModel) x) :=
    ⟨⟨g.inner,g.toContinuousRiemannianMetric.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace FourManifold := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,FourModel) FourManifold
  let : MeasurableSpace FourManifold := borel FourManifold
  let : BorelSpace FourManifold := ⟨rfl⟩
  have hh := compact_regular_level_intrinsic_finite (hu.comp fourToThree_smooth) (K:=univ) isCompact_univ
    (fun x _ => four_lift_regular u hu hr x)
  change Measure.hausdorffMeasure 3 {x | (u ∘ fourToThree) x=0}≠(∞ : ℝ≥0∞)
  apply ne_of_lt
  simpa [FourModel,Euclidean] using hh
lemma four_sign_nodal_real (g : SmoothMetric FourModel FourManifold) (R : ℝ) :
    ∃ D : ℝ, 0<D ∧ ∀ u : ThreeManifold → ℝ,
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u → ThreeRegular u →
      ∀ L : ℝ, 0≤L → ThreeSignAbove R u L → L < D*(nodalMeasure g 3 (u ∘ fourToThree)).toReal := by
  obtain ⟨D,hD,hbound⟩ := four_signCertificate_bound g R
  refine ⟨D,hD,?_⟩
  intro u hu hr L hL hs
  obtain ⟨I,hI,partition,hpart,d,hd,hscore⟩ := hs
  have hh := hscore.trans_le (hbound u hu.continuous I hI partition d hd)
  have hfin := four_nodal_finite g u hu hr
  have hhreal := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).mpr hh
  simpa only [ENNReal.toReal_ofReal hL,ENNReal.toReal_mul,ENNReal.coe_toReal] using hhreal
lemma four_witnesses_unbounded (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (hw : ∀ n : ℕ, ThreeLargeWitness R g ((n:ℝ)+1) ((n:ℝ)+1)) :
    HasUnboundedNodalRatio (fourProductMetric g) 4 := by
  classical
  choose k hk e u heB heD hu hu0 hue hreg hscore using hw
  have hepos (n : ℕ) : 0<e n := lt_trans (by positivity) (heB n)
  have hfin (n : ℕ) : nodalMeasure (fourProductMetric g) 3 (u n ∘ fourToThree) ≠ (∞ : ℝ≥0∞) :=
    four_nodal_finite _ _ (hu n) (hreg n)
  obtain ⟨D,hD,hbound⟩ := four_sign_nodal_real (fourProductMetric g) R
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have heratio (n : ℕ) : ((n:ℝ)+1)/(2*D) ≤
      (nodalMeasure (fourProductMetric g) 3 (u n ∘ fourToThree)).toReal / Real.sqrt (e n) := by
    have hkpos : (0:ℝ)<k n := by exact_mod_cast (show 0<k n by have := hk n; omega)
    have hnp : (0:ℝ)≤(n:ℝ)+1 := by positivity
    have hscore' := hbound (u n) (hu n) (hreg n) (((n:ℝ)+1)*(k n:ℝ))
      (mul_nonneg hnp hkpos.le) (hscore n)
    have hsqrtpos := Real.sqrt_pos.mpr (hepos n)
    have hsq := Real.sq_sqrt (hepos n).le
    have hsqrt : Real.sqrt (e n) ≤ 2*(k n:ℝ) := by
      have := heD n
      nlinarith
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*D) hsqrtpos).mpr
    have hh := mul_le_mul_of_nonneg_left hsqrt hnp
    nlinarith
  refine ⟨fun n => u n ∘ fourToThree,e,?_,?_,?_⟩
  · intro n
    refine ⟨(hu n).comp fourToThree_smooth,?_,hepos n,?_,hfin n⟩
    · intro heq
      apply hu0 n
      funext q
      exact congrFun heq (q.1,(q.2,1))
    · intro p
      rw [laplaceBeltrami_four_lift g (u n) (hu n) p]
      exact hue n (fourToThree p)
  · exact tendsto_atTop_mono (fun n => (heB n).le) hbase
  · exact tendsto_atTop_mono heratio (hbase.atTop_div_const (by positivity : (0:ℝ)<2*D))

theorem sphere_two_torus_two :
    ∃ g : SmoothMetric FourModel FourManifold,
      HasUnboundedNodalRatio g 4 := by
  obtain ⟨R,hR,g,hg⟩ := exists_three_fixed_witnesses
  exact ⟨fourProductMetric g,four_witnesses_unbounded R g hg⟩
end YauCounterexamples
end

end OAI
