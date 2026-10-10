import OAI.Geometry.EinsteinFour.AngularTrace
import OAI.Geometry.EinsteinFour.ChartConnectionTransition
import OAI.Geometry.EinsteinFour.CurvatureTensors02
import OAI.Geometry.EinsteinFour.EuclideanHausdorffFactor
import OAI.Geometry.EinsteinFour.FrameOrientationContinuity
import OAI.Geometry.EinsteinFour.JacobiDensityMeasurability
import OAI.Geometry.EinsteinFour.JacobiNormalized
import OAI.Geometry.EinsteinFour.LocalCoordinateMeasure
import OAI.Geometry.EinsteinFour.ScalarH1CompositionL2
import OAI.Geometry.EinsteinFour.ScalarLpNormVariation
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMeasure
import OAI.Geometry.EinsteinFour.WeightedAreaInequality
import OAI.Geometry.EinsteinFour.WeylEstimates01
import OAI.Geometry.EinsteinFour.WeylEstimates03
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sequences

namespace OAI


section

/-! Exact unit-speed length and endpoint distance bounds for the actual
complete geodesics, including their intrinsic unit-tangent formulation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameGeodesic_pathELength (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (a b : ℝ) :
    (let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I4 (frameGeodesic g k e) a b) = ENNReal.ofReal (b - a) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change (∫⁻ s in Icc a b, metricTangentENorm g (frameGeodesic g k e s)
    (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g k e) s 1)) = _
  simp_rw [frameGeodesic_metric_speed]
  simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc]

theorem frameGeodesic_distance_le (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (a b : ℝ) :
    metricEDistance g (frameGeodesic g k e a) (frameGeodesic g k e b) ≤
      ENNReal.ofReal |b - a| := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hbound (s t : ℝ) (hst : s ≤ t) :
      metricEDistance g (frameGeodesic g k e s) (frameGeodesic g k e t) ≤
        ENNReal.ofReal (t - s) := by
    change Manifold.riemannianEDist I4 _ _ ≤ _
    exact (Manifold.riemannianEDist_le_pathELength
      (frameGeodesic_contMDiff g k e).contMDiffOn rfl rfl hst).trans_eq
        (frameGeodesic_pathELength g k e s t)
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hbound a b hab
  · have hs : metricEDistance g (frameGeodesic g k e a) (frameGeodesic g k e b) =
        metricEDistance g (frameGeodesic g k e b) (frameGeodesic g k e a) :=
      Manifold.riemannianEDist_comm
    rw [hs, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact hbound b a hba

theorem frameGeodesic_distance_from_start (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (t : ℝ) :
    metricEDistance g e.base (frameGeodesic g k e t) ≤ ENNReal.ofReal |t| := by
  simpa only [frameGeodesic, parallelFrameFlowMap_zero, sub_zero] using
    frameGeodesic_distance_le g k e 0 t

def unitGeodesic (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) (t : ℝ) : M := (unitTangentFlowMap g o t u).base

theorem unitGeodesic_eq_frameGeodesic (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) :
    unitGeodesic g o u = frameGeodesic g 0 (unitTangentFrame g o u) := rfl

theorem unitGeodesic_contMDiff (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) : ContMDiff 𝓘(ℝ, ℝ) I4 1 (unitGeodesic g o u) :=
  frameGeodesic_contMDiff g 0 (unitTangentFrame g o u)

theorem unitGeodesic_distance_le (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) (a b : ℝ) :
    metricEDistance g (unitGeodesic g o u a) (unitGeodesic g o u b) ≤
      ENNReal.ofReal |b - a| :=
  frameGeodesic_distance_le g 0 (unitTangentFrame g o u) a b

theorem unitGeodesic_distance_from_start (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) (t : ℝ) :
    metricEDistance g u.base (unitGeodesic g o u t) ≤ ENNReal.ofReal |t| := by
  have hbase : (unitTangentFrame g o u).base = u.base :=
    congrArg UnitTangentBundle.base (unitTangentOfFrame_lift g o u)
  simpa only [← unitGeodesic_eq_frameGeodesic g o u, hbase] using
    frameGeodesic_distance_from_start g 0 (unitTangentFrame g o u) t

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite subdivision of a compact curve segment whose individual
closed pieces lie in single coordinate charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def affinePartitionTime (a b : ℝ) (n i : ℕ) : ℝ := a + (b - a) * (i : ℝ) / (n : ℝ)

theorem affinePartitionTime_zero (a b : ℝ) (n : ℕ) : affinePartitionTime a b n 0 = a := by
  simp [affinePartitionTime]

theorem affinePartitionTime_last (a b : ℝ) (n : ℕ) (hn : 0 < n) :
    affinePartitionTime a b n n = b := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [affinePartitionTime, hnr]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem exists_finite_curve_chart_partition (γ : ℝ → M) (hγ : Continuous γ)
    (a b : ℝ) (hab : a < b) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → M, ∀ i < n,
      MapsTo γ (Icc (affinePartitionTime a b n i) (affinePartitionTime a b n (i + 1)))
        (chartAt FourSpace (c i)).source := by
  let U := fun c : M => γ ⁻¹' (chartAt FourSpace c).source
  have hU : ∀ c, IsOpen (U c) := fun c => (chartAt FourSpace c).open_source.preimage hγ
  have hcov : Icc a b ⊆ ⋃ c : M, U c := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, mem_chart_source FourSpace (γ t)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hU hcov
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ + 1)
  have hnposR : 0 < (n : ℝ) := by
    have : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.mpr hab.le) hδ.le
    linarith
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have hstep : (b - a) / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnposR).mpr
    have h := (div_lt_iff₀ hδ).mp (show (b - a) / δ < (n : ℝ) by linarith)
    nlinarith
  have htime : ∀ i ≤ n, affinePartitionTime a b n i ∈ Icc a b := by
    intro i hi
    have hir : (i : ℝ) ≤ n := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    constructor
    · have hfrac0 : 0 ≤ (b - a) * (i : ℝ) / (n : ℝ) := by positivity
      dsimp [affinePartitionTime]
      linarith
    · dsimp [affinePartitionTime]
      have hfrac : (b - a) * (i : ℝ) / (n : ℝ) ≤ b - a := by
        apply (div_le_iff₀ hnposR).mpr
        nlinarith
      linarith
  have hc : ∀ i < n, ∃ c : M, ball (affinePartitionTime a b n i) δ ⊆ U c := by
    intro i hi
    exact hball _ (htime i hi.le)
  choose c hc using fun i : {i : ℕ // i < n} => hc i.val i.property
  let C : ℕ → M := fun i => if hi : i < n then c ⟨i, hi⟩ else γ a
  refine ⟨n, hnpos, C, fun i hi t ht => ?_⟩
  have hdist : dist t (affinePartitionTime a b n i) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have hdiff : affinePartitionTime a b n (i + 1) - affinePartitionTime a b n i =
        (b - a) / (n : ℝ) := by
      simp only [affinePartitionTime, Nat.cast_add, Nat.cast_one]
      ring
    linarith [ht.2]
  have hm := hc ⟨i, hi⟩ (show t ∈ ball (affinePartitionTime a b n i) δ from hdist)
  simpa only [C, dite_eq_left hi, U, Set.mem_preimage] using hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quadratic normal endpoint curve depends only on its base point
and its actual tangent vector, not on the frame used to represent it. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_map (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) :
    WithLp.toLp 2 (frameChartMatrix g c e *ᵥ WithLp.ofLp v) =
      chartForwardOperator c e.base (e.frame.map v) := by
  let Q := (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap
  have hcol (i : Fin 4) : Q (coordinateVector i) =
      WithLp.toLp 2 (fun j => frameChartMatrix g c e j i) := by
    change chartForwardOperator c e.base (e.frame.map (coordinateVector i)) = _
    rw [e.frame.map_coordinateVector]
    exact (frameChart_column_eq_derivative g c e i he).symm
  have hQ : Q v = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ WithLp.ofLp v) := by
    have hsum : (∑ i, (WithLp.ofLp v) i • coordinateVector i) = v :=
      sum_coordinateVector (WithLp.ofLp v)
    conv_lhs => rw [← hsum]
    rw [map_sum]
    simp only [map_smul,hcol]
    ext j
    simp [Matrix.mulVec,dotProduct,mul_comm]
  exact hQ.symm

theorem normalQuadraticEndpointCurve_zero (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : normalQuadraticEndpointCurve g e a 0 = e.base := by
  rw [normalQuadraticEndpointCurve,normalEndpointQuadratic_zero]
  exact (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)

theorem normalQuadraticEndpointCurve_continuousAt (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : ContinuousAt (normalQuadraticEndpointCurve g e a) 0 := by
  have hin : normalEndpointQuadratic g e a 0 ∈ (chartAt FourSpace e.base).target := by
    rw [normalEndpointQuadratic_zero]
    exact (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  exact ((chartAt FourSpace e.base).continuousAt_symm hin).comp
    (f := normalEndpointQuadratic g e a) (normalEndpointQuadratic_contDiff g e a).continuous.continuousAt

theorem normalQuadraticEndpointCurve_eq (g : SmoothMetric M) (e f : FrameBundle g)
    (a b : Fin 3 → ℝ) (hbase : e.base = f.base)
    (hvec : e.frame.map (WithLp.toLp 2 (Fin.cons 0 a)) =
      f.frame.map (WithLp.toLp 2 (Fin.cons 0 b))) :
    normalQuadraticEndpointCurve g e a = normalQuadraticEndpointCurve g f b := by
  cases e with
  | mk x E =>
    cases f with
    | mk y F =>
      change x = y at hbase
      subst y
      have hd : normalEndpointDirection g (⟨x,E⟩ : FrameBundle g) a =
          normalEndpointDirection g (⟨x,F⟩ : FrameBundle g) b := by
        apply WithLp.toLp_injective 2
        change WithLp.toLp 2 (frameChartMatrix g x (⟨x,E⟩ : FrameBundle g) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Fin.cons 0 a))) =
          WithLp.toLp 2 (frameChartMatrix g x (⟨x,F⟩ : FrameBundle g) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (Fin.cons 0 b)))
        rw [frameChart_map g x _ (mem_chart_source FourSpace x),
          frameChart_map g x _ (mem_chart_source FourSpace x),hvec]
      funext s
      simp only [normalQuadraticEndpointCurve,normalEndpointQuadratic,
        normalEndpointAcceleration,hd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive radial extension of the actual unit-speed geodesic flow.
Its ambient measure preservation suffices for every unit-speed frame flow,
by continuity across energy shells and normal-frame averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- Radius is constant and multiplies the time of the unit-speed flow. -/
def unitTangentRadialFlow (g : SmoothMetric M) (o : FrameOrientation g) (t : ℝ)
    (p : PositiveRadius × UnitTangentBundle g) : PositiveRadius × UnitTangentBundle g :=
  (p.1, unitTangentFlowMap g o (p.1.val * t) p.2)

theorem unitTangentRadialFlow_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) : Continuous (unitTangentRadialFlow g o t) :=
  continuous_fst.prodMk ((unitTangentFlowMap_continuous g o).comp
    (((continuous_subtype_val.comp continuous_fst).mul_const t).prodMk continuous_snd))

def unitTangentRadialHomeomorph (g : SmoothMetric M) (o : FrameOrientation g) (t : ℝ) :
    (PositiveRadius × UnitTangentBundle g) ≃ₜ (PositiveRadius × UnitTangentBundle g) where
  toFun := unitTangentRadialFlow g o t
  invFun := unitTangentRadialFlow g o (-t)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change unitTangentFlowMap g o (p.1.val * -t)
        (unitTangentFlowMap g o (p.1.val * t) p.2) = p.2
      rw [← unitTangentFlowMap_add, mul_neg, neg_add_cancel, unitTangentFlowMap_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · change unitTangentFlowMap g o (p.1.val * t)
        (unitTangentFlowMap g o (p.1.val * -t) p.2) = p.2
      rw [← unitTangentFlowMap_add, mul_neg, add_neg_cancel, unitTangentFlowMap_zero]
  continuous_toFun := unitTangentRadialFlow_continuous g o t
  continuous_invFun := unitTangentRadialFlow_continuous g o (-t)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem unitTangentFlow_preserves_of_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (hambient : MeasurePreserving (unitTangentRadialFlow g o t)
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))) :
    MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o) := by
  let : PseudoMetrizableSpace (UnitTangentBundle g) := unitTangentBundle_pseudoMetrizable g o
  have h := measurePreserving_cubicEnergyShell (canonicalUnitTangentMeasure g o)
    (fun p : PositiveRadius × UnitTangentBundle g =>
      unitTangentFlowMap g o (p.1.val * t) p.2)
    (continuous_snd.comp (unitTangentRadialFlow_continuous g o t)) hambient
    (⟨1, by norm_num [PositiveRadius]⟩ : PositiveRadius)
  simpa only [one_mul] using h

theorem allFrameFlows_preserve_of_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (hambient : ∀ t, MeasurePreserving (unitTangentRadialFlow g o t)
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))) (k : Fin 4) (t : ℝ) :
    MeasurePreserving (parallelFrameFlowMap g k t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) :=
  allFrameFlows_preserve_of_unitTangent o
    (fun s => unitTangentFlow_preserves_of_radial g o s (hambient s)) k t

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential in an orthonormal frame, constructed from the
complete unit-speed geodesics. The zero vector is included continuously,
using the proved metric length bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def frameExponentialNonzero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : ({0}ᶜ : Set FourSpace)) : M :=
  unitGeodesic g o (unitTangentTurn e (euclideanPolarHomeomorph v).1)
    (euclideanPolarHomeomorph v).2.val

def frameExponential (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : FourSpace → M :=
  Function.extend (Subtype.val : ({0}ᶜ : Set FourSpace) → FourSpace)
    (frameExponentialNonzero g o e) (fun _ => e.base)

theorem frameExponential_nonzero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : ({0}ᶜ : Set FourSpace)) :
    frameExponential g o e v.val = frameExponentialNonzero g o e v :=
  Subtype.val_injective.extend_apply _ _ v

theorem frameExponential_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : frameExponential g o e 0 = e.base := by
  apply Function.extend_apply'
  rintro ⟨v, hv⟩
  exact (show (v : FourSpace) ≠ 0 from v.property) hv

theorem frameExponential_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (q : Directions) (r : PositiveRadius) :
    frameExponential g o e (r.val • q.val) = unitGeodesic g o (unitTangentTurn e q) r.val := by
  let p : Directions × PositiveRadius := (q, r)
  have hv := frameExponential_nonzero g o e (euclideanPolarHomeomorph.symm p)
  simpa only [euclideanPolarHomeomorph_symm_coe, euclideanPolarReconstruction,
    frameExponentialNonzero, Homeomorph.apply_symm_apply] using hv

theorem frameExponential_distance (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) :
    metricEDistance g e.base (frameExponential g o e v) ≤ ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero, ENNReal.ofReal_zero]
    exact le_of_eq (Manifold.riemannianEDist_self (I := I4))
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
    have hr : (euclideanPolarHomeomorph w).2.val = ‖v‖ := by
      exact homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    rw [frameExponential_nonzero g o e w]
    have h := unitGeodesic_distance_from_start g o
      (unitTangentTurn e (euclideanPolarHomeomorph w).1)
      (euclideanPolarHomeomorph w).2.val
    have hb : (unitTangentTurn e (euclideanPolarHomeomorph w).1).base = e.base := rfl
    simpa only [frameExponentialNonzero, hb, hr, abs_of_nonneg (norm_nonneg v)] using h

theorem frameExponentialNonzero_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponentialNonzero g o e) := by
  have hu : Continuous (fun v : ({0}ᶜ : Set FourSpace) =>
      unitTangentTurn e (euclideanPolarHomeomorph v).1) :=
    (continuous_unitTangentTurn_fixed e).comp (euclideanPolarHomeomorph.continuous.fst)
  have ht : Continuous (fun v : ({0}ᶜ : Set FourSpace) =>
      (euclideanPolarHomeomorph v).2.val) :=
    continuous_subtype_val.comp euclideanPolarHomeomorph.continuous.snd
  exact (continuous_unitTangentBase g).comp
    ((unitTangentFlowMap_continuous g o).comp (ht.prodMk hu))

variable [T3Space M]

theorem frameExponential_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponential g o e) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  have ho : ContinuousOn (frameExponential g o e) ({0}ᶜ : Set FourSpace) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (frameExponentialNonzero_continuous g o e).congr
      (fun v => (frameExponential_nonzero g o e v).symm)
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    apply (tendsto_iff_edist_tendsto_0).mpr
    have hn : Tendsto (fun w : FourSpace => ENNReal.ofReal ‖w‖) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun w : FourSpace => ENNReal.ofReal ‖w‖) :=
        ENNReal.continuous_ofReal.comp continuous_norm
      simpa only [norm_zero, ENNReal.ofReal_zero] using hc.tendsto 0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn
      (fun _ => bot_le) (fun w => ?_)
    rw [frameExponential_zero, edist_comm]
    exact frameExponential_distance g o e w
  · exact (ho v hv).continuousAt (isOpen_compl_singleton.mem_nhds hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joining two chart partitions at the corner of a piecewise C1 normal
field, and reconstructing the two index integrals from their finite sums. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

def joinedPartitionTime (a c b : ℝ) (n m i : ℕ) : ℝ :=
  if i ≤ n then affinePartitionTime a c n i else affinePartitionTime c b m (i - n)

theorem affinePartitionTime_step_lt (a b : ℝ) (n i : ℕ) (hab : a < b) (hn : 0 < n) :
    affinePartitionTime a b n i < affinePartitionTime a b n (i + 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : affinePartitionTime a b n (i + 1) - affinePartitionTime a b n i =
      (b - a) / (n : ℝ) := by
    simp only [affinePartitionTime, Nat.cast_add, Nat.cast_one]
    ring
  have hp : 0 < (b - a) / (n : ℝ) := div_pos (sub_pos.mpr hab) hnR
  linarith

theorem joinedPartitionTime_left (a c b : ℝ) (n m i : ℕ) (hi : i ≤ n) :
    joinedPartitionTime a c b n m i = affinePartitionTime a c n i := by
  simp only [joinedPartitionTime, ite_eq_left hi]

theorem joinedPartitionTime_right (a c b : ℝ) (n m j : ℕ) (hn : 0 < n) :
    joinedPartitionTime a c b n m (n + j) = affinePartitionTime c b m j := by
  by_cases hj : j = 0
  · subst j
    rw [Nat.add_zero, joinedPartitionTime_left _ _ _ _ _ _ le_rfl,
      affinePartitionTime_last _ _ _ hn, affinePartitionTime_zero]
  · have hnot : ¬ n + j ≤ n := by omega
    simp only [joinedPartitionTime, ite_eq_right hnot, Nat.add_sub_cancel_left]

theorem joinedPartitionTime_zero (a c b : ℝ) (n m : ℕ) :
    joinedPartitionTime a c b n m 0 = a := by
  rw [joinedPartitionTime_left _ _ _ _ _ _ (Nat.zero_le _), affinePartitionTime_zero]

theorem joinedPartitionTime_last (a c b : ℝ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    joinedPartitionTime a c b n m (n + m) = b := by
  rw [joinedPartitionTime_right _ _ _ _ _ _ hn, affinePartitionTime_last _ _ _ hm]

theorem joinedPartitionTime_step_lt (a c b : ℝ) (n m i : ℕ)
    (hac : a < c) (hcb : c < b) (hn : 0 < n) (hm : 0 < m) :
    joinedPartitionTime a c b n m i < joinedPartitionTime a c b n m (i + 1) := by
  by_cases hi : i < n
  · rw [joinedPartitionTime_left _ _ _ _ _ _ hi.le,
      joinedPartitionTime_left _ _ _ _ _ _ hi]
    exact affinePartitionTime_step_lt a c n i hac hn
  · have heq : i = n + (i - n) := by omega
    rw [heq, show n + (i - n) + 1 = n + (i - n + 1) by omega,
      joinedPartitionTime_right _ _ _ _ _ _ hn, joinedPartitionTime_right _ _ _ _ _ _ hn]
    exact affinePartitionTime_step_lt c b m (i - n) hcb hm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem joinedPartition_chart_cover (γ : ℝ → M) (a c b : ℝ) (n m : ℕ) (hn : 0 < n)
    (C D : ℕ → M)
    (hC : ∀ i < n, MapsTo γ (Icc (affinePartitionTime a c n i)
      (affinePartitionTime a c n (i + 1))) (chartAt FourSpace (C i)).source)
    (hD : ∀ j < m, MapsTo γ (Icc (affinePartitionTime c b m j)
      (affinePartitionTime c b m (j + 1))) (chartAt FourSpace (D j)).source) :
    ∀ i < n + m, MapsTo γ (Icc (joinedPartitionTime a c b n m i)
      (joinedPartitionTime a c b n m (i + 1)))
      (chartAt FourSpace (if i < n then C i else D (i - n))).source := by
  intro i hi
  by_cases hil : i < n
  · rw [ite_eq_left hil, joinedPartitionTime_left _ _ _ _ _ _ hil.le,
      joinedPartitionTime_left _ _ _ _ _ _ hil]
    exact hC i hil
  · have heq : i = n + (i - n) := by omega
    have hj : i - n < m := by omega
    rw [ite_eq_right hil]
    rw [heq, show n + (i - n) + 1 = n + (i - n + 1) by omega,
      joinedPartitionTime_right _ _ _ _ _ _ hn, joinedPartitionTime_right _ _ _ _ _ _ hn,
      Nat.add_sub_cancel_left]
    exact hD (i - n) hj

theorem sum_intervalIntegral_partition (f : ℝ → ℝ) (hf : Continuous f) (T : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ r in T i..T (i + 1), f r) = ∫ r in T 0..T n, f r := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

theorem joinedPartition_sum_integral (a c b : ℝ) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G) :
    (∑ i ∈ Finset.range (n + m),
      ∫ r in joinedPartitionTime a c b n m i..joinedPartitionTime a c b n m (i + 1),
        (if i < n then F r else G r)) =
      (∫ r in a..c, F r) + ∫ r in c..b, G r := by
  rw [Finset.sum_range_add]
  have hl : (∑ i ∈ Finset.range n,
      ∫ r in joinedPartitionTime a c b n m i..joinedPartitionTime a c b n m (i + 1),
        (if i < n then F r else G r)) = ∫ r in a..c, F r := by
    calc
      _ = ∑ i ∈ Finset.range n, ∫ r in affinePartitionTime a c n i..
          affinePartitionTime a c n (i + 1), F r := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simp only [ite_eq_left hi', joinedPartitionTime_left _ _ _ _ _ _ hi'.le,
          joinedPartitionTime_left _ _ _ _ _ _ hi']
      _ = _ := by
        rw [sum_intervalIntegral_partition F hF, affinePartitionTime_zero,
          affinePartitionTime_last _ _ _ hn]
  have hr : (∑ j ∈ Finset.range m,
      ∫ r in joinedPartitionTime a c b n m (n + j)..joinedPartitionTime a c b n m (n + j + 1),
        (if n + j < n then F r else G r)) = ∫ r in c..b, G r := by
    calc
      _ = ∑ j ∈ Finset.range m, ∫ r in affinePartitionTime c b m j..
          affinePartitionTime c b m (j + 1), G r := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : ¬ n + j < n := by omega
        simp only [ite_eq_right hj, show n + j + 1 = n + (j + 1) by omega,
          joinedPartitionTime_right _ _ _ _ _ _ hn]
      _ = _ := by
        rw [sum_intervalIntegral_partition G hG, affinePartitionTime_zero,
          affinePartitionTime_last _ _ _ hm]
  rw [hl, hr]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Two elementary assembly steps for the actual Hamiltonian-volume proof:
local image-measure identities glue, and a neighborhood of preserving times
for the complete unit tangent flow gives every real time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

theorem measure_eq_of_local_restrict {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [SecondCountableTopology X] (μ ν : Measure X)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ.restrict U = ν.restrict U) :
    μ = ν := by
  choose U hU hx hm using hlocal
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds (fun x => (hU x).mem_nhds (hx x))
  exact Measure.ext_of_biUnion_eq_univ hs hcover (fun x _ => hm x)

/-- Pointwise local domination suffices for domination of the measures.
This applies the same countable-cover argument to their lattice infimum. -/
theorem measure_le_of_local_restrict {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ ν : Measure X)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ.restrict U ≤ ν.restrict U) :
    μ ≤ ν := by
  apply inf_eq_left.mp
  apply measure_eq_of_local_restrict
  intro x
  obtain ⟨U, hU, hx, hm⟩ := hlocal x
  refine ⟨U, hU, hx, ?_⟩
  have hi : (μ ⊓ ν).restrict U = μ.restrict U ⊓ ν.restrict U := by
    simpa only [Set.image_insert_eq, Set.image_singleton, sInf_pair] using
      (Measure.restrict_sInf_eq_sInf_restrict (m := {μ, ν})
        (by simp : ({μ, ν} : Set (Measure X)).Nonempty) hU.measurableSet)
  rw [hi, inf_eq_left.mpr hm]

/-- Arbitrarily sharp local lower comparisons give exact global
domination, with no differentiation theorem for measures required. -/
theorem measure_le_of_sharp_local_comparison {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ ν : Measure X)
    (hlocal : ∀ a : ℝ≥0∞, a < 1 → ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (a • μ).restrict U ≤ ν.restrict U) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro A _hA
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  have h := measure_le_of_local_restrict (a • μ) ν (hlocal a ha)
  simpa only [Measure.smul_apply, smul_eq_mul] using h A

/-- Local image-measure identities for a homeomorphism determine its
pushforward on the whole second-countable space. -/
theorem measurePreserving_of_local_image {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (f : X ≃ₜ X) (μ : Measure X)
    (hlocal : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      Measure.map f (μ.restrict U) = μ.restrict (f '' U)) :
    MeasurePreserving f μ μ := by
  choose U hU hx hm using hlocal
  obtain ⟨s, hs, hcover⟩ := countable_cover_nhds (fun x => (hU x).mem_nhds (hx x))
  have himage : ⋃ x ∈ s, f '' U x = (univ : Set X) := by
    rw [← image_iUnion₂, hcover, image_univ_of_surjective f.surjective]
  refine ⟨f.measurable, Measure.ext_of_biUnion_eq_univ hs himage ?_⟩
  intro x _
  rw [f.measurableEmbedding.restrict_map μ (f '' U x),
    preimage_image_eq _ f.injective]
  exact hm x

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- It suffices to preserve the actual unit tangent probability for a
fixed nonempty time interval around zero. Completeness and the group law
then give preservation for every real time. -/
theorem unitTangentFlow_preserves_of_near_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (ε : ℝ) (hε : 0 < ε)
    (hnear : ∀ t ∈ Ioo (-ε) ε, MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o)) (t : ℝ) :
    MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hnzero : (n : ℝ) ≠ 0 := hnpos.ne'
  let s : ℝ := t / n
  have hs : |s| < ε := by
    dsimp [s]
    rw [abs_div, abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hstep := hnear s (abs_lt.mp hs)
  have hmul (m : ℕ) : MeasurePreserving (unitTangentFlowMap g o ((m : ℝ) * s))
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o) := by
    induction m with
    | zero =>
      convert MeasurePreserving.id (canonicalUnitTangentMeasure g o) using 1
      funext u
      simp only [Nat.cast_zero, zero_mul, unitTangentFlowMap_zero, id_eq]
    | succ m ih =>
      have h := ih.comp hstep
      convert h using 1
      funext u
      rw [Nat.cast_succ, add_mul, one_mul, unitTangentFlowMap_add]
      rfl
  have heq : (n : ℝ) * s = t := by dsimp [s]; field_simp
  simpa only [heq] using hmul n

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial geodesic motion, in each local cotangent chart, is
the constructed kinetic Hamiltonian flow. No continuous frame choice is
needed: uniqueness allows an arbitrary positive frame at the initial point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def unitRadialCotangentState (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g) : CotangentCoordinates :=
  unitCotangentState g c p.1.val p.2

omit [T2Space M] [CompactSpace M] in
theorem unitRadialCotangentState_continuousAt (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (unitRadialCotangentState g c) p := by
  exact ContinuousAt.comp (x := p)
    (g := fun q : ℝ × UnitTangentBundle g => unitCotangentState g c q.1 q.2)
    (f := fun q : PositiveRadius × UnitTangentBundle g => (q.1.val, q.2))
    (unitCotangentState_continuousAt g c p.1.val p.2 hp)
    (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt)

theorem hasDerivAt_unitTangentRadial_cotangent (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (ht : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => unitRadialCotangentState g c (unitTangentRadialFlow g o s p))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (unitRadialCotangentState g c (unitTangentRadialFlow g o t p))) t := by
  obtain ⟨e, he, hue⟩ := exists_positive_unitTangent_frame g o p.2
  have heq (s : ℝ) : unitRadialCotangentState g c (unitTangentRadialFlow g o s p) =
      radialFrameCotangentState g c 0 (p.1.val,
        parallelFrameFlowMap g 0 (p.1.val * s) e) := by
    change unitCotangentState g c p.1.val
      (unitTangentFlowMap g o (p.1.val * s) p.2) = _
    rw [← hue, unitTangentFlowMap_of_frame g o _ e he, unitCotangentState_frame]
  have hbase : (parallelFrameFlowMap g 0 (p.1.val * t) e).base =
      (unitTangentRadialFlow g o t p).2.base := by
    change (parallelFrameFlowMap g 0 (p.1.val * t) e).base =
      (unitTangentFlowMap g o (p.1.val * t) p.2).base
    rw [← hue, unitTangentFlowMap_of_frame g o _ e he]
    rfl
  have h := radialFrameFlowMap_cotangent_derivative g c 0 p.1.val t e (hbase.symm ▸ ht)
  have hfun : (fun s => unitRadialCotangentState g c (unitTangentRadialFlow g o s p)) =
      (fun s => radialFrameCotangentState g c 0 (p.1.val,
        parallelFrameFlowMap g 0 (p.1.val * s) e)) := funext heq
  rw [hfun, heq]
  exact h

theorem unitTangentRadialFlow_joint_continuous (g : SmoothMetric M) (o : FrameOrientation g) :
    Continuous (fun z : ℝ × (PositiveRadius × UnitTangentBundle g) =>
      unitTangentRadialFlow g o z.1 z.2) := by
  have hr : Continuous (fun z : ℝ × (PositiveRadius × UnitTangentBundle g) => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hu : Continuous (fun z : ℝ × (PositiveRadius × UnitTangentBundle g) => z.2.2) :=
    continuous_snd.comp continuous_snd
  exact hr.prodMk ((unitTangentFlowMap_continuous g o).comp
    (((continuous_subtype_val.comp hr).mul continuous_fst).prodMk hu))

private theorem unitTangentRadialFlow_chart_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
      ∃ δ > (0 : ℝ), ∀ q ∈ U, ∀ t ∈ Ioo (-δ) δ,
        (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace c).source := by
  have hb : Continuous (fun u : UnitTangentBundle g => u.base) :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp
      (show Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) from
        continuous_induced_dom)
  have hc := (hb.comp (continuous_snd.comp
    (unitTangentRadialFlow_joint_continuous g o))).continuousAt (x := (0, p))
  have hzero : (unitTangentRadialFlow g o 0 p).2 = p.2 := by
    change unitTangentFlowMap g o (p.1.val * 0) p.2 = p.2
    rw [mul_zero, unitTangentFlowMap_zero]
  have hn : {z : ℝ × (PositiveRadius × UnitTangentBundle g) |
      (unitTangentRadialFlow g o z.1 z.2).2.base ∈ (chartAt FourSpace c).source}
      ∈ 𝓝 ((0 : ℝ), p) := hc.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds (by
      change (unitTangentRadialFlow g o 0 p).2.base ∈ (chartAt FourSpace c).source
      rw [hzero]
      exact hp))
  obtain ⟨T, U, hT, h0, hU, hpU, hTU⟩ := mem_nhds_prod_iff'.mp hn
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨U, hU, hpU, δ, hδ, fun q hq t ht => ?_⟩
  have htT : t ∈ T := hδT (by simpa only [Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs] using abs_lt.mpr ht)
  exact hTU (show (t, q) ∈ T ×ˢ U from ⟨htT, hq⟩)

/-- A common open intrinsic neighborhood is conjugate to the actual local
Hamiltonian flow. This is the local input for transporting its volume law. -/
theorem exists_unitTangent_localHamiltonian (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
      ∃ F : KineticLocalFlow g c (unitRadialCotangentState g c p),
        (∀ q ∈ U, unitRadialCotangentState g c q ∈
          Metric.ball (unitRadialCotangentState g c p) F.radius) ∧
        (∀ q ∈ U, EqOn (fun t => F.map (unitRadialCotangentState g c q, t))
          (fun t => unitRadialCotangentState g c (unitTangentRadialFlow g o t q))
          (Ioo (-F.time) F.time)) := by
  obtain ⟨F₀⟩ := exists_kineticLocalFlow g c (unitRadialCotangentState g c p)
    ((chartAt FourSpace c).map_source hp)
  obtain ⟨V, hV, hpV, δ, hδ, hchart⟩ :=
    unitTangentRadialFlow_chart_neighborhood g o c p hp
  have hn : {q : PositiveRadius × UnitTangentBundle g | unitRadialCotangentState g c q ∈
      Metric.ball (unitRadialCotangentState g c p) F₀.radius} ∈ 𝓝 p :=
    (unitRadialCotangentState_continuousAt g c p hp).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self F₀.radius_pos))
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hn
  let τ := min F₀.time δ
  have hτ : 0 < τ := lt_min F₀.time_pos hδ
  let F := F₀.restrictTime τ hτ (min_le_left _ _)
  have htime {t : ℝ} (ht : t ∈ Ioo (-F.time) F.time) : t ∈ Ioo (-δ) δ := by
    have hle : F.time ≤ δ := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨V ∩ W, hV.inter hW, ⟨hpV, hpW⟩, F, (fun q hq => hWsub hq.2), ?_⟩
  intro q hq
  apply F.eq_on _ (hWsub hq.2)
  · change unitCotangentState g c q.1.val
      (unitTangentFlowMap g o (q.1.val * 0) q.2) = _
    rw [mul_zero, unitTangentFlowMap_zero]
    rfl
  · intro t ht
    exact hasDerivAt_unitTangentRadial_cotangent g o c q t (hchart q hq.1 t (htime ht))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial exponential is the actual local kinetic endpoint map near
zero. A common coordinate interval works for every unit direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Lowering the initial frame vector in a fixed coordinate chart. -/
def frameMomentumMap (g : SmoothMetric M) (c : M) (e : FrameBundle g) :
    FourSpace →L[ℝ] FourSpace :=
  (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (metricInChart g c (chartAt FourSpace c e.base))).comp
      ((chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap)

theorem unitCotangentState_turn (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (r : ℝ) (q : Directions) :
    unitCotangentState g c r (unitTangentTurn e q) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e (r • q.val)) := by
  have hv : (unitTangentTurn e q).vector = e.frame.map q.val := e.frame.turn_first q
  rw [unitCotangentState, unitChartVelocity_eq_derivative c _ he]
  change (_, r • WithLp.toLp 2 (_ *ᵥ WithLp.ofLp
    (chartForwardOperator c e.base (unitTangentTurn e q).vector))) = _
  rw [hv]
  simp only [frameMomentumMap, map_smul, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap']
  rfl

variable [T2Space M] [CompactSpace M]

theorem unitGeodesic_turn_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (q : Directions) :
    unitGeodesic g o (unitTangentTurn e q) 0 = e.base := by
  rw [unitGeodesic, unitTangentFlowMap_zero]
  rfl

theorem unitGeodesic_turn_joint_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    Continuous (fun p : ℝ × Directions => unitGeodesic g o (unitTangentTurn e p.2) p.1) := by
  have harg : Continuous (fun p : ℝ × Directions => (p.1, unitTangentTurn e p.2)) :=
    continuous_fst.prodMk ((continuous_unitTangentTurn_fixed e).comp continuous_snd)
  exact (continuous_unitTangentBase g).comp ((unitTangentFlowMap_continuous g o).comp harg)

private theorem direction_uniform_neighborhood {X : Type*} [TopologicalSpace X]
    (b : ℝ × Directions → X) (hb : Continuous b) (S : Set X) (hS : IsOpen S)
    (hzero : ∀ q, b (0, q) ∈ S) :
    ∃ δ > (0 : ℝ), ∀ q : Directions, ∀ t ∈ Ioo (-δ) δ, b (t, q) ∈ S := by
  have hz : ({0} : Set ℝ) ×ˢ (univ : Set Directions) ⊆ b ⁻¹' S := by
    rintro ⟨t, q⟩ ⟨ht, _⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero q
  obtain ⟨T, U, hT, _, h0, hU, hTU⟩ :=
    generalized_tube_lemma (s := ({0} : Set ℝ)) (t := (univ : Set Directions))
      isCompact_singleton isCompact_univ (hS.preimage hb) hz
  have h0T : (0 : ℝ) ∈ T := h0 rfl
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0T)
  refine ⟨δ, hδ, fun q t ht => hTU ?_⟩
  exact ⟨hδT (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    using abs_lt.mpr ht), hU (mem_univ q)⟩

theorem unitGeodesic_uniform_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ δ > (0 : ℝ), ∀ q : Directions, ∀ t ∈ Ioo (-δ) δ,
      unitGeodesic g o (unitTangentTurn e q) t ∈ (chartAt FourSpace c).source := by
  apply direction_uniform_neighborhood
    (fun p : ℝ × Directions => unitGeodesic g o (unitTangentTurn e p.2) p.1)
    (unitGeodesic_turn_joint_continuous g o e)
    (chartAt FourSpace c).source (chartAt FourSpace c).open_source
  intro q
  rw [unitGeodesic_turn_zero]
  exact he

/-- Every sufficiently short radial geodesic starting at a fixed frame
satisfies the same constructed local Hamiltonian flow, uniformly in direction. -/
theorem KineticLocalFlow.radial_endpoint_uniform (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (F : KineticLocalFlow g c (chartAt FourSpace c e.base, 0)) :
    ∃ ε > (0 : ℝ), ∀ q : Directions, ∀ r : ℝ, 0 < r → r < ε →
      ∀ t ∈ Ioo (-F.time) F.time,
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e (r • q.val)), t) =
          unitCotangentState g c r (unitTangentFlowMap g o (r * t) (unitTangentTurn e q)) := by
  obtain ⟨δ, hδ, hchart⟩ := unitGeodesic_uniform_chart g o c e he
  let P := frameMomentumMap g c e
  let ε := min (F.radius / (‖P‖ + 1)) (δ / (F.time + 1))
  have hP : 0 < ‖P‖ + 1 := by positivity
  have htime : 0 < F.time + 1 := by linarith [F.time_pos]
  have hε : 0 < ε := lt_min (div_pos F.radius_pos hP) (div_pos hδ htime)
  refine ⟨ε, hε, fun q r hr hrε t ht => ?_⟩
  have hrP : r * (‖P‖ + 1) < F.radius :=
    (lt_div_iff₀ hP).mp (hrε.trans_le (min_le_left _ _))
  have hrδ : r * (F.time + 1) < δ :=
    (lt_div_iff₀ htime).mp (hrε.trans_le (min_le_right _ _))
  have hqn : ‖q.val‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using q.property
  have hmoment : ‖P (r • q.val)‖ < F.radius := by
    have h := P.le_opNorm (r • q.val)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hqn, mul_one] at h
    nlinarith [norm_nonneg P]
  have hinit : (chartAt FourSpace c e.base, P (r • q.val)) ∈
      Metric.ball (chartAt FourSpace c e.base, 0) F.radius := by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_self, dist_zero_right,
      max_eq_right (norm_nonneg _)] using hmoment
  have hsource (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      unitGeodesic g o (unitTangentTurn e q) (r * s) ∈ (chartAt FourSpace c).source := by
    apply hchart q (r * s)
    have hsabs : |s| < F.time := abs_lt.mpr hs
    have hsmall : |r * s| < δ := by
      rw [abs_mul, abs_of_pos hr]
      nlinarith [abs_nonneg s]
    exact abs_lt.mp hsmall
  have hsol (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :=
    hasDerivAt_unitTangentRadial_cotangent g o c
      (⟨r, hr⟩, unitTangentTurn e q) s (hsource s hs)
  have heq := F.eq_on _ hinit
    (fun s => unitCotangentState g c r (unitTangentFlowMap g o (r * s) (unitTangentTurn e q)))
    (by simpa only [mul_zero, unitTangentFlowMap_zero] using
      unitCotangentState_turn g c e he r q) hsol
  exact heq ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local comparison on an open chart domain. The measures outside the
chart play no role, so neighborhoods are required only at its points. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measure_restrict_eq_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [SecondCountableTopology X] (μ ν : Measure X) (T : Set X)
    (hlocal : ∀ x ∈ T, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ T ∧
      μ.restrict U = ν.restrict U) : μ.restrict T = ν.restrict T := by
  choose U hU hx hsub heq using hlocal
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof T).elim_nhds_subcover'
    U (fun x hxT => (hU x hxT).mem_nhds (hx x hxT))
  have hcov : (⋃ x ∈ s, U (x : X) x.property) = T := by
    apply Subset.antisymm _ hcover
    apply iUnion₂_subset
    intro x _
    exact hsub x x.property
  rw [← hcov]
  exact (Measure.restrict_biUnion_congr hs).mpr (fun x _ => heq x x.property)

theorem measure_restrict_le_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ ν : Measure X) (T : Set X) (hT : IsOpen T)
    (hlocal : ∀ x ∈ T, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ T ∧
      μ.restrict U ≤ ν.restrict U) : μ.restrict T ≤ ν.restrict T := by
  have hinf : (μ ⊓ ν).restrict T = μ.restrict T ⊓ ν.restrict T := by
    simpa only [Set.image_insert_eq, Set.image_singleton, sInf_pair] using
      (Measure.restrict_sInf_eq_sInf_restrict (m := {μ, ν})
        (by simp : ({μ, ν} : Set (Measure X)).Nonempty) hT.measurableSet)
  apply inf_eq_left.mp
  rw [← hinf]
  apply measure_restrict_eq_of_local
  intro x hx
  obtain ⟨U, hU, hxU, hUT, hle⟩ := hlocal x hx
  refine ⟨U, hU, hxU, hUT, ?_⟩
  have hi : (μ ⊓ ν).restrict U = μ.restrict U ⊓ ν.restrict U := by
    simpa only [Set.image_insert_eq, Set.image_singleton, sInf_pair] using
      (Measure.restrict_sInf_eq_sInf_restrict (m := {μ, ν})
        (by simp : ({μ, ν} : Set (Measure X)).Nonempty) hU.measurableSet)
  rw [hi, inf_eq_left.mpr hle]

theorem measure_restrict_le_of_sharp_local_comparison {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ ν : Measure X) (T : Set X) (hT : IsOpen T)
    (hlocal : ∀ a : ℝ≥0∞, a < 1 → ∀ x ∈ T, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ U ⊆ T ∧ (a • μ).restrict U ≤ ν.restrict U) :
    μ.restrict T ≤ ν.restrict T := by
  apply Measure.le_iff.mpr
  intro A _
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  have h := measure_restrict_le_of_local (a • μ) ν T hT (hlocal a ha)
  simpa only [Measure.restrict_smul, Measure.smul_apply, smul_eq_mul] using h A

end
end PositiveEinsteinFour.Geometry
end


section

/-! Open cotangent neighborhoods for the actual radial flow. The local
Hamiltonian volume identity holds on every measurable subset of the initial
ball, and the intrinsic flow remains in the same chart on a common interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace KineticLocalFlow

/-- The proved unit Jacobian applies to any measurable part of the initial
ball. This is the form used after shrinking an intrinsic neighborhood. -/
theorem map_volume_restrict {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time)
    (s : Set CotangentCoordinates) (hs : MeasurableSet s)
    (hsub : s ⊆ Metric.ball p F.radius) :
    Measure.map (fun q => F.map (q, t)) (volume.restrict s) =
      volume.restrict ((fun q => F.map (q, t)) '' s) := by
  exact cotangent_map_volume_of_det_one _ s hs
    (fun q hq => (F.initial_derivative q (hsub hq) t ht).differentiableAt)
    ((F.injective_slice t ht).mono hsub)
    (fun q hq => by rw [F.jacobian_det q (hsub hq) t ht, abs_one])

end KineticLocalFlow

theorem unitRadialCotangentState_injOn (g : SmoothMetric M) (c : M) :
    InjOn (unitRadialCotangentState g c)
      {q | q.2.base ∈ (chartAt FourSpace c).source} := by
  intro p hp q hq heq
  let a : PositiveRadius × ChartUnitTangent g c := (p.1, ⟨p.2, hp⟩)
  let b : PositiveRadius × ChartUnitTangent g c := (q.1, ⟨q.2, hq⟩)
  have hab : a = b := (unitTangentCotangentHomeomorph g c).injective
    (Subtype.ext heq)
  exact congrArg (fun x : PositiveRadius × ChartUnitTangent g c => (x.1, x.2.val)) hab

theorem unitRadialCotangentState_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (unitRadialCotangentState g c)
      {q | q.2.base ∈ (chartAt FourSpace c).source} :=
  fun p hp => (unitRadialCotangentState_continuousAt g c p hp).continuousWithinAt

theorem isOpen_unitRadialCotangentState_image (g : SmoothMetric M) (c : M)
    (U : Set (PositiveRadius × UnitTangentBundle g)) (hU : IsOpen U)
    (hsource : ∀ q ∈ U, q.2.base ∈ (chartAt FourSpace c).source) :
    IsOpen (unitRadialCotangentState g c '' U) := by
  let E : PositiveRadius × ChartUnitTangent g c →
      PositiveRadius × UnitTangentBundle g := fun q => (q.1, q.2.val)
  have hE : Continuous E := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  let H := unitTangentCotangentHomeomorph g c
  have hN : IsOpen {z : CotangentCoordinates |
      z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0} :=
    ((chartAt FourSpace c).open_target.preimage continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)
  have hopen : IsOpen (Subtype.val '' (H '' (E ⁻¹' U))) :=
    hN.isOpenMap_subtype_val _ (H.isOpenMap _ (hU.preimage hE))
  have heq : Subtype.val '' (H '' (E ⁻¹' U)) = unitRadialCotangentState g c '' U := by
    ext z
    constructor
    · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨E q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      let a : PositiveRadius × ChartUnitTangent g c :=
        (q.1, ⟨q.2, hsource q hq⟩)
      exact ⟨H a, ⟨a, hq, rfl⟩, rfl⟩
  rwa [heq] at hopen

variable [T2Space M] [CompactSpace M]

private theorem radial_chart_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
      ∃ δ > (0 : ℝ), ∀ q ∈ U, ∀ t ∈ Ioo (-δ) δ,
        (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace c).source := by
  have hb : Continuous (fun u : UnitTangentBundle g => u.base) :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp
      (show Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) from
        continuous_induced_dom)
  have hc := (hb.comp (continuous_snd.comp
    (unitTangentRadialFlow_joint_continuous g o))).continuousAt (x := (0, p))
  have hzero : (unitTangentRadialFlow g o 0 p).2 = p.2 := by
    change unitTangentFlowMap g o (p.1.val * 0) p.2 = p.2
    rw [mul_zero, unitTangentFlowMap_zero]
  have hn : {z : ℝ × (PositiveRadius × UnitTangentBundle g) |
      (unitTangentRadialFlow g o z.1 z.2).2.base ∈ (chartAt FourSpace c).source}
      ∈ 𝓝 ((0 : ℝ), p) := hc.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds (by
      change (unitTangentRadialFlow g o 0 p).2.base ∈ (chartAt FourSpace c).source
      rw [hzero]
      exact hp))
  obtain ⟨T, U, hT, h0, hU, hpU, hTU⟩ := mem_nhds_prod_iff'.mp hn
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨U, hU, hpU, δ, hδ, fun q hq t ht => ?_⟩
  have htT : t ∈ T := hδT (by simpa only [Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs] using abs_lt.mpr ht)
  exact hTU (show (t, q) ∈ T ×ˢ U from ⟨htT, hq⟩)

/-- An intrinsic neighborhood has an open cotangent image lying in the
initial Hamiltonian ball. Every trajectory stays in the chosen base chart,
and its cotangent image agrees with the constructed Hamiltonian flow. -/
theorem exists_unitTangent_cotangentNeighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g),
      ∃ V : Set CotangentCoordinates,
      ∃ F : KineticLocalFlow g c (unitRadialCotangentState g c p),
        IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ unitRadialCotangentState g c p ∈ V ∧
        V = unitRadialCotangentState g c '' U ∧
        V ⊆ Metric.ball (unitRadialCotangentState g c p) F.radius ∧
        (∀ z ∈ V, z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) ∧
        (∀ q ∈ U, ∀ t ∈ Ioo (-F.time) F.time,
          (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace c).source) ∧
        (∀ q ∈ U, EqOn (fun t => F.map (unitRadialCotangentState g c q, t))
          (fun t => unitRadialCotangentState g c (unitTangentRadialFlow g o t q))
          (Ioo (-F.time) F.time)) := by
  obtain ⟨U₀, hU₀, hpU₀, F₀, hball, heq⟩ :=
    exists_unitTangent_localHamiltonian g o c p hp
  obtain ⟨U₁, hU₁, hpU₁, δ, hδ, hchart⟩ := radial_chart_neighborhood g o c p hp
  let τ := min F₀.time δ
  have hτ : 0 < τ := lt_min F₀.time_pos hδ
  let F := F₀.restrictTime τ hτ (min_le_left _ _)
  let U := U₀ ∩ U₁
  have htime {t : ℝ} (ht : t ∈ Ioo (-F.time) F.time) :
      t ∈ Ioo (-F₀.time) F₀.time ∧ t ∈ Ioo (-δ) δ := by
    have h0 : F.time ≤ F₀.time := min_le_left _ _
    have h1 : F.time ≤ δ := min_le_right _ _
    constructor <;> constructor <;> linarith [ht.1, ht.2]
  have hsource (q) (hq : q ∈ U) : q.2.base ∈ (chartAt FourSpace c).source := by
    have h := hchart q hq.2 0 (by constructor <;> linarith)
    change (unitTangentFlowMap g o (q.1.val * 0) q.2).base ∈ _ at h
    simpa only [mul_zero, unitTangentFlowMap_zero] using h
  let V := unitRadialCotangentState g c '' U
  refine ⟨U, V, F, hU₀.inter hU₁, ⟨hpU₀, hpU₁⟩,
    isOpen_unitRadialCotangentState_image g c U (hU₀.inter hU₁) hsource,
    ⟨p, ⟨hpU₀, hpU₁⟩, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨q, hq, rfl⟩
    exact hball q hq.1
  · rintro z ⟨q, hq, rfl⟩
    exact ⟨(chartAt FourSpace c).map_source (hsource q hq),
      unitCotangentState_momentum_ne_zero g c q.1.val q.1.property q.2 (hsource q hq)⟩
  · intro q hq t ht
    exact hchart q hq.2 t (htime ht).2
  · intro q hq t ht
    exact heq q hq.1 (htime ht).1

/-- Transporting the intrinsic neighborhood and transporting its cotangent
image give the same set. -/
theorem kinetic_radial_image (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p) (t : ℝ)
    (U : Set (PositiveRadius × UnitTangentBundle g))
    (heq : ∀ q ∈ U, F.map (unitRadialCotangentState g c q, t) =
      unitRadialCotangentState g c (unitTangentRadialFlow g o t q)) :
    (fun z => F.map (z, t)) '' (unitRadialCotangentState g c '' U) =
      unitRadialCotangentState g c '' (unitTangentRadialFlow g o t '' U) := by
  rw [image_image, image_image]
  exact image_congr heq

theorem isOpen_kinetic_radial_image (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p) (t : ℝ)
    (U : Set (PositiveRadius × UnitTangentBundle g)) (hU : IsOpen U)
    (hchart : ∀ q ∈ U, (unitTangentRadialFlow g o t q).2.base ∈
      (chartAt FourSpace c).source)
    (heq : ∀ q ∈ U, F.map (unitRadialCotangentState g c q, t) =
      unitRadialCotangentState g c (unitTangentRadialFlow g o t q)) :
    IsOpen ((fun z => F.map (z, t)) '' (unitRadialCotangentState g c '' U)) := by
  rw [kinetic_radial_image g o c F t U heq]
  apply isOpen_unitRadialCotangentState_image g c
  · exact (unitTangentRadialHomeomorph g o t).isOpenMap U hU
  · rintro q ⟨r, hr, rfl⟩
    exact hchart r hr

theorem kinetic_radial_image_subset_nonzero_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ)
    (U : Set (PositiveRadius × UnitTangentBundle g))
    (hchart : ∀ q ∈ U, (unitTangentRadialFlow g o t q).2.base ∈
      (chartAt FourSpace c).source)
    (heq : ∀ q ∈ U, F.map (unitRadialCotangentState g c q, t) =
      unitRadialCotangentState g c (unitTangentRadialFlow g o t q)) :
    (fun z => F.map (z, t)) '' (unitRadialCotangentState g c '' U) ⊆
      {z | z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0} := by
  rw [kinetic_radial_image g o c F t U heq]
  rintro z ⟨q, ⟨r, hr, rfl⟩, rfl⟩
  have hs := hchart r hr
  exact ⟨(chartAt FourSpace c).map_source hs,
    unitCotangentState_momentum_ne_zero g c r.1.val r.1.property
      (unitTangentRadialFlow g o t r).2 hs⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative of the actual radial exponential at the zero vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_chart_eventually_kinetic (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (F : KineticLocalFlow g c (chartAt FourSpace c e.base, 0))
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) (ht0 : 0 < t) :
    ∀ᶠ v in 𝓝 (0 : FourSpace),
      chartAt FourSpace c (frameExponential g o e (t • v)) =
        (F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)).1 := by
  obtain ⟨ε, hε, hradial⟩ := F.radial_endpoint_uniform g o c e he
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) hε] with v hv
  have hvε : ‖v‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  by_cases hv0 : v = 0
  · subst v
    simp only [smul_zero, frameExponential_zero, map_zero]
    exact (congrArg Prod.fst (F.zero_momentum_fixed g c _
      ((chartAt FourSpace c).map_source he) t ht)).symm
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv0⟩
    let q := (euclideanPolarHomeomorph w).1
    let r := (euclideanPolarHomeomorph w).2
    have hr : 0 < r.val := r.property
    have hrnorm : r.val = ‖v‖ := homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    have hvr : r.val • q.val = v := by
      have h := congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
      exact h
    have hexp : frameExponential g o e (t • v) =
        unitGeodesic g o (unitTangentTurn e q) (r.val * t) := by
      rw [← hvr, smul_smul]
      simpa only [mul_comm] using
        frameExponential_radial g o e q ⟨t * r.val, mul_pos ht0 hr⟩
    rw [hexp]
    have hh := congrArg Prod.fst (hradial q r.val hr (hrnorm ▸ hvε) t ht)
    rw [hvr] at hh
    exact hh.symm

omit [T2Space M] [CompactSpace M] in
/-- Raising the lowered initial vector cancels the metric. -/
theorem raise_frameMomentumMap (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      ((metricInChart g c (chartAt FourSpace c e.base))⁻¹)).comp (frameMomentumMap g c e) =
      (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap := by
  let G := metricInChart g c (chartAt FourSpace c e.base)
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.mpr
    (metricInChart_posDef g c _ ((chartAt FourSpace c).map_source he)).det_pos.ne'
  have hG : (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G⁻¹).comp
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G) =
      ContinuousLinearMap.id ℝ FourSpace := by
    change (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G⁻¹) *
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) G) = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
  rw [frameMomentumMap, ← ContinuousLinearMap.comp_assoc]
  rw [hG, ContinuousLinearMap.id_comp]

theorem frameExponential_chart_strictDerivative_rescaled (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (F : KineticLocalFlow g c (chartAt FourSpace c e.base, 0))
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) (ht0 : 0 < t) :
    HasStrictFDerivAt (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t • (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap) 0 := by
  let P := frameMomentumMap g c e
  have hF : HasStrictFDerivAt (fun p : FourSpace => (F.map ((chartAt FourSpace c e.base, p), t)).1)
      (t • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        ((metricInChart g c (chartAt FourSpace c e.base))⁻¹)) (P 0) := by
    simpa only [map_zero] using F.zero_momentum_endpoint_strictDerivative g c _
      ((chartAt FourSpace c).map_source he) t ht
  have hh := hF.comp 0 P.hasStrictFDerivAt
  have hD : (t • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      ((metricInChart g c (chartAt FourSpace c e.base))⁻¹)).comp P =
      t • (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap := by
    rw [ContinuousLinearMap.smul_comp, raise_frameMomentumMap g c e he]
  rw [hD] at hh
  exact hh.congr_of_eventuallyEq (Filter.EventuallyEq.symm
    (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0))

/-- The actual radial exponential has at zero exactly the initial frame map
in any fixed chart. -/
theorem frameExponential_chart_strictDerivative_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    HasStrictFDerivAt (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v))
      ((chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  let t := F.time / 2
  have ht0 : 0 < t := half_pos F.time_pos
  have ht : t ∈ Ioo (-F.time) F.time := by dsimp [t]; constructor <;> linarith [F.time_pos]
  let Q := (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap
  have hd := frameExponential_chart_strictDerivative_rescaled g o c e he F t ht ht0
  have hs : HasStrictFDerivAt (fun v : FourSpace => t⁻¹ • v)
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).hasStrictFDerivAt
  have hd' : HasStrictFDerivAt (fun v : FourSpace =>
      chartAt FourSpace c (frameExponential g o e (t • v))) (t • Q) (t⁻¹ • (0 : FourSpace)) := by
    simpa only [smul_zero] using hd
  have h := hd'.comp 0 hs
  have hf : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  have hD : (t • Q).comp (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) = Q := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
  change HasStrictFDerivAt (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v))))
    ((t • Q).comp (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace)) 0 at h
  rw [hf, hD] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Put the actual metric and density comparisons into the same
constant-density form. All estimates are on genuine chart measures. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

private theorem ofReal_sqrt_four (x : ℝ) (hx : 0 ≤ x) :
    (ENNReal.ofReal (Real.sqrt x)) ^ (4 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  congr 1
  calc
    Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 := by ring
    _ = x ^ 2 := by rw [Real.sq_sqrt hx]

private theorem ofReal_inv_sqrt_four (x : ℝ) (hx : 0 < x) :
    (ENNReal.ofReal (1 / Real.sqrt x)) ^ (4 : ℝ) = (ENNReal.ofReal (x ^ 2))⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hx),
    show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast, ← ENNReal.inv_pow]
  rw [← ENNReal.rpow_natCast _ 4]
  norm_num only [Nat.cast_ofNat]
  rw [ofReal_sqrt_four x hx.le]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem exists_chartHausdorff_constant_bounds (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∀ A : Set FourSpace, MeasurableSet A → A ⊆ U →
        chartHausdorffMeasure g c A ≤ ENNReal.ofReal ((1 + δ) ^ 2) *
          ((euclideanHausdorffFactor : ℝ≥0∞) *
            (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A)) ∧
        ENNReal.ofReal ((1 - δ) ^ 2) *
          ((euclideanHausdorffFactor : ℝ≥0∞) *
            (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A)) ≤
          chartHausdorffMeasure g c A := by
  obtain ⟨U, hU, hzU, hUt, hbound⟩ := exists_metricHausdorff_chart_bounds g c z₀ δ hδ hδone
  refine ⟨U, hU, hzU, hUt, ?_⟩
  intro A hA hAU
  have h := hbound A hAU
  rw [hausdorff_frozenFrame_symm_image] at h
  rw [ofReal_sqrt_four _ (by linarith), ofReal_inv_sqrt_four _ (by linarith)] at h
  rw [chartHausdorffMeasure_apply g c A hA (hAU.trans hUt)]
  refine ⟨h.1, ?_⟩
  have hq : ENNReal.ofReal ((1 - δ) ^ 2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (by linarith)))
  have hlow := mul_le_mul_right h.2 (ENNReal.ofReal ((1 - δ) ^ 2))
  have hcancel : ENNReal.ofReal ((1 - δ) ^ 2) *
      ((ENNReal.ofReal ((1 - δ) ^ 2))⁻¹ *
        metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A)) =
      metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hq ENNReal.ofReal_ne_top, one_mul]
  rw [hcancel] at hlow
  simpa only [mul_assoc] using hlow

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial canonical measure in actual cotangent coordinates. The only
technical geometric input is the exact normalized base-chart density; the
spherical factor and all fiber Jacobians follow from polar coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology ENNReal

noncomputable section

local instance radialChartSphereProbability : IsProbabilityMeasure sphereMeasure :=
  actual_sphereMeasure_probability

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartBaseDensity (g : SmoothMetric M) (c : M) : Measure (ChartTarget c) :=
  (chartCoordinateMeasure c).withDensity
    (fun z => ENNReal.ofReal (chartVolumeDensity g c z))

instance chartBaseDensity_sfinite (g : SmoothMetric M) (c : M) :
    SFinite (chartBaseDensity g c) := by
  unfold chartBaseDensity
  infer_instance

def gramChartUnitTangent (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × Directions) : UnitTangentBundle g :=
  unitTangentTurn (chartGramSection g c 1 (by simp) p.1) p.2

theorem continuous_gramChartUnitTangent (g : SmoothMetric M) (c : M) :
    Continuous (gramChartUnitTangent g c) :=
  continuous_unitTangentTurn.comp
    (((continuous_chartGramSection g c 1 (by simp)).comp continuous_fst).prodMk continuous_snd)

private theorem localGramSection_chart_inverse (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) :
    localGramSection g c 1 (by simp) ((chartAt FourSpace c).symm z.val) =
      chartGramSection g c 1 (by simp) z := by
  classical
  rw [localGramSection, dite_eq_left ((chartAt FourSpace c).map_target z.property)]
  apply congrArg (chartGramSection g c 1 (by simp))
  exact Subtype.ext ((chartAt FourSpace c).right_inv z.property)

private theorem chartGramFrame_map (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) (v : FourSpace) :
    (chartGramFrame g c 1 (by simp) z).map v =
      chartBackwardOperator c z.val
        (WithLp.toLp 2 (chartGramMatrix g c 1 z.val *ᵥ WithLp.ofLp v)) := by
  let e := chartGramFrame g c 1 (by simp) z
  have hvec (i : Fin 4) : e.map (coordinateVector i) = e.vector i := by
    ext j
    simp [OrthonormalFrame.map_apply, coordinateVector]
  have hv : (∑ i, v i • coordinateVector i) = v :=
    sum_coordinateVector (WithLp.ofLp v)
  calc
    e.map v = ∑ i, v i • e.vector i := by
      conv_lhs => rw [← hv]
      rw [map_sum]
      simp only [map_smul, hvec]
    _ = chartBackwardOperator c z.val
        (∑ i, v i • WithLp.toLp 2 (fun j => chartGramMatrix g c 1 z.val j i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      exact congrArg (fun w : FourSpace => v i • w)
        (chartGramFrame_vector g c 1 (by simp) z i)
    _ = _ := by
      congr 1
      ext j
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        smul_eq_mul, mulVec]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem gramChartUnitTangent_velocity (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) (q : Directions) :
    unitChartVelocity c (gramChartUnitTangent g c (z, q)) =
      WithLp.toLp 2 (chartGramMatrix g c 1 z.val *ᵥ WithLp.ofLp q.val) := by
  have hbase : (gramChartUnitTangent g c (z, q)).base =
      (chartAt FourSpace c).symm z.val := rfl
  have hvector : unitTangentVector (gramChartUnitTangent g c (z, q)) =
      (chartGramFrame g c 1 (by simp) z).map q.val :=
    (chartGramFrame g c 1 (by simp) z).turn_first q
  have hu : (gramChartUnitTangent g c (z, q)).base ∈ (chartAt FourSpace c).source := by
    rw [hbase]
    exact (chartAt FourSpace c).map_target z.property
  rw [unitChartVelocity_eq_derivative c _ hu, hbase, hvector,
    chartGramFrame_map]
  exact congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
    L (WithLp.toLp 2 (chartGramMatrix g c 1 z.val *ᵥ WithLp.ofLp q.val)))
    (chartForward_backward c z.val z.property)

def gramRadialLift (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × (Directions × PositiveRadius)) :
    PositiveRadius × UnitTangentBundle g :=
  (p.2.2, gramChartUnitTangent g c (p.1, p.2.1))

theorem continuous_gramRadialLift (g : SmoothMetric M) (c : M) :
    Continuous (gramRadialLift g c) :=
  (continuous_snd.comp continuous_snd).prodMk
    ((continuous_gramChartUnitTangent g c).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))

theorem gramRadialLift_cotangent (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × (Directions × PositiveRadius)) :
    unitRadialCotangentState g c (gramRadialLift g c p) =
      ((chartPolarLowering g c p).1.val, (chartPolarLowering g c p).2) := by
  have hz := (chartAt FourSpace c).right_inv p.1.property
  have hv := gramChartUnitTangent_velocity g c p.1 p.2.1
  change (chartAt FourSpace c ((chartAt FourSpace c).symm p.1.val),
    p.2.2.val • WithLp.toLp 2
      (metricInChart g c (chartAt FourSpace c ((chartAt FourSpace c).symm p.1.val)) *ᵥ
        WithLp.ofLp (unitChartVelocity c (gramChartUnitTangent g c (p.1, p.2.1))))) = _
  rw [hz, hv]
  apply Prod.ext
  · rfl
  change p.2.2.val • WithLp.toLp 2
      (metricInChart g c p.1.val *ᵥ
        (chartGramMatrix g c 1 p.1.val *ᵥ WithLp.ofLp p.2.1.val)) =
    WithLp.toLp 2 ((metricInChart g c p.1.val * chartGramMatrix g c 1 p.1.val) *ᵥ
      WithLp.ofLp (p.2.2.val • p.2.1.val))
  rw [WithLp.ofLp_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

private theorem canonicalUnitTangentMeasure_chartDensity (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (K : ℝ≥0∞)
    (hbase : (normalizedVolume g).restrict (chartAt FourSpace c).source =
      K • Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
        (chartBaseDensity g c)) :
    (canonicalUnitTangentMeasure g o).restrict
      {u | u.base ∈ (chartAt FourSpace c).source} =
      K • Measure.map (gramChartUnitTangent g c)
        ((chartBaseDensity g c).prod sphereMeasure) := by
  obtain ⟨s, hs, _hb, he⟩ := exists_measurable_gram_extension g o c
  let L : M × Directions → UnitTangentBundle g := fun p => unitTangentTurn (s p.1) p.2
  have hL : Measurable L := continuous_unitTangentTurn.measurable.comp
    ((hs.comp measurable_fst).prodMk measurable_snd)
  have hB : Measurable (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) :=
    ((chartAt FourSpace c).continuousOn_symm.comp_continuous continuous_subtype_val
      (fun z => z.property)).measurable
  have hsection : (canonicalUnitTangentMeasure g o).restrict
      {u | u.base ∈ (chartAt FourSpace c).source} =
      Measure.map L (((normalizedVolume g).restrict (chartAt FourSpace c).source).prod
        sphereMeasure) := by
    rw [canonicalUnitTangentMeasure_restrict_chart]
    apply Measure.map_congr
    have hmem : ∀ᵐ p : M × Directions ∂
        (((normalizedVolume g).restrict (chartAt FourSpace c).source).prod sphereMeasure),
        p.1 ∈ (chartAt FourSpace c).source := by
      apply (Measure.ae_prod_iff_ae_ae
        ((chartAt FourSpace c).open_source.measurableSet.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem (chartAt FourSpace c).open_source.measurableSet] with x hx
      exact Filter.Eventually.of_forall (fun _ => hx)
    filter_upwards [hmem] with p hp
    exact congrArg (fun e => unitTangentTurn e p.2) (he hp).symm
  rw [hsection, hbase, Measure.prod_smul_left,
    Measure.map_smul _ hL.aemeasurable]
  congr 1
  have hprod : (Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
      (chartBaseDensity g c)).prod sphereMeasure =
      Measure.map (Prod.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) id)
        ((chartBaseDensity g c).prod sphereMeasure) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (chartBaseDensity g c) sphereMeasure hB measurable_id)
  rw [hprod, Measure.map_map hL (hB.prodMap measurable_id)]
  apply congrArg (fun f => Measure.map f ((chartBaseDensity g c).prod sphereMeasure))
  funext p
  change unitTangentTurn (s ((chartAt FourSpace c).symm p.1.val)) p.2 = _
  rw [he ((chartAt FourSpace c).map_target p.1.property), localGramSection_chart_inverse]
  rfl

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
private theorem gramRadialLift_map (g : SmoothMetric M) (c : M) :
    Measure.map (gramRadialLift g c)
      ((chartBaseDensity g c).prod (sphereMeasure.prod (Measure.volumeIoiPow 3))) =
      (Measure.volumeIoiPow 3).prod
        (Measure.map (gramChartUnitTangent g c) ((chartBaseDensity g c).prod sphereMeasure)) := by
  let ν := chartBaseDensity g c
  let ρ := Measure.volumeIoiPow 3
  have hA := (measurePreserving_prodAssoc ν sphereMeasure ρ).symm
    MeasurableEquiv.prodAssoc
  have hC : MeasurePreserving Prod.swap ((ν.prod sphereMeasure).prod ρ)
      (ρ.prod (ν.prod sphereMeasure)) := Measure.measurePreserving_swap
  have hU : MeasurePreserving (gramChartUnitTangent g c) (ν.prod sphereMeasure)
      (Measure.map (gramChartUnitTangent g c) (ν.prod sphereMeasure)) :=
    ⟨(continuous_gramChartUnitTangent g c).measurable, rfl⟩
  have h := ((MeasurePreserving.id ρ).prod hU).comp (hC.comp hA)
  exact h.map_eq

private def measurableRadialState (g : SmoothMetric M) (c : M) :
    PositiveRadius × UnitTangentBundle g → CotangentCoordinates :=
  open Classical in
  {p | p.2.base ∈ (chartAt FourSpace c).source}.piecewise
    (unitRadialCotangentState g c) (fun _ => 0)

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
private theorem measurable_measurableRadialState (g : SmoothMetric M) (c : M) :
    Measurable (measurableRadialState g c) := by
  classical
  exact (unitRadialCotangentState_continuousOn g c).measurable_piecewise
    continuousOn_const (((chartAt FourSpace c).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet)

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [Nonempty M] in
private theorem cotangentCoordinateInclusion_map (c : M) :
    Measure.map (fun p : ChartTarget c × FourSpace => (p.1.val, p.2))
      ((chartCoordinateMeasure c).prod volume) =
      (volume : Measure CotangentCoordinates).restrict
        {p | p.1 ∈ (chartAt FourSpace c).target} := by
  have hS : MeasurePreserving (Subtype.val : ChartTarget c → FourSpace)
      (chartCoordinateMeasure c) (volume.restrict (chartAt FourSpace c).target) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet
      (volume : Measure FourSpace)
  have h := hS.prod (MeasurePreserving.id (volume : Measure FourSpace))
  change Measure.map _ _ = ((volume : Measure FourSpace).prod volume).restrict _
  have hset : {p : CotangentCoordinates | p.1 ∈ (chartAt FourSpace c).target} =
      (chartAt FourSpace c).target ×ˢ (univ : Set FourSpace) := by ext p; simp
  rw [hset]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  exact h.map_eq

/-- The normalization factor is the base density factor divided by the
actual Euclidean angular mass. No flow preservation is assumed. -/
theorem unitRadialCotangentState_map (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (K : ℝ≥0∞)
    (hbase : (normalizedVolume g).restrict (chartAt FourSpace c).source =
      K • Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
        (chartBaseDensity g c)) :
    Measure.map (unitRadialCotangentState g c)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        {p | p.2.base ∈ (chartAt FourSpace c).source}) =
      (K / polarAngularMass) • (volume : Measure CotangentCoordinates).restrict
        {p | p.1 ∈ (chartAt FourSpace c).target} := by
  classical
  let ν := (chartBaseDensity g c).prod (sphereMeasure.prod (Measure.volumeIoiPow 3))
  let D : Set (PositiveRadius × UnitTangentBundle g) :=
    {p | p.2.base ∈ (chartAt FourSpace c).source}
  let μ := ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict D
  have hD : MeasurableSet D := ((chartAt FourSpace c).open_source.preimage
    ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet
  have hμ : μ = K • Measure.map (gramRadialLift g c) ν := by
    have hDprod : D = univ ×ˢ {u | u.base ∈ (chartAt FourSpace c).source} := by
      ext p
      simp [D]
    dsimp [μ]
    rw [hDprod]
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      canonicalUnitTangentMeasure_chartDensity g o c K hbase, Measure.prod_smul_right,
      ← gramRadialLift_map]
  have hactual : Measure.map (unitRadialCotangentState g c) μ =
      Measure.map (measurableRadialState g c) μ := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hD] with p hp
    exact (piecewise_eq_of_mem D _ _ hp).symm
  let P := chartPolarLowering g c
  have hP : Measurable P := by
    apply (continuous_chartCotangentLowering g c).measurable.comp
    exact (continuous_fst.prodMk
      (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).smul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))).measurable
  have hpolar : Measure.map P ν = polarAngularMass⁻¹ •
      ((chartCoordinateMeasure c).prod (volume : Measure FourSpace)) := by
    have h := (chartPolarLowering_measurePreserving g c).map_eq
    rw [Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.map_smul _ hP.aemeasurable] at h
    have hi := congrArg (fun m : Measure (ChartTarget c × FourSpace) => polarAngularMass⁻¹ • m) h
    simpa only [ν, chartBaseDensity, smul_smul, ENNReal.inv_mul_cancel polarAngularMass_ne_zero
      polarAngularMass_ne_top, one_smul] using hi
  have hfun : measurableRadialState g c ∘ gramRadialLift g c =
      (fun p : ChartTarget c × FourSpace => (p.1.val, p.2)) ∘ P := by
    funext p
    rw [Function.comp_apply, measurableRadialState, piecewise_eq_of_mem]
    · exact gramRadialLift_cotangent g c p
    · exact (chartAt FourSpace c).map_target p.1.property
  have hI : Measurable (fun p : ChartTarget c × FourSpace => (p.1.val, p.2)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).measurable
  change Measure.map (unitRadialCotangentState g c) μ = _
  rw [hactual, hμ, Measure.map_smul _ (measurable_measurableRadialState g c).aemeasurable,
    Measure.map_map (measurable_measurableRadialState g c)
      (continuous_gramRadialLift g c).measurable, hfun,
    ← Measure.map_map hI hP, hpolar, Measure.map_smul _ hI.aemeasurable,
    cotangentCoordinateInclusion_map, smul_smul]
  rw [div_eq_mul_inv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact invariant radius slabs. A finite collection of the constructed
Hamiltonian charts provides one positive time valid throughout each slab. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def radialSlab (g : SmoothMetric M) (a b : ℝ) :
    Set (PositiveRadius × UnitTangentBundle g) :=
  {p | a ≤ p.1.val ∧ p.1.val ≤ b}

theorem isCompact_radialSlab (g : SmoothMetric M) (o : FrameOrientation g)
    {a b : ℝ} (ha : 0 < a) : IsCompact (radialSlab g a b) := by
  let : CompactSpace (UnitTangentBundle g) := compact_unitTangentBundle g o
  let f : Icc a b × UnitTangentBundle g → PositiveRadius × UnitTangentBundle g :=
    fun p => (⟨p.1.val, lt_of_lt_of_le ha p.1.property.1⟩, p.2)
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk
      (fun p => lt_of_lt_of_le ha p.1.property.1)).prodMk continuous_snd
  have heq : f '' univ = radialSlab g a b := by
    ext p
    constructor
    · rintro ⟨q, _, rfl⟩
      exact q.1.property
    · intro hp
      exact ⟨(⟨p.1.val, hp⟩, p.2), mem_univ _, rfl⟩
  rw [← heq]
  exact isCompact_univ.image hf

theorem unitTangentRadialFlow_mem_slab (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) (p : PositiveRadius × UnitTangentBundle g) :
    unitTangentRadialFlow g o t p ∈ radialSlab g a b ↔ p ∈ radialSlab g a b := Iff.rfl

/-- The restriction is the actual radial flow, with inverse negative time. -/
def unitTangentRadialSlabHomeomorph (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) : radialSlab g a b ≃ₜ radialSlab g a b where
  toFun p := ⟨unitTangentRadialFlow g o t p.val, p.property⟩
  invFun p := ⟨unitTangentRadialFlow g o (-t) p.val, p.property⟩
  left_inv p := Subtype.ext ((unitTangentRadialHomeomorph g o t).left_inv p.val)
  right_inv p := Subtype.ext ((unitTangentRadialHomeomorph g o t).right_inv p.val)
  continuous_toFun := ((unitTangentRadialFlow_continuous g o t).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((unitTangentRadialFlow_continuous g o (-t)).comp
    continuous_subtype_val).subtype_mk _

theorem unitTangentRadialSlabHomeomorph_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (a b : ℝ) (p : radialSlab g a b) :
    unitTangentRadialSlabHomeomorph g o a b 0 p = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change unitTangentFlowMap g o (p.val.1.val * 0) p.val.2 = p.val.2
    rw [mul_zero, unitTangentFlowMap_zero]

theorem unitTangentRadialSlabHomeomorph_add (g : SmoothMetric M) (o : FrameOrientation g)
    (a b s t : ℝ) (p : radialSlab g a b) :
    unitTangentRadialSlabHomeomorph g o a b (s + t) p =
      unitTangentRadialSlabHomeomorph g o a b s
        (unitTangentRadialSlabHomeomorph g o a b t p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change unitTangentFlowMap g o (p.val.1.val * (s + t)) p.val.2 =
      unitTangentFlowMap g o (p.val.1.val * s)
        (unitTangentFlowMap g o (p.val.1.val * t) p.val.2)
    rw [mul_add, unitTangentFlowMap_add]

/-- Data produced by the local Hamiltonian theorem, retaining the actual
coordinate map and the common interval of agreement with radial motion. -/
structure RadialHamiltonianChart (g : SmoothMetric M) (o : FrameOrientation g) where
  anchor : PositiveRadius × UnitTangentBundle g
  center : M
  domain : Set (PositiveRadius × UnitTangentBundle g)
  image : Set CotangentCoordinates
  flow : KineticLocalFlow g center (unitRadialCotangentState g center anchor)
  open_domain : IsOpen domain
  anchor_mem : anchor ∈ domain
  open_image : IsOpen image
  image_eq : image = unitRadialCotangentState g center '' domain
  image_subset_ball : image ⊆ Metric.ball (unitRadialCotangentState g center anchor) flow.radius
  image_in_chart : ∀ z ∈ image, z.1 ∈ (chartAt FourSpace center).target ∧ z.2 ≠ 0
  trajectory_in_chart : ∀ q ∈ domain, ∀ t ∈ Ioo (-flow.time) flow.time,
    (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace center).source
  conjugacy : ∀ q ∈ domain, EqOn
    (fun t => flow.map (unitRadialCotangentState g center q, t))
    (fun t => unitRadialCotangentState g center (unitTangentRadialFlow g o t q))
    (Ioo (-flow.time) flow.time)

theorem exists_radialHamiltonianChart (g : SmoothMetric M) (o : FrameOrientation g)
    (p : PositiveRadius × UnitTangentBundle g) :
    ∃ C : RadialHamiltonianChart g o, p ∈ C.domain := by
  obtain ⟨U, V, F, hU, hpU, hV, _hpV, hVU, hball, hin, hchart, heq⟩ :=
    exists_unitTangent_cotangentNeighborhood g o p.2.base p
      (mem_chart_source FourSpace p.2.base)
  exact ⟨{
    anchor := p
    center := p.2.base
    domain := U
    image := V
    flow := F
    open_domain := hU
    anchor_mem := hpU
    open_image := hV
    image_eq := hVU
    image_subset_ball := hball
    image_in_chart := hin
    trajectory_in_chart := hchart
    conjugacy := heq }, hpU⟩

private theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ ε > (0 : ℝ), ∀ i ∈ s, ε ≤ f i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _hf
    exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    intro hf
    obtain ⟨ε, hε, he⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) ε, lt_min (hf i (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (he j hj)

/-- A single positive time works in actual Hamiltonian charts around all
points of a compact radius slab. The centers and charts may vary pointwise. -/
theorem radialSlab_uniform_hamiltonian_time (g : SmoothMetric M) (o : FrameOrientation g)
    {a b : ℝ} (ha : 0 < a) :
    ∃ ε > (0 : ℝ), ∀ p ∈ radialSlab g a b,
      ∃ C : RadialHamiltonianChart g o, p ∈ C.domain ∧ ε ≤ C.flow.time := by
  classical
  choose C hC using exists_radialHamiltonianChart g o
  obtain ⟨s, hs⟩ := (isCompact_radialSlab g o ha).elim_finite_subcover
    (fun p => (C p).domain) (fun p => (C p).open_domain)
    (fun p _ => mem_iUnion.mpr ⟨p, hC p⟩)
  obtain ⟨ε, hε, he⟩ := finite_positive_lower_bound s
    (fun p => (C p).flow.time) (fun p _ => (C p).flow.time_pos)
  refine ⟨ε, hε, fun p hp => ?_⟩
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs hp)
  exact ⟨C q, hpq, he q hq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify metric Hausdorff measure in a chart from the proved sharp
metric comparison and the continuous density, using local measure gluing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

private theorem density_comparison_parameter (a : ℝ) (ha : 0 ≤ a) (haone : a < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      a * (1 + δ) ^ 2 ≤ 1 - δ ∧ a * (1 + δ) ≤ (1 - δ) ^ 2 := by
  let δ := (1 - a) / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ < 1 := by dsimp [δ]; linarith
  have heq : a = 1 - 8 * δ := by dsimp [δ]; ring
  refine ⟨δ, hδ, hδone, ?_, ?_⟩
  · rw [heq]
    nlinarith [sq_nonneg δ, mul_nonneg hδ.le (sq_nonneg δ)]
  · rw [heq]
    nlinarith [sq_nonneg δ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem chartHausdorffMeasure_eq_density (g : SmoothMetric M) (c : M) :
    (chartHausdorffMeasure g c).restrict (chartAt FourSpace c).target =
      (euclideanHausdorffFactor : ℝ≥0∞) •
        ((volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))).restrict
          (chartAt FourSpace c).target) := by
  let μ := chartHausdorffMeasure g c
  let C : ℝ≥0∞ := euclideanHausdorffFactor
  let D : Measure FourSpace := volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))
  let ν : Measure FourSpace := C • D
  have hlocal (a : ℝ≥0∞) (ha : a < 1) (z : FourSpace)
      (hz : z ∈ (chartAt FourSpace c).target) :
      ∃ U : Set FourSpace, IsOpen U ∧ z ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
        (a • μ).restrict U ≤ ν.restrict U ∧ (a • ν).restrict U ≤ μ.restrict U := by
    have hatop : a ≠ ⊤ := ne_top_of_lt ha
    have haReal : a.toReal < 1 := by
      exact (ENNReal.toReal_lt_toReal hatop (by simp)).mpr ha
    obtain ⟨δ, hδ, hδone, hc₁, hc₂⟩ :=
      density_comparison_parameter a.toReal ENNReal.toReal_nonneg haReal
    let z₀ : ChartTarget c := ⟨z, hz⟩
    obtain ⟨U₁, hU₁, hz₁, hUt₁, hM⟩ := exists_chartHausdorff_constant_bounds g c z₀ δ hδ hδone
    obtain ⟨U₂, hU₂, hz₂, _hUt₂, hD⟩ := exists_chartDensity_local_bounds g c z₀ δ hδ
    let U := U₁ ∩ U₂
    have hcE₁ : a * ENNReal.ofReal ((1 + δ) ^ 2) ≤ ENNReal.ofReal (1 - δ) := by
      rw [← ENNReal.ofReal_toReal hatop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal hc₁
    have hcE₂ : a * ENNReal.ofReal (1 + δ) ≤ ENNReal.ofReal ((1 - δ) ^ 2) := by
      rw [← ENNReal.ofReal_toReal hatop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal hc₂
    have hvalues (A : Set FourSpace) (hA : MeasurableSet A) (hAU : A ⊆ U) :
        a * μ A ≤ ν A ∧ a * ν A ≤ μ A := by
      let X : ℝ≥0∞ := C * (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A)
      have hm := hM A hA (fun x hx => (hAU hx).1)
      have hd := hD A hA (fun x hx => (hAU hx).2)
      have hdlo : ENNReal.ofReal (1 - δ) * X ≤ ν A := by
        calc
          _ = C * (ENNReal.ofReal ((1 - δ) * chartVolumeDensity g c z₀) * volume A) := by
            rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - δ)]
            dsimp [X]
            ac_rfl
          _ ≤ C * D A := mul_le_mul_right hd.1 C
          _ = ν A := rfl
      have hdhi : ν A ≤ ENNReal.ofReal (1 + δ) * X := by
        calc
          _ = C * D A := rfl
          _ ≤ C * (ENNReal.ofReal ((1 + δ) * chartVolumeDensity g c z₀) * volume A) :=
            mul_le_mul_right hd.2 C
          _ = _ := by
            rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + δ)]
            dsimp [X]
            ac_rfl
      constructor
      · calc
          a * μ A ≤ a * (ENNReal.ofReal ((1 + δ) ^ 2) * X) :=
            mul_le_mul_right hm.1 a
          _ = (a * ENNReal.ofReal ((1 + δ) ^ 2)) * X := (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal (1 - δ) * X := mul_le_mul_left hcE₁ X
          _ ≤ ν A := hdlo
      · calc
          a * ν A ≤ a * (ENNReal.ofReal (1 + δ) * X) := mul_le_mul_right hdhi a
          _ = (a * ENNReal.ofReal (1 + δ)) * X := (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal ((1 - δ) ^ 2) * X := mul_le_mul_left hcE₂ X
          _ ≤ μ A := hm.2
    refine ⟨U, hU₁.inter hU₂, ⟨hz₁, hz₂⟩, fun x hx => hUt₁ hx.1, ?_, ?_⟩
    · apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
      exact (hvalues (A ∩ U) (hA.inter (hU₁.inter hU₂).measurableSet) inter_subset_right).1
    · apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
      exact (hvalues (A ∩ U) (hA.inter (hU₁.inter hU₂).measurableSet) inter_subset_right).2
  have heq : μ.restrict (chartAt FourSpace c).target = ν.restrict (chartAt FourSpace c).target := by
    apply le_antisymm
    · apply measure_restrict_le_of_sharp_local_comparison μ ν _ (chartAt FourSpace c).open_target
      intro a ha z hz
      obtain ⟨U, hU, hzU, hUt, hm, _⟩ := hlocal a ha z hz
      exact ⟨U, hU, hzU, hUt, hm⟩
    · apply measure_restrict_le_of_sharp_local_comparison ν μ _ (chartAt FourSpace c).open_target
      intro a ha z hz
      obtain ⟨U, hU, hzU, hUt, _, hm⟩ := hlocal a ha z hz
      exact ⟨U, hU, hzU, hUt, hm⟩
  simpa only [ν, Measure.restrict_smul] using heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine local normal-coordinate chart for the constructed radial
exponential, obtained from its actual derivative at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem chartForwardOperator_center (x : M) :
    chartForwardOperator x x = ContinuousLinearMap.id ℝ FourSpace := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun K : TangentSpace I4 x →L[ℝ]
      TangentSpace I4 (extChartAt I4 x x) => K (show TangentSpace I4 x from v))
    (mfderiv_extChartAt_self (I := I4) (x := x))
  simp only [I4, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at h
  exact h

omit [T2Space M] [CompactSpace M] in
theorem frameMap_isUnit (g : SmoothMetric M) (e : FrameBundle g) :
    IsUnit e.frame.map.toContinuousLinearMap := by
  have hm : IsUnit e.frame.matrix :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero)
  have h := hm.map (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)).toMonoidHom
  change IsUnit (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) e.frame.matrix) at h
  have heq : e.frame.map.toContinuousLinearMap =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) e.frame.matrix := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rwa [heq]

variable [T3Space M]

/-- The actual exponential agrees on a neighborhood of zero with a local
homeomorphism onto a neighborhood of its base point. -/
theorem frameExponential_localChart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      0 ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  let L := e.frame.map.toContinuousLinearMap
  have hL : IsUnit L := frameMap_isUnit g e
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hf : HasStrictFDerivAt
      (fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v))
      (E : FourSpace →L[ℝ] FourSpace) 0 := by
    rw [hE]
    have h := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using h
  let C := hf.toOpenPartialHomeomorph _
  let U := (frameExponential g o e) ⁻¹' (chartAt FourSpace e.base).source
  have hU : IsOpen U := (chartAt FourSpace e.base).open_source.preimage
    (frameExponential_continuous g o e)
  let D := (C.trans (chartAt FourSpace e.base).symm).restrOpen U hU
  have hzero : (0 : FourSpace) ∈ U := by
    change frameExponential g o e 0 ∈ (chartAt FourSpace e.base).source
    rw [frameExponential_zero]
    exact mem_chart_source FourSpace e.base
  refine ⟨D, ?_, ?_⟩
  · change 0 ∈ (C.trans (chartAt FourSpace e.base).symm).source ∩ U
    refine ⟨⟨hf.mem_toOpenPartialHomeomorph_source, ?_⟩, hzero⟩
    change chartAt FourSpace e.base (frameExponential g o e 0) ∈
      (chartAt FourSpace e.base).target
    exact (chartAt FourSpace e.base).map_source hzero
  · intro v hv
    have hvU : v ∈ U := hv.2
    change (chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base (frameExponential g o e v)) = frameExponential g o e v
    exact (chartAt FourSpace e.base).left_inv hvU

end
end PositiveEinsteinFour.Geometry
end


section

/-! Measurable extensions of the actual radial cotangent chart and its
inverse. The extensions agree with the homeomorphism on its genuine domain;
the arbitrary value outside that domain is used only for measurability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def radialCotangentStateExtension (g : SmoothMetric M) (c : M) :
    PositiveRadius × UnitTangentBundle g → CotangentCoordinates :=
  open Classical in
  {p | p.2.base ∈ (chartAt FourSpace c).source}.piecewise
    (unitRadialCotangentState g c) (fun _ => 0)

theorem radialCotangentStateExtension_eq (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    radialCotangentStateExtension g c p = unitRadialCotangentState g c p := by
  classical
  exact piecewise_eq_of_mem _ _ _ hp

def cotangentRadialInverseOn (g : SmoothMetric M) (c : M)
    (z : NonzeroCotangentChart c) : PositiveRadius × UnitTangentBundle g :=
  let p := (unitTangentCotangentHomeomorph g c).symm z
  (p.1, p.2.val)

theorem continuous_cotangentRadialInverseOn (g : SmoothMetric M) (c : M) :
    Continuous (cotangentRadialInverseOn g c) :=
  ((unitTangentCotangentHomeomorph g c).symm.continuous.fst).prodMk
    (continuous_subtype_val.comp
      (unitTangentCotangentHomeomorph g c).symm.continuous.snd)

def cotangentRadialRetraction (g : SmoothMetric M) (c : M) :
    CotangentCoordinates → PositiveRadius × UnitTangentBundle g :=
  Function.extend (Subtype.val : NonzeroCotangentChart c → CotangentCoordinates)
    (cotangentRadialInverseOn g c)
    (fun _ => (⟨1, by norm_num⟩, unitTangentOfFrame (frameAt g c)))

theorem cotangentRadialRetraction_on (g : SmoothMetric M) (c : M)
    (z : NonzeroCotangentChart c) :
    cotangentRadialRetraction g c z.val = cotangentRadialInverseOn g c z := by
  exact Subtype.val_injective.extend_apply _ _ z

theorem cotangentRadialRetraction_source (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    (cotangentRadialRetraction g c z).2.base ∈ (chartAt FourSpace c).source := by
  rw [cotangentRadialRetraction_on g c (⟨z, hz⟩ : NonzeroCotangentChart c)]
  exact ((unitTangentCotangentHomeomorph g c).symm
    (⟨z, hz⟩ : NonzeroCotangentChart c)).2.property

/-- The measurable inverse recovers the original intrinsic radial state. -/
theorem cotangentRadialRetraction_state (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    cotangentRadialRetraction g c (unitRadialCotangentState g c p) = p := by
  let a : PositiveRadius × ChartUnitTangent g c := (p.1, ⟨p.2, hp⟩)
  let H := unitTangentCotangentHomeomorph g c
  calc
    cotangentRadialRetraction g c (unitRadialCotangentState g c p) =
        cotangentRadialInverseOn g c (H a) :=
      cotangentRadialRetraction_on g c (H a)
    _ = p := by
      change ((H.symm (H a)).1, (H.symm (H a)).2.val) = p
      rw [H.symm_apply_apply]

theorem cotangentRadialRetraction_extension (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    cotangentRadialRetraction g c (radialCotangentStateExtension g c p) = p := by
  rw [radialCotangentStateExtension_eq g c p hp]
  exact cotangentRadialRetraction_state g c p hp

/-- On the nonzero cotangent chart, the extension's inverse is also a right inverse. -/
theorem unitRadialCotangentState_retraction (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    unitRadialCotangentState g c (cotangentRadialRetraction g c z) = z := by
  let q : NonzeroCotangentChart c := ⟨z, hz⟩
  let H := unitTangentCotangentHomeomorph g c
  rw [cotangentRadialRetraction_on g c q]
  exact congrArg Subtype.val (H.apply_symm_apply q)

theorem radialCotangentStateExtension_retraction (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    radialCotangentStateExtension g c (cotangentRadialRetraction g c z) = z := by
  rw [radialCotangentStateExtension_eq g c _ (cotangentRadialRetraction_source g c z hz)]
  exact unitRadialCotangentState_retraction g c z hz

variable [CompactSpace M]

theorem measurable_radialCotangentStateExtension (g : SmoothMetric M) (c : M) :
    Measurable (radialCotangentStateExtension g c) := by
  classical
  exact (unitRadialCotangentState_continuousOn g c).measurable_piecewise
    continuousOn_const (((chartAt FourSpace c).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet)

theorem measurable_cotangentRadialRetraction (g : SmoothMetric M) (c : M) :
    Measurable (cotangentRadialRetraction g c) := by
  apply (MeasurableEmbedding.subtype_coe (s := {z : CotangentCoordinates |
    z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0})
      (((chartAt FourSpace c).open_target.preimage continuous_fst).inter
        (isOpen_compl_singleton.preimage continuous_snd)).measurableSet).measurable_extend
  · exact (continuous_cotangentRadialInverseOn g c).measurable
  · exact measurable_const

end
end PositiveEinsteinFour.Geometry
end


section

/-! Technical measure reductions for the actual radial flow. Local image
identities on a compact slab give every time on that slab; a countable
exhaustion then gives the ambient measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem isClosed_radialSlab (g : SmoothMetric M) (a b : ℝ) :
    IsClosed (radialSlab g a b) :=
  isClosed_Icc.preimage (continuous_subtype_val.comp continuous_fst)

theorem unitTangentRadialFlow_preimage_slab (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) :
    unitTangentRadialFlow g o t ⁻¹' radialSlab g a b = radialSlab g a b := rfl

theorem unitTangentRadialFlow_image_slab (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) :
    unitTangentRadialFlow g o t '' radialSlab g a b = radialSlab g a b := by
  change unitTangentRadialHomeomorph g o t '' radialSlab g a b = _
  rw [(unitTangentRadialHomeomorph g o t).image_eq_preimage_symm]
  rfl

theorem unitTangentRadialFlow_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (p : PositiveRadius × UnitTangentBundle g) : unitTangentRadialFlow g o 0 p = p := by
  apply Prod.ext
  · rfl
  · change unitTangentFlowMap g o (p.1.val * 0) p.2 = p.2
    rw [mul_zero, unitTangentFlowMap_zero]

theorem unitTangentRadialFlow_add (g : SmoothMetric M) (o : FrameOrientation g)
    (s t : ℝ) (p : PositiveRadius × UnitTangentBundle g) :
    unitTangentRadialFlow g o (s + t) p =
      unitTangentRadialFlow g o s (unitTangentRadialFlow g o t p) := by
  apply Prod.ext
  · rfl
  · change unitTangentFlowMap g o (p.1.val * (s + t)) p.2 =
      unitTangentFlowMap g o (p.1.val * s)
        (unitTangentFlowMap g o (p.1.val * t) p.2)
    rw [mul_add, unitTangentFlowMap_add]

/-- A local ambient image identity restricts to the invariant slab. -/
theorem radialSlab_restrict_local_image (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (a b t : ℝ)
    (U : Set (PositiveRadius × UnitTangentBundle g))
    (hlocal : Measure.map (unitTangentRadialFlow g o t) (μ.restrict U) =
      μ.restrict (unitTangentRadialFlow g o t '' U)) :
    Measure.map (unitTangentRadialFlow g o t) ((μ.restrict (radialSlab g a b)).restrict U) =
      (μ.restrict (radialSlab g a b)).restrict (unitTangentRadialFlow g o t '' U) := by
  have hS := (isClosed_radialSlab g a b).measurableSet
  have hf := (unitTangentRadialFlow_continuous g o t).measurable
  calc
    _ = Measure.map (unitTangentRadialFlow g o t)
        ((μ.restrict U).restrict (radialSlab g a b)) :=
      congrArg (Measure.map (unitTangentRadialFlow g o t)) (Measure.restrict_comm hS).symm
    _ = (Measure.map (unitTangentRadialFlow g o t) (μ.restrict U)).restrict
        (radialSlab g a b) := by
      rw [Measure.restrict_map hf hS, unitTangentRadialFlow_preimage_slab]
    _ = (μ.restrict (unitTangentRadialFlow g o t '' U)).restrict (radialSlab g a b) := by
      rw [hlocal]
    _ = _ := Measure.restrict_comm hS

/-- It suffices to supply ambient local image identities at points of the
slab. Outside it, both restricted measures vanish. -/
theorem radialSlab_preserves_of_local_image (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (a b t : ℝ)
    (hlocal : ∀ p ∈ radialSlab g a b,
      ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
        Measure.map (unitTangentRadialFlow g o t) (μ.restrict U) =
          μ.restrict (unitTangentRadialFlow g o t '' U)) :
    MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b)) := by
  apply measurePreserving_of_local_image (unitTangentRadialHomeomorph g o t)
  intro p
  by_cases hp : p ∈ radialSlab g a b
  · obtain ⟨U, hU, hpU, hm⟩ := hlocal p hp
    exact ⟨U, hU, hpU, radialSlab_restrict_local_image g o μ a b t U hm⟩
  · have hS := (isClosed_radialSlab g a b).measurableSet
    refine ⟨(radialSlab g a b)ᶜ, (isClosed_radialSlab g a b).isOpen_compl, hp, ?_⟩
    have himage : unitTangentRadialFlow g o t '' (radialSlab g a b)ᶜ =
        (radialSlab g a b)ᶜ := by
      change unitTangentRadialHomeomorph g o t '' (radialSlab g a b)ᶜ = _
      rw [image_compl_eq (unitTangentRadialHomeomorph g o t).bijective]
      change (unitTangentRadialFlow g o t '' radialSlab g a b)ᶜ = _
      rw [unitTangentRadialFlow_image_slab]
    change Measure.map (unitTangentRadialFlow g o t)
        ((μ.restrict (radialSlab g a b)).restrict (radialSlab g a b)ᶜ) =
      (μ.restrict (radialSlab g a b)).restrict
        (unitTangentRadialFlow g o t '' (radialSlab g a b)ᶜ)
    rw [himage, Measure.restrict_restrict hS.compl, compl_inter_self,
      Measure.restrict_empty, Measure.map_zero]

/-- The group law turns a neighborhood of preserving times into all times,
for the measure restricted to one invariant slab. -/
theorem radialSlab_preserves_of_near_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (a b ε : ℝ) (hε : 0 < ε)
    (hnear : ∀ t ∈ Ioo (-ε) ε, MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b))) (t : ℝ) :
    MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hnzero : (n : ℝ) ≠ 0 := hnpos.ne'
  let s : ℝ := t / n
  have hs : |s| < ε := by
    dsimp [s]
    rw [abs_div, abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hstep := hnear s (abs_lt.mp hs)
  have hmul (m : ℕ) : MeasurePreserving (unitTangentRadialFlow g o ((m : ℝ) * s))
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b)) := by
    induction m with
    | zero =>
      have hzero : unitTangentRadialFlow g o 0 = id :=
        funext (unitTangentRadialFlow_zero g o)
      simpa only [Nat.cast_zero, zero_mul, hzero] using
        MeasurePreserving.id (μ.restrict (radialSlab g a b))
    | succ m ih =>
      have h := ih.comp hstep
      convert h using 1
      funext p
      rw [Nat.cast_succ, add_mul, one_mul, unitTangentRadialFlow_add]
      rfl
  have heq : (n : ℝ) * s = t := by dsimp [s]; field_simp [hnzero]
  simpa only [heq] using hmul n

def exhaustingRadialSlab (g : SmoothMetric M) (n : ℕ) :
    Set (PositiveRadius × UnitTangentBundle g) :=
  radialSlab g (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)

omit [T2Space M] [CompactSpace M] in
theorem iUnion_exhaustingRadialSlab (g : SmoothMetric M) :
    (⋃ n, exhaustingRadialSlab g n) = univ := by
  apply univ_subset_iff.mp
  intro p _
  obtain ⟨n, hn⟩ := exists_nat_gt (max p.1.val (p.1.val)⁻¹)
  have hu : p.1.val < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hl : (p.1.val)⁻¹ < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hp : 0 < p.1.val := p.1.property
  have hmul : 1 < (n : ℝ) * p.1.val :=
    (div_lt_iff₀ hp).mp (by simpa only [one_div] using hl)
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  change 1 / ((n : ℝ) + 1) ≤ p.1.val ∧ p.1.val ≤ (n : ℝ) + 1
  constructor
  · apply (div_le_iff₀ hnpos).mpr
    nlinarith
  · linarith

/-- Preservation on the countable family of slabs determines preservation
of the whole radial measure, without a finiteness hypothesis. -/
theorem unitTangentRadial_preserves_of_slabs (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (t : ℝ)
    (hslabs : ∀ n, MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (exhaustingRadialSlab g n)) (μ.restrict (exhaustingRadialSlab g n))) :
    MeasurePreserving (unitTangentRadialFlow g o t) μ μ := by
  have hf := (unitTangentRadialFlow_continuous g o t).measurable
  refine ⟨hf, Measure.ext_of_iUnion_eq_univ (iUnion_exhaustingRadialSlab g) ?_⟩
  intro n
  change (Measure.map (unitTangentRadialFlow g o t) μ).restrict
      (radialSlab g (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) =
    μ.restrict (radialSlab g (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1))
  rw [Measure.restrict_map hf (isClosed_radialSlab g _ _).measurableSet,
    unitTangentRadialFlow_preimage_slab]
  exact (hslabs n).map_eq

/-- Final technical reduction: uniform small-time local image identities
on each compact slab suffice for ambient radial preservation at every time. -/
theorem unitTangentRadial_preserves_of_slab_local_images
    (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g))
    (hlocal : ∀ n, ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε,
      ∀ p ∈ exhaustingRadialSlab g n,
        ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
          Measure.map (unitTangentRadialFlow g o t) (μ.restrict U) =
            μ.restrict (unitTangentRadialFlow g o t '' U)) (t : ℝ) :
    MeasurePreserving (unitTangentRadialFlow g o t) μ μ := by
  apply unitTangentRadial_preserves_of_slabs g o μ t
  intro n
  obtain ⟨ε, hε, hnear⟩ := hlocal n
  apply radialSlab_preserves_of_near_zero g o μ _ _ ε hε ?_ t
  intro s hs
  exact radialSlab_preserves_of_local_image g o μ _ _ s (hnear s hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruct the actual base measure from its proved chart density.
The last identity is the normalized base input for the cotangent product. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem continuous_chartInverse_restrict (c : M) :
    Continuous (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((chartAt FourSpace c).symm.continuousAt z.property).comp
    continuous_subtype_val.continuousAt

theorem metricHausdorffMeasure_restrict_chart (g : SmoothMetric M) (c : M) :
    (metricHausdorffMeasure g).restrict (chartAt FourSpace c).source =
      (euclideanHausdorffFactor : ℝ≥0∞) •
        Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
          ((chartCoordinateMeasure c).withDensity
            (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  let φ : ChartTarget c → M := fun z => (chartAt FourSpace c).symm z.val
  have hφ : Measurable φ := (continuous_chartInverse_restrict c).measurable
  ext A hA
  let B : Set FourSpace := Subtype.val '' (φ ⁻¹' A)
  have hB : MeasurableSet B :=
    (MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet).measurableSet_image'
      (hφ hA)
  have hBt : B ⊆ (chartAt FourSpace c).target := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hBA : (chartAt FourSpace c).symm '' B = A ∩ (chartAt FourSpace c).source := by
    ext x
    constructor
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨hq, (chartAt FourSpace c).map_target q.property⟩
    · rintro ⟨hxA, hxs⟩
      refine ⟨chartAt FourSpace c x, ?_, (chartAt FourSpace c).left_inv hxs⟩
      refine ⟨⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source hxs⟩, ?_, rfl⟩
      change (chartAt FourSpace c).symm (chartAt FourSpace c x) ∈ A
      rwa [(chartAt FourSpace c).left_inv hxs]
  have hchart := congrArg (fun μ : Measure FourSpace => μ B)
    (chartHausdorffMeasure_eq_density g c)
  simp only [Measure.restrict_apply hB, inter_eq_left.mpr hBt,
    Measure.smul_apply, smul_eq_mul] at hchart
  rw [chartHausdorffMeasure_apply g c B hB hBt, hBA] at hchart
  have hdensity : ((chartCoordinateMeasure c).withDensity
      (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) (φ ⁻¹' A) =
      (volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) B := by
    rw [withDensity_apply _ (hφ hA), withDensity_apply _ hB]
    exact setLIntegral_subtype (chartAt FourSpace c).open_target.measurableSet
      (φ ⁻¹' A) (fun z => ENNReal.ofReal (chartVolumeDensity g c z))
  rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hφ hA, hdensity]
  exact hchart

def riemannianChartFactor : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi ^ 2 / 32) * (euclideanHausdorffFactor : ℝ≥0∞)

theorem volumeMeasure_restrict_chart (g : SmoothMetric M) (c : M) :
    (volumeMeasure g).restrict (chartAt FourSpace c).source =
      riemannianChartFactor •
        Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
          ((chartCoordinateMeasure c).withDensity
            (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  rw [volumeMeasure_eq_scaled_hausdorff, Measure.restrict_smul,
    metricHausdorffMeasure_restrict_chart, smul_smul]
  rfl

def normalizedChartFactor (g : SmoothMetric M) : ℝ≥0∞ :=
  (volumeMeasure g univ)⁻¹ * riemannianChartFactor

theorem normalizedVolume_restrict_chart (g : SmoothMetric M) (c : M) :
    (normalizedVolume g).restrict (chartAt FourSpace c).source =
      normalizedChartFactor g •
        Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
          ((chartCoordinateMeasure c).withDensity
            (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  rw [normalizedVolume, Measure.restrict_smul, volumeMeasure_restrict_chart, smul_smul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth coordinate changes for the actual cotangent states used by the
radial geodesic flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def cotangentChartTransition (g : SmoothMetric M) (c d : M)
    (p : CotangentCoordinates) : CotangentCoordinates :=
  (chartTransition c d p.1,
    WithLp.toLp 2 (metricInChart g d (chartTransition c d p.1) *ᵥ
      (chartTransitionMatrix c d p.1 *ᵥ
        ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2))))

theorem cotangentChartTransition_contDiffAt (g : SmoothMetric M) (c d : M)
    (p : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm p.1 ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (cotangentChartTransition g c d) p := by
  have hφ : ContDiffAt ℝ ∞ (fun q : CotangentCoordinates => chartTransition c d q.1) p :=
    (chartTransition_contDiffAt c d p.1 hp hd).comp p contDiffAt_fst
  have hout : chartTransition c d p.1 ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hd
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => metricInChart g d (chartTransition c d q.1) i j) p :=
    by
      have hOuter : ContDiffAt ℝ ∞ (fun z : FourSpace => metricInChart g d z i j)
          (chartTransition c d p.1) := metricInChart_contDiffAt g d _ hout i j
      exact hOuter.comp p hφ
  have hD (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => chartTransitionMatrix c d q.1 i j) p :=
    (chartTransitionMatrix_contDiffAt c d p.1 hp hd i j).comp p contDiffAt_fst
  have hInv (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : CotangentCoordinates => (metricInChart g c q.1)⁻¹ i j) p :=
    (metricInChart_inv_contDiffAt g c p.1 hp
      (metricInChart_posDef g c p.1 hp).det_pos.ne' i j).comp p contDiffAt_fst
  have hP (i : Fin 4) : ContDiffAt ℝ ∞ (fun q : CotangentCoordinates => q.2 i) p := by
    fun_prop
  apply hφ.prodMk
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℝ ∞ (fun q : CotangentCoordinates =>
    ∑ j, metricInChart g d (chartTransition c d q.1) i j *
      ∑ k, chartTransitionMatrix c d q.1 j k *
        ∑ l, (metricInChart g c q.1)⁻¹ k l * q.2 l) p
  apply ContDiffAt.sum
  intro j _
  apply (hG i j).mul
  apply ContDiffAt.sum
  intro k _
  apply (hD j k).mul
  exact ContDiffAt.sum (fun l _ => (hInv k l).mul (hP l))

theorem unitChartVelocity_change (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (u : UnitTangentBundle g)
    (hc : u.base ∈ (chartAt FourSpace c).source)
    (hd : u.base ∈ (chartAt FourSpace d).source) :
    unitChartVelocity d u = WithLp.toLp 2
      (chartTransitionMatrix c d (chartAt FourSpace c u.base) *ᵥ
        WithLp.ofLp (unitChartVelocity c u)) := by
  obtain ⟨e, _he, hue⟩ := exists_positive_unitTangent_frame g o u
  have hb : e.base = u.base := congrArg UnitTangentBundle.base hue
  have hce : e.base ∈ (chartAt FourSpace c).source := by rwa [hb]
  have hde : e.base ∈ (chartAt FourSpace d).source := by rwa [hb]
  have hm := frameChartMatrix_change g c d e hce hde
  rw [← hue]
  change WithLp.toLp 2 (fun i => frameChartMatrix g d e i 0) =
    WithLp.toLp 2 (chartTransitionMatrix c d (chartAt FourSpace c e.base) *ᵥ
      (fun i => frameChartMatrix g c e i 0))
  ext i
  exact (congrFun (congrFun hm i) 0).symm

theorem cotangentChartTransition_unitState (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (r : ℝ) (u : UnitTangentBundle g)
    (hc : u.base ∈ (chartAt FourSpace c).source)
    (hd : u.base ∈ (chartAt FourSpace d).source) :
    cotangentChartTransition g c d (unitCotangentState g c r u) =
      unitCotangentState g d r u := by
  have hφ : chartTransition c d (chartAt FourSpace c u.base) = chartAt FourSpace d u.base := by
    rw [chartTransition, (chartAt FourSpace c).left_inv hc]
  have hv : chartTransitionMatrix c d (chartAt FourSpace c u.base) *ᵥ
      WithLp.ofLp (unitChartVelocity c u) = WithLp.ofLp (unitChartVelocity d u) := by
    exact congrArg WithLp.ofLp (unitChartVelocity_change g o c d u hc hd).symm
  have hraise := congrArg WithLp.ofLp (raisedChartVelocity_unitCotangentState g c r u hc)
  apply Prod.ext
  · exact hφ
  · change WithLp.toLp 2
        (metricInChart g d (chartTransition c d (chartAt FourSpace c u.base)) *ᵥ
          (chartTransitionMatrix c d (chartAt FourSpace c u.base) *ᵥ
            WithLp.ofLp (raisedChartVelocity g c (unitCotangentState g c r u)))) = _
    rw [hraise, WithLp.ofLp_smul, Matrix.mulVec_smul, hv, hφ, Matrix.mulVec_smul]
    rfl

theorem cotangentChartTransition_radialState (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : p.2.base ∈ (chartAt FourSpace d).source) :
    cotangentChartTransition g c d (unitRadialCotangentState g c p) =
      unitRadialCotangentState g d p :=
  cotangentChartTransition_unitState g o c d p.1.val p.2 hc hd

theorem cotangentChartTransition_retraction (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0)
    (hd : (cotangentRadialRetraction g c z).2.base ∈ (chartAt FourSpace d).source) :
    cotangentChartTransition g c d z =
      unitRadialCotangentState g d (cotangentRadialRetraction g c z) := by
  have h := cotangentChartTransition_radialState g o c d (cotangentRadialRetraction g c z)
    (cotangentRadialRetraction_source g c z hz) hd
  rwa [unitRadialCotangentState_retraction g c z hz] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial canonical measure in cotangent coordinates, with the base
chart identity derived from the metric Hausdorff measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actual_unitRadialCotangentState_map (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) :
    Measure.map (unitRadialCotangentState g c)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        {p | p.2.base ∈ (chartAt FourSpace c).source}) =
      (normalizedChartFactor g / polarAngularMass) •
        (volume : Measure CotangentCoordinates).restrict
          {p | p.1 ∈ (chartAt FourSpace c).target} := by
  apply unitRadialCotangentState_map g o c
  simpa only [chartBaseDensity] using normalizedVolume_restrict_chart g c

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Riemannian volume, evaluated on a measurable
set in one chart. This is the target measure for the weighted area bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem chart_image_measurable (c : M) (A : Set M) (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt FourSpace c).source) :
    MeasurableSet ((chartAt FourSpace c) '' A) := by
  let C := chartAt FourSpace c
  let H := C.toHomeomorphSourceTarget
  have hA' : MeasurableSet ((Subtype.val : C.source → M) ⁻¹' A) :=
    measurable_subtype_coe hA
  have hB' := H.toMeasurableEquiv.measurableSet_image.mpr hA'
  have hB := (MeasurableEmbedding.subtype_coe C.open_target.measurableSet).measurableSet_image' hB'
  convert hB using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨H ⟨x, hAc hx⟩, ⟨⟨x, hAc hx⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.val, hx, rfl⟩

theorem volumeMeasure_chart_image (g : SmoothMetric M) (c : M)
    (A : Set M) (hA : MeasurableSet A) (hAc : A ⊆ (chartAt FourSpace c).source) :
    volumeMeasure g A = riemannianChartFactor *
      ∫⁻ z in (chartAt FourSpace c) '' A, ENNReal.ofReal (chartVolumeDensity g c z) := by
  let B := (chartAt FourSpace c) '' A
  have hB : MeasurableSet B := chart_image_measurable c A hA hAc
  have hBt : B ⊆ (chartAt FourSpace c).target := by
    rintro z ⟨x, hx, rfl⟩
    exact (chartAt FourSpace c).map_source (hAc hx)
  have hback : (chartAt FourSpace c).symm '' B = A := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      rwa [(chartAt FourSpace c).left_inv (hAc hy)]
    · intro hx
      exact ⟨chartAt FourSpace c x, ⟨x, hx, rfl⟩, (chartAt FourSpace c).left_inv (hAc hx)⟩
  have h := congrArg (fun μ : Measure FourSpace => μ B) (chartHausdorffMeasure_eq_density g c)
  simp only [Measure.restrict_apply hB, inter_eq_left.mpr hBt,
    Measure.smul_apply, smul_eq_mul] at h
  rw [chartHausdorffMeasure_apply g c B hB hBt, hback, withDensity_apply _ hB] at h
  rw [volumeMeasure_eq_scaled_hausdorff, Measure.smul_apply, smul_eq_mul, h]
  exact (mul_assoc _ _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp upper normalization needed by the polar volume estimate.
Arbitrarily fine ball covers with nearly optimal total Lebesgue measure
bound the unnormalized fourth Hausdorff measure. Only the upper bound is
needed; no isodiametric inequality or equality case is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal _root_.Topology

noncomputable section

theorem fourSpace_volume_ball (x : FourSpace) (r : ℝ) :
    volume (ball x r) = ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  simpa [FourSpace] using
    InnerProductSpace.volume_ball_of_dim_even (E := FourSpace) (k := 2) (by simp [FourSpace]) x r

theorem fourSpace_volume_closedBall (x : FourSpace) (r : ℝ) :
    volume (closedBall x r) = ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  simpa [FourSpace] using
    InnerProductSpace.volume_closedBall_of_dim_even (E := FourSpace) (k := 2)
      (by simp [FourSpace]) x r

private theorem ball_normalization_product :
    ENNReal.ofReal (32 / Real.pi ^ 2) * ENNReal.ofReal (Real.pi ^ 2 / 2) = 16 := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : (32 / Real.pi ^ 2) * (Real.pi ^ 2 / 2) = 16 := by field_simp; ring
  rw [h]
  norm_num

private theorem fourSpace_ediam_closedBall_le (x : FourSpace) {r : ℝ} (hr : 0 ≤ r) :
    Metric.ediam (closedBall x r) ≤ 2 * ENNReal.ofReal r := by
  rw [← Metric.closedEBall_ofReal hr]
  exact Metric.ediam_closedEBall_le

private theorem fourSpace_ball_cost (x : FourSpace) {r : ℝ} (hr : 0 ≤ r) :
    Metric.ediam (closedBall x r) ^ (4 : ℝ) ≤
      ENNReal.ofReal (32 / Real.pi ^ 2) * volume (closedBall x r) := by
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
  calc
    Metric.ediam (closedBall x r) ^ 4 ≤ (2 * ENNReal.ofReal r) ^ 4 :=
      pow_le_pow_left₀ zero_le (fourSpace_ediam_closedBall_le x hr) 4
    _ = 16 * ENNReal.ofReal r ^ 4 := by rw [mul_pow]; norm_num
    _ = ENNReal.ofReal (32 / Real.pi ^ 2) * volume (closedBall x r) := by
      rw [fourSpace_volume_closedBall, mul_left_comm,
        ball_normalization_product, mul_comm]

theorem euclideanHausdorff_unitBall_le :
    (Measure.hausdorffMeasure 4 : Measure FourSpace) (ball 0 1) ≤ 16 := by
  classical
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcovers (n : ℕ) : ∃ (s : Set FourSpace) (r : FourSpace → ℝ),
      s.Countable ∧ s ⊆ ball 0 1 ∧ (∀ x ∈ s, r x ∈ Ioo 0 (δ n)) ∧
      (ball (0 : FourSpace) 1 ⊆ ⋃ x ∈ s, closedBall x (r x)) ∧
      (∑' x : s, volume (closedBall x.val (r x.val))) ≤
        volume (ball (0 : FourSpace) 1) + ENNReal.ofReal (δ n) := by
    apply Besicovitch.exists_closedBall_covering_tsum_measure_le volume
      (ne_of_gt (ENNReal.ofReal_pos.mpr (hδpos n))) (fun _ => Ioo 0 (δ n)) (ball 0 1)
    intro x _ ε hε
    refine ⟨min (δ n) ε / 2, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact half_pos (lt_min (hδpos n) hε)
    · exact (half_lt_self (lt_min (hδpos n) hε)).trans_le (min_le_left _ _)
    · exact half_pos (lt_min (hδpos n) hε)
    · exact (half_lt_self (lt_min (hδpos n) hε)).trans_le (min_le_right _ _)
  choose s r hcount _hradcenter hrad hcover hsum using hcovers
  let : ∀ n, Countable (s n) := fun n => (hcount n).to_subtype
  have hδe : Tendsto (fun n => ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδ
  have hdiam : Tendsto (fun n => 2 * ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using!
      (ENNReal.continuous_const_mul (a := 2) (by norm_num)).continuousAt.tendsto.comp hδe
  have hH := Measure.hausdorffMeasure_le_liminf_tsum (ι := fun n => s n) 4
    (ball (0 : FourSpace) 1) (fun n => 2 * ENNReal.ofReal (δ n)) hdiam
    (fun n x => closedBall x.val (r n x.val))
    (Eventually.of_forall fun n x =>
      (fourSpace_ediam_closedBall_le x.val (hrad n x.val x.property).1.le).trans
        (by gcongr; exact (hrad n x.val x.property).2.le))
    (Eventually.of_forall fun n => by simpa only [iUnion_subtype] using hcover n)
  have hcost (n : ℕ) :
      (∑' x : s n, Metric.ediam (closedBall x.val (r n x.val)) ^ (4 : ℝ)) ≤
      ENNReal.ofReal (32 / Real.pi ^ 2) *
        (volume (ball (0 : FourSpace) 1) + ENNReal.ofReal (δ n)) := by
    calc
      _ ≤ ∑' x : s n, ENNReal.ofReal (32 / Real.pi ^ 2) *
          volume (closedBall x.val (r n x.val)) :=
        ENNReal.tsum_le_tsum fun x => fourSpace_ball_cost x.val (hrad n x.val x.property).1.le
      _ = ENNReal.ofReal (32 / Real.pi ^ 2) *
          ∑' x : s n, volume (closedBall x.val (r n x.val)) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact hsum n
  have hlim : Tendsto (fun n => ENNReal.ofReal (32 / Real.pi ^ 2) *
      (volume (ball (0 : FourSpace) 1) + ENNReal.ofReal (δ n))) atTop (𝓝 16) := by
    have h := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (32 / Real.pi ^ 2))
      ENNReal.ofReal_ne_top).continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := volume (ball (0 : FourSpace) 1))).add hδe)
    simpa only [Function.comp_apply, add_zero, fourSpace_volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
      ball_normalization_product] using! h
  exact hH.trans ((Filter.liminf_le_liminf (Eventually.of_forall hcost)).trans_eq hlim.liminf_eq)

theorem euclideanHausdorffFactor_le :
    (euclideanHausdorffFactor : ℝ≥0∞) ≤ ENNReal.ofReal (32 / Real.pi ^ 2) := by
  have h := euclideanHausdorff_unitBall_le
  rw [euclideanHausdorff_apply, fourSpace_volume_ball, ENNReal.ofReal_one,
    one_pow, one_mul, ← ball_normalization_product] at h
  exact (ENNReal.mul_le_mul_iff_left (by positivity : ENNReal.ofReal (Real.pi ^ 2 / 2) ≠ 0)
    ENNReal.ofReal_ne_top).mp h

theorem riemannianChartFactor_le_one : riemannianChartFactor ≤ 1 := by
  calc
    riemannianChartFactor ≤ ENNReal.ofReal (Real.pi ^ 2 / 32) *
        ENNReal.ofReal (32 / Real.pi ^ 2) :=
      by dsimp only [riemannianChartFactor]; gcongr; exact euclideanHausdorffFactor_le
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h : Real.pi ^ 2 / 32 * (32 / Real.pi ^ 2) = 1 := by
        field_simp
      rw [h, ENNReal.ofReal_one]

theorem polarAngularMass_eq : polarAngularMass = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [polarAngularMass_eq_ball, fourSpace_volume_ball, ENNReal.ofReal_one, one_pow, one_mul]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local coordinate expressions of the actual radial flow. Coordinate
composition is proved from the intrinsic group law and actual chart inverses. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem cotangentRadialRetraction_continuousAt (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) :
    ContinuousAt (cotangentRadialRetraction g c) z := by
  let S : Set CotangentCoordinates := {q | q.1 ∈ (chartAt FourSpace c).target ∧ q.2 ≠ 0}
  have hS : IsOpen S :=
    ((chartAt FourSpace c).open_target.preimage continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)
  have hc : Continuous (fun q : NonzeroCotangentChart c => cotangentRadialRetraction g c q.val) :=
    (continuous_cotangentRadialInverseOn g c).congr
      (fun q => (cotangentRadialRetraction_on g c q).symm)
  have hcont : ContinuousOn (cotangentRadialRetraction g c) S :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact (hcont z hz).continuousAt (hS.mem_nhds hz)

variable [T2Space M] [CompactSpace M]

def radialCoordinateFlow (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (t : ℝ) (z : CotangentCoordinates) : CotangentCoordinates :=
  unitRadialCotangentState g d (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z))

theorem radialCoordinateFlow_at_state (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source) :
    radialCoordinateFlow g o c d t (unitRadialCotangentState g c p) =
      unitRadialCotangentState g d (unitTangentRadialFlow g o t p) := by
  rw [radialCoordinateFlow, cotangentRadialRetraction_state g c p hc]

theorem radialCoordinateFlow_continuousAt (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source) :
    ContinuousAt (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p) := by
  have hz : (unitRadialCotangentState g c p).1 ∈ (chartAt FourSpace c).target ∧
      (unitRadialCotangentState g c p).2 ≠ 0 :=
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hr := cotangentRadialRetraction_continuousAt g c _ hz
  have hflow := (unitTangentRadialFlow_continuous g o t).continuousAt.comp hr
  have hout := unitRadialCotangentState_continuousAt g d (unitTangentRadialFlow g o t p) hd
  have hout' : ContinuousAt (unitRadialCotangentState g d)
      (unitTangentRadialFlow g o t (cotangentRadialRetraction g c
        (unitRadialCotangentState g c p))) := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hout
  exact hout'.comp (f := fun z : CotangentCoordinates =>
    unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)) hflow

/-- The intrinsic group law becomes coordinate composition on a genuine
neighborhood of the starting cotangent state. -/
theorem radialCoordinateFlow_add_eventually (g : SmoothMetric M) (o : FrameOrientation g)
    (c m d : M) (s t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hm : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace m).source) :
    radialCoordinateFlow g o c d (s + t) =ᶠ[𝓝 (unitRadialCotangentState g c p)]
      (radialCoordinateFlow g o m d s ∘ radialCoordinateFlow g o c m t) := by
  have hz : (unitRadialCotangentState g c p).1 ∈ (chartAt FourSpace c).target ∧
      (unitRadialCotangentState g c p).2 ≠ 0 :=
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hr := cotangentRadialRetraction_continuousAt g c _ hz
  have hb : ContinuousAt (fun z : CotangentCoordinates =>
      (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)).2.base)
      (unitRadialCotangentState g c p) :=
    (continuous_unitTangentBase g).continuousAt.comp
      (continuous_snd.continuousAt.comp ((unitTangentRadialFlow_continuous g o t).continuousAt.comp hr))
  have hm' : (unitTangentRadialFlow g o t (cotangentRadialRetraction g c
      (unitRadialCotangentState g c p))).2.base ∈ (chartAt FourSpace m).source := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hm
  filter_upwards [hb.preimage_mem_nhds ((chartAt FourSpace m).open_source.mem_nhds hm')] with z hz'
  change unitRadialCotangentState g d
      (unitTangentRadialFlow g o (s + t) (cotangentRadialRetraction g c z)) =
    unitRadialCotangentState g d (unitTangentRadialFlow g o s
      (cotangentRadialRetraction g m (unitRadialCotangentState g m
        (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)))))
  rw [cotangentRadialRetraction_state g m _ hz', unitTangentRadialFlow_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! An almost-everywhere chart representative is a representative for
the actual normalized Riemannian measure on the corresponding base open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

/-- Lebesgue almost-everywhere equality in a chart transfers to actual
normalized volume.  No measurability assumption on the representatives is
needed, and the open set need not be contained in the chart target. -/
theorem scalar_chart_representative_ae (g : SmoothMetric M) (c : M)
    (U : Set FourSpace) (hU : IsOpen U) (b : M → ℝ) (F : FourSpace → ℝ)
    (h : (fun z => b ((chartAt FourSpace c).symm z)) =ᵐ[volume.restrict U] F) :
    b =ᵐ[(normalizedVolume g).restrict
      ((chartAt FourSpace c).source ∩ (chartAt FourSpace c) ⁻¹' U)]
      (fun x => F (chartAt FourSpace c x)) := by
  let e := chartAt FourSpace c
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let φ : ChartTarget c → M := fun z => e.symm z.val
  have he : MeasurableEmbedding φ :=
    e.symm.isOpenEmbedding_restrict.measurableEmbedding
  have hfull : ∀ᵐ z ∂(volume : Measure FourSpace),
      z ∈ U → b (e.symm z) = F z :=
    (ae_restrict_iff' hU.measurableSet).mp h
  have hsub : ∀ᵐ z ∂μ, z.val ∈ U → b (e.symm z.val) = F z.val :=
    (ae_restrict_iff_subtype e.open_target.measurableSet).mp
      (ae_restrict_of_ae hfull)
  have hweight : ∀ᵐ z ∂μ.withDensity ρ,
      z.val ∈ U → b (e.symm z.val) = F z.val :=
    hsub.filter_mono (withDensity_absolutelyContinuous μ ρ).ae_le
  have hmap : ∀ᵐ x ∂Measure.map φ (μ.withDensity ρ),
      e x ∈ U → b x = F (e x) := by
    apply he.ae_map_iff.mpr
    filter_upwards [hweight] with z hz
    change e (e.symm z.val) ∈ U → b (e.symm z.val) = F (e (e.symm z.val))
    rwa [e.right_inv z.property]
  have hsource : ∀ᵐ x ∂(normalizedVolume g).restrict e.source,
      e x ∈ U → b x = F (e x) := by
    rw [normalizedVolume_restrict_chart g c]
    exact Measure.ae_smul_measure hmap (normalizedChartFactor g)
  have hbase := (ae_restrict_iff' e.open_source.measurableSet).mp hsource
  apply (ae_restrict_iff' (e.isOpen_inter_preimage hU).measurableSet).mpr
  filter_upwards [hbase] with x hx
  intro hxU
  exact hx hxU.1 hxU.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous differentiability of the actual radial flow is local in cotangent charts
and is stable under its intrinsic time-composition law. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def RadialFlowContDiffAt (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (p : PositiveRadius × UnitTangentBundle g) : Prop :=
  ∀ c d : M, p.2.base ∈ (chartAt FourSpace c).source →
    (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source →
    ContDiffAt ℝ 1 (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p)

omit [T2Space M] [CompactSpace M] in
private theorem radial_state_domain_nhds (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source) :
    {z : CotangentCoordinates | z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0} ∈
      𝓝 (unitRadialCotangentState g c p) := by
  apply (((chartAt FourSpace c).open_target.preimage continuous_fst).inter
    (isOpen_compl_singleton.preimage continuous_snd)).mem_nhds
  exact ⟨(chartAt FourSpace c).map_source hc,
    unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩

theorem radialCoordinateFlow_zero_eventually (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : p.2.base ∈ (chartAt FourSpace d).source) :
    radialCoordinateFlow g o c d 0 =ᶠ[𝓝 (unitRadialCotangentState g c p)]
      cotangentChartTransition g c d := by
  have hz := radial_state_domain_nhds g c p hc
  have hret := cotangentRadialRetraction_continuousAt g c (unitRadialCotangentState g c p)
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hb := (continuous_unitTangentBase g).continuousAt.comp
    (continuous_snd.continuousAt.comp hret)
  have hd' : (cotangentRadialRetraction g c (unitRadialCotangentState g c p)).2.base ∈
      (chartAt FourSpace d).source := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hd
  filter_upwards [hz, hb.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hd')] with z hzc hzd
  rw [radialCoordinateFlow, unitTangentRadialFlow_zero,
    cotangentChartTransition_retraction g o c d z hzc hzd]

theorem radialFlowContDiffAt_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (p : PositiveRadius × UnitTangentBundle g) : RadialFlowContDiffAt g o 0 p := by
  intro c d hc hd
  rw [unitTangentRadialFlow_zero] at hd
  have hin : (chartAt FourSpace c).symm (unitRadialCotangentState g c p).1 ∈
      (chartAt FourSpace d).source := by
    change (chartAt FourSpace c).symm (chartAt FourSpace c p.2.base) ∈ _
    rwa [(chartAt FourSpace c).left_inv hc]
  exact ((cotangentChartTransition_contDiffAt g c d _
    ((chartAt FourSpace c).map_source hc) hin).of_le (by simp)).congr_of_eventuallyEq
      (radialCoordinateFlow_zero_eventually g o c d p hc hd)

/-- A derivative in one pair of actual charts gives the derivative in every
pair of charts at the same source and target. -/
theorem radialFlowContDiffAt_of_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (p : PositiveRadius × UnitTangentBundle g) (c₀ d₀ : M)
    (hc₀ : p.2.base ∈ (chartAt FourSpace c₀).source)
    (hd₀ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₀).source)
    (hcore : ContDiffAt ℝ 1 (radialCoordinateFlow g o c₀ d₀ t)
      (unitRadialCotangentState g c₀ p)) : RadialFlowContDiffAt g o t p := by
  intro c d hc hd
  have hin := radialFlowContDiffAt_zero g o p c c₀ hc
    (by simpa only [unitTangentRadialFlow_zero] using hc₀)
  have hcore' : ContDiffAt ℝ 1 (radialCoordinateFlow g o c₀ d₀ t)
      (radialCoordinateFlow g o c c₀ 0 (unitRadialCotangentState g c p)) := by
    simpa only [radialCoordinateFlow_at_state g o c c₀ 0 p hc, unitTangentRadialFlow_zero] using hcore
  have hmid := hcore'.comp (unitRadialCotangentState g c p) hin
  have hmid' : ContDiffAt ℝ 1 (radialCoordinateFlow g o c d₀ t)
      (unitRadialCotangentState g c p) := by
    apply hmid.congr_of_eventuallyEq
    simpa only [add_zero] using radialCoordinateFlow_add_eventually g o c c₀ d₀ t 0 p hc
      (by simpa only [unitTangentRadialFlow_zero] using hc₀)
  have hout := radialFlowContDiffAt_zero g o (unitTangentRadialFlow g o t p) d₀ d hd₀
    (by simpa only [unitTangentRadialFlow_zero] using hd)
  have hout' : ContDiffAt ℝ 1 (radialCoordinateFlow g o d₀ d 0)
      (radialCoordinateFlow g o c d₀ t (unitRadialCotangentState g c p)) := by
    simpa only [radialCoordinateFlow_at_state g o c d₀ t p hc] using hout
  apply (hout'.comp (unitRadialCotangentState g c p) hmid').congr_of_eventuallyEq
  simpa only [zero_add] using radialCoordinateFlow_add_eventually g o c d₀ d 0 t p hc hd₀

theorem RadialFlowContDiffAt.add (g : SmoothMetric M) (o : FrameOrientation g)
    (s t : ℝ) (p : PositiveRadius × UnitTangentBundle g)
    (hs : RadialFlowContDiffAt g o s (unitTangentRadialFlow g o t p))
    (ht : RadialFlowContDiffAt g o t p) : RadialFlowContDiffAt g o (s + t) p := by
  intro c d hc hd
  let m := (unitTangentRadialFlow g o t p).2.base
  have hm : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace m).source :=
    mem_chart_source FourSpace m
  have hmid := ht c m hc hm
  have hout := hs m d hm (by simpa only [← unitTangentRadialFlow_add] using hd)
  have hout' : ContDiffAt ℝ 1 (radialCoordinateFlow g o m d s)
      (radialCoordinateFlow g o c m t (unitRadialCotangentState g c p)) := by
    simpa only [radialCoordinateFlow_at_state g o c m t p hc] using hout
  exact (hout'.comp (unitRadialCotangentState g c p) hmid).congr_of_eventuallyEq
    (radialCoordinateFlow_add_eventually g o c m d s t p hc hm)

theorem RadialHamiltonianChart.contDiffAt (g : SmoothMetric M) (o : FrameOrientation g)
    (C : RadialHamiltonianChart g o) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p ∈ C.domain) (t : ℝ) (ht : t ∈ Ioo (-C.flow.time) C.flow.time) :
    RadialFlowContDiffAt g o t p := by
  have hzero : (0 : ℝ) ∈ Ioo (-C.flow.time) C.flow.time :=
    ⟨by linarith [C.flow.time_pos], C.flow.time_pos⟩
  have hc : p.2.base ∈ (chartAt FourSpace C.center).source := by
    simpa only [unitTangentRadialFlow_zero] using C.trajectory_in_chart p hp 0 hzero
  have hd := C.trajectory_in_chart p hp t ht
  apply radialFlowContDiffAt_of_chart g o t p C.center C.center hc hd
  have hz := radial_state_domain_nhds g C.center p hc
  have hr := cotangentRadialRetraction_continuousAt g C.center (unitRadialCotangentState g C.center p)
    ⟨(chartAt FourSpace C.center).map_source hc,
      unitCotangentState_momentum_ne_zero g C.center p.1.val p.1.property p.2 hc⟩
  have hp' : cotangentRadialRetraction g C.center (unitRadialCotangentState g C.center p) ∈ C.domain := by
    rwa [cotangentRadialRetraction_state g C.center p hc]
  have heq : radialCoordinateFlow g o C.center C.center t =ᶠ[𝓝 (unitRadialCotangentState g C.center p)]
      (fun z => C.flow.map (z, t)) := by
    filter_upwards [hz, hr.preimage_mem_nhds (C.open_domain.mem_nhds hp')] with z hzc hzp
    have h := C.conjugacy (cotangentRadialRetraction g C.center z) hzp ht
    rw [unitRadialCotangentState_retraction g C.center z hzc] at h
    exact h.symm
  have hball : unitRadialCotangentState g C.center p ∈
      Metric.ball (unitRadialCotangentState g C.center C.anchor) C.flow.radius := by
    apply C.image_subset_ball
    rw [C.image_eq]
    exact mem_image_of_mem _ hp
  exact (C.flow.contDiffAt_slice _ hball t ht).congr_of_eventuallyEq heq


/-- Compact radius slabs give one interval of continuously differentiable flow times. -/
theorem radialFlowContDiffAt_uniform_time (g : SmoothMetric M) (o : FrameOrientation g)
    (a b : ℝ) (ha : 0 < a) :
    ∃ ε > (0 : ℝ), ∀ p ∈ radialSlab g a b, ∀ t : ℝ, |t| < ε →
      RadialFlowContDiffAt g o t p := by
  obtain ⟨ε, hε, hcharts⟩ := radialSlab_uniform_hamiltonian_time g o (b := b) ha
  refine ⟨ε, hε, fun p hp t ht => ?_⟩
  obtain ⟨C, hpC, hεC⟩ := hcharts p hp
  apply C.contDiffAt g o p hpC t
  have htime : |t| < C.flow.time := ht.trans_le hεC
  exact abs_lt.mp htime

/-- The constructed complete radial flow is continuously differentiable in its initial
cotangent state at every time. No differentiability of a chosen global ODE
solution is assumed. -/
theorem radialFlowContDiffAt_all_time (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (p : PositiveRadius × UnitTangentBundle g) :
    RadialFlowContDiffAt g o t p := by
  let a := p.1.val / 2
  let b := 2 * p.1.val
  have ha : 0 < a := half_pos p.1.property
  have hp : p ∈ radialSlab g a b := by
    change p.1.val / 2 ≤ p.1.val ∧ p.1.val ≤ 2 * p.1.val
    have hr : 0 < p.1.val := p.1.property
    constructor <;> linarith
  obtain ⟨ε, hε, hlocal⟩ := radialFlowContDiffAt_uniform_time g o a b ha
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hnzero : (n : ℝ) ≠ 0 := hnpos.ne'
  let s : ℝ := t / n
  have hs : |s| < ε := by
    dsimp [s]
    rw [abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hmul (m : ℕ) : ∀ q ∈ radialSlab g a b,
      RadialFlowContDiffAt g o ((m : ℝ) * s) q := by
    induction m with
    | zero =>
      intro q _hq
      simpa only [Nat.cast_zero, zero_mul] using radialFlowContDiffAt_zero g o q
    | succ m ih =>
      intro q hq
      have hq' : unitTangentRadialFlow g o ((m : ℝ) * s) q ∈ radialSlab g a b :=
        (unitTangentRadialFlow_mem_slab g o a b _ q).mpr hq
      have hstep := hlocal _ hq' s hs
      have h := RadialFlowContDiffAt.add g o s ((m : ℝ) * s) q hstep (ih q hq)
      convert h using 1
      rw [Nat.cast_succ]
      ring
  have heq : (n : ℝ) * s = t := by dsimp [s]; field_simp [hnzero]
  simpa only [heq] using hmul n p hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local preservation of radial canonical measure. The coordinate
measure is identified from Hausdorff density, and the Hamiltonian determinant
identity is transported through the genuine cotangent chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace KineticLocalFlow

def measurableSlice {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ) : CotangentCoordinates → CotangentCoordinates :=
  open Classical in
  (Metric.ball p F.radius).piecewise (fun z => F.map (z, t)) (fun _ => 0)

theorem measurableSlice_eq {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ) (z : CotangentCoordinates)
    (hz : z ∈ Metric.ball p F.radius) : F.measurableSlice t z = F.map (z, t) := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz

theorem measurable_measurableSlice {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p) (t : ℝ)
    (ht : t ∈ Ioo (-F.time) F.time) : Measurable (F.measurableSlice t) := by
  classical
  have hc : ContinuousOn (fun z => F.map (z, t)) (Metric.ball p F.radius) :=
    F.continuous_map.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz, ht⟩)
  exact hc.measurable_piecewise continuousOn_const Metric.isOpen_ball.measurableSet

theorem measurableSlice_map_volume {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p) (t : ℝ)
    (ht : t ∈ Ioo (-F.time) F.time) (s : Set CotangentCoordinates)
    (hs : MeasurableSet s) (hsub : s ⊆ Metric.ball p F.radius) :
    Measure.map (F.measurableSlice t) (volume.restrict s) =
      volume.restrict (F.measurableSlice t '' s) := by
  have heq : EqOn (F.measurableSlice t) (fun z => F.map (z, t)) s :=
    fun z hz => F.measurableSlice_eq t z (hsub hz)
  calc
    _ = Measure.map (fun z => F.map (z, t)) (volume.restrict s) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs] with z hz
      exact heq hz
    _ = volume.restrict ((fun z => F.map (z, t)) '' s) :=
      F.map_volume_restrict t ht s hs hsub
    _ = _ := congrArg (fun A => volume.restrict A) (image_congr heq).symm

end KineticLocalFlow

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actual_radialCotangentStateExtension_map (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) :
    Measure.map (radialCotangentStateExtension g c)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        {p | p.2.base ∈ (chartAt FourSpace c).source}) =
      (normalizedChartFactor g / polarAngularMass) •
        (volume : Measure CotangentCoordinates).restrict
          {p | p.1 ∈ (chartAt FourSpace c).target} := by
  rw [← actual_unitRadialCotangentState_map g o c]
  apply Measure.map_congr
  have hS : MeasurableSet {p : PositiveRadius × UnitTangentBundle g |
      p.2.base ∈ (chartAt FourSpace c).source} :=
    ((chartAt FourSpace c).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet
  filter_upwards [ae_restrict_mem hS] with p hp
  exact radialCotangentStateExtension_eq g c p hp

/-- Every actual Hamiltonian chart preserves the actual radial measure
on its open domain for the full interval provided by that chart. -/
theorem RadialHamiltonianChart.map_radialMeasure (g : SmoothMetric M)
    (o : FrameOrientation g) (C : RadialHamiltonianChart g o)
    (t : ℝ) (ht : t ∈ Ioo (-C.flow.time) C.flow.time) :
    Measure.map (unitTangentRadialFlow g o t)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict C.domain) =
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        (unitTangentRadialFlow g o t '' C.domain) := by
  let S : Set (PositiveRadius × UnitTangentBundle g) :=
    {p | p.2.base ∈ (chartAt FourSpace C.center).source}
  let f := radialCotangentStateExtension g C.center
  let r := cotangentRadialRetraction g C.center
  let Φ := unitTangentRadialFlow g o t
  let F := C.flow.measurableSlice t
  have hzero : (0 : ℝ) ∈ Ioo (-C.flow.time) C.flow.time := by
    constructor <;> linarith [C.flow.time_pos]
  have hUS : C.domain ⊆ S := by
    intro p hp
    have h := C.trajectory_in_chart p hp 0 hzero
    simpa only [unitTangentRadialFlow_zero] using! h
  have hΦS : Φ '' C.domain ⊆ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact C.trajectory_in_chart p hp t ht
  have hS : MeasurableSet S :=
    ((chartAt FourSpace C.center).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet
  have heq : EqOn f (unitRadialCotangentState g C.center) S :=
    fun p hp => radialCotangentStateExtension_eq g C.center p hp
  have hfU : f '' C.domain = C.image := by
    rw [C.image_eq]
    exact image_congr (fun p hp => heq (hUS hp))
  have hΦopen : IsOpen (Φ '' C.domain) :=
    (unitTangentRadialHomeomorph g o t).isOpenMap _ C.open_domain
  have hfΦU : IsOpen (f '' (Φ '' C.domain)) := by
    have himage : f '' (Φ '' C.domain) =
        unitRadialCotangentState g C.center '' (Φ '' C.domain) :=
      image_congr (fun p hp => heq (hΦS hp))
    rw [himage]
    exact isOpen_unitRadialCotangentState_image g C.center _ hΦopen hΦS
  apply local_image_measure_of_coordinates _ volume
    (normalizedChartFactor g / polarAngularMass) f r
    (measurable_radialCotangentStateExtension g C.center)
    (measurable_cotangentRadialRetraction g C.center) S
    {z | z.1 ∈ (chartAt FourSpace C.center).target} hS
    (fun p hp => cotangentRadialRetraction_extension g C.center p hp) ?_
    (actual_radialCotangentStateExtension_map g o C.center) Φ F
    (unitTangentRadialFlow_continuous g o t).measurable
    (C.flow.measurable_measurableSlice t ht) C.domain C.open_domain.measurableSet
    hUS hΦS hΦopen.measurableSet ?_ hfΦU.measurableSet ?_ ?_
  · intro p hp
    rw [heq hp]
    exact (chartAt FourSpace C.center).map_source hp
  · rw [hfU]
    exact C.open_image.measurableSet
  · intro p hp
    change f (Φ p) = C.flow.measurableSlice t (f p)
    rw [heq (hΦS ⟨p, hp, rfl⟩), heq (hUS hp),
      C.flow.measurableSlice_eq t _ (C.image_subset_ball (by
        rw [C.image_eq]; exact ⟨p, hp, rfl⟩))]
    exact (C.conjugacy p hp ht).symm
  · rw [hfU]
    exact C.flow.measurableSlice_map_volume t ht C.image C.open_image.measurableSet
      C.image_subset_ball

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lebesgue almost-everywhere coordinate statements, including weak
convergence statements, transfer to the actual normalized volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem scalar_chart_ae_predicate (g : SmoothMetric M) (c : M)
    (P : FourSpace → Prop) (hP : ∀ᵐ z ∂(volume : Measure FourSpace), P z) :
    ∀ᵐ x ∂normalizedVolume g,
      x ∈ (chartAt FourSpace c).source → P (chartAt FourSpace c x) := by
  let e := chartAt FourSpace c
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let φ : ChartTarget c → M := fun z => e.symm z.val
  have he : MeasurableEmbedding φ := e.symm.isOpenEmbedding_restrict.measurableEmbedding
  have hsub : ∀ᵐ z ∂μ, P z.val :=
    (ae_restrict_iff_subtype e.open_target.measurableSet).mp (ae_restrict_of_ae hP)
  have hw : ∀ᵐ z ∂μ.withDensity ρ, P z.val :=
    hsub.filter_mono (withDensity_absolutelyContinuous μ ρ).ae_le
  have hm : ∀ᵐ x ∂Measure.map φ (μ.withDensity ρ), P (e x) := by
    apply he.ae_map_iff.mpr
    filter_upwards [hw] with z hz
    change P (e (e.symm z.val))
    rwa [e.right_inv z.property]
  have hs : ∀ᵐ x ∂(normalizedVolume g).restrict e.source, P (e x) := by
    rw [normalizedVolume_restrict_chart g c]
    exact Measure.ae_smul_measure hm (normalizedChartFactor g)
  exact (ae_restrict_iff' e.open_source.measurableSet).mp hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Preservation of the canonical frame measure by the actual complete
parallel-frame flows. Local Hamiltonian preservation is glued on compact
radius slabs; the radial measure is then disintegrated on energy shells. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem unitTangentRadialFlow_measurePreserving (g : SmoothMetric M)
    (o : FrameOrientation g) (t : ℝ) :
    MeasurePreserving (unitTangentRadialFlow g o t)
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)) := by
  apply unitTangentRadial_preserves_of_slab_local_images g o _ ?_ t
  intro n
  have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨ε, hε, hlocal⟩ := radialSlab_uniform_hamiltonian_time g o
    (b := (n : ℝ) + 1) ha
  refine ⟨ε, hε, fun s hs p hp => ?_⟩
  obtain ⟨C, hpC, hεC⟩ := hlocal p hp
  have hsC : s ∈ Ioo (-C.flow.time) C.flow.time := by
    constructor <;> linarith [hs.1, hs.2]
  exact ⟨C.domain, C.open_domain, hpC, C.map_radialMeasure g o s hsC⟩

theorem unitTangentFlow_measurePreserving (g : SmoothMetric M)
    (o : FrameOrientation g) (t : ℝ) :
    MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o) :=
  unitTangentFlow_preserves_of_radial g o t (unitTangentRadialFlow_measurePreserving g o t)

/-- The actual parallel-frame flow preserves base Riemannian volume times
orthonormal-fiber Haar probability, in every distinguished frame direction. -/
theorem parallelFrameFlowMap_measurePreserving (g : SmoothMetric M)
    (o : FrameOrientation g) (k : Fin 4) (t : ℝ) :
    MeasurePreserving (parallelFrameFlowMap g k t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) :=
  allFrameFlows_preserve_of_radial g o (unitTangentRadialFlow_measurePreserving g o) k t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous differentiability of the actual exponential in coordinate
charts, including the zero vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_frame_endpoint (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (v : FourSpace) (hv : v ≠ 0) :
    (radialCoordinateFlow g o c d 1
      (chartAt FourSpace c e.base, frameMomentumMap g c e v)).1 =
      chartAt FourSpace d (frameExponential g o e v) := by
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c (r, unitTangentTurn e q) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  rw [← hstate, radialCoordinateFlow_at_state g o c d 1 _ he]
  change chartAt FourSpace d (unitTangentFlowMap g o (r.val * 1) (unitTangentTurn e q)).base = _
  rw [mul_one, ← hvr, frameExponential_radial]
  rfl

theorem frameExponential_chart_contDiffAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ContDiffAt ℝ 1 (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  let t := F.time / 2
  have ht0 : 0 < t := half_pos F.time_pos
  have ht : t ∈ Ioo (-F.time) F.time := by
    dsimp [t]
    constructor <;> linarith [F.time_pos]
  have hinit : ContDiffAt ℝ 1
      (fun v : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  have hF : ContDiffAt ℝ 1 (fun z => F.map (z, t))
      (chartAt FourSpace c e.base, frameMomentumMap g c e 0) := by
    simpa only [map_zero] using F.contDiffAt_slice _ (Metric.mem_ball_self F.radius_pos) t ht
  have hlocal : ContDiffAt ℝ 1
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v))) 0 := by
    have hcompose : ContDiffAt ℝ 1 (fun v : FourSpace =>
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)) 0 :=
      ContDiffAt.comp (f := fun v : FourSpace =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v))
        (g := fun z : CotangentCoordinates => F.map (z, t)) 0 hF hinit
    exact hcompose.fst.congr_of_eventuallyEq
      (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0)
  have hscale : ContDiffAt ℝ 1 (fun v : FourSpace => t⁻¹ • v) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff.contDiffAt
  have hlocal' : ContDiffAt ℝ 1
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t⁻¹ • (0 : FourSpace)) := by simpa only [smul_zero] using hlocal
  have h := hlocal'.comp 0 hscale
  have heq : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  change ContDiffAt ℝ 1 (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v)))) 0 at h
  rwa [heq] at h

theorem frameExponential_chart_contDiffAt_nonzero (g : SmoothMetric M)
    (o : FrameOrientation g) (d : M) (e : FrameBundle g) (v : FourSpace) (hv : v ≠ 0)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 1 (fun w : FourSpace => chartAt FourSpace d (frameExponential g o e w)) v := by
  let c := e.base
  have he : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace e.base
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  let p : PositiveRadius × UnitTangentBundle g := (r, unitTangentTurn e q)
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c p =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  have hout : (unitTangentRadialFlow g o 1 p).2.base = frameExponential g o e v := by
    change (unitTangentFlowMap g o (r.val * 1) (unitTangentTurn e q)).base = _
    rw [mul_one, ← hvr, frameExponential_radial]
    rfl
  have hcore := radialFlowContDiffAt_all_time g o 1 p c d he (by rwa [hout])
  rw [hstate] at hcore
  have hinit : ContDiffAt ℝ 1
      (fun w : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e w)) v :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  apply ((hcore.comp v hinit).fst).congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hv] with z hz
  exact (radialCoordinateFlow_frame_endpoint g o c d e he z hz).symm

/-- Every coordinate representation of the constructed exponential is C1
where its value belongs to that coordinate chart. -/
theorem frameExponential_chart_contDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (d : M) (e : FrameBundle g) (v : FourSpace)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 1 (fun w : FourSpace => chartAt FourSpace d (frameExponential g o e w)) v := by
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero] at hd
    exact frameExponential_chart_contDiffAt_zero g o d e hd
  · exact frameExponential_chart_contDiffAt_nonzero g o d e v hv hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative of the actual complete radial flow solves the kinetic
variational equation. The proof uses local flow composition at each time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- A local kinetic flow at the endpoint factors the complete coordinate
flow on a neighborhood of its initial state. -/
theorem radialCoordinateFlow_local_factor (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source) :
    ∃ F : KineticLocalFlow g d (unitRadialCotangentState g d (unitTangentRadialFlow g o t p)),
      ∀ s ∈ Ioo (-F.time) F.time,
        radialCoordinateFlow g o c d (s + t) =ᶠ[𝓝 (unitRadialCotangentState g c p)]
          (fun z => F.map (radialCoordinateFlow g o c d t z, s)) := by
  obtain ⟨U, hU, hpU, F, _hball, hconj⟩ :=
    exists_unitTangent_localHamiltonian g o d (unitTangentRadialFlow g o t p) hd
  refine ⟨F, fun s hs => ?_⟩
  have hr := cotangentRadialRetraction_continuousAt g c (unitRadialCotangentState g c p)
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hf := (unitTangentRadialFlow_continuous g o t).continuousAt.comp hr
  have hpU' : unitTangentRadialFlow g o t
      (cotangentRadialRetraction g c (unitRadialCotangentState g c p)) ∈ U := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hpU
  filter_upwards [hf.preimage_mem_nhds (hU.mem_nhds hpU')] with z hz
  have h := hconj (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)) hz hs
  change unitRadialCotangentState g d
      (unitTangentRadialFlow g o (s + t) (cotangentRadialRetraction g c z)) = _
  rw [unitTangentRadialFlow_add]
  exact h.symm

/-- The true spatial derivative, rather than a separately chosen solution,
satisfies the linearized Hamiltonian equation at every valid chart time. -/
theorem radialCoordinateFlow_fderiv_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c d : M) (p : PositiveRadius × UnitTangentBundle g)
    (t : ℝ) (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source) :
    HasDerivAt
      (fun s => fderiv ℝ (radialCoordinateFlow g o c d s) (unitRadialCotangentState g c p))
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g d))
          (unitRadialCotangentState g d (unitTangentRadialFlow g o t p))).comp
        (fderiv ℝ (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p))) t := by
  let z := unitRadialCotangentState g c p
  let q := unitRadialCotangentState g d (unitTangentRadialFlow g o t p)
  let D := fderiv ℝ (radialCoordinateFlow g o c d t) z
  obtain ⟨F, hfactor⟩ := radialCoordinateFlow_local_factor g o c d p t hc hd
  have hpoint : radialCoordinateFlow g o c d t z = q :=
    radialCoordinateFlow_at_state g o c d t p hc
  have hD : HasFDerivAt (radialCoordinateFlow g o c d t) D z :=
    ((radialFlowContDiffAt_all_time g o t p c d hc hd).differentiableAt (by simp)).hasFDerivAt
  have hball : q ∈ Metric.ball q F.radius := Metric.mem_ball_self F.radius_pos
  have hzero : (0 : ℝ) ∈ Ioo (-F.time) F.time :=
    ⟨by linarith [F.time_pos], F.time_pos⟩
  have hspatial (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      fderiv ℝ (radialCoordinateFlow g o c d (s + t)) z =
        (F.variation (q, s)).comp D := by
    have hFs := F.initial_derivative q hball s hs
    rw [← hpoint] at hFs
    simpa only [hpoint] using ((hFs.comp z hD).congr_of_eventuallyEq (hfactor s hs)).fderiv
  have hvar := F.variation_derivative q hball 0 hzero
  have hcomp := hvar.clm_comp (hasDerivAt_const (0 : ℝ) D)
  have hcomp' : HasDerivAt (fun s => (F.variation (q, s)).comp D)
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g d)) q).comp D) 0 := by
    simpa only [F.initial q hball, F.initial_variation q hball,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_zero, add_zero] using hcomp
  have heq : (fun s => fderiv ℝ (radialCoordinateFlow g o c d (s + t)) z) =ᶠ[𝓝 0]
      (fun s => (F.variation (q, s)).comp D) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact hspatial s hs
  have hshift := hcomp'.congr_of_eventuallyEq heq
  have hshift' : HasDerivAt
      (fun s => fderiv ℝ (radialCoordinateFlow g o c d (s + t)) z)
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g d)) q).comp D) (t - t) := by
    simpa only [sub_self] using hshift
  have h := hshift'.comp_sub_const t t
  simpa only [sub_add_cancel] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Canonical parallel calculus: flow existence, differentiability and
measure preservation follow from the metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def canonicalParallelMetricData (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : ParallelMetricData g (canonicalFrameMeasure g o) :=
  actualParallelMetricData g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic

def actualCanonicalData (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g)
    (poisson : PetersenPoissonInput g (canonicalFrameMeasure g o))
    (jacobi : JacobiRealizationData (canonicalParallelMetricData g o hRic).toMetricGreenData)
    (gap : GurskyLeBrunGapInput g o) (hodge : GurskyLeBrunHodgeInput g o)
    (model : DerdzinskiHitchinInput g o) : PublishedOrientedData g o :=
  actualCanonicalPublishedOrientedData g o (parallelFrameFlowMap_measurePreserving g o)
    hRic poisson jacobi gap hodge model

variable [SecondCountableTopology M] [ConnectedSpace M]

/-- Analytic, polar, topological and rigidity hypotheses imply the two-model
oriented classification. -/
theorem models_of_actual_canonical_data (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g)
    (poisson : PetersenPoissonInput g (canonicalFrameMeasure g o))
    (jacobi : JacobiRealizationData (canonicalParallelMetricData g o hRic).toMetricGreenData)
    (gap : GurskyLeBrunGapInput g o) (hodge : GurskyLeBrunHodgeInput g o)
    (model : DerdzinskiHitchinInput g o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) :=
  (actualCanonicalData g o hRic poisson jacobi gap hodge model).models
    hRic hEinstein hpositive

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every finite derivative of the actual exponential exists near its zero
vector. The kinetic representation is evaluated at a sufficiently small
positive time and then rescaled, so no global smooth-flow input is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_chart_contDiffAt_zero_order (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (n : ℕ) :
    ContDiffAt ℝ n (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  obtain ⟨t, ht0, ht, hFt⟩ := F.exists_pos_contDiffAt_slice
    ((chartAt FourSpace c).map_source he) n
  have hinit : ContDiffAt ℝ n
      (fun v : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  have hF : ContDiffAt ℝ n (fun z => F.map (z, t))
      (chartAt FourSpace c e.base, frameMomentumMap g c e 0) := by
    simpa only [map_zero] using hFt
  have hlocal : ContDiffAt ℝ n
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v))) 0 := by
    have hcompose : ContDiffAt ℝ n (fun v : FourSpace =>
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)) 0 :=
      ContDiffAt.comp (f := fun v : FourSpace =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v))
        (g := fun z : CotangentCoordinates => F.map (z, t)) 0 hF hinit
    exact hcompose.fst.congr_of_eventuallyEq
      (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0)
  have hscale : ContDiffAt ℝ n (fun v : FourSpace => t⁻¹ • v) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff.contDiffAt
  have hlocal' : ContDiffAt ℝ n
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t⁻¹ • (0 : FourSpace)) := by simpa only [smul_zero] using hlocal
  have h := hlocal'.comp 0 hscale
  have heq : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  change ContDiffAt ℝ n (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v)))) 0 at h
  rwa [heq] at h

theorem frameExponential_chart_smoothAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ContDiffAt ℝ ∞ (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 :=
  contDiffAt_infty.mpr (frameExponential_chart_contDiffAt_zero_order g o c e he)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The position component of the actual variation transforms as a tangent
vector. Its coordinates in a fixed orthonormal frame are chart independent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_position_change_eventually (g : SmoothMetric M)
    (o : FrameOrientation g) (c d₀ d₁ : M) (p : PositiveRadius × UnitTangentBundle g)
    (t : ℝ) (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd₀ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₀).source) :
    (fun z => (radialCoordinateFlow g o c d₁ t z).1) =ᶠ[𝓝 (unitRadialCotangentState g c p)]
      (fun z => chartTransition d₀ d₁ (radialCoordinateFlow g o c d₀ t z).1) := by
  have hr := cotangentRadialRetraction_continuousAt g c (unitRadialCotangentState g c p)
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hb : ContinuousAt (fun z : CotangentCoordinates =>
      (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)).2.base)
      (unitRadialCotangentState g c p) :=
    (continuous_unitTangentBase g).continuousAt.comp
      (continuous_snd.continuousAt.comp ((unitTangentRadialFlow_continuous g o t).continuousAt.comp hr))
  have hd' : (unitTangentRadialFlow g o t
      (cotangentRadialRetraction g c (unitRadialCotangentState g c p))).2.base ∈
      (chartAt FourSpace d₀).source := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hd₀
  filter_upwards [hb.preimage_mem_nhds ((chartAt FourSpace d₀).open_source.mem_nhds hd')] with z hz
  change chartAt FourSpace d₁ _ =
    chartAt FourSpace d₁ ((chartAt FourSpace d₀).symm (chartAt FourSpace d₀ _))
  rw [(chartAt FourSpace d₀).left_inv hz]

theorem radialCoordinateFlow_position_fderiv_change (g : SmoothMetric M)
    (o : FrameOrientation g) (c d₀ d₁ : M) (p : PositiveRadius × UnitTangentBundle g)
    (t : ℝ) (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd₀ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₀).source)
    (hd₁ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₁).source)
    (a : CotangentCoordinates) :
    WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₁ t)
      (unitRadialCotangentState g c p) a).1) =
      chartTransitionMatrix d₀ d₁ (chartAt FourSpace d₀ (unitTangentRadialFlow g o t p).2.base) *ᵥ
        WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₀ t)
          (unitRadialCotangentState g c p) a).1) := by
  let z := unitRadialCotangentState g c p
  let x := (unitTangentRadialFlow g o t p).2.base
  have hD₀ := ((radialFlowContDiffAt_all_time g o t p c d₀ hc hd₀).differentiableAt
    (by simp)).hasFDerivAt
  have hD₁ := ((radialFlowContDiffAt_all_time g o t p c d₁ hc hd₁).differentiableAt
    (by simp)).hasFDerivAt
  have hxinv : (chartAt FourSpace d₀).symm (chartAt FourSpace d₀ x) = x :=
    (chartAt FourSpace d₀).left_inv hd₀
  have hφ := ((chartTransition_contDiffAt d₀ d₁ (chartAt FourSpace d₀ x)
    ((chartAt FourSpace d₀).map_source hd₀) (by
      rw [hxinv]
      exact hd₁)).differentiableAt
      (by simp)).hasFDerivAt
  have hpoint : (radialCoordinateFlow g o c d₀ t z).1 = chartAt FourSpace d₀ x :=
    congrArg Prod.fst (radialCoordinateFlow_at_state g o c d₀ t p hc)
  rw [← hpoint] at hφ
  have hcomp := hφ.comp z hD₀.fst
  have hnew := hcomp.congr_of_eventuallyEq
    (radialCoordinateFlow_position_change_eventually g o c d₀ d₁ p t hc hd₀)
  have heval := congrArg (fun L : CotangentCoordinates →L[ℝ] FourSpace => L a)
    (hD₁.fst.unique hnew)
  change (fderiv ℝ (radialCoordinateFlow g o c d₁ t) z a).1 =
    fderiv ℝ (chartTransition d₀ d₁) (radialCoordinateFlow g o c d₀ t z).1
      ((fderiv ℝ (radialCoordinateFlow g o c d₀ t) z a).1) at heval
  rw [hpoint, ← chartTransitionMatrix_mulVec] at heval
  exact congrArg WithLp.ofLp heval

def radialVariationInFrame (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (e : FrameBundle g) (a : CotangentCoordinates) : Fin 4 → ℝ :=
  (frameChartMatrix g d e)⁻¹ *ᵥ WithLp.ofLp
    ((fderiv ℝ (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p) a).1)

theorem radialVariationInFrame_chart_independent (g : SmoothMetric M) (o : FrameOrientation g)
    (c d₀ d₁ : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (e : FrameBundle g) (a : CotangentCoordinates)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (he : e.base = (unitTangentRadialFlow g o t p).2.base)
    (hd₀ : e.base ∈ (chartAt FourSpace d₀).source)
    (hd₁ : e.base ∈ (chartAt FourSpace d₁).source) :
    radialVariationInFrame g o c d₀ p t e a = radialVariationInFrame g o c d₁ p t e a := by
  let E₀ := frameChartMatrix g d₀ e
  let E₁ := frameChartMatrix g d₁ e
  let A := chartTransitionMatrix d₀ d₁ (chartAt FourSpace d₀ e.base)
  let Y₀ := WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₀ t)
    (unitRadialCotangentState g c p) a).1)
  let Y₁ := WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₁ t)
    (unitRadialCotangentState g c p) a).1)
  have hY : Y₁ = A *ᵥ Y₀ := by
    simpa only [Y₀, Y₁, A, he] using radialCoordinateFlow_position_fderiv_change
      g o c d₀ d₁ p t hc (he ▸ hd₀) (he ▸ hd₁) a
  have hE : A * E₀ = E₁ := frameChartMatrix_change g d₀ d₁ e hd₀ hd₁
  have h₀ : IsUnit E₀.det := Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g d₀ e hd₀)
  have h₁ : IsUnit E₁.det := Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g d₁ e hd₁)
  have hvec : E₁ *ᵥ (E₀⁻¹ *ᵥ Y₀) = Y₁ := by
    rw [← hE, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ h₀, Matrix.mul_one, hY]
  change E₀⁻¹ *ᵥ Y₀ = E₁⁻¹ *ᵥ Y₁
  rw [← hvec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h₁, Matrix.one_mulVec]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification and integration of the actual Jacobi determinant with
its first-conjugate-point truncation. The family is the single global
solution attached to each actual frame, independent of endpoint time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def actualJacobiMatrix (g : SmoothMetric M) (hRic : RicciThree g)
    (p : ℝ × FrameBundle g) : NormalMatrix :=
  (actualJacobiSolution g hRic p.2).J p.1

theorem actualRegularJacobi_truncatedDensity_eq (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    (actualRegularJacobi g hRic e t).truncatedDensity =
      truncatedJacobiDensity (actualJacobiMatrix g hRic) (t, e) := by
  classical
  simp only [RegularJacobi.truncatedDensity, actualRegularJacobi_J,
    truncatedJacobiDensity, preconjugateSet, actualJacobiMatrix, Set.mem_ofPred_eq]
  rfl

theorem actualRegularJacobi_truncatedDensity_scaled (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (u : ℝ) :
    (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity =
      truncatedJacobiDensity (fun p => actualJacobiMatrix g hRic (Real.pi * p.1, p.2))
        (u, e) := by
  rw [truncatedJacobiDensity_rescale _ Real.pi Real.pi_pos]
  exact actualRegularJacobi_truncatedDensity_eq g hRic e _

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

private theorem actualJacobiDensity_integrable_of_continuous (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hJ : Continuous (actualJacobiMatrix g hRic)) (t : ℝ) :
    Integrable (fun e => (actualRegularJacobi g hRic e t).truncatedDensity)
      (canonicalFrameMeasure g o) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have h := integrable_truncatedJacobiDensity_slice (canonicalFrameMeasure g o)
    (actualJacobiMatrix g hRic) hJ t
  apply h.congr
  exact Filter.Eventually.of_forall (fun e =>
    (actualRegularJacobi_truncatedDensity_eq g hRic e t).symm)

private theorem actualJacobiDensity_intervalIntegrable_of_continuous (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hJ : Continuous (actualJacobiMatrix g hRic)) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u => ∫ e, (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
        ∂canonicalFrameMeasure g o) volume a b := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hJ' : Continuous
      (fun p : ℝ × FrameBundle g => actualJacobiMatrix g hRic (Real.pi * p.1, p.2)) :=
    hJ.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have h := intervalIntegrable_truncatedJacobiDensity_average
    (canonicalFrameMeasure g o) _ hJ' a b hab
  have heq : (fun u => ∫ e, truncatedJacobiDensity
      (fun p => actualJacobiMatrix g hRic (Real.pi * p.1, p.2)) (u, e)
        ∂canonicalFrameMeasure g o) =
      (fun u => ∫ e, (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
        ∂canonicalFrameMeasure g o) := by
    funext u
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun e =>
      (actualRegularJacobi_truncatedDensity_scaled g hRic e u).symm)
  rwa [heq] at h

theorem actualJacobiDensity_integrable (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) :
    Integrable (fun e => (actualRegularJacobi g hRic e t).truncatedDensity)
      (canonicalFrameMeasure g o) :=
  actualJacobiDensity_integrable_of_continuous g o hRic
    (actualJacobiJ_joint_continuous g hRic) t

theorem actualJacobiDensity_intervalIntegrable (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable
      (fun u => ∫ e, (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
        ∂canonicalFrameMeasure g o) volume a b :=
  actualJacobiDensity_intervalIntegrable_of_continuous g o hRic
    (actualJacobiJ_joint_continuous g hRic) a b hab

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual derivative of the complete radial flow, expressed in a
parallel orthonormal frame along its unit-speed geodesic. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def frameUnitRadialState {g : SmoothMetric M} (e : FrameBundle g) :
    PositiveRadius × UnitTangentBundle g := (⟨1, show (0 : ℝ) < 1 from zero_lt_one⟩, unitTangentOfFrame e)

def frameKineticCurve (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (t : ℝ) : CotangentCoordinates :=
  unitRadialCotangentState g c (unitTangentRadialFlow g o t (frameUnitRadialState e))

def frameKineticVariation (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : CotangentCoordinates :=
  fderiv ℝ (radialCoordinateFlow g o e.base c t)
    (unitRadialCotangentState g e.base (frameUnitRadialState e)) a

def frameGeodesicCoordinateCurve (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (t : ℝ) : FourSpace × FourSpace :=
  kineticVelocityCoordinates g c (frameKineticCurve g o c e t)

def frameGeodesicCoordinateVariation (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : FourSpace × FourSpace :=
  fderiv ℝ (kineticVelocityCoordinates g c) (frameKineticCurve g o c e t)
    (frameKineticVariation g o c e a t)

theorem frameUnitRadialState_flow (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    (unitTangentRadialFlow g o t (frameUnitRadialState e)).2 =
      unitTangentOfFrame (parallelFrameFlowMap g 0 t e) := by
  change unitTangentFlowMap g o (1 * t) (unitTangentOfFrame e) = _
  rw [one_mul, unitTangentFlowMap_of_frame g o t e he]

theorem frameKineticCurve_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    frameKineticCurve g o c e t =
      unitCotangentState g c 1 (unitTangentOfFrame (parallelFrameFlowMap g 0 t e)) := by
  change unitCotangentState g c 1
    (unitTangentRadialFlow g o t (frameUnitRadialState e)).2 = _
  rw [frameUnitRadialState_flow g o e he t]

theorem frameGeodesicCoordinateCurve_position (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    (frameGeodesicCoordinateCurve g o c e t).1 =
      chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base := by
  change (frameKineticCurve g o c e t).1 = _
  rw [frameKineticCurve_eq g o c e he t]
  rfl

theorem frameGeodesicCoordinateCurve_velocity (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    WithLp.ofLp (frameGeodesicCoordinateCurve g o c e t).2 =
      fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0 := by
  change WithLp.ofLp (raisedChartVelocity g c (frameKineticCurve g o c e t)) = _
  rw [frameKineticCurve_eq g o c e he t,
    raisedChartVelocity_unitCotangentState g c 1 _ hc, one_smul]
  rfl

theorem frameKineticCurve_hasDerivAt (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameKineticCurve g o c e)
      (cotangentHamiltonianField (kineticHamiltonian g c) (frameKineticCurve g o c e t)) t := by
  apply hasDerivAt_unitTangentRadial_cotangent g o c (frameUnitRadialState e) t
  simpa only [frameUnitRadialState_flow g o e he t, unitTangentOfFrame] using hc

theorem frameKineticVariation_hasDerivAt (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameKineticVariation g o c e a)
      (fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c))
        (frameKineticCurve g o c e t) (frameKineticVariation g o c e a t)) t := by
  have hd := radialCoordinateFlow_fderiv_hasDerivAt g o e.base c (frameUnitRadialState e) t
    (mem_chart_source FourSpace e.base) (by
      simpa only [frameUnitRadialState_flow g o e he t, unitTangentOfFrame] using hc)
  simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using! hd.clm_apply (hasDerivAt_const t a)

theorem frameGeodesicCoordinateCurve_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameGeodesicCoordinateCurve g o c e)
      (geodesicCoordinateField g c (frameGeodesicCoordinateCurve g o c e t)) t := by
  apply kinetic_geodesic_curve g c (frameKineticCurve g o c e) t
  · rw [frameKineticCurve_eq g o c e he t]
    exact (chartAt FourSpace c).map_source hc
  · exact frameKineticCurve_hasDerivAt g o c e he t hc

theorem frameGeodesicCoordinateVariation_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameGeodesicCoordinateVariation g o c e a)
      (fderiv ℝ (geodesicCoordinateField g c) (frameGeodesicCoordinateCurve g o c e t)
        (frameGeodesicCoordinateVariation g o c e a t)) t := by
  apply kinetic_geodesic_variation g c (frameKineticCurve g o c e)
    (frameKineticVariation g o c e a) t
  · rw [frameKineticCurve_eq g o c e he t]
    exact (chartAt FourSpace c).map_source hc
  · exact frameKineticCurve_hasDerivAt g o c e he t hc
  · exact frameKineticVariation_hasDerivAt g o c e he a t hc


theorem frameGeodesicCoordinateVariation_fst (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    (frameGeodesicCoordinateVariation g o c e a t).1 =
      (frameKineticVariation g o c e a t).1 := by
  have hp : (frameKineticCurve g o c e t).1 ∈ (chartAt FourSpace c).target := by
    rw [frameKineticCurve_eq g o c e he t]
    exact (chartAt FourSpace c).map_source hc
  change (fderiv ℝ (kineticVelocityCoordinates g c) _ _).1 = _
  rw [kineticVelocityCoordinates_fderiv g c _ _ hp]
  rfl

theorem frameGeodesic_normal_variation (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (geodesicNormalPosition g c (parallelFrameFlowMap g 0 · e)
      (frameGeodesicCoordinateVariation g o c e a))
      (geodesicNormalVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t) t ∧
    HasDerivAt (geodesicNormalVelocity g c (parallelFrameFlowMap g 0 · e)
      (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a))
      (-((1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) *ᵥ
        geodesicNormalPosition g c (parallelFrameFlowMap g 0 · e)
          (frameGeodesicCoordinateVariation g o c e a) t)) t := by
  apply actual_geodesic_normal_variation g c (parallelFrameFlowMap g 0 · e)
    (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t hc
  · exact frameGeodesicCoordinateCurve_position g o c e he t
  · exact frameGeodesicCoordinateCurve_velocity g o c e he t hc
  · exact frameGeodesicCoordinateCurve_hasDerivAt g o c e he t hc
  · exact frameGeodesicCoordinateVariation_hasDerivAt g o c e he a t hc
  · have h := parallelFrameCurveAt_fixedChart g c (parallelFrameFlowMap g 0 · e) t 0
      (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt hc
      (parallelFrameFlowMap_primitive g 0 e t)
    have hE := (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t h
    rw [frameGeodesicCoordinateCurve_position g o c e he t,
      frameGeodesicCoordinateCurve_velocity g o c e he t hc]
    exact fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual exterior derivative along parallel frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormExterior_covariant (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (e : FrameBundle g) (i j k : Fin 4) :
    twoFormFramedCovariantDerivative o (smoothOneFormExterior (o := o) u).val e ![i,j,k] =
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e
        ![i,j,k] -
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e
        ![i,k,j] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hD : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
  have hsub := (hD.parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k]).sub
    (hD.parallel_derivative γ 0 i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![k,j])
  have heq : (fun t => covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![j,k] -
      covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![k,j]) =
      fun t => twoFormFramedValue o (smoothOneFormExterior (o := o) u).val (γ t) ![j,k] := by
    funext t
    exact (smoothOneFormExterior_framed u (γ t) j k).symm
  change HasDerivAt (fun t =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![j,k] -
      covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![k,j]) _ 0 at hsub
  rw [heq] at hsub
  have hd := (smoothOneFormExterior (o := o) u).property.framedValue_parallel_derivative
    γ 0 i (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k]
  have h := hd.unique hsub
  rw [hzero] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic L2 pairing of actual smooth one-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance oneFormPairingCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def smoothOneFormL2Pairing (u v : smoothCovariantFields M 1) : ℝ :=
  ∫ e, ∑ i, covariantFieldFramed g u.val e ![i] * covariantFieldFramed g v.val e ![i]
    ∂canonicalFrameMeasure g o

theorem smoothOneForm_pairing_integrable (u v : smoothCovariantFields M 1) :
    Integrable (fun e => ∑ i, covariantFieldFramed g u.val e ![i] *
      covariantFieldFramed g v.val e ![i]) (canonicalFrameMeasure g o) := by
  apply integrable_finsetSum
  intro i _
  exact (((continuous_apply _).comp u.property.continuous_framed).mul
    ((continuous_apply _).comp v.property.continuous_framed)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem smoothOneFormL2Pairing_comm (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) u v = smoothOneFormL2Pairing (o := o) v u := by
  unfold smoothOneFormL2Pairing
  apply integral_congr_ae
  filter_upwards [] with e
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem smoothOneFormL2Pairing_add (u v w : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (u + v) w =
      smoothOneFormL2Pairing (o := o) u w + smoothOneFormL2Pairing (o := o) v w := by
  unfold smoothOneFormL2Pairing
  simp only [Submodule.coe_add, covariantFieldFramed_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  exact integral_add (smoothOneForm_pairing_integrable u w) (smoothOneForm_pairing_integrable v w)

theorem smoothOneFormL2Pairing_smul (r : ℝ) (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (r • u) v = r * smoothOneFormL2Pairing (o := o) u v := by
  unfold smoothOneFormL2Pairing
  simp only [Submodule.coe_smul, covariantFieldFramed_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum, integral_const_mul]

theorem smoothOneFormL2Pairing_self (u : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) u u =
      ∫ x, covariantFieldNormSq g u.val x ∂normalizedVolume g := by
  rw [oneForm_norm_integral (o := o)]
  simp only [smoothOneFormL2Pairing, pow_two]

theorem smoothOneFormL2Pairing_sub (u v w : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (u - v) w =
      smoothOneFormL2Pairing (o := o) u w - smoothOneFormL2Pairing (o := o) v w := by
  rw [sub_eq_add_neg, smoothOneFormL2Pairing_add, ← neg_one_smul ℝ v,
    smoothOneFormL2Pairing_smul]
  ring

theorem smoothOneFormL2Pairing_nonneg (u : smoothCovariantFields M 1) :
    0 ≤ smoothOneFormL2Pairing (o := o) u u := by
  apply integral_nonneg
  intro e
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

theorem smoothOneFormL2Pairing_definite (u : smoothCovariantFields M 1)
    (hu : smoothOneFormL2Pairing (o := o) u u = 0) : u = 0 := by
  apply oneForm_eq_zero_of_norm_integral (g := g) u
  rwa [smoothOneFormL2Pairing_self] at hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar first jet and its Dirichlet pairing.  The Hilbert space
below is the closure of smooth first jets, with the value coordinate retained;
no solvability or elliptic estimate is built into its definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- Smooth real scalar functions, with their pointwise vector-space structure. -/
def smoothScalarModule (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :
    Submodule ℝ (M → ℝ) where
  carrier := {a | ContMDiff I4 𝓘(ℝ, ℝ) ∞ a}
  zero_mem' := contMDiff_const
  add_mem' := fun ha hb => ha.add hb
  smul_mem' := fun c a ha => by
    change ContMDiff I4 𝓘(ℝ, ℝ) ∞ (c • a)
    simpa only [Pi.smul_apply, smul_eq_mul] using! contMDiff_const.mul ha

abbrev SmoothScalar := ↥(smoothScalarModule M)

private theorem smoothScalarData {μ : Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) (a : SmoothScalar (M := M)) :
    ScalarCovariantData d.toMetricGreenData a :=
  Classical.choice (d.scalarCalculus.toPetersenInput a a.property)

/-- Viewing a smooth scalar on the orthonormal frame bundle. -/
def smoothScalarValue (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] C(FrameBundle g, ℝ) where
  toFun a := ⟨fun e => a.val e.base, actual_scalarValue_continuous g a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each actual frame component of the scalar differential is linear. -/
def smoothScalarGradient {μ : Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) (i : Fin 4) :
    SmoothScalar (M := M) →ₗ[ℝ] C(FrameBundle g, ℝ) where
  toFun a := ⟨fun e => scalarGradient g a e i,
    actual_scalarGradient_continuous g a.property i⟩
  map_add' a b := by
    ext e
    obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
    change (d.toMetricGreenData.flow i).map 0 f = e at hf
    have h := ((smoothScalarData d (a + b)).derivativeValue i 0 f).unique
      (((smoothScalarData d a).derivativeValue i 0 f).add
        ((smoothScalarData d b).derivativeValue i 0 f))
    simpa only [hf] using! h
  map_smul' c a := by
    ext e
    obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
    change (d.toMetricGreenData.flow i).map 0 f = e at hf
    have h := ((smoothScalarData d (c • a)).derivativeValue i 0 f).unique
      (((smoothScalarData d a).derivativeValue i 0 f).const_mul c)
    simpa only [hf, Pi.smul_apply, smul_eq_mul] using! h

variable {μ : Measure (FrameBundle g)} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

abbrev ScalarL2 (g : SmoothMetric M) (μ : Measure (FrameBundle g)) := Lp ℝ 2 μ

def smoothScalarValueL2 (g : SmoothMetric M) (μ : Measure (FrameBundle g))
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] :
    SmoothScalar (M := M) →ₗ[ℝ] ScalarL2 g μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (smoothScalarValue g)

def smoothScalarGradientL2 (d : ParallelMetricData g μ) (i : Fin 4) :
    SmoothScalar (M := M) →ₗ[ℝ] ScalarL2 g μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (smoothScalarGradient d i)

/-- The actual scalar Dirichlet pairing in the frame measure. -/
def smoothScalarDirichlet (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) : ℝ :=
  ∑ i : Fin 4, inner ℝ (smoothScalarGradientL2 d i a) (smoothScalarGradientL2 d i b)

theorem smoothScalarDirichlet_eq_integral (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    smoothScalarDirichlet d a b =
      ∫ e, ∑ i, scalarGradient g a e i * scalarGradient g b e i ∂μ := by
  unfold smoothScalarDirichlet smoothScalarGradientL2
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousMap.inner_toLp, conj_trivial]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with e
    exact mul_comm _ _
  · intro i _
    exact ((actual_scalarGradient_continuous g a.property i).mul
      (actual_scalarGradient_continuous g b.property i)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

theorem smoothScalarDirichlet_green (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    smoothScalarDirichlet d a b = -(∫ e, a.val e.base * scalarLaplacian g b e ∂μ) := by
  rw [smoothScalarDirichlet_eq_integral]
  exact (smoothScalarData d a).scalar_pairing_green (smoothScalarData d b)

theorem smoothScalarDirichlet_nonneg (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) : 0 ≤ smoothScalarDirichlet d a a :=
  Finset.sum_nonneg (fun _i _ => real_inner_self_nonneg)

theorem smoothScalarDirichlet_symm (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) : smoothScalarDirichlet d a b = smoothScalarDirichlet d b a := by
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

/-- The value and four derivative coordinates, in a genuine Hilbert product. -/
abbrev ScalarJetL2 (g : SmoothMetric M) (μ : Measure (FrameBundle g)) :=
  PiLp 2 (fun _ : Option (Fin 4) => ScalarL2 g μ)

def smoothScalarFirstJet (d : ParallelMetricData g μ) :
    SmoothScalar (M := M) →ₗ[ℝ] ScalarJetL2 g μ :=
  (WithLp.linearEquiv 2 ℝ (Option (Fin 4) → ScalarL2 g μ)).symm.toLinearMap.comp
    (LinearMap.pi fun j => match j with
      | none => smoothScalarValueL2 g μ
      | some i => smoothScalarGradientL2 d i)

/-- Intrinsic first-order Sobolev space generated by actual smooth scalars. -/
def scalarH1 (d : ParallelMetricData g μ) : Submodule ℝ (ScalarJetL2 g μ) :=
  (LinearMap.range (smoothScalarFirstJet d)).topologicalClosure

instance scalarH1_complete (d : ParallelMetricData g μ) : CompleteSpace (scalarH1 d) :=
  (Submodule.isClosed_topologicalClosure
    (LinearMap.range (smoothScalarFirstJet d))).isComplete.completeSpace_coe

def scalarH1Value (d : ParallelMetricData g μ) : scalarH1 d →L[ℝ] ScalarL2 g μ :=
  (PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none).comp (scalarH1 d).subtypeL

def scalarH1Gradient (d : ParallelMetricData g μ) (i : Fin 4) :
    scalarH1 d →L[ℝ] ScalarL2 g μ :=
  (PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)).comp (scalarH1 d).subtypeL

def smoothScalarToH1 (d : ParallelMetricData g μ) (a : SmoothScalar (M := M)) :
    scalarH1 d :=
  ⟨smoothScalarFirstJet d a, Submodule.le_topologicalClosure _ ⟨a, rfl⟩⟩

theorem scalarH1_inner (d : ParallelMetricData g μ) (u v : scalarH1 d) :
    inner ℝ u v = inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
      ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
  change (∑ j : Option (Fin 4), inner ℝ (u.val j) (v.val j)) = _
  rw [Fintype.sum_option]
  rfl

@[simp] theorem scalarH1Value_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    scalarH1Value d (smoothScalarToH1 d a) = smoothScalarValueL2 g μ a := rfl

@[simp] theorem scalarH1Gradient_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    scalarH1Gradient d i (smoothScalarToH1 d a) = smoothScalarGradientL2 d i a := rfl

/-- The weak solution of the shifted scalar equation.  Its construction is
the Hilbert adjoint of value evaluation, so needs no elliptic premise. -/
def scalarShiftedSolution (d : ParallelMetricData g μ) : ScalarL2 g μ →L[ℝ] scalarH1 d :=
  (scalarH1Value d).adjoint

theorem scalarShiftedSolution_weak (d : ParallelMetricData g μ)
    (f : ScalarL2 g μ) (v : scalarH1 d) :
    inner ℝ (scalarH1Value d (scalarShiftedSolution d f)) (scalarH1Value d v) +
      ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarShiftedSolution d f))
        (scalarH1Gradient d i v) = inner ℝ f (scalarH1Value d v) := by
  rw [← scalarH1_inner]
  exact (scalarH1Value d).adjoint_inner_left v f

theorem scalarShiftedSolution_unique (d : ParallelMetricData g μ)
    (f : ScalarL2 g μ) (u : scalarH1 d)
    (hu : ∀ v : scalarH1 d,
      inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
        ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) =
          inner ℝ f (scalarH1Value d v)) :
    u = scalarShiftedSolution d f := by
  apply ext_inner_left ℝ
  intro v
  calc
    inner ℝ v u = inner ℝ u v := real_inner_comm _ _
    _ = inner ℝ f (scalarH1Value d v) := (scalarH1_inner d u v).trans (hu v)
    _ = inner ℝ (scalarShiftedSolution d f) v :=
      ((scalarH1_inner d (scalarShiftedSolution d f) v).trans
        (scalarShiftedSolution_weak d f v)).symm
    _ = inner ℝ v (scalarShiftedSolution d f) := real_inner_comm _ _

/-- The value of the weak shifted solution, as an operator on scalar `L²`. -/
def scalarWeakResolvent (d : ParallelMetricData g μ) : ScalarL2 g μ →L[ℝ] ScalarL2 g μ :=
  (scalarH1Value d).comp (scalarShiftedSolution d)

theorem scalarWeakResolvent_symmetric (d : ParallelMetricData g μ)
    (f h : ScalarL2 g μ) :
    inner ℝ (scalarWeakResolvent d f) h = inner ℝ f (scalarWeakResolvent d h) := by
  change inner ℝ (scalarH1Value d ((scalarH1Value d).adjoint f)) h =
    inner ℝ f (scalarH1Value d ((scalarH1Value d).adjoint h))
  rw [← (scalarH1Value d).adjoint_inner_right,
    (scalarH1Value d).adjoint_inner_left]

theorem scalarWeakResolvent_nonneg (d : ParallelMetricData g μ) (f : ScalarL2 g μ) :
    0 ≤ inner ℝ f (scalarWeakResolvent d f) := by
  change 0 ≤ inner ℝ f (scalarH1Value d ((scalarH1Value d).adjoint f))
  rw [← (scalarH1Value d).adjoint_inner_left]
  exact real_inner_self_nonneg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Frame-bundle integral realizations of the intrinsic two-form pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem frameTensorPairing_three (A B : CovariantCoordinates 3) :
    frameTensorPairing A B = ∑ i, ∑ j, ∑ k, A ![i,j,k] * B ![i,j,k] := by
  unfold frameTensorPairing
  simp only [sum_tensor_indices_cons, Fintype.sum_unique]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_inner (u v : M → TwoFormFour) (e : FrameBundle g) :
    inner ℝ (twoFormFrameValue o u e) (twoFormFrameValue o v e) =
      inner ℝ (u e.base) (v e.base) :=
  (twoFormFrameIsometry _ ((o.frame e.base).changeMatrix_orthogonal e.frame)).inner_map_map _ _

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

theorem smoothTwoFormL2Inner_eq_frame (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner u v = ∫ e,
      inner ℝ (twoFormFrameValue o u.val e) (twoFormFrameValue o v.val e)
        ∂canonicalFrameMeasure g o := by
  unfold smoothTwoFormL2Inner
  rw [← canonicalFrameMeasure_integral_base g o _ (smoothTwoForm_pairing_integrable u v)]
  apply integral_congr_ae
  filter_upwards [] with e
  exact (twoFormFrameValue_inner u.val v.val e).symm

theorem smoothTwoFormCurvatureInner_eq_frame (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormCurvature u) v = ∫ e,
      inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
        (twoFormFrameValue o u.val e)) (twoFormFrameValue o v.val e)
          ∂canonicalFrameMeasure g o := by
  rw [smoothTwoFormL2Inner_eq_frame]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [← twoFormCurvatureField_frame]
  rfl

theorem smoothTwoFormCovariantEnergy_eq_frame (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v = (1 / 2 : ℝ) * ∫ e,
      ∑ i, ∑ j, ∑ k, twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
        twoFormFramedCovariantDerivative o v.val e ![i,j,k] ∂canonicalFrameMeasure g o := by
  unfold smoothTwoFormCovariantEnergy
  rw [← canonicalFrameMeasure_integral_base g o _ (smoothTwoFormCovariantPairing_integrable u v)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [twoFormCovariantPairing_eq_frame, frameTensorPairing_three]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form rough Green identity from the actual invariant parallel
flows. No integration-by-parts input is added to the geometry. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormGreen_compactFrame : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem smoothTwoForm_direction_green (hRic : RicciThree g) (u v : smoothTwoForms o)
    (i : Fin 4) (a : Fin 2 → Fin 4) :
    (∫ e, twoFormFramedCovariantDerivative o u.val e (Fin.cons i a) *
      twoFormFramedCovariantDerivative o v.val e (Fin.cons i a) ∂canonicalFrameMeasure g o) =
      -(∫ e, twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons i a))
        ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedValue o u.val e a,
    (continuous_apply a).comp u.property.continuous_framedValue⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o u.val e (Fin.cons i a),
    (continuous_apply _).comp u.property.continuous_framedCovariantDerivative⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o v.val e (Fin.cons i a),
    (continuous_apply _).comp v.property.continuous_framedCovariantDerivative⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons i a)),
    (continuous_apply _).comp v.property.continuous_framedSecondDerivative⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.framedValue_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) a
  · intro t e
    exact v.property.framedCovariant_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) (Fin.cons i a)

theorem smoothTwoForm_rough_green (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v = -(1 / 2 : ℝ) *
      ∫ e, frameTensorPairing (twoFormFramedValue o u.val e)
        (twoFormFramedRoughTrace o v.val e) ∂canonicalFrameMeasure g o := by
  let μ := canonicalFrameMeasure g o
  let A : Fin 4 → (Fin 2 → Fin 4) → FrameBundle g → ℝ := fun i a e =>
    twoFormFramedCovariantDerivative o u.val e (Fin.cons i a) *
      twoFormFramedCovariantDerivative o v.val e (Fin.cons i a)
  let B : Fin 4 → (Fin 2 → Fin 4) → FrameBundle g → ℝ := fun i a e =>
    twoFormFramedValue o u.val e a *
      twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons i a))
  have hA (i : Fin 4) (a : Fin 2 → Fin 4) : Integrable (A i a) μ :=
    (((continuous_apply _).comp u.property.continuous_framedCovariantDerivative).mul
      ((continuous_apply _).comp v.property.continuous_framedCovariantDerivative)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB (i : Fin 4) (a : Fin 2 → Fin 4) : Integrable (B i a) μ :=
    (((continuous_apply _).comp u.property.continuous_framedValue).mul
      ((continuous_apply _).comp v.property.continuous_framedSecondDerivative)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : (∫ e, ∑ i, ∑ a, A i a e ∂μ) = -(∫ e, ∑ a, ∑ i, B i a e ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hA i a)),
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun i _ => hB i a))]
    simp_rw [integral_finsetSum _ (fun a _ => hA _ a),
      integral_finsetSum _ (fun i _ => hB i _)]
    have hi (i : Fin 4) (a : Fin 2 → Fin 4) : (∫ e, A i a e ∂μ) = -(∫ e, B i a e ∂μ) :=
      smoothTwoForm_direction_green hRic u v i a
    simp_rw [hi, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have he : (fun e : FrameBundle g => twoFormCovariantPairing o u.val v.val e.base) =
      fun e => (1 / 2 : ℝ) * ∑ i, ∑ a, A i a e := by
    funext e
    rw [twoFormCovariantPairing_eq_frame]
    unfold frameTensorPairing
    rw [sum_tensor_indices_cons]
  unfold smoothTwoFormCovariantEnergy
  rw [← canonicalFrameMeasure_integral_base g o _ (smoothTwoFormCovariantPairing_integrable u v),
    he, integral_const_mul, hg]
  have hr : (fun e => ∑ a, ∑ i, B i a e) = fun e =>
      frameTensorPairing (twoFormFramedValue o u.val e) (twoFormFramedRoughTrace o v.val e) := by
    funext e
    simp only [B, frameTensorPairing, twoFormFramedRoughTrace, Finset.mul_sum]
  rw [hr]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The polar-volume inequality for the metric and its Jacobi fields. See
Petersen, Riemannian Geometry, §§5.7, 6.3 and 7.1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def ActualJacobiPolarInput (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : Prop :=
  volumeRatio g ≤ (3 * Real.pi / 4) *
    ((∫ u in (0 : ℝ)..(5 / 8), ∫ e,
        (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
          ∂canonicalFrameMeasure g o) +
      ∫ u in (5 / 8 : ℝ)..1, ∫ e,
        (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
          ∂canonicalFrameMeasure g o)

def actualJacobiRealizationData (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpolar : ActualJacobiPolarInput g o hRic) :
    JacobiRealizationData (canonicalParallelMetricData g o hRic).toMetricGreenData where
  jacobi u e := actualRegularJacobi g hRic e (Real.pi * u)
  curvature u e r := by
    rw [actualRegularJacobi_R]
    rfl
  densityIntegrable u _ _ := actualJacobiDensity_integrable g o hRic (Real.pi * u)
  firstIntegral := actualJacobiDensity_intervalIntegrable g o hRic 0 (5 / 8) (by norm_num)
  secondIntegral := actualJacobiDensity_intervalIntegrable g o hRic (5 / 8) 1 (by norm_num)
  polar := hpolar

def actualCanonicalData_of_polar (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g)
    (poisson : PetersenPoissonInput g (canonicalFrameMeasure g o))
    (hpolar : ActualJacobiPolarInput g o hRic)
    (gap : GurskyLeBrunGapInput g o) (hodge : GurskyLeBrunHodgeInput g o)
    (model : DerdzinskiHitchinInput g o) : PublishedOrientedData g o :=
  actualCanonicalData g o hRic poisson (actualJacobiRealizationData g o hRic hpolar)
    gap hodge model

variable [SecondCountableTopology M] [ConnectedSpace M]

theorem models_of_actual_polar_data (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g)
    (poisson : PetersenPoissonInput g (canonicalFrameMeasure g o))
    (hpolar : ActualJacobiPolarInput g o hRic)
    (gap : GurskyLeBrunGapInput g o) (hodge : GurskyLeBrunHodgeInput g o)
    (model : DerdzinskiHitchinInput g o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) :=
  (actualCanonicalData_of_polar g o hRic poisson hpolar gap hodge model).models
    hRic hEinstein hpositive

end
end PositiveEinsteinFour.Geometry
end


section

/-! Before the first conjugate point the Jacobi determinant is positive.
The proof removes the initial zero by `dslope`, then uses continuity and
invertibility on the whole closed interval. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

private theorem positive_of_continuousOn_nonzero (f : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hf : ContinuousOn f (Icc 0 t)) (hzero : 0 < f 0)
    (hne : ∀ s ∈ Icc 0 t, f s ≠ 0) : 0 < f t := by
  by_contra hnot
  have hle : f t ≤ 0 := le_of_not_gt hnot
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' ht hf ⟨hle, hzero.le⟩
  exact hne s hs hfs

theorem jacobi_det_pos_of_preconjugate (J : ℝ → NormalMatrix) (t : ℝ)
    (ht : 0 < t) (hc : ContinuousOn J (Icc 0 t))
    (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (J s)) :
    0 < (J t).det := by
  have hnorm := normalizedJacobi_continuousOn hc hJ
  have hunit := normalizedJacobi_isUnit hJ0 hJ hpre
  have hdet : Continuous (fun A : NormalMatrix => A.det) := continuous_id.matrix_det
  have hp : 0 < (normalizedJacobi J t).det := by
    apply positive_of_continuousOn_nonzero (fun s => (normalizedJacobi J s).det) t ht.le
      (hdet.comp_continuousOn hnorm)
    · rw [normalizedJacobi_zero hJ, Matrix.det_one]
      norm_num
    · intro s hs
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (hunit s hs)).ne_zero
  rw [normalizedJacobi_pos hJ0 ht.ne', Matrix.det_smul, Fintype.card_fin] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr ht) 3)).mp hp

theorem MatrixJacobiSolution.det_pos_of_preconjugate {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (t : ℝ) (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    0 < (d.J t).det := by
  apply jacobi_det_pos_of_preconjugate d.J t ht d.continuous_J.continuousOn
    d.initial_position
  · simpa only [d.initial_velocity] using d.position_derivative 0
  · exact hpre

theorem RegularJacobi.det_pos_of_preconjugate {t : ℝ} (d : RegularJacobi t)
    (ht : 0 < t) (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    0 < (d.J t).det := by
  apply jacobi_det_pos_of_preconjugate d.J t ht
    (fun s hs => (d.position_derivative s hs).continuousAt.continuousWithinAt)
    d.initial_position
  · simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  · exact hpre

theorem RegularJacobi.truncatedDensity_nonneg {t : ℝ} (d : RegularJacobi t)
    (ht : 0 ≤ t) : 0 ≤ d.truncatedDensity := by
  classical
  unfold RegularJacobi.truncatedDensity
  split_ifs with hpre
  · by_cases ht0 : t = 0
    · subst t
      rw [d.initial_position, Matrix.det_zero]
    · exact (d.det_pos_of_preconjugate (lt_of_le_of_ne ht (Ne.symm ht0)) hpre).le
  · exact le_rfl

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Jacobi
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_det_pos_of_preconjugate (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    0 < ((actualJacobiSolution g hRic e).J t).det :=
  (actualJacobiSolution g hRic e).det_pos_of_preconjugate t ht hpre

theorem actualJacobi_abs_det_eq_truncatedDensity (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (t : ℝ) (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    |((actualJacobiSolution g hRic e).J t).det| =
      (actualRegularJacobi g hRic e t).truncatedDensity := by
  classical
  have hp : ∀ s, 0 < s → s ≤ t → IsUnit ((actualRegularJacobi g hRic e t).J s) := by
    simpa only [actualRegularJacobi_J] using hpre
  rw [RegularJacobi.truncatedDensity, ite_eq_left hp, actualRegularJacobi_J]
  exact abs_of_pos (actualJacobi_det_pos_of_preconjugate g hRic e t ht hpre)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local normal Jacobi equations glue to a global equation: the
position components are chart independent, and the velocity is their
derivative. No chart is required to contain an entire geodesic. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def actualNormalVariationPosition (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : Fin 3 → ℝ := fun i =>
  radialVariationInFrame g o e.base (parallelFrameFlowMap g 0 t e).base
    (frameUnitRadialState e) t (parallelFrameFlowMap g 0 t e) a i.succ

def actualNormalVariationVelocity (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (a : CotangentCoordinates) : ℝ → Fin 3 → ℝ :=
  deriv (actualNormalVariationPosition g o e a)

theorem actualNormalVariationPosition_eq_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualNormalVariationPosition g o e a t =
      geodesicNormalPosition g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateVariation g o c e a) t := by
  have hb : (parallelFrameFlowMap g 0 t e).base =
      (unitTangentRadialFlow g o t (frameUnitRadialState e)).2.base :=
    (congrArg UnitTangentBundle.base (frameUnitRadialState_flow g o e he t)).symm
  have h := radialVariationInFrame_chart_independent g o e.base
    (parallelFrameFlowMap g 0 t e).base c (frameUnitRadialState e) t
    (parallelFrameFlowMap g 0 t e) a (mem_chart_source FourSpace e.base) hb
    (mem_chart_source FourSpace _) hc
  funext i
  change radialVariationInFrame g o e.base (parallelFrameFlowMap g 0 t e).base
      (frameUnitRadialState e) t (parallelFrameFlowMap g 0 t e) a i.succ =
    ((frameChartMatrix g c (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ WithLp.ofLp
      (frameGeodesicCoordinateVariation g o c e a t).1) i.succ
  rw [frameGeodesicCoordinateVariation_fst g o c e he a t hc]
  exact congrFun h i.succ

theorem actualNormalVariationPosition_eventually_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualNormalVariationPosition g o e a =ᶠ[𝓝 t]
      geodesicNormalPosition g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateVariation g o c e a) := by
  have hnear := ((continuous_frameBase g).comp
    (parallelFrameFlowMap_curve_continuous g 0 e)).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
  filter_upwards [hnear] with s hs
  exact actualNormalVariationPosition_eq_chart g o c e he a s hs

theorem actualNormalVariationPosition_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ) :
    HasDerivAt (actualNormalVariationPosition g o e a)
      (actualNormalVariationVelocity g o e a t) t := by
  let c := (parallelFrameFlowMap g 0 t e).base
  have hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have h := (frameGeodesic_normal_variation g o c e he a t hc).1.congr_of_eventuallyEq
    (actualNormalVariationPosition_eventually_chart g o c e he a t hc)
  exact h.differentiableAt.hasDerivAt

theorem actualNormalVariationVelocity_eq_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualNormalVariationVelocity g o e a t =
      geodesicNormalVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t := by
  exact ((frameGeodesic_normal_variation g o c e he a t hc).1.congr_of_eventuallyEq
    (actualNormalVariationPosition_eventually_chart g o c e he a t hc)).deriv

theorem actualNormalVariationVelocity_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ) :
    HasDerivAt (actualNormalVariationVelocity g o e a)
      (-((1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) *ᵥ
        actualNormalVariationPosition g o e a t)) t := by
  let c := (parallelFrameFlowMap g 0 t e).base
  have hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have hnear := ((continuous_frameBase g).comp
    (parallelFrameFlowMap_curve_continuous g 0 e)).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
  have heq : actualNormalVariationVelocity g o e a =ᶠ[𝓝 t]
      geodesicNormalVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) := by
    filter_upwards [hnear] with s hs
    exact actualNormalVariationVelocity_eq_chart g o c e he a s hs
  have h := (frameGeodesic_normal_variation g o c e he a t hc).2.congr_of_eventuallyEq heq
  rw [← actualNormalVariationPosition_eq_chart g o c e he a t hc] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 Hilbert completion of smooth covariant one-forms.
The completion uses the definite intrinsic metric pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

structure SmoothL2OneForm (_o : FrameOrientation g) where
  toSmooth : smoothCovariantFields M 1

def smoothL2OneFormEquiv (o : FrameOrientation g) :
    SmoothL2OneForm o ≃ smoothCovariantFields M 1 where
  toFun := SmoothL2OneForm.toSmooth
  invFun := SmoothL2OneForm.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CoeOut (SmoothL2OneForm o) (smoothCovariantFields M 1) := ⟨SmoothL2OneForm.toSmooth⟩

instance : Zero (SmoothL2OneForm o) := ⟨⟨0⟩⟩
instance : Add (SmoothL2OneForm o) := ⟨fun u v => ⟨u.toSmooth + v.toSmooth⟩⟩
instance : Neg (SmoothL2OneForm o) := ⟨fun u => ⟨-u.toSmooth⟩⟩
instance : Sub (SmoothL2OneForm o) := ⟨fun u v => ⟨u.toSmooth - v.toSmooth⟩⟩
instance : SMul ℕ (SmoothL2OneForm o) := ⟨fun r u => ⟨r • u.toSmooth⟩⟩
instance : SMul ℤ (SmoothL2OneForm o) := ⟨fun r u => ⟨r • u.toSmooth⟩⟩
instance : SMul ℝ (SmoothL2OneForm o) := ⟨fun r u => ⟨r • u.toSmooth⟩⟩

instance : AddCommGroup (SmoothL2OneForm o) :=
  Function.Injective.addCommGroup SmoothL2OneForm.toSmooth (smoothL2OneFormEquiv o).injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def smoothL2OneFormAddHom : SmoothL2OneForm o →+ smoothCovariantFields M 1 where
  toFun := SmoothL2OneForm.toSmooth
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℝ (SmoothL2OneForm o) :=
  Function.Injective.module ℝ smoothL2OneFormAddHom (smoothL2OneFormEquiv o).injective
    (fun _ _ => rfl)

instance smoothOneFormInnerCore : InnerProductSpace.Core ℝ (SmoothL2OneForm o) where
  inner u v := smoothOneFormL2Pairing (o := o) u v
  conj_inner_symm u v := by
    simpa only [conj_trivial] using smoothOneFormL2Pairing_comm (o := o) v u
  re_inner_nonneg u := smoothOneFormL2Pairing_nonneg u.toSmooth
  add_left u v w := smoothOneFormL2Pairing_add u.toSmooth v.toSmooth w.toSmooth
  smul_left u v r := by
    change smoothOneFormL2Pairing (o := o) (r • (u : smoothCovariantFields M 1)) v =
      r * smoothOneFormL2Pairing (o := o) u v
    exact smoothOneFormL2Pairing_smul r u.toSmooth v.toSmooth
  definite u hu := by
    apply (smoothL2OneFormEquiv o).injective
    exact smoothOneFormL2Pairing_definite u.toSmooth hu

instance smoothOneFormNormedAddCommGroup : NormedAddCommGroup (SmoothL2OneForm o) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance smoothOneFormInnerProductSpace : InnerProductSpace ℝ (SmoothL2OneForm o) :=
  InnerProductSpace.ofCore _

theorem smoothOneForm_inner_eq (u v : SmoothL2OneForm o) :
    inner ℝ u v = smoothOneFormL2Pairing (o := o) u v := rfl

theorem smoothOneForm_norm_sq (u : SmoothL2OneForm o) :
    ‖u‖ ^ 2 = ∫ x, covariantFieldNormSq g (u : smoothCovariantFields M 1).val x
      ∂normalizedVolume g := by
  rw [← real_inner_self_eq_norm_sq]
  exact smoothOneFormL2Pairing_self u.toSmooth

def OneFormL2 (o : FrameOrientation g) := UniformSpace.Completion (SmoothL2OneForm o)
  deriving NormedAddCommGroup, NormedSpace ℝ, InnerProductSpace ℝ, CompleteSpace

def smoothOneFormToL2 : SmoothL2OneForm o →ₗᵢ[ℝ] OneFormL2 o :=
  UniformSpace.Completion.toComplₗᵢ

theorem smoothOneFormToL2_dense : DenseRange (smoothOneFormToL2 (o := o)) :=
  UniformSpace.Completion.denseRange_coe

theorem smoothOneFormToL2_injective : Function.Injective (smoothOneFormToL2 (o := o)) :=
  (smoothOneFormToL2 (o := o)).injective

theorem smoothOneFormToL2_inner (u v : SmoothL2OneForm o) :
    inner ℝ (smoothOneFormToL2 u) (smoothOneFormToL2 v) =
      smoothOneFormL2Pairing (o := o) u v :=
  UniformSpace.Completion.inner_coe u v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized Weyl cube root is an actual smooth base scalar.
Its moments and Dirichlet energy agree with the frame quantities in the
regularized gap argument. The sharp scalar inequality remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- Positive regularization makes the Weyl cube root smooth even on its zero set. -/
def regularizedPlusWeylScalar (o : FrameOrientation g) (ε : ℝ) (hε : 0 < ε) :
    SmoothScalar (M := M) := by
  refine ⟨fun x => (plusNorm o x ^ 2 + ε ^ 2) ^ (1 / 6 : ℝ), ?_⟩
  intro x
  have hp : 0 < plusNorm o x ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  exact (Real.contDiffAt_rpow_const_of_ne hp.ne').comp_contMDiffAt
    (f := fun x : M => plusNorm o x ^ 2 + ε ^ 2)
    ((actual_plusNorm_square_smooth o).add contMDiff_const).contMDiffAt

theorem regularizedPlusWeylScalar_frame (o : FrameOrientation g)
    (ε : ℝ) (hε : 0 < ε) (e : FrameBundle g) (he : e ∈ o.positive) :
    (regularizedPlusWeylScalar o ε hε).val e.base =
      regularizedWeylRoot ε (plusWeyl g e.base e.frame) := by
  change (plusNorm o e.base ^ 2 + ε ^ 2) ^ (1 / 6 : ℝ) = _
  rw [regularizedWeylRoot_eq, actual_plusNorm_frame o e he]

theorem regularizedPlusWeylScalar_gradient {μ : Measure (FrameBundle g)}
    (p : ParallelMetricData g μ) (o : FrameOrientation g)
    (hflow : OrientationPreservingFlow p.toMetricGreenData o)
    (ε : ℝ) (hε : 0 < ε) (e : FrameBundle g) (he : e ∈ o.positive)
    (i : Fin 4) :
    scalarGradient g (regularizedPlusWeylScalar o ε hε).val e i =
      p.toMetricGreenData.weylRootFirstField ε hε i e := by
  let a := regularizedPlusWeylScalar o ε hε
  let s : ScalarCovariantData p.toMetricGreenData a.val :=
    Classical.choice (p.scalarCalculus.toPetersenInput a.val a.property)
  exact scalarGradient_eq_of_frame_derivative s o hflow
    (p.toMetricGreenData.weylRootField ε)
    (fun i => p.toMetricGreenData.weylRootFirstField ε hε i)
    (regularizedPlusWeylScalar_frame o ε hε)
    (p.toMetricGreenData.regularizedWeylRoot_derivative ε hε) e he i

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance weylScalarFrameCompact : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem regularizedPlusWeylScalar_moment (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o))
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (∫ e, p.toMetricGreenData.weylRootField ε e ^ n ∂canonicalFrameMeasure g o) =
      ∫ x, (regularizedPlusWeylScalar o ε hε).val x ^ n ∂normalizedVolume g := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  calc
    _ = ∫ e : FrameBundle g,
        (regularizedPlusWeylScalar o ε hε).val e.base ^ n
          ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      rw [regularizedPlusWeylScalar_frame o ε hε e he]
      rfl
    _ = _ := canonicalFrameMeasure_integral_base g o _
      (((regularizedPlusWeylScalar o ε hε).property.continuous.pow n).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

theorem regularizedPlusWeylScalar_dirichlet (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o))
    (hflow : OrientationPreservingFlow p.toMetricGreenData o)
    (ε : ℝ) (hε : 0 < ε) :
    smoothScalarDirichlet p (regularizedPlusWeylScalar o ε hε)
      (regularizedPlusWeylScalar o ε hε) =
      ∫ e, ∑ i, p.toMetricGreenData.weylRootFirstField ε hε i e ^ 2
        ∂canonicalFrameMeasure g o := by
  rw [smoothScalarDirichlet_eq_integral]
  apply integral_congr_ae
  filter_upwards [canonicalFrameMeasure_supported g o] with e he
  apply Finset.sum_congr rfl
  intro i _
  rw [regularizedPlusWeylScalar_gradient p o hflow ε hε e he i, pow_two]

/-- The sharp scalar inequality in normalized base volume, with the actual
Dirichlet pairing. Its geometric proof is independent of this transfer. -/
def SharpScalarSobolev (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o)) : Prop :=
  ∀ a : SmoothScalar (M := M),
    Real.sqrt (∫ x, a.val x ^ 4 ∂normalizedVolume g) ≤
      (∫ x, a.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet p a a / 2

theorem sharpScalarSobolev_regularized (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o))
    (hflow : OrientationPreservingFlow p.toMetricGreenData o)
    (hsharp : SharpScalarSobolev o p) (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (∫ e, p.toMetricGreenData.weylRootField ε e ^ 4
      ∂canonicalFrameMeasure g o) ≤
      (∫ e, p.toMetricGreenData.weylRootField ε e ^ 2
        ∂canonicalFrameMeasure g o) +
      (∫ e, ∑ i, p.toMetricGreenData.weylRootFirstField ε hε i e ^ 2
        ∂canonicalFrameMeasure g o) / 2 := by
  rw [regularizedPlusWeylScalar_moment o p ε hε 4,
    regularizedPlusWeylScalar_moment o p ε hε 2,
    ← regularizedPlusWeylScalar_dirichlet o p hflow ε hε]
  exact hsharp (regularizedPlusWeylScalar o ε hε)

theorem canonicalParallelMetricData_orientation (o : FrameOrientation g)
    (hRic : RicciThree g) :
    OrientationPreservingFlow (canonicalParallelMetricData g o hRic).toMetricGreenData o := by
  intro i t e
  exact ((canonicalParallelMetricData g o hRic).flow i).orientation_preserving
    (fun e => actualParallelMetricData_zero g (canonicalFrameMeasure g o)
      (parallelFrameFlowMap_measurePreserving g o) hRic i e) o t e

/-- Actual smooth scalar Sobolev suffices for the Weyl gap. No special
Sobolev premise on frame fields or their derivatives is needed. -/
theorem plus_gap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hsharp : SharpScalarSobolev o (canonicalParallelMetricData g o hRic))
    (hnonzero : ∃ x, plusNorm o x ≠ 0) :
    1 ≤ ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
  apply plus_gap_of_regularized_sharp_sobolev g o
    (canonicalParallelMetricData g o hRic).toMetricGreenData
  · exact sharpScalarSobolev_regularized o (canonicalParallelMetricData g o hRic)
      (canonicalParallelMetricData_orientation o hRic) hsharp
  · exact hnonzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local C1 representatives of one actual L2 function agree on
overlaps by full support of Riemannian volume, and hence glue globally. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The gluing uses only the actual full-support volume and local smooth
representatives.  No global C1 regularity or elliptic premise is assumed. -/
theorem scalar_C1_representative_of_local (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g))
    (hlocal : ∀ x : M, ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) 1 f U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] f) :
    ∃ F : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) 1 F ∧ F =ᵐ[normalizedVolume g] b := by
  let := normalizedVolume_isOpenPosMeasure g
  choose U f hU hx hf hb using hlocal
  let F : M → ℝ := fun x => f x x
  have hagree (x y : M) (hy : y ∈ U x) : F y = f x y := by
    have hb₁ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hb y)
    have hb₂ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hb x)
    have heq : EqOn (f y) (f x) (U y ∩ U x) :=
      Measure.eqOn_open_of_ae_eq (hb₁.symm.trans hb₂) ((hU y).inter (hU x))
        ((hf y).continuousOn.mono inter_subset_left)
        ((hf x).continuousOn.mono inter_subset_right)
    exact heq ⟨hx y, hy⟩
  have hF : ContMDiff I4 𝓘(ℝ, ℝ) 1 F := by
    intro x
    apply ((hf x).contMDiffAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq
    filter_upwards [(hU x).mem_nhds (hx x)] with y hy
    exact hagree x y hy
  refine ⟨F, hF, ?_⟩
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have heach (x : M) : ∀ᵐ y ∂normalizedVolume g, y ∈ U x → F y = b y := by
    have he := (ae_restrict_iff' (hU x).measurableSet).mp (hb x)
    filter_upwards [he] with y hy
    intro hyU
    exact (hagree x y hyU).trans (hy hyU).symm
  have hfin : ∀ᵐ y ∂normalizedVolume g, ∀ x : s, y ∈ U x → F y = b y :=
    ae_all_iff.mpr (fun x => heach x)
  filter_upwards [hfin] with y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact hy ⟨x, hxs⟩ hyx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported Euclidean test functions inside a chart extend to
genuine global smooth scalar tests, by zero outside that chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarChartLift (c : M) (ψ : FourSpace → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ (chartAt FourSpace c).source then ψ (chartAt FourSpace c x) else 0

omit [IsManifold I4 ∞ M] in
theorem scalarChartLift_on_source (c : M) (ψ : FourSpace → ℝ) {x : M}
    (hx : x ∈ (chartAt FourSpace c).source) :
    scalarChartLift c ψ x = ψ (chartAt FourSpace c x) := by
  simp only [scalarChartLift, ite_eq_left hx]

omit [IsManifold I4 ∞ M] in
theorem scalarChartLift_symm (c : M) (ψ : FourSpace → ℝ) {z : FourSpace}
    (hz : z ∈ (chartAt FourSpace c).target) :
    scalarChartLift c ψ ((chartAt FourSpace c).symm z) = ψ z := by
  rw [scalarChartLift_on_source c ψ ((chartAt FourSpace c).map_target hz),
    (chartAt FourSpace c).right_inv hz]

omit [IsManifold I4 ∞ M] in
theorem scalarChartLift_support (c : M) (ψ : FourSpace → ℝ) :
    support (scalarChartLift c ψ) ⊆ (chartAt FourSpace c).symm '' tsupport ψ := by
  classical
  intro x hx
  by_cases hs : x ∈ (chartAt FourSpace c).source
  · refine ⟨chartAt FourSpace c x, subset_closure ?_, (chartAt FourSpace c).left_inv hs⟩
    simpa only [mem_support, scalarChartLift, ite_eq_left hs] using hx
  · exact False.elim (hx (by simp only [scalarChartLift, ite_eq_right hs]))

theorem scalarChartLift_smooth [T2Space M] (c : M) (ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (scalarChartLift c ψ) := by
  let K := (chartAt FourSpace c).symm '' tsupport ψ
  have hK : IsCompact K := hc.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hs)
  have hKs : K ⊆ (chartAt FourSpace c).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (chartAt FourSpace c).map_target (hs hz)
  intro x
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · have h := hψ.contMDiff.contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hx)
    apply h.congr_of_eventuallyEq
    filter_upwards [(chartAt FourSpace c).open_source.mem_nhds hx] with y hy
    exact scalarChartLift_on_source c ψ hy
  · have hxK : x ∉ K := fun hxK => hx (hKs hxK)
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact notMem_support.mp (fun h => hy (scalarChartLift_support c ψ h))

def scalarChartTest [T2Space M] (c : M) (ψ : FourSpace → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) : SmoothScalar (M := M) :=
  ⟨scalarChartLift c ψ, scalarChartLift_smooth c ψ hψ hc hs⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local continuous representatives of one actual L2 function agree on
overlaps by full support of Riemannian volume, and hence glue globally. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The gluing uses only the actual full-support volume and local smooth
representatives.  No global continuity or elliptic premise is assumed. -/
theorem scalar_continuous_representative_of_local (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g))
    (hlocal : ∀ x : M, ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContinuousOn f U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] f) :
    ∃ F : M → ℝ, Continuous F ∧ F =ᵐ[normalizedVolume g] b := by
  let := normalizedVolume_isOpenPosMeasure g
  choose U f hU hx hf hb using hlocal
  let F : M → ℝ := fun x => f x x
  have hagree (x y : M) (hy : y ∈ U x) : F y = f x y := by
    have hb₁ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hb y)
    have hb₂ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hb x)
    have heq : EqOn (f y) (f x) (U y ∩ U x) :=
      Measure.eqOn_open_of_ae_eq (hb₁.symm.trans hb₂) ((hU y).inter (hU x))
        ((hf y).mono inter_subset_left)
        ((hf x).mono inter_subset_right)
    exact heq ⟨hx y, hy⟩
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply ((hf x).continuousAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq
    filter_upwards [(hU x).mem_nhds (hx x)] with y hy
    exact hagree x y hy
  refine ⟨F, hF, ?_⟩
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have heach (x : M) : ∀ᵐ y ∂normalizedVolume g, y ∈ U x → F y = b y := by
    have he := (ae_restrict_iff' (hU x).measurableSet).mp (hb x)
    filter_upwards [he] with y hy
    intro hyU
    exact (hagree x y hyU).trans (hy hyU).symm
  have hfin : ∀ᵐ y ∂normalizedVolume g, ∀ x : s, y ∈ U x → F y = b y :=
    ae_all_iff.mpr (fun x => heach x)
  filter_upwards [hfin] with y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact hy ⟨x, hxs⟩ hyx

end
end PositiveEinsteinFour.Geometry
end


section

/-! A bounded-derivative smooth scalar chain rule on the actual first-jet
closure.  The proof uses smooth approximation and strong convergence of
bounded multipliers, rather than assuming a weak chain rule. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff BigOperators _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarCompose (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (a : SmoothScalar (M := M)) : SmoothScalar (M := M) :=
  ⟨fun x => φ (a.val x), hφ.contMDiff.comp a.property⟩

theorem smoothScalarCompose_gradient {μ : Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (a : SmoothScalar (M := M)) (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarCompose φ hφ a).val e i =
      deriv φ (a.val e.base) * scalarGradient g a.val e i := by
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let b := smoothScalarCompose φ hφ a
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  have hd := sa.derivativeValue i 0 f
  rw [hf] at hd
  have hb := sb.derivativeValue i 0 f
  rw [hf] at hb
  have houter : HasDerivAt φ (deriv φ (a.val e.base)) (a.val e.base) :=
    (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc := HasDerivAt.comp (h₂ := φ)
    (h := fun t : ℝ => a.val (((d.toMetricGreenData.flow i).map t) f).base)
    0 (by simpa only [hf] using houter) hd
  exact hb.unique hc

variable {μ : Measure (FrameBundle g)} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

private theorem scalarValueL2_coe (a : SmoothScalar (M := M)) :
    smoothScalarValueL2 g μ a =ᵐ[μ] fun e => a.val e.base :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (smoothScalarValue g a)

private theorem scalarGradientL2_coe (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradientL2 d i a =ᵐ[μ] fun e => scalarGradient g a.val e i :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (smoothScalarGradient d i a)

private theorem scalarCompose_value (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C : ℝ≥0} (hLip : LipschitzWith C φ) (hzero : φ 0 = 0)
    (a : SmoothScalar (M := M)) :
    smoothScalarValueL2 g μ (smoothScalarCompose φ hφ a) =
      hLip.compLp hzero (smoothScalarValueL2 g μ a) := by
  apply Lp.ext
  filter_upwards [scalarValueL2_coe (g := g) (μ := μ) a,
    scalarValueL2_coe (g := g) (μ := μ) (smoothScalarCompose φ hφ a),
    hLip.coeFn_compLp hzero (smoothScalarValueL2 g μ a)] with e ha hb hc
  rw [hb, hc]
  change φ (a.val e.base) = φ (smoothScalarValueL2 g μ a e)
  rw [ha]

private theorem scalarCompose_gradient (d : ParallelMetricData g μ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {D : ℝ}
    (hbound : ∀ r, |deriv φ r| ≤ D) (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradientL2 d i (smoothScalarCompose φ hφ a) =
      scalarCompositionL2Multiply (fun e => deriv φ (smoothScalarValueL2 g μ a e))
        ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable (smoothScalarValueL2 g μ a)))
        (fun e => hbound _) (smoothScalarGradientL2 d i a) := by
  apply Lp.ext
  filter_upwards [scalarGradientL2_coe d (smoothScalarCompose φ hφ a) i,
    scalarGradientL2_coe d a i, scalarValueL2_coe (g := g) (μ := μ) a,
    scalarCompositionL2Multiply_coe (fun e => deriv φ (smoothScalarValueL2 g μ a e))
      ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (smoothScalarValueL2 g μ a)))
      (fun e => hbound _) (smoothScalarGradientL2 d i a)] with e h₁ h₂ h₃ h₄
  rw [h₁, h₄, h₂, h₃]
  exact smoothScalarCompose_gradient d φ hφ a e i

/-- Composition by a smooth function with bounded derivative preserves the
actual scalar H¹ closure and has the expected four weak derivatives. -/
theorem scalarH1_compose_exists (d : ParallelMetricData g μ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0}
    (hLip : LipschitzWith C φ) (hzero : φ 0 = 0)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ r, |deriv φ r| ≤ D)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d, scalarH1Value d v = hLip.compLp hzero (scalarH1Value d u) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => deriv φ (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp u.property
  choose a ha using hs
  have hjet : Tendsto (fun n => smoothScalarFirstJet d (a n)) atTop (𝓝 u.val) := by
    simpa only [ha] using ht
  let V : ℕ → ScalarL2 g μ := fun n => smoothScalarValueL2 g μ (a n)
  have hV : Tendsto V atTop (𝓝 (scalarH1Value d u)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none).continuous.tendsto
      u.val |>.comp hjet
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hV).exists_seq_tendsto_ae
  let f : ℕ → ScalarL2 g μ := fun n => V (ns n)
  let G : Fin 4 → ℕ → ScalarL2 g μ := fun i n => smoothScalarGradientL2 d i (a (ns n))
  have hG (i : Fin 4) : Tendsto (G i) atTop (𝓝 (scalarH1Gradient d i u)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)).continuous.tendsto
      u.val |>.comp hjet).comp hns.tendsto_atTop
  let k : ℕ → FrameBundle g → ℝ := fun n e => deriv φ (f n e)
  let k₀ : FrameBundle g → ℝ := fun e => deriv φ (scalarH1Value d u e)
  have hk (n : ℕ) : AEStronglyMeasurable (k n) μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f n))
  have hk₀ : AEStronglyMeasurable k₀ μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (scalarH1Value d u))
  have hkD (n : ℕ) (e : FrameBundle g) : |k n e| ≤ D := hbound _
  have hk₀D (e : FrameBundle g) : |k₀ e| ≤ D := hbound _
  have hkconv : ∀ᵐ e ∂μ, Tendsto (fun n => k n e) atTop (𝓝 (k₀ e)) := by
    filter_upwards [hAE] with e he
    exact (hφ.continuous_deriv (by simp)).continuousAt.tendsto.comp he
  let v₀ : ScalarL2 g μ := hLip.compLp hzero (scalarH1Value d u)
  let vG : Fin 4 → ScalarL2 g μ := fun i =>
    scalarCompositionL2Multiply k₀ hk₀ hk₀D (scalarH1Gradient d i u)
  let p : Option (Fin 4) → ScalarL2 g μ := fun j => match j with
    | none => v₀
    | some i => vG i
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin 4) => ScalarL2 g μ)
  let v : ScalarJetL2 g μ := E.symm p
  have hc : Tendsto (fun n => E (smoothScalarFirstJet d
      (smoothScalarCompose φ hφ (a (ns n))))) atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro j
    cases j with
    | none =>
      change Tendsto (fun n => smoothScalarValueL2 g μ
        (smoothScalarCompose φ hφ (a (ns n)))) atTop (𝓝 v₀)
      simp only [scalarCompose_value φ hφ hLip hzero]
      exact (hLip.continuous_compLp hzero).continuousAt.tendsto.comp (hV.comp hns.tendsto_atTop)
    | some i =>
      change Tendsto (fun n => smoothScalarGradientL2 d i
        (smoothScalarCompose φ hφ (a (ns n)))) atTop (𝓝 (vG i))
      simp only [scalarCompose_gradient d φ hφ hbound]
      exact scalarCompositionL2Multiply_tendsto hk hk₀ hD hkD hk₀D hkconv (hG i)
  have hvlim : Tendsto (fun n => smoothScalarFirstJet d
      (smoothScalarCompose φ hφ (a (ns n)))) atTop (𝓝 v) := by
    simpa only [Function.comp_def, E.symm_apply_apply] using!
      (E.symm.continuous.tendsto p).comp hc
  have hv : v ∈ scalarH1 d := by
    apply (Submodule.isClosed_topologicalClosure (LinearMap.range (smoothScalarFirstJet d))).mem_of_tendsto hvlim
    exact Eventually.of_forall fun n => Submodule.le_topologicalClosure _
      ⟨smoothScalarCompose φ hφ (a (ns n)), rfl⟩
  refine ⟨⟨v, hv⟩, rfl, ?_⟩
  intro i
  exact scalarCompositionL2Multiply_coe k₀ hk₀ hk₀D (scalarH1Gradient d i u)

/-- A bound on the ordinary derivative supplies the Lipschitz hypothesis. -/
theorem scalarH1_compose_exists_of_deriv_bound (d : ParallelMetricData g μ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hzero : φ 0 = 0)
    {D : ℝ≥0} (hbound : ∀ r, |deriv φ r| ≤ D) (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => φ (scalarH1Value d u e)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => deriv φ (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  have hLip : LipschitzWith D φ := lipschitzWith_of_nnnorm_deriv_le
    (hφ.differentiable (by simp)) (fun r => by
      exact_mod_cast (show ‖deriv φ r‖ ≤ (D : ℝ) by simpa only [Real.norm_eq_abs] using hbound r))
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists d φ hφ hLip hzero D.coe_nonneg hbound u
  refine ⟨v, ?_, hgrad⟩
  rw [hv]
  exact hLip.coeFn_compLp hzero _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Values in the first-jet completion are actual base scalars.  Pullback from
normalized Riemannian volume is an isometry with closed image, so this property
survives completion of the smooth scalar jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarBase_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance scalarBase_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def scalarBasePullback (g : SmoothMetric M) (o : FrameOrientation g) :
    Lp ℝ 2 (normalizedVolume g) →ₗᵢ[ℝ] ScalarL2 g (canonicalFrameMeasure g o) :=
  Lp.compMeasurePreservingₗᵢ ℝ FrameBundle.base (canonicalFrameMeasure_base g o)

theorem scalarBasePullback_closed (g : SmoothMetric M) (o : FrameOrientation g) :
    IsClosed (range (scalarBasePullback g o)) :=
  (scalarBasePullback g o).isometry.isClosedEmbedding.isClosed_range

def smoothScalarBaseL2 (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ ⟨a.val, a.property.continuous⟩

theorem scalarBasePullback_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (a : SmoothScalar (M := M)) :
    scalarBasePullback g o (smoothScalarBaseL2 g a) =
      smoothScalarValueL2 g (canonicalFrameMeasure g o) a := by
  apply Lp.ext
  have hcomp := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ)))
  filter_upwards [Lp.coeFn_compMeasurePreserving (smoothScalarBaseL2 g a)
      (canonicalFrameMeasure_base g o), hcomp,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
      (smoothScalarValue g a)] with e h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

/-- No extra dependence on the orthonormal frame appears in the value
coordinate when completing smooth scalar first jets. -/
theorem scalarH1_base_representative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    ∃ f : Lp ℝ 2 (normalizedVolume g), scalarBasePullback g o f = scalarH1Value d u := by
  let p₀ : ScalarJetL2 g (canonicalFrameMeasure g o) →L[ℝ]
      ScalarL2 g (canonicalFrameMeasure g o) :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g (canonicalFrameMeasure g o)) none
  have hclosed : IsClosed {v : ScalarJetL2 g (canonicalFrameMeasure g o) |
      p₀ v ∈ range (scalarBasePullback g o)} :=
    (scalarBasePullback_closed g o).preimage p₀.continuous
  have hsub : closure (range (smoothScalarFirstJet d)) ⊆
      {v : ScalarJetL2 g (canonicalFrameMeasure g o) |
        p₀ v ∈ range (scalarBasePullback g o)} := by
    apply hclosed.closure_subset_iff.mpr
    rintro v ⟨a, rfl⟩
    exact ⟨smoothScalarBaseL2 g a, scalarBasePullback_smooth g o a⟩
  exact hsub u.property

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous mean and its kernel on the actual scalar first-jet
completion.  Mean subtraction changes only the value coordinate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section Probability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Pairwise square oscillation is twice the variance for a probability
measure.  Both integrals are ordinary real Bochner integrals. -/
theorem continuous_pairwise_square_integral (a : C(X, ℝ)) :
    (∫ x, ∫ y, (a x - a y) ^ 2 ∂μ ∂μ) =
      2 * ((∫ x, (a x) ^ 2 ∂μ) - (∫ x, a x ∂μ) ^ 2) := by
  have ha : Integrable a μ := a.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have ha₂ : Integrable (fun x => (a x) ^ 2) μ :=
    (a.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hinner (x : X) : (∫ y, (a x - a y) ^ 2 ∂μ) =
      (a x) ^ 2 - 2 * a x * (∫ y, a y ∂μ) + (∫ y, (a y) ^ 2 ∂μ) := by
    calc
      (∫ y, (a x - a y) ^ 2 ∂μ) =
          ∫ y, ((a x) ^ 2 - (2 * a x) * a y) + (a y) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := by
        rw [integral_add (f := fun y => (a x) ^ 2 - (2 * a x) * a y)
            (g := fun y => (a y) ^ 2) ((integrable_const _).sub (ha.const_mul _)) ha₂,
          integral_sub (f := fun _ => (a x) ^ 2) (g := fun y => (2 * a x) * a y)
            (integrable_const _) (ha.const_mul _), integral_const_mul]
        simp
  simp_rw [hinner]
  rw [integral_add (f := fun x => (a x) ^ 2 - 2 * a x * (∫ y, a y ∂μ))
      (g := fun _ => ∫ y, (a y) ^ 2 ∂μ)
      (ha₂.sub ((ha.const_mul 2).mul_const _)) (integrable_const _),
    integral_sub (f := fun x => (a x) ^ 2)
      (g := fun x => 2 * a x * (∫ y, a y ∂μ)) ha₂ ((ha.const_mul 2).mul_const _),
    integral_mul_const,
    integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

theorem continuous_pairwise_square_integral_of_mean_zero (a : C(X, ℝ))
    (ha : (∫ x, a x ∂μ) = 0) :
    (∫ x, ∫ y, (a x - a y) ^ 2 ∂μ ∂μ) = 2 * (∫ x, (a x) ^ 2 ∂μ) := by
  rw [continuous_pairwise_square_integral μ a, ha]
  ring

end Probability

section FirstJet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- A constant as an actual smooth scalar function. -/
def smoothScalarConst (c : ℝ) : SmoothScalar (M := M) :=
  ⟨fun _ => c, contMDiff_const⟩

theorem smoothScalarGradient_const (d : ParallelMetricData g μ) (i : Fin 4) (c : ℝ) :
    smoothScalarGradient d i (smoothScalarConst c) = 0 := by
  ext e
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  let s := Classical.choice (d.scalarCalculus.toPetersenInput
    (smoothScalarConst (M := M) c) (smoothScalarConst (M := M) c).property)
  have h := (s.derivativeValue i 0 f).unique (hasDerivAt_const 0 c)
  simpa only [hf] using! h

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The constant one in scalar `L²`. -/
def scalarL2One (g : SmoothMetric M) (μ : Measure (FrameBundle g))
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] : ScalarL2 g μ :=
  smoothScalarValueL2 g μ (smoothScalarConst 1)

/-- The genuine constant first jet, with zero derivative coordinates. -/
def scalarH1One (d : ParallelMetricData g μ) : scalarH1 d :=
  smoothScalarToH1 d (smoothScalarConst 1)

@[simp] theorem scalarH1Value_one (d : ParallelMetricData g μ) :
    scalarH1Value d (scalarH1One d) = scalarL2One g μ := rfl

@[simp] theorem scalarH1Gradient_one (d : ParallelMetricData g μ) (i : Fin 4) :
    scalarH1Gradient d i (scalarH1One d) = 0 := by
  change smoothScalarGradientL2 d i (smoothScalarConst 1) = 0
  simp only [smoothScalarGradientL2, LinearMap.comp_apply,
    smoothScalarGradient_const, map_zero]

/-- Integration of the value coordinate, represented by inner product with
the constant one and hence continuous on the actual `H¹` completion. -/
def scalarH1Mean (d : ParallelMetricData g μ) : scalarH1 d →L[ℝ] ℝ :=
  (innerSL ℝ (scalarL2One g μ)).comp (scalarH1Value d)

theorem scalarH1Mean_apply (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1Mean d u = inner ℝ (scalarL2One g μ) (scalarH1Value d u) := rfl

theorem scalarH1Mean_smooth (d : ParallelMetricData g μ) (a : SmoothScalar (M := M)) :
    scalarH1Mean d (smoothScalarToH1 d a) = ∫ e, a.val e.base ∂μ := by
  change inner ℝ (ContinuousMap.toLp 2 μ ℝ
    (smoothScalarValue g (smoothScalarConst 1)))
    (ContinuousMap.toLp 2 μ ℝ (smoothScalarValue g a)) = _
  rw [ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  change (∫ e, a.val e.base * (1 : ℝ) ∂μ) = _
  simp only [mul_one]

theorem scalarH1Mean_eq_inner_one (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1Mean d u = inner ℝ (scalarH1One d) u := by
  rw [scalarH1_inner]
  simp only [scalarH1Value_one, scalarH1Gradient_one, inner_zero_left,
    Finset.sum_const_zero, add_zero, scalarH1Mean_apply]

/-- The closed subspace on which the actual value coordinate has mean zero. -/
def scalarH1MeanZero (d : ParallelMetricData g μ) : Submodule ℝ (scalarH1 d) :=
  (scalarH1Mean d).ker

theorem scalarH1MeanZero_closed (d : ParallelMetricData g μ) :
    IsClosed (scalarH1MeanZero d : Set (scalarH1 d)) :=
  (scalarH1Mean d).isClosed_ker

@[simp] theorem mem_scalarH1MeanZero (d : ParallelMetricData g μ) (u : scalarH1 d) :
    u ∈ scalarH1MeanZero d ↔ scalarH1Mean d u = 0 := Iff.rfl

instance scalarH1MeanZero_complete (d : ParallelMetricData g μ) :
    CompleteSpace (scalarH1MeanZero d) :=
  (scalarH1MeanZero_closed d).isComplete.completeSpace_coe

/-- Subtract the constant jet with coefficient equal to the scalar mean. -/
def scalarH1SubtractMean (d : ParallelMetricData g μ) : scalarH1 d →L[ℝ] scalarH1 d :=
  ContinuousLinearMap.id ℝ _ - (scalarH1Mean d).smulRight (scalarH1One d)

theorem scalarH1SubtractMean_apply (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1SubtractMean d u = u - scalarH1Mean d u • scalarH1One d := rfl

@[simp] theorem scalarH1Gradient_subtractMean (d : ParallelMetricData g μ)
    (u : scalarH1 d) (i : Fin 4) :
    scalarH1Gradient d i (scalarH1SubtractMean d u) = scalarH1Gradient d i u := by
  rw [scalarH1SubtractMean_apply, map_sub, map_smul]
  simp only [scalarH1Gradient_one, smul_zero, sub_zero]

theorem scalarH1Value_subtractMean (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1Value d (scalarH1SubtractMean d u) =
      scalarH1Value d u - scalarH1Mean d u • scalarL2One g μ := by
  rw [scalarH1SubtractMean_apply, map_sub, map_smul, scalarH1Value_one]

variable [IsProbabilityMeasure μ]

@[simp] theorem scalarH1Mean_one (d : ParallelMetricData g μ) :
    scalarH1Mean d (scalarH1One d) = 1 := by
  rw [scalarH1One, scalarH1Mean_smooth]
  simp only [smoothScalarConst, integral_const, probReal_univ, one_smul]

@[simp] theorem scalarH1Mean_subtractMean (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarH1Mean d (scalarH1SubtractMean d u) = 0 := by
  rw [scalarH1SubtractMean_apply, map_sub, map_smul]
  simp only [scalarH1Mean_one, smul_eq_mul, mul_one, sub_self]

omit [IsProbabilityMeasure μ] in
theorem scalarH1SubtractMean_eq_self (d : ParallelMetricData g μ) (u : scalarH1 d)
    (hu : u ∈ scalarH1MeanZero d) : scalarH1SubtractMean d u = u := by
  rw [scalarH1SubtractMean_apply, (mem_scalarH1MeanZero d u).mp hu,
    zero_smul, sub_zero]

@[simp] theorem scalarH1SubtractMean_idempotent (d : ParallelMetricData g μ)
    (u : scalarH1 d) :
    scalarH1SubtractMean d (scalarH1SubtractMean d u) = scalarH1SubtractMean d u := by
  rw [scalarH1SubtractMean_apply, scalarH1Mean_subtractMean, zero_smul, sub_zero]

/-- The mean-subtraction projection with its closed mean-zero codomain. -/
def scalarH1MeanZeroProjection (d : ParallelMetricData g μ) :
    scalarH1 d →L[ℝ] scalarH1MeanZero d :=
  (scalarH1SubtractMean d).codRestrict (scalarH1MeanZero d)
    (fun u => scalarH1Mean_subtractMean d u)

/-- Subtracting the actual integral preserves smoothness. -/
def smoothScalarSubtractMean (a : SmoothScalar (M := M)) : SmoothScalar (M := M) :=
  a - (∫ e, a.val e.base ∂μ) • smoothScalarConst 1

omit [IsProbabilityMeasure μ] in
theorem smoothScalarSubtractMean_toH1 (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    smoothScalarToH1 d (smoothScalarSubtractMean (μ := μ) a) =
      scalarH1SubtractMean d (smoothScalarToH1 d a) := by
  rw [scalarH1SubtractMean_apply, scalarH1Mean_smooth]
  apply Subtype.ext
  change smoothScalarFirstJet d (a - (∫ e, a.val e.base ∂μ) • smoothScalarConst 1) = _
  rw [map_sub, map_smul]
  rfl

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] [IsProbabilityMeasure μ] in
@[simp] theorem smoothScalarGradient_subtractMean (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradient d i (smoothScalarSubtractMean (μ := μ) a) =
      smoothScalarGradient d i a := by
  unfold smoothScalarSubtractMean
  rw [map_sub, map_smul, smoothScalarGradient_const, smul_zero, sub_zero]

omit [IsProbabilityMeasure μ] in
@[simp] theorem smoothScalarGradientL2_subtractMean (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradientL2 d i (smoothScalarSubtractMean (μ := μ) a) =
      smoothScalarGradientL2 d i a := by
  rw [← scalarH1Gradient_smooth, smoothScalarSubtractMean_toH1,
    scalarH1Gradient_subtractMean, scalarH1Gradient_smooth]

theorem smoothScalarSubtractMean_mean_zero (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    (∫ e, (smoothScalarSubtractMean (μ := μ) a).val e.base ∂μ) = 0 := by
  rw [← scalarH1Mean_smooth d, smoothScalarSubtractMean_toH1,
    scalarH1Mean_subtractMean]

end FirstJet

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local smooth representatives of one actual L2 function agree on
overlaps by full support of Riemannian volume, and hence glue globally. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The gluing uses only the actual full-support volume and local smooth
representatives.  No global smoothness or elliptic premise is assumed. -/
theorem scalar_smooth_representative_of_local (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g))
    (hlocal : ∀ x : M, ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) ∞ f U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] f) :
    ∃ F : SmoothScalar (M := M), F.val =ᵐ[normalizedVolume g] b := by
  let := normalizedVolume_isOpenPosMeasure g
  choose U f hU hx hf hb using hlocal
  let F : M → ℝ := fun x => f x x
  have hagree (x y : M) (hy : y ∈ U x) : F y = f x y := by
    have hb₁ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hb y)
    have hb₂ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hb x)
    have heq : EqOn (f y) (f x) (U y ∩ U x) :=
      Measure.eqOn_open_of_ae_eq (hb₁.symm.trans hb₂) ((hU y).inter (hU x))
        ((hf y).continuousOn.mono inter_subset_left)
        ((hf x).continuousOn.mono inter_subset_right)
    exact heq ⟨hx y, hy⟩
  have hF : ContMDiff I4 𝓘(ℝ, ℝ) ∞ F := by
    intro x
    apply ((hf x).contMDiffAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq
    filter_upwards [(hU x).mem_nhds (hx x)] with y hy
    exact hagree x y hy
  refine ⟨⟨F, hF⟩, ?_⟩
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have heach (x : M) : ∀ᵐ y ∂normalizedVolume g, y ∈ U x → F y = b y := by
    have he := (ae_restrict_iff' (hU x).measurableSet).mp (hb x)
    filter_upwards [he] with y hy
    intro hyU
    exact (hagree x y hyU).trans (hy hyU).symm
  have hfin : ∀ᵐ y ∂normalizedVolume g, ∀ x : s, y ∈ U x → F y = b y :=
    ae_all_iff.mpr (fun x => heach x)
  filter_upwards [hfin] with y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact hy ⟨x, hxs⟩ hyx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compatibility of the weak shifted solution with the actual smooth scalar
Laplacian.  Smooth jets determine the entire Hilbert completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

def smoothScalarLaplacianField (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    C(FrameBundle g, ℝ) :=
  ⟨scalarLaplacian g a,
    continuous_finsetSum _ (fun i _ => actual_scalarHessian_continuous g a.property i i)⟩

def smoothScalarLaplacianL2 (a : SmoothScalar (M := M)) : ScalarL2 g μ :=
  ContinuousMap.toLp 2 μ ℝ (smoothScalarLaplacianField g a)

def smoothScalarShiftedRhs (a : SmoothScalar (M := M)) : ScalarL2 g μ :=
  smoothScalarValueL2 g μ a - smoothScalarLaplacianL2 a

theorem smoothScalarShiftedRhs_pairing (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarShiftedRhs (g := g) (μ := μ) a) (smoothScalarValueL2 g μ b) =
      inner ℝ (smoothScalarValueL2 g μ a) (smoothScalarValueL2 g μ b) +
        smoothScalarDirichlet d a b := by
  rw [smoothScalarShiftedRhs, inner_sub_left]
  have h : inner ℝ (smoothScalarLaplacianL2 (g := g) (μ := μ) a)
      (smoothScalarValueL2 g μ b) = ∫ e, b.val e.base * scalarLaplacian g a e ∂μ := by
    simpa only [conj_trivial] using!
      ContinuousMap.inner_toLp μ (smoothScalarLaplacianField g a) (smoothScalarValue g b)
  rw [h, smoothScalarDirichlet_symm d a b, smoothScalarDirichlet_green]
  exact sub_eq_add_neg _ _

theorem scalarH1_eq_of_smooth_tests (d : ParallelMetricData g μ) (u v : scalarH1 d)
    (h : ∀ a : SmoothScalar (M := M),
      inner ℝ u (smoothScalarToH1 d a) = inner ℝ v (smoothScalarToH1 d a)) : u = v := by
  have hc : IsClosed {w : ScalarJetL2 g μ | inner ℝ u.val w = inner ℝ v.val w} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hs : closure (range (smoothScalarFirstJet d)) ⊆
      {w : ScalarJetL2 g μ | inner ℝ u.val w = inner ℝ v.val w} := by
    apply hc.closure_subset_iff.mpr
    rintro w ⟨a, rfl⟩
    exact h a
  apply ext_inner_right ℝ
  intro w
  exact hs w.property

/-- The Hilbert construction inverts `1 - Δ` on every actual smooth scalar.
This identifies the weak resolvent with the geometric operator. -/
theorem scalarShiftedSolution_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    scalarShiftedSolution d (smoothScalarShiftedRhs (g := g) (μ := μ) a) =
      smoothScalarToH1 d a := by
  apply scalarH1_eq_of_smooth_tests d
  intro b
  rw [scalarH1_inner, scalarShiftedSolution_weak, scalarH1Value_smooth,
    smoothScalarShiftedRhs_pairing, scalarH1_inner, scalarH1Value_smooth,
    scalarH1Value_smooth]
  rfl

theorem scalarWeakResolvent_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    scalarWeakResolvent d (smoothScalarShiftedRhs (g := g) (μ := μ) a) =
      smoothScalarValueL2 g μ a := by
  change scalarH1Value d (scalarShiftedSolution d _) = _
  rw [scalarShiftedSolution_smooth, scalarH1Value_smooth]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth functions as degree-zero covariant fields and their actual
one-form differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarCovariantField (f : SmoothScalar (M := M)) : smoothCovariantFields M 0 :=
  ⟨fun x _ => f.val x, by
    intro c z hz a
    simpa only [covariantFieldCoordinates, frameTensor_zero, scalarCoordinates] using
      scalarCoordinates_contDiffAt f.property c z hz a⟩

theorem smoothScalarCovariantField_coordinates (f : SmoothScalar (M := M)) (c : M) :
    covariantFieldCoordinates (smoothScalarCovariantField f).val c = scalarCoordinates f.val c := by
  funext z a
  exact frameTensor_zero _ _ a

def covariantScalarFunction (u : smoothCovariantFields M 0) : M → ℝ := fun x => u.val x ![]

theorem covariantScalarFunction_smooth (u : smoothCovariantFields M 0) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (covariantScalarFunction u) := by
  intro c
  have hz := mem_chart_target FourSpace c
  have h := (u.property c _ hz ![]).contMDiffAt.comp c
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      (mem_chart_source FourSpace c))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c)] with x hx
  change u.val x ![] = covariantFieldCoordinates u.val c (chartAt FourSpace c x) ![]
  simp only [covariantFieldCoordinates, frameTensor_zero, (chartAt FourSpace c).left_inv hx]

def smoothCovariantScalar (u : smoothCovariantFields M 0) : SmoothScalar (M := M) :=
  ⟨covariantScalarFunction u, covariantScalarFunction_smooth u⟩

def smoothScalarDifferential (g : SmoothMetric M) (f : SmoothScalar (M := M)) :
    smoothCovariantFields M 1 := smoothCovariantDerivative g (smoothScalarCovariantField f)

theorem smoothScalarDifferential_framed (f : SmoothScalar (M := M))
    (e : FrameBundle g) (i : Fin 4) :
    covariantFieldFramed g (smoothScalarDifferential g f).val e ![i] =
      scalarGradient g f.val e i := by
  rw [covariantFieldFramed_eq]
  change frameTensor e.frame.matrix (covariantDerivative g e.base
    (covariantFieldCoordinates (smoothScalarCovariantField f).val e.base)
      (chartAt FourSpace e.base e.base)) ![i] = _
  rw [smoothScalarCovariantField_coordinates]
  rfl

theorem smoothScalarDifferential_derivative (f : SmoothScalar (M := M))
    (e : FrameBundle g) (i j : Fin 4) :
    covariantFieldFramed g (covariantFieldDerivative g (smoothScalarDifferential g f).val)
      e ![i,j] = scalarHessian g f.val e i j := by
  have h := (smoothScalarCovariantField f).property.framed_second (g := g) e
  rw [smoothScalarCovariantField_coordinates] at h
  exact congrFun h ![i,j]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exterior and trace tensors of a two-form covariant derivative.
Their norms are independent of the orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormExteriorTensor (A : CovariantCoordinates 3) : CovariantCoordinates 3 :=
  A - (fun v => A (v ∘ Equiv.swap 0 1)) +
    fun v => A (v ∘ (Equiv.swap 0 2).trans (Equiv.swap 0 1))

theorem twoFormExteriorTensor_apply (A : CovariantCoordinates 3) (i j k : Fin 4) :
    twoFormExteriorTensor A ![i,j,k] =
      twoFormExteriorComponent (fun p q r => A ![p,q,r]) i j k := by
  have hs : ![i,j,k] ∘ Equiv.swap (0 : Fin 3) 1 = ![j,i,k] := by
    funext a
    fin_cases a <;> simp [Equiv.swap_apply_def]
  have hc : ![i,j,k] ∘ (Equiv.swap (0 : Fin 3) 2).trans (Equiv.swap 0 1) = ![k,i,j] := by
    funext a
    fin_cases a <;> simp [Function.comp_def, Equiv.swap_apply_def]
  simp only [twoFormExteriorTensor, Pi.add_apply, Pi.sub_apply, hs, hc,
    twoFormExteriorComponent]

theorem twoFormExteriorTensor_frame (E : Mat4) (A : CovariantCoordinates 3) :
    twoFormExteriorTensor (frameTensor E A) = frameTensor E (twoFormExteriorTensor A) := by
  funext v
  simp only [twoFormExteriorTensor, Pi.add_apply, Pi.sub_apply,
    frameTensor_add, frameTensor_sub, frameTensor_permute]

def twoFormCodiffTensor (A : CovariantCoordinates 3) : CovariantCoordinates 1 :=
  fun v => -∑ i, A ![i,i,v 0]

theorem twoFormCodiffTensor_apply (A : CovariantCoordinates 3) (k : Fin 4) :
    twoFormCodiffTensor A ![k] = twoFormCodiffComponent (fun p q r => A ![p,q,r]) k := rfl

private theorem trace_three_frame (E : Mat4) (A : CovariantCoordinates 3)
    (k : Fin 4) : (∑ i, frameTensor E A ![i,i,k]) =
      ∑ a, ∑ b, ∑ c, (E * Eᵀ) a b * E c k * A ![a,b,c] := by
  simp only [frameTensor_three]
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ i, E a i * E b i * E c k * A ![a,b,c] := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = _ := by
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

theorem twoFormCodiffTensor_frame (E : Mat4) (hE : E * Eᵀ = 1)
    (A : CovariantCoordinates 3) :
    twoFormCodiffTensor (frameTensor E A) = frameTensor E (twoFormCodiffTensor A) := by
  funext v
  have hv : ![v 0] = v := by ext i; fin_cases i; rfl
  rw [← hv]
  change -(∑ i, frameTensor E A ![i,i,v 0]) =
    frameTensor E (twoFormCodiffTensor A) (Fin.cons (v 0) ![])
  rw [trace_three_frame, hE, frameTensor_cons]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, frameTensor_zero,
    twoFormCodiffTensor, Fin.cons_zero]
  have hs (a : Fin 4) :
      (∑ b : Fin 4, ∑ c : Fin 4,
        if a = b then E c (v 0) * A ![a,b,c] else (0 : ℝ)) =
        ∑ c : Fin 4, E c (v 0) * A ![a,a,c] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    simp
  change -(∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    if a = b then E c (v 0) * A ![a,b,c] else (0 : ℝ)) =
      ∑ c : Fin 4, E c (v 0) * -(∑ a : Fin 4, A ![a,a,c])
  simp only [hs]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]

theorem twoFormDeRhamQuadratic_tensor (A : CovariantCoordinates 3) :
    twoFormDeRhamQuadratic (fun i j k => A ![i,j,k]) =
      (1 / 6 : ℝ) * frameTensorSquareNorm (twoFormExteriorTensor A) +
        frameTensorSquareNorm (twoFormCodiffTensor A) := by
  have he : frameTensorSquareNorm (twoFormExteriorTensor A) =
      ∑ i, ∑ j, ∑ k, twoFormExteriorComponent (fun p q r => A ![p,q,r]) i j k ^ 2 := by
    rw [frameTensorSquareNorm, frameTensorPairing_three]
    simp only [twoFormExteriorTensor_apply, pow_two]
  have hc : frameTensorSquareNorm (twoFormCodiffTensor A) =
      ∑ k, twoFormCodiffComponent (fun p q r => A ![p,q,r]) k ^ 2 := by
    unfold frameTensorSquareNorm frameTensorPairing
    simp only [sum_tensor_indices_cons, Fintype.sum_unique, pow_two]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [he, hc]
  rfl

theorem twoFormDeRhamQuadratic_frame (E : Mat4) (hE : E * Eᵀ = 1)
    (A : CovariantCoordinates 3) :
    twoFormDeRhamQuadratic (fun i j k => frameTensor E A ![i,j,k]) =
      twoFormDeRhamQuadratic (fun i j k => A ![i,j,k]) := by
  rw [twoFormDeRhamQuadratic_tensor, twoFormDeRhamQuadratic_tensor,
    twoFormExteriorTensor_frame, twoFormCodiffTensor_frame E hE,
    frameTensor_norm_orthogonal E hE, frameTensor_norm_orthogonal E hE]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rough Green pairing is bounded by the L2 value norm.
This is the estimate needed to close the covariant derivative graph. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

abbrev TwoTensorEuclidean := EuclideanSpace ℝ (Fin 2 → Fin 4)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormBound_compactFrame : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def smoothTwoFormEuclideanValue (u : smoothTwoForms o) : C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun e => WithLp.toLp 2 (twoFormFramedValue o u.val e),
    (PiLp.continuous_toLp 2 _).comp u.property.continuous_framedValue⟩

def smoothTwoFormEuclideanTrace (u : smoothTwoForms o) : C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun e => WithLp.toLp 2 (twoFormFramedRoughTrace o u.val e),
    (PiLp.continuous_toLp 2 _).comp u.property.continuous_framedRoughTrace⟩

def smoothTwoFormTensorValueL2 (u : smoothTwoForms o) : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u)

def smoothTwoFormTensorTraceL2 (u : smoothTwoForms o) : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanTrace u)

private theorem continuousTwoTensor_inner_toLp (F G : C(FrameBundle g, TwoTensorEuclidean)) :
    inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F)
      (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ G) =
        ∫ e, inner ℝ (F e) (G e) ∂canonicalFrameMeasure g o := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) G] with e hF hG
  rw [hF, hG]

theorem smoothTwoFormTensorValueL2_norm_sq (u : smoothTwoForms o) :
    ‖smoothTwoFormTensorValueL2 u‖ ^ 2 = 2 * smoothTwoFormL2Inner u u := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u))
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u)) = _
  rw [continuousTwoTensor_inner_toLp]
  have hp (e : FrameBundle g) :
      inner ℝ (smoothTwoFormEuclideanValue u e) (smoothTwoFormEuclideanValue u e) =
        2 * ‖u.val e.base‖ ^ 2 := by
    change frameTensorSquareNorm (twoFormFramedValue o u.val e) = _
    exact twoFormFramedValue_norm o u.val e
  simp_rw [hp]
  rw [integral_const_mul]
  congr 1
  rw [smoothTwoFormL2Inner_self]
  exact canonicalFrameMeasure_integral_base g o (fun x => ‖u.val x‖ ^ 2)
    (by simpa only [real_inner_self_eq_norm_sq] using smoothTwoForm_pairing_integrable u u)

theorem smoothTwoFormTensorValueL2_norm_le (u : SmoothL2TwoForm o) :
    ‖smoothTwoFormTensorValueL2 (u : smoothTwoForms o)‖ ≤ 2 * ‖u‖ := by
  have h := smoothTwoFormTensorValueL2_norm_sq (u : smoothTwoForms o)
  have hu : smoothTwoFormL2Inner (u : smoothTwoForms o) u = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [hu] at h
  nlinarith [norm_nonneg u, norm_nonneg (smoothTwoFormTensorValueL2 (u : smoothTwoForms o))]

theorem smoothTwoFormTensorValueTrace_inner (u v : smoothTwoForms o) :
    inner ℝ (smoothTwoFormTensorValueL2 u) (smoothTwoFormTensorTraceL2 v) =
      ∫ e, frameTensorPairing (twoFormFramedValue o u.val e)
        (twoFormFramedRoughTrace o v.val e) ∂canonicalFrameMeasure g o := by
  change inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u))
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanTrace v)) = _
  rw [continuousTwoTensor_inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with e
  change (∑ a, inner ℝ (twoFormFramedValue o u.val e a) (twoFormFramedRoughTrace o v.val e a)) = _
  simp only [RCLike.inner_apply, conj_trivial, frameTensorPairing, mul_comm]

theorem smoothTwoFormCovariantEnergy_L2_bound (hRic : RicciThree g)
    (u : SmoothL2TwoForm o) (v : smoothTwoForms o) :
    |smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v| ≤
      ‖u‖ * ‖smoothTwoFormTensorTraceL2 v‖ := by
  have hg := smoothTwoForm_rough_green hRic (u : smoothTwoForms o) v
  have ht := smoothTwoFormTensorValueTrace_inner (u : smoothTwoForms o) v
  rw [← ht] at hg
  have hi := abs_real_inner_le_norm (smoothTwoFormTensorValueL2 (u : smoothTwoForms o))
    (smoothTwoFormTensorTraceL2 v)
  have hn := mul_le_mul_of_nonneg_right (smoothTwoFormTensorValueL2_norm_le u)
    (norm_nonneg (smoothTwoFormTensorTraceL2 v))
  rw [hg, abs_mul]
  norm_num
  nlinarith only [hi, hn]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed-direction integration by parts for the actual two-form jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem smoothTwoForm_mixed_green (hRic : RicciThree g) (u v : smoothTwoForms o)
    (i j : Fin 4) (a b : Fin 2 → Fin 4) :
    (∫ e, twoFormFramedCovariantDerivative o u.val e (Fin.cons i a) *
      twoFormFramedCovariantDerivative o v.val e (Fin.cons j b) ∂canonicalFrameMeasure g o) =
      -(∫ e, twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons j b))
        ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedValue o u.val e a,
    (continuous_apply a).comp u.property.continuous_framedValue⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o u.val e (Fin.cons i a),
    (continuous_apply _).comp u.property.continuous_framedCovariantDerivative⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o v.val e (Fin.cons j b),
    (continuous_apply _).comp v.property.continuous_framedCovariantDerivative⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons j b)),
    (continuous_apply _).comp v.property.continuous_framedSecondDerivative⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.framedValue_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) a
  · intro t e
    exact v.property.framedCovariant_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) (Fin.cons j b)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of a smooth third-order tensor by the actual inverse metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def covariantMetricTraceThree (G : Mat4) (T : CovariantCoordinates 3) : CovariantCoordinates 1 :=
  fun v => -(∑ a, ∑ b, G a b * T (Fin.cons a (Fin.cons b v)))

theorem covariantMetricTraceThree_frame (E : Mat4) (T : CovariantCoordinates 3) :
    twoFormCodiffTensor (frameTensor E T) =
      frameTensor E (covariantMetricTraceThree (E * Eᵀ) T) := by
  funext v
  have hp : (∑ i, frameTensor E T (Fin.cons i (Fin.cons i v))) =
      frameTensor E (fun w => ∑ a, ∑ b, (E * Eᵀ) a b * T (Fin.cons a (Fin.cons b w))) v := by
    simp only [frameTensor_cons]
    rw [Finset.sum_comm]
    calc
      (∑ a, ∑ i, E a i * ∑ b, E b i * frameTensor E
          (fun w => T (Fin.cons a (Fin.cons b w))) v) =
          ∑ a, ∑ b, (∑ i, E a i * E b i) * frameTensor E
            (fun w => T (Fin.cons a (Fin.cons b w))) v := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        symm
        rw [frameTensor_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [frameTensor_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [frameTensor_const_mul]
        rfl
  have hi (i : Fin 4) : ![i,i,v 0] = Fin.cons i (Fin.cons i v) := by
    ext a
    fin_cases a <;> rfl
  change -(∑ i, frameTensor E T ![i,i,v 0]) = _
  simp_rw [hi]
  rw [hp]
  exact (frameTensor_neg E _ v).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

def covariantMetricTraceField (g : SmoothMetric M) (T : M → CovariantCoordinates 3) :
    M → CovariantCoordinates 1 :=
  fun x => covariantMetricTraceThree (chartMetric g x)⁻¹ (T x)

theorem covariantMetricTraceField_framed (T : M → CovariantCoordinates 3) (e : FrameBundle g) :
    covariantFieldFramed g (covariantMetricTraceField g T) e =
      twoFormCodiffTensor (covariantFieldFramed g T e) := by
  simp only [covariantFieldFramed_eq]
  rw [covariantMetricTraceThree_frame, e.frame.matrix_mul_transpose]
  rfl

theorem covariantFieldFramed_chart (T : M → CovariantCoordinates n)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    covariantFieldFramed g T (chartGramSection g c S hS z) =
      frameTensor (chartGramMatrix g c S z) (covariantFieldCoordinates T c z) := by
  rw [covariantFieldFramed_eq]
  change frameTensor (chartInverseMatrix c z * chartGramMatrix g c S z) (T _) = _
  rw [frameTensor_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The trace-three Jacobi equation has no preconjugate interval longer
than π, by finite Dirichlet positivity and its first sine mode. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped _root_.Topology

noncomputable section

theorem firstEigenvalue_eventually_neg {t : ℝ} (ht : Real.pi < t) :
    ∀ᶠ N : ℕ in atTop, firstEigenvalue t N < 0 := by
  have hlim : Real.pi ^ 2 - t ^ 2 < 0 := by nlinarith [Real.pi_pos]
  filter_upwards [(scaledFirstEigenvalue_tendsto t).eventually
    (eventually_lt_nhds hlim)] with N hN
  have hsq : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
  change ((N : ℝ) + 1) ^ 2 * firstEigenvalue t N < 0 at hN
  by_contra hnot
  exact (not_lt_of_ge (mul_nonneg hsq.le (le_of_not_gt hnot))) hN

/-- On the first sine mode a trace-free curvature defect has zero trace. -/
theorem trace_first_mode_curvatureDirichlet {N : ℕ} (hN : 0 < N)
    (t : ℝ) (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0) :
    ((modeEmbedding (unitFirstSineVector N))ᵀ * curvatureDirichlet t A *
      modeEmbedding (unitFirstSineVector N)).trace = 3 * firstEigenvalue t N := by
  let E := modeEmbedding (unitFirstSineVector N)
  have heigen : scalarLift (referenceMatrix t N) * E = firstEigenvalue t N • E :=
    scalarLift_mode_eigenvector (referenceMatrix t N) (unitFirstSineVector N)
      (firstEigenvalue t N) (unitFirstSineVector_eigenvector N _)
  have hbase : Eᵀ * scalarLift (referenceMatrix t N) * E =
      firstEigenvalue t N • (1 : NormalMatrix) := by
    rw [Matrix.mul_assoc, heigen, Matrix.mul_smul,
      modeEmbedding_orthonormal _ (unitFirstSineVector_norm hN)]
  have hdefect : (Eᵀ * Matrix.blockDiagonal A * E).trace = 0 :=
    trace_mode_compression_defect A _ hA
  change (Eᵀ * curvatureDirichlet t A * E).trace = _
  rw [curvatureDirichlet, Matrix.mul_sub, Matrix.sub_mul, hbase,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, hdefect]
  norm_num [Matrix.trace_one]
  ring

theorem firstEigenvalue_nonneg_of_curvatureDirichlet {N : ℕ} (hN : 0 < N)
    (t : ℝ) (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0)
    (hpos : (curvatureDirichlet t A).PosSemidef) :
    0 ≤ firstEigenvalue t N := by
  have hp := (hpos.conjTranspose_mul_mul_same
    (modeEmbedding (unitFirstSineVector N))).trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,
    trace_first_mode_curvatureDirichlet hN t A hA] at hp
  linarith

/-- The Einstein trace condition forces a conjugate point by any time strictly greater than π. -/
theorem RegularJacobi.le_pi_of_preconjugate {t : ℝ} (d : RegularJacobi t)
    (htrace : ∀ s, (d.R s).trace = 3)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) : t ≤ Real.pi := by
  by_contra hnot
  have ht : Real.pi < t := lt_of_not_ge hnot
  have hpos := d.curvatureDirichlet_eventually_posDef (Real.pi_pos.trans ht) hpre
  obtain ⟨N, hNpos, hNneg, hN⟩ :=
    (hpos.and ((firstEigenvalue_eventually_neg ht).and
      (eventually_ge_atTop 1))).exists
  have hA : ∀ i : Fin N,
      (d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1).trace = 0 := by
    intro i
    rw [Matrix.trace_sub, htrace, Matrix.trace_one]
    norm_num
  have hnonneg := firstEigenvalue_nonneg_of_curvatureDirichlet
    (show 0 < N by omega) t _ hA hNpos.posSemidef
  exact (not_lt_of_ge hnonneg) hNneg

theorem RegularJacobi.exists_singular_of_pi_lt {t : ℝ} (d : RegularJacobi t)
    (htrace : ∀ s, (d.R s).trace = 3) (ht : Real.pi < t) :
    ∃ s, 0 < s ∧ s ≤ t ∧ ¬ IsUnit (d.J s) := by
  by_contra hnot
  push Not at hnot
  exact (not_le_of_gt ht) (d.le_pi_of_preconjugate htrace hnot)

theorem RegularJacobi.truncatedDensity_eq_zero_of_pi_lt {t : ℝ}
    (d : RegularJacobi t) (htrace : ∀ s, (d.R s).trace = 3)
    (ht : Real.pi < t) : d.truncatedDensity = 0 := by
  classical
  rw [RegularJacobi.truncatedDensity, ite_eq_right]
  intro hpre
  exact (not_le_of_gt ht) (d.le_pi_of_preconjugate htrace hpre)

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobiCurvature_trace (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (s : ℝ) : (actualJacobiCurvature g e s).trace = 3 := by
  apply frameCurvatureField_add_one_trace g _ (actual_einstein_decomposition _ hRic)
    (actual_weyl_traceFree _ hRic).1 (actual_weyl_traceFree _ hRic).2

theorem actualJacobi_le_pi_of_preconjugate (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    t ≤ Real.pi := by
  apply (actualRegularJacobi g hRic e t).le_pi_of_preconjugate
  · simpa only [actualRegularJacobi_R] using actualJacobiCurvature_trace g hRic e
  · simpa only [actualRegularJacobi_J] using hpre

theorem actualJacobi_exists_singular_of_pi_lt (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) (ht : Real.pi < t) :
    ∃ s, 0 < s ∧ s ≤ t ∧ ¬ IsUnit ((actualJacobiSolution g hRic e).J s) := by
  have h := (actualRegularJacobi g hRic e t).exists_singular_of_pi_lt
    (fun s => by rw [actualRegularJacobi_R]; exact actualJacobiCurvature_trace g hRic e s) ht
  simpa only [actualRegularJacobi_J] using h

theorem actualJacobi_truncatedDensity_eq_zero_of_pi_lt (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (t : ℝ) (ht : Real.pi < t) :
    (actualRegularJacobi g hRic e t).truncatedDensity = 0 := by
  apply (actualRegularJacobi g hRic e t).truncatedDensity_eq_zero_of_pi_lt _ ht
  intro s
  rw [actualRegularJacobi_R]
  exact actualJacobiCurvature_trace g hRic e s

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual global normal variation with the matrix
Jacobi solution, with its initial data derived from vertical momentum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_self_zero_fderiv (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source) :
    fderiv ℝ (radialCoordinateFlow g o c c 0) (unitRadialCotangentState g c p) =
      ContinuousLinearMap.id ℝ CotangentCoordinates := by
  have hz : {z : CotangentCoordinates | z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0}
      ∈ 𝓝 (unitRadialCotangentState g c p) :=
    (((chartAt FourSpace c).open_target.preimage continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)).mem_nhds
        ⟨(chartAt FourSpace c).map_source hc,
          unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have heq : radialCoordinateFlow g o c c 0 =ᶠ[𝓝 (unitRadialCotangentState g c p)] id := by
    filter_upwards [hz] with z hz
    rw [radialCoordinateFlow, unitTangentRadialFlow_zero,
      unitRadialCotangentState_retraction g c z hz]
    rfl
  exact ((hasFDerivAt_id (unitRadialCotangentState g c p)).congr_of_eventuallyEq heq).fderiv

def frameNormalInitialVariation (g : SmoothMetric M) (e : FrameBundle g)
    (w : Fin 3 → ℝ) : CotangentCoordinates :=
  (0, WithLp.toLp 2
    (metricInChart g e.base (chartAt FourSpace e.base e.base) *ᵥ
      (frameChartMatrix g e.base e *ᵥ Fin.cons 0 w)))

theorem actualNormalVariation_initial (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (w : Fin 3 → ℝ) :
    actualNormalVariationPosition g o e (frameNormalInitialVariation g e w) 0 = 0 ∧
      actualNormalVariationVelocity g o e (frameNormalInitialVariation g e w) 0 = w := by
  let a := frameNormalInitialVariation g e w
  let p := unitRadialCotangentState g e.base (frameUnitRadialState e)
  have hc : (parallelFrameFlowMap g 0 0 e).base ∈ (chartAt FourSpace e.base).source := by
    rw [parallelFrameFlowMap_zero]
    exact mem_chart_source FourSpace e.base
  have hp : p.1 ∈ (chartAt FourSpace e.base).target :=
    (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hzero : frameKineticCurve g o e.base e 0 = p := by
    change unitRadialCotangentState g e.base
      (unitTangentRadialFlow g o 0 (frameUnitRadialState e)) = p
    rw [unitTangentRadialFlow_zero]
  have hvar : frameKineticVariation g o e.base e a 0 = a := by
    change fderiv ℝ (radialCoordinateFlow g o e.base e.base 0) p a = a
    rw [radialCoordinateFlow_self_zero_fderiv g o e.base (frameUnitRadialState e)
      (mem_chart_source FourSpace e.base)]
    rfl
  have hZ : frameGeodesicCoordinateVariation g o e.base e a 0 =
      fderiv ℝ (kineticVelocityCoordinates g e.base) p
        (0, WithLp.toLp 2 (metricInChart g e.base p.1 *ᵥ
          (frameChartMatrix g e.base (parallelFrameFlowMap g 0 0 e) *ᵥ Fin.cons 0 w))) := by
    change fderiv ℝ (kineticVelocityCoordinates g e.base) (frameKineticCurve g o e.base e 0)
      (frameKineticVariation g o e.base e a 0) = _
    rw [hzero, hvar, parallelFrameFlowMap_zero]
    rfl
  have h := kinetic_normal_initial_data g e.base (parallelFrameFlowMap g 0 · e)
    (frameGeodesicCoordinateCurve g o e.base e)
    (frameGeodesicCoordinateVariation g o e.base e a) p w 0 hc hp hZ
  rw [actualNormalVariationPosition_eq_chart g o e.base e he a 0 hc,
    actualNormalVariationVelocity_eq_chart g o e.base e he a 0 hc]
  exact h

variable [T3Space M]

theorem actualNormalVariation_eq_jacobi (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (w : Fin 3 → ℝ) (t : ℝ) :
    actualNormalVariationPosition g o e (frameNormalInitialVariation g e w) t =
        (actualJacobiSolution g hRic e).J t *ᵥ w ∧
      actualNormalVariationVelocity g o e (frameNormalInitialVariation g e w) t =
        (actualJacobiSolution g hRic e).V t *ᵥ w := by
  let a := frameNormalInitialVariation g e w
  have hinit := actualNormalVariation_initial g o e he w
  have hzero : (0 : ℝ) ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  exact actual_normal_jacobi_eq_mulVec g hRic e
    (actualNormalVariationPosition g o e a) (actualNormalVariationVelocity g o e a)
    w _ _ hzero hinit.1 hinit.2
    (fun s _ => actualNormalVariationPosition_hasDerivAt g o e he a s)
    (fun s _ => actualNormalVariationVelocity_hasDerivAt g o e he a s) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reversing the actual frame orientation exchanges the two Weyl norms.
The plus-block Sobolev argument therefore proves both norm gaps, without
assuming reflection preservation of a fixed oriented frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem frameReflectionMatrix_det : frameReflectionMatrix.det = -1 := by
  norm_num [frameReflectionMatrix, Matrix.det_diagonal, Fin.prod_univ_succ, orientationSign]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem OrthonormalFrame.reflect_det {c : M} (e : OrthonormalFrame g c) :
    e.reflect.matrix.det = -e.matrix.det := by
  change (e.matrix * frameReflectionMatrix).det = _
  rw [Matrix.det_mul, frameReflectionMatrix_det, mul_neg_one]

/-- The opposite orientation is the pullback of the original orientation
through the concrete single-axis reflection. -/
def FrameOrientation.reversed (o : FrameOrientation g) : FrameOrientation g where
  positive := frameReflection ⁻¹' o.positive
  clopen := o.clopen.preimage (continuous_frameReflection g)
  nonempty_fiber c := by
    refine ⟨(o.frame c).reflect, ?_⟩
    change (⟨c, (o.frame c).reflect.reflect⟩ : FrameBundle g) ∈ o.positive
    rw [OrthonormalFrame.reflect_reflect]
    exact o.frame_positive c
  compatible c e f he := by
    change (⟨c, e.reflect⟩ : FrameBundle g) ∈ o.positive at he
    change (⟨c, f.reflect⟩ : FrameBundle g) ∈ o.positive ↔ _
    simpa only [OrthonormalFrame.reflect_det, neg_mul_neg] using
      o.compatible c e.reflect f.reflect he

theorem FrameOrientation.mem_reversed_iff (o : FrameOrientation g) (e : FrameBundle g) :
    e ∈ o.reversed.positive ↔ frameReflection e ∈ o.positive := Iff.rfl

theorem FrameOrientation.reversed_positive_iff_not (o : FrameOrientation g)
    (e : FrameBundle g) : e ∈ o.reversed.positive ↔ e ∉ o.positive := by
  rcases e with ⟨c, e⟩
  change (⟨c, e.reflect⟩ : FrameBundle g) ∈ o.positive ↔
    (⟨c, e⟩ : FrameBundle g) ∉ o.positive
  rw [o.positive_iff_det c e.reflect, o.positive_iff_det c e,
    OrthonormalFrame.reflect_det, mul_neg]
  have hn : (o.frame c).matrix.det * e.matrix.det ≠ 0 :=
    mul_ne_zero (o.frame c).det_ne_zero e.det_ne_zero
  constructor
  · intro h hpos
    linarith
  · intro h
    have hneg := lt_of_le_of_ne (le_of_not_gt h) hn
    linarith

theorem plusNorm_reversed (o : FrameOrientation g) (x : M) :
    plusNorm o.reversed x = minusNorm o x := by
  let e := o.reversed.frame x
  have hp : (⟨x, e.reflect⟩ : FrameBundle g) ∈ o.positive := o.reversed.frame_positive x
  have he := actual_minusNorm_frame o (⟨x, e.reflect⟩ : FrameBundle g) hp
  change minusNorm o x = normalizedBlockNorm (minusWeyl g x e.reflect) at he
  rw [minusWeyl_reflect] at he
  exact he.symm

theorem minusNorm_reversed (o : FrameOrientation g) (x : M) :
    minusNorm o.reversed x = plusNorm o x := by
  let e := o.reversed.frame x
  have hp : (⟨x, e.reflect⟩ : FrameBundle g) ∈ o.positive := o.reversed.frame_positive x
  have he := actual_plusNorm_frame o (⟨x, e.reflect⟩ : FrameBundle g) hp
  change plusNorm o x = normalizedBlockNorm (plusWeyl g x e.reflect) at he
  rw [plusWeyl_reflect] at he
  exact he.symm

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance oppositeGap_frameCompact : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

/-- The same sharp scalar inequality, used with the opposite orientation,
gives the minus-block gap. -/
theorem minus_gap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hsharp : SharpScalarSobolev o.reversed (canonicalParallelMetricData g o.reversed hRic))
    (hnonzero : ∃ x, minusNorm o x ≠ 0) :
    1 ≤ ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g := by
  have hn : ∃ x, plusNorm o.reversed x ≠ 0 := by
    simpa only [plusNorm_reversed] using hnonzero
  simpa only [plusNorm_reversed] using
    plus_gap_of_sharpScalarSobolev o.reversed hRic hsharp hn

/-- Both scalar Sobolev instances suffice for the original geometric gap
input. The sharp scalar premise remains explicit. -/
theorem gurskyLeBrunGap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hplus : SharpScalarSobolev o (canonicalParallelMetricData g o hRic))
    (hminus : SharpScalarSobolev o.reversed (canonicalParallelMetricData g o.reversed hRic)) :
    GurskyLeBrunGapInput g o :=
  ⟨plus_gap_of_sharpScalarSobolev o hRic hplus,
    minus_gap_of_sharpScalarSobolev o hRic hminus⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Classification from the Poisson, polar comparison, Weyl gap,
Hodge and half-flat model hypotheses. -/

namespace PositiveEinsteinFour

open EinsteinFour _root_.OAI.PositiveEinsteinFour.Geometry
open scoped Manifold ContDiff

noncomputable section

universe u

structure RemainingOrientedData {M : Type u} [TopologicalSpace M]
    [ChartedSpace FourSpace M] [IsManifold I4 ∞ M] [T3Space M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    (g : SmoothMetric M) (o : FrameOrientation g) (hRic : RicciThree g) where
  poisson : PetersenPoissonInput g (canonicalFrameMeasure g o)
  polar : ActualJacobiPolarInput g o hRic
  gap : GurskyLeBrunGapInput g o
  hodge : GurskyLeBrunHodgeInput g o
  model : DerdzinskiHitchinInput g o

def RemainingOrientedInputs (X : ClosedOrientedMetricFour.{u}) : Prop :=
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  ∀ (g : SmoothMetric X.manifold) (o : FrameOrientation g) (hRic : RicciThree g),
    IsEinstein g → HasPositiveSectionalCurvature g → Nonempty (RemainingOrientedData g o hRic)

theorem RemainingOrientedInputs.toPublished {X : ClosedOrientedMetricFour.{u}}
    (h : RemainingOrientedInputs X) : OrientedPublishedInputs X := by
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  intro g o hRic hEinstein hpositive
  obtain ⟨p⟩ := h g o hRic hEinstein hpositive
  exact ⟨actualCanonicalData_of_polar g o hRic p.poisson p.polar p.gap p.hodge p.model⟩

variable (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure RemainingClassificationInputs : Prop where
  oriented : ∀ X : ClosedOrientedMetricFour.{u}, RemainingOrientedInputs X
  unoriented : ∀ g : SmoothMetric M, UnorientedPublishedInputs g

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]

/-- The S4/CP2/RP4 classification under the Poisson, polar comparison,
Weyl gap, Hodge and half-flat model hypotheses. -/
theorem classificationOn_of_remaining_inputs (h : RemainingClassificationInputs M) :
    ClassificationOn M :=
  classificationOn_of_published_inputs M
    ⟨fun X => (h.oriented X).toPublished, h.unoriented⟩

end
end PositiveEinsteinFour
end


section

/-! The differential of an actual smooth scalar is a closed one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothScalarDifferential_closed (f : SmoothScalar (M := M)) :
    smoothOneFormExterior (o := o) (smoothScalarDifferential g f) = 0 := by
  have hz (e : FrameBundle g) : twoFormFramedValue o
      (smoothOneFormExterior (o := o) (smoothScalarDifferential g f)).val e = 0 := by
    funext a
    have ha : a = ![a 0,a 1] := by ext k; fin_cases k <;> rfl
    rw [ha, smoothOneFormExterior_framed, smoothScalarDifferential_derivative,
      smoothScalarDifferential_derivative, actual_scalarHessian_symmetric f.property e (a 0) (a 1)]
    simp only [sub_self, Pi.zero_apply]
  apply Subtype.ext
  funext x
  apply twoFormTensor_injective
  have h := hz ⟨x,o.frame x⟩
  rw [twoFormFramedValue_eq, twoFormFrameValue_at_orientation] at h
  exact h.trans (map_zero twoFormTensorLinear).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-zero differential as a linear map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarCovariantLinear : SmoothScalar (M := M) →ₗ[ℝ] smoothCovariantFields M 0 where
  toFun := smoothScalarCovariantField
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem smoothScalarDifferential_add (f h : SmoothScalar (M := M)) :
    smoothScalarDifferential g (f + h) =
      smoothScalarDifferential g f + smoothScalarDifferential g h := by
  change smoothCovariantDerivative g (smoothScalarCovariantLinear (f + h)) = _
  rw [map_add]
  apply Subtype.ext
  exact covariantFieldDerivative_add (smoothScalarCovariantField f)
    (smoothScalarCovariantField h)

theorem smoothScalarDifferential_smul (r : ℝ) (f : SmoothScalar (M := M)) :
    smoothScalarDifferential g (r • f) = r • smoothScalarDifferential g f := by
  change smoothCovariantDerivative g (smoothScalarCovariantLinear (r • f)) = _
  rw [map_smul]
  apply Subtype.ext
  exact covariantFieldDerivative_smul r (smoothScalarCovariantField f)

def smoothScalarDifferentialLinear (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] smoothCovariantFields M 1 where
  toFun := smoothScalarDifferential g
  map_add' := smoothScalarDifferential_add
  map_smul' := smoothScalarDifferential_smul

theorem smoothScalarDifferential_const (c : ℝ) :
    smoothScalarDifferential g (smoothScalarConst c) = 0 := by
  apply Subtype.ext
  funext x a
  change covariantDerivative g x
    (covariantFieldCoordinates (smoothScalarCovariantField (smoothScalarConst c)).val x)
    (chartAt FourSpace x x) a = 0
  rw [smoothScalarCovariantField_coordinates]
  simp [covariantDerivative, scalarCoordinates, smoothScalarConst, partialDeriv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual C4 scalar cutoff used in the heat
parametrix, paired against smooth scalar eigenfunctions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalar_finite_value_derivative (d : ParallelMetricData g μ) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => f ((d.flow i).map s e).base)
      (scalarGradient g f ((d.flow i).map t e) i) t := by
  have h := scalar_finite_parallel_derivative g hf _ t i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) 0 (by omega) ![]
  convert h using 1
  · funext s
    rw [frameTensor_zero]
    change f ((d.flow i).map s e).base = f ((chartAt FourSpace
      ((d.flow i).map s e).base).symm (chartAt FourSpace
        ((d.flow i).map s e).base ((d.flow i).map s e).base))
    rw [(chartAt FourSpace _).left_inv (mem_chart_source FourSpace _)]
  · rfl

theorem scalar_finite_gradient_derivative (d : ParallelMetricData g μ) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (i j : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => scalarGradient g f ((d.flow i).map s e) j)
      (scalarHessian g f ((d.flow i).map t e) i j) t :=
  scalar_finite_parallel_derivative g hf _ t i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) 1 (by omega) ![j]

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalar_finite_pairing_green (d : ParallelMetricData g μ) {f h : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (hh : ContMDiff I4 𝓘(ℝ, ℝ) 4 h) :
    (∫ e, ∑ i : Fin 4, scalarGradient g f e i * scalarGradient g h e i ∂μ) =
      -(∫ e, f e.base * scalarLaplacian g h e ∂μ) := by
  let fv : C(FrameBundle g, ℝ) := ⟨fun e => f e.base,
    hf.continuous.comp (continuous_frameBase g)⟩
  let fg (i : Fin 4) : C(FrameBundle g, ℝ) :=
    ⟨fun e => scalarGradient g f e i, scalar_finite_gradient_continuous g hf i⟩
  let hg (i : Fin 4) : C(FrameBundle g, ℝ) :=
    ⟨fun e => scalarGradient g h e i, scalar_finite_gradient_continuous g hh i⟩
  let hH (i : Fin 4) : C(FrameBundle g, ℝ) :=
    ⟨fun e => scalarHessian g h e i i, scalar_finite_hessian_continuous g hh i i⟩
  have hi (i : Fin 4) := scalar_flow_green (d := d.toMetricGreenData) i fv (fg i)
    (hg i) (hH i) (scalar_finite_value_derivative d hf i)
      (scalar_finite_gradient_derivative d hh i i)
  have hl (i : Fin 4) : Integrable
      (fun e => scalarGradient g f e i * scalarGradient g h e i) μ :=
    ((fg i).continuous.mul (hg i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : Fin 4) : Integrable (fun e => f e.base * scalarHessian g h e i i) μ :=
    (fv.continuous.mul (hH i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp only [fv, fg, hg, hH, ContinuousMap.coe_mk] at hi
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun e => (Finset.mul_sum _ _ _).symm

theorem scalar_finite_laplacian_symmetric (d : ParallelMetricData g μ) {f h : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (hh : ContMDiff I4 𝓘(ℝ, ℝ) 4 h) :
    (∫ e, scalarLaplacian g f e * h e.base ∂μ) =
      ∫ e, f e.base * scalarLaplacian g h e ∂μ := by
  have hfG := scalar_finite_pairing_green d hf hh
  have hhG := scalar_finite_pairing_green d hh hf
  have hgrad : (fun e : FrameBundle g =>
      ∑ i : Fin 4, scalarGradient g f e i * scalarGradient g h e i) =
      fun e => ∑ i : Fin 4, scalarGradient g h e i * scalarGradient g f e i := by
    funext e
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hgrad] at hfG
  have hi : (∫ e, scalarLaplacian g f e * h e.base ∂μ) =
      ∫ e, h e.base * scalarLaplacian g f e ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun e => mul_comm _ _
  linarith only [hfG, hhG, hi]

variable [T3Space M] [CompactSpace M]

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalar_finite_laplacian_continuous {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) : Continuous (scalarLaplacianBase g f) := by
  let := actual_compactFrameBundle g
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  change Continuous (fun e : FrameBundle g => scalarLaplacianBase g f e.base)
  simp_rw [← scalarLaplacian_eq_base]
  exact continuous_finsetSum _ (fun i _ => scalar_finite_hessian_continuous g hf i i)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalar_finite_laplacian_base_symmetric (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {f h : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (hh : ContMDiff I4 𝓘(ℝ, ℝ) 4 h) :
    (∫ x, scalarLaplacianBase g f x * h x ∂normalizedVolume g) =
      ∫ x, f x * scalarLaplacianBase g h x ∂normalizedVolume g := by
  let := actual_compactFrameBundle g
  have hleft : Continuous (fun x => scalarLaplacianBase g f x * h x) :=
    (scalar_finite_laplacian_continuous (g := g) hf).mul hh.continuous
  have hright : Continuous (fun x => f x * scalarLaplacianBase g h x) :=
    hf.continuous.mul (scalar_finite_laplacian_continuous (g := g) hh)
  rw [← (canonicalFrameMeasure_base g o).map_eq,
    integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable hleft.aestronglyMeasurable,
    integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable hright.aestronglyMeasurable]
  simpa only [← scalarLaplacian_eq_base] using scalar_finite_laplacian_symmetric d hf hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Limits of the value and all four weak derivatives remain in the actual
intrinsic first-jet closure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarH1_jet_limit (d : ParallelMetricData g μ) (v : ℕ → scalarH1 d)
    (f : ScalarL2 g μ) (G : Fin 4 → ScalarL2 g μ)
    (hf : Tendsto (fun n => scalarH1Value d (v n)) atTop (𝓝 f))
    (hG : ∀ i, Tendsto (fun n => scalarH1Gradient d i (v n)) atTop (𝓝 (G i))) :
    ∃ u : scalarH1 d, scalarH1Value d u = f ∧ ∀ i, scalarH1Gradient d i u = G i := by
  let p : Option (Fin 4) → ScalarL2 g μ := fun j => match j with
    | none => f
    | some i => G i
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin 4) => ScalarL2 g μ)
  have hp : Tendsto (fun n => E (v n).val) atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro j
    cases j with
    | none => exact hf
    | some i => exact hG i
  have hlim : Tendsto (fun n => (v n).val) atTop (𝓝 (E.symm p)) := by
    simpa only [Function.comp_def, E.symm_apply_apply] using!
      (E.symm.continuous.tendsto p).comp hp
  have hu : E.symm p ∈ scalarH1 d := by
    apply (Submodule.isClosed_topologicalClosure (LinearMap.range (smoothScalarFirstJet d))).mem_of_tendsto hlim
    exact Eventually.of_forall (fun n => (v n).property)
  exact ⟨⟨E.symm p, hu⟩, rfl, fun _ => rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rational Brezis--Kato tests with bounded derivatives.  Their exact
algebra relates the tested Dirichlet form to the square test, uniformly as
the truncation parameter tends to zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

def scalarKatoTest (lam s : ℝ) : ℝ := s ^ 3 / (1 + lam * s ^ 2)

def scalarKatoSquare (lam s : ℝ) : ℝ := s ^ 2 / Real.sqrt (1 + lam * s ^ 2)

def scalarKatoTestRate (lam s : ℝ) : ℝ :=
  s ^ 2 * (3 + lam * s ^ 2) / (1 + lam * s ^ 2) ^ 2

def scalarKatoSquareRate (lam s : ℝ) : ℝ :=
  s * (2 + lam * s ^ 2) / ((1 + lam * s ^ 2) * Real.sqrt (1 + lam * s ^ 2))

theorem scalarKato_den_pos {lam : ℝ} (hlam : 0 < lam) (s : ℝ) : 0 < 1 + lam * s ^ 2 :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hlam.le (sq_nonneg s))

theorem scalarKatoTest_smooth {lam : ℝ} (hlam : 0 < lam) : ContDiff ℝ ∞ (scalarKatoTest lam) := by
  exact (contDiff_id.pow 3).div
    (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    (fun s => (scalarKato_den_pos hlam s).ne')

theorem scalarKatoSquare_smooth {lam : ℝ} (hlam : 0 < lam) : ContDiff ℝ ∞ (scalarKatoSquare lam) := by
  exact (contDiff_id.pow 2).div
    ((contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).sqrt
      (fun s => (scalarKato_den_pos hlam s).ne'))
    (fun s => (Real.sqrt_pos.mpr (scalarKato_den_pos hlam s)).ne')

theorem scalarKatoTest_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    HasDerivAt (scalarKatoTest lam) (scalarKatoTestRate lam s) s := by
  have hd : HasDerivAt (fun r : ℝ => 1 + lam * r ^ 2) (2 * lam * s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul lam).const_add 1 using 1 <;>
      simp [mul_comm, mul_left_comm]
  convert ((hasDerivAt_id s).pow 3).div hd (scalarKato_den_pos hlam s).ne' using 1
  · rfl
  · simp only [scalarKatoTestRate, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
    congr 1
    ring

theorem scalarKatoSquare_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    HasDerivAt (scalarKatoSquare lam) (scalarKatoSquareRate lam s) s := by
  have hd : HasDerivAt (fun r : ℝ => 1 + lam * r ^ 2) (2 * lam * s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul lam).const_add 1 using 1 <;>
      simp [mul_comm, mul_left_comm]
  have hp := scalarKato_den_pos hlam s
  have hr := Real.sqrt_pos.mpr hp
  have hs : HasDerivAt (fun r : ℝ => Real.sqrt (1 + lam * r ^ 2))
      (lam * s / Real.sqrt (1 + lam * s ^ 2)) s := by
    convert (Real.hasDerivAt_sqrt hp.ne').comp s hd using 1
    · rfl
    · field_simp
  have hsq := Real.sq_sqrt hp.le
  convert ((hasDerivAt_id s).pow 2).div hs hr.ne' using 1
  · rfl
  · simp only [scalarKatoSquareRate, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hsq]
    field_simp [hp.ne', hr.ne']
    have hsq' : Real.sqrt (1 + s ^ 2 * lam) ^ 2 = 1 + s ^ 2 * lam := by
      simpa only [mul_comm lam] using hsq
    nlinarith only [congrArg (fun r : ℝ => (2 * s) * r) hsq']

theorem scalarKatoTest_deriv {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    deriv (scalarKatoTest lam) s = scalarKatoTestRate lam s :=
  (scalarKatoTest_hasDerivAt hlam s).deriv

theorem scalarKatoSquare_deriv {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    deriv (scalarKatoSquare lam) s = scalarKatoSquareRate lam s :=
  (scalarKatoSquare_hasDerivAt hlam s).deriv

@[simp] theorem scalarKatoTest_zero (lam : ℝ) : scalarKatoTest lam 0 = 0 := by
  simp [scalarKatoTest]

@[simp] theorem scalarKatoSquare_zero (lam : ℝ) : scalarKatoSquare lam 0 = 0 := by
  simp [scalarKatoSquare]

theorem scalarKato_test_square {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    s * scalarKatoTest lam s = scalarKatoSquare lam s ^ 2 := by
  simp only [scalarKatoTest, scalarKatoSquare, div_pow,
    Real.sq_sqrt (scalarKato_den_pos hlam s).le]
  ring

theorem scalarKatoTest_abs_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    |scalarKatoTest lam s| ≤ lam⁻¹ * |s| := by
  rw [scalarKatoTest, abs_div, abs_pow, abs_of_pos (scalarKato_den_pos hlam s)]
  apply (div_le_iff₀ (scalarKato_den_pos hlam s)).mpr
  apply (mul_le_mul_iff_right₀ hlam).mp
  have hpow : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ, sq_abs]; ring
  rw [hpow]
  field_simp [hlam.ne']
  nlinarith only [abs_nonneg s]

theorem scalarKatoSquare_sq_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    scalarKatoSquare lam s ^ 2 ≤ s ^ 4 := by
  rw [scalarKatoSquare, div_pow, Real.sq_sqrt (scalarKato_den_pos hlam s).le]
  calc
    (s ^ 2) ^ 2 / (1 + lam * s ^ 2) ≤ (s ^ 2) ^ 2 :=
      div_le_self (sq_nonneg _) (by nlinarith [mul_nonneg hlam.le (sq_nonneg s)])
    _ = s ^ 4 := by ring

theorem scalarKatoTestRate_nonneg {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    0 ≤ scalarKatoTestRate lam s := by
  unfold scalarKatoTestRate
  positivity

theorem scalarKatoTestRate_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    scalarKatoTestRate lam s ≤ 3 / lam := by
  unfold scalarKatoTestRate
  apply (div_le_div_iff₀ (sq_pos_of_pos (scalarKato_den_pos hlam s)) hlam).mpr
  have hx : 0 ≤ lam * s ^ 2 := mul_nonneg hlam.le (sq_nonneg s)
  nlinarith [sq_nonneg (lam * s ^ 2)]

theorem scalarKatoSquareRate_sq_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    scalarKatoSquareRate lam s ^ 2 ≤ 2 * scalarKatoTestRate lam s := by
  have hp := scalarKato_den_pos hlam s
  have hx : 0 ≤ lam * s ^ 2 := mul_nonneg hlam.le (sq_nonneg s)
  have hpoly : (2 + lam * s ^ 2) ^ 2 ≤ 2 * (3 + lam * s ^ 2) * (1 + lam * s ^ 2) := by
    nlinarith [sq_nonneg (lam * s ^ 2)]
  calc
    scalarKatoSquareRate lam s ^ 2 =
        (s ^ 2 * (2 + lam * s ^ 2) ^ 2) / ((1 + lam * s ^ 2) ^ 2 * (1 + lam * s ^ 2)) := by
      rw [scalarKatoSquareRate, div_pow, mul_pow, mul_pow, Real.sq_sqrt hp.le]
    _ ≤ (s ^ 2 * (2 * (3 + lam * s ^ 2) * (1 + lam * s ^ 2))) /
        ((1 + lam * s ^ 2) ^ 2 * (1 + lam * s ^ 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (sq_nonneg s))
        (by positivity)
    _ = 2 * scalarKatoTestRate lam s := by
      unfold scalarKatoTestRate
      field_simp [hp.ne']

theorem scalarKatoSquareRate_abs_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    |scalarKatoSquareRate lam s| ≤ 6 / lam + 1 := by
  have hs := scalarKatoSquareRate_sq_le hlam s
  have ht := scalarKatoTestRate_le hlam s
  have hq : 0 ≤ 6 / lam := by positivity
  have ht' : 2 * scalarKatoTestRate lam s ≤ 6 / lam := by
    calc
      _ ≤ 2 * (3 / lam) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = _ := by ring
  have hsq := hs.trans ht'
  nlinarith only [hsq, hq, sq_abs (scalarKatoSquareRate lam s),
    sq_nonneg (|scalarKatoSquareRate lam s| - 1)]

theorem scalarKatoSquare_tendsto (s : ℝ) :
    Tendsto (fun lam : ℝ => scalarKatoSquare lam s) (𝓝 0) (𝓝 (s ^ 2)) := by
  have hd : Tendsto (fun lam : ℝ => Real.sqrt (1 + lam * s ^ 2)) (𝓝 0) (𝓝 1) := by
    have hi : Tendsto (fun lam : ℝ => 1 + lam * s ^ 2) (𝓝 0) (𝓝 1) := by
      have hh : Tendsto (fun lam : ℝ => lam * s ^ 2) (𝓝 0) (𝓝 0) := by
        simpa only [zero_mul, id_eq] using! (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).mul_const (s ^ 2)
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hh
    simpa only [Function.comp_def, Real.sqrt_one] using! (Real.continuous_sqrt.tendsto 1).comp hi
  simpa only [scalarKatoSquare, Pi.div_apply, div_one] using!
    tendsto_const_nhds.div hd one_ne_zero

/-- A uniform fourth-moment bound for the rational square tests gives the
eighth moment of the original function by Fatou's lemma. -/
theorem scalarKato_memLp_eight_of_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
    (hbound : ∀ lam : ℝ, 0 < lam →
      eLpNorm (fun x => scalarKatoSquare lam (f x)) 4 μ ≤ C) : MemLp f 8 μ := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hlam (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlamlim : Tendsto lam atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => scalarKatoSquare (lam n) (f x))
      atTop (𝓝 (f x ^ 2)) :=
    Eventually.of_forall fun x => (scalarKatoSquare_tendsto (f x)).comp hlamlim
  have hsq : MemLp (fun x => f x ^ 2) 4 μ :=
    lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hbound (lam n) (hlam n))
      (fun n => (scalarKatoSquare_smooth (hlam n)).continuous.comp_aestronglyMeasurable hf)
      (hf.pow 2) hlim) (lt_top_iff_ne_top.mpr hC)
  have hexp : (8 : ℝ≥0∞) / 2 = 4 := by
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  apply (memLp_norm_rpow_iff (p := 8) (q := 2) hf (by norm_num) (by norm_num)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    hexp] using hsq

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarH1_katoTest_exists (d : ParallelMetricData g μ) {lam : ℝ} (hlam : 0 < lam)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => scalarKatoTest lam (scalarH1Value d u e)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => scalarKatoTestRate lam (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  have hbound (s : ℝ) : |deriv (scalarKatoTest lam) s| ≤ 3 / lam := by
    rw [scalarKatoTest_deriv hlam, abs_of_nonneg (scalarKatoTestRate_nonneg hlam s)]
    exact scalarKatoTestRate_le hlam s
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists_of_deriv_bound d (scalarKatoTest lam)
    (scalarKatoTest_smooth hlam) (scalarKatoTest_zero lam)
    (D := ⟨3 / lam, by positivity⟩) hbound u
  refine ⟨v, hv, ?_⟩
  intro i
  simpa only [scalarKatoTest_deriv hlam] using hgrad i

theorem scalarH1_katoSquare_exists (d : ParallelMetricData g μ) {lam : ℝ} (hlam : 0 < lam)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => scalarKatoSquare lam (scalarH1Value d u e)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => scalarKatoSquareRate lam (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists_of_deriv_bound d (scalarKatoSquare lam)
    (scalarKatoSquare_smooth hlam) (scalarKatoSquare_zero lam)
    (D := ⟨6 / lam + 1, by positivity⟩) (fun s => by
      rw [scalarKatoSquare_deriv hlam]
      exact scalarKatoSquareRate_abs_le hlam s) u
  refine ⟨v, hv, ?_⟩
  intro i
  simpa only [scalarKatoSquare_deriv hlam] using hgrad i

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth nonpositive test detecting the negative set, with nonnegative
bounded derivative. It is admissible in the actual H1 closure. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology ContDiff NNReal

noncomputable section

def scalarNegativeTest (r : ℝ) : ℝ := -Real.smoothTransition (-r)

theorem scalarNegativeTest_smooth : ContDiff ℝ ∞ scalarNegativeTest :=
  (Real.smoothTransition.contDiff.comp contDiff_id.neg).neg

theorem scalarNegativeTest_zero : scalarNegativeTest 0 = 0 := by
  simp [scalarNegativeTest]

theorem scalarNegativeTest_nonpos (r : ℝ) : scalarNegativeTest r ≤ 0 :=
  neg_nonpos.mpr (Real.smoothTransition.nonneg _)

theorem scalarNegativeTest_eq_zero {r : ℝ} (hr : 0 ≤ r) : scalarNegativeTest r = 0 := by
  rw [scalarNegativeTest, Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hr), neg_zero]

theorem scalarNegativeTest_neg {r : ℝ} (hr : r < 0) : scalarNegativeTest r < 0 :=
  neg_neg_of_pos (Real.smoothTransition.pos_of_pos (neg_pos.mpr hr))

theorem scalarNegativeTest_monotone : Monotone scalarNegativeTest := by
  intro a b hab
  exact neg_le_neg (Real.smoothTransition.monotone (neg_le_neg hab))

theorem scalarNegativeTest_deriv_nonneg (r : ℝ) : 0 ≤ deriv scalarNegativeTest r :=
  scalarNegativeTest_monotone.deriv_nonneg

theorem scalarNegativeTest_deriv_bound :
    ∃ D : ℝ≥0, ∀ r : ℝ, |deriv scalarNegativeTest r| ≤ D := by
  have hc : Continuous (deriv scalarNegativeTest) :=
    scalarNegativeTest_smooth.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro r
  by_cases hr : r ∈ Icc (-1 : ℝ) 0
  · exact (hC _ ⟨r, hr, rfl⟩).trans (le_max_left _ _)
  · have hout : r < -1 ∨ 0 < r := by
      simpa only [mem_Icc, not_and_or, not_le] using hr
    rcases hout with hr | hr
    · have he : scalarNegativeTest =ᶠ[𝓝 r] fun _ => (-1 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hr] with s hs
        have hs' : s < -1 := hs
        dsimp [scalarNegativeTest]
        rw [Real.smoothTransition.one_of_one_le (by linarith)]
      rw [he.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _
    · have he : scalarNegativeTest =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
        exact scalarNegativeTest_eq_zero hs.le
      rw [he.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _

theorem scalarNegativeTest_product_nonneg (r : ℝ) : 0 ≤ r * scalarNegativeTest r := by
  by_cases hr : 0 ≤ r
  · rw [scalarNegativeTest_eq_zero hr, mul_zero]
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hr) (scalarNegativeTest_nonpos r)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth bounded-derivative approximations of the subcritical power
s ↦ |s|^q s, for 0 < q < 2. Their derivative growth is uniformly quadratic. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped _root_.Topology ContDiff

noncomputable section

def scalarNonlinearTruncation (q ε s : ℝ) : ℝ :=
  s * (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2)

def scalarNonlinearTruncationDerivative (q ε s : ℝ) : ℝ :=
  (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) *
    (1 + q * s ^ 2 / (s ^ 2 + ε) - 2 * ε * s ^ 2 / (1 + ε * s ^ 2))

theorem scalarNonlinearTruncation_smooth (q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (scalarNonlinearTruncation q ε) := by
  have ha : ContDiff ℝ ∞ (fun s : ℝ => s ^ 2 + ε) := by fun_prop
  have hb : ContDiff ℝ ∞ (fun s : ℝ => 1 + ε * s ^ 2) := by fun_prop
  exact (contDiff_id.mul (ha.rpow_const_of_ne (fun s => ne_of_gt (by positivity)))).div hb
    (fun s => ne_of_gt (by positivity))

theorem scalarNonlinearTruncation_hasDeriv (q : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (scalarNonlinearTruncation q ε)
      (scalarNonlinearTruncationDerivative q ε s) s := by
  have ha : 0 < s ^ 2 + ε := by positivity
  have hb : 0 < 1 + ε * s ^ 2 := by positivity
  have hpow := (((hasDerivAt_id s).pow 2).add_const ε).rpow_const
    (p := q / 2) (Or.inl ha.ne')
  have h := ((hasDerivAt_id s).mul hpow).div
    (((hasDerivAt_id s).pow 2).const_mul ε |>.const_add 1) hb.ne'
  convert h using 1
  · rfl
  · dsimp [scalarNonlinearTruncationDerivative]
    rw [Real.rpow_sub ha]
    simp only [Real.rpow_one]
    field_simp

theorem scalarNonlinearTruncation_deriv (q : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (scalarNonlinearTruncation q ε) s = scalarNonlinearTruncationDerivative q ε s :=
  (scalarNonlinearTruncation_hasDeriv q hε s).deriv

theorem scalarNonlinearTruncation_zero (q ε : ℝ) :
    scalarNonlinearTruncation q ε 0 = 0 := by
  simp [scalarNonlinearTruncation]

theorem scalarNonlinearTruncation_power_bound {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    (s ^ 2 + ε) ^ (q / 2) ≤ 1 + s ^ 2 := by
  by_cases hs : s ^ 2 + ε ≤ 1
  · exact (Real.rpow_le_one (by positivity) hs (by positivity)).trans
      (le_add_of_nonneg_right (sq_nonneg _))
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hs)
      (show q / 2 ≤ 1 by linarith)
    rw [Real.rpow_one] at h
    linarith

theorem scalarNonlinearTruncation_bracket_bound {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (s : ℝ) :
    |1 + q * s ^ 2 / (s ^ 2 + ε) - 2 * ε * s ^ 2 / (1 + ε * s ^ 2)| ≤ 5 := by
  have ha : 0 < s ^ 2 + ε := by positivity
  have hb : 0 < 1 + ε * s ^ 2 := by positivity
  have hA0 : 0 ≤ q * s ^ 2 / (s ^ 2 + ε) := by positivity
  have hA : q * s ^ 2 / (s ^ 2 + ε) ≤ q := (div_le_iff₀ ha).mpr (by nlinarith)
  have hB0 : 0 ≤ 2 * ε * s ^ 2 / (1 + ε * s ^ 2) := by positivity
  have hB : 2 * ε * s ^ 2 / (1 + ε * s ^ 2) ≤ 2 :=
    (div_le_iff₀ hb).mpr (by nlinarith)
  apply abs_le.mpr
  constructor <;> linarith

theorem scalarNonlinearTruncation_deriv_growth {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    |deriv (scalarNonlinearTruncation q ε) s| ≤ 5 * (1 + s ^ 2) := by
  rw [scalarNonlinearTruncation_deriv q hε, scalarNonlinearTruncationDerivative, abs_mul]
  have hfrac : 0 ≤ (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) := by positivity
  rw [abs_of_nonneg hfrac]
  have hf : (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) ≤ 1 + s ^ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact (scalarNonlinearTruncation_power_bound hq hq2 hε hε1 s).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [mul_nonneg hε.le (sq_nonneg s)]))
  exact (mul_le_mul hf (scalarNonlinearTruncation_bracket_bound hq hq2 hε s)
    (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

theorem scalarNonlinearTruncation_deriv_bounded {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    |deriv (scalarNonlinearTruncation q ε) s| ≤ 5 / ε := by
  rw [scalarNonlinearTruncation_deriv q hε, scalarNonlinearTruncationDerivative, abs_mul]
  have hfrac : 0 ≤ (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) := by positivity
  rw [abs_of_nonneg hfrac]
  have hf : (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) ≤ 1 / ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    apply (scalarNonlinearTruncation_power_bound hq hq2 hε hε1 s).trans
    rw [div_mul_eq_mul_div, one_mul]
    apply (le_div_iff₀ hε).mpr
    nlinarith [sq_nonneg s]
  have h := mul_le_mul hf (scalarNonlinearTruncation_bracket_bound hq hq2 hε s)
    (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / ε)
  convert h using 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth Poincaré estimate passes to the actual first-jet completion.
It makes the Dirichlet form coercive on the closed mean-zero subspace and
therefore supplies a unique mean-zero weak Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

private def fourGradientDirichlet {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : Fin 4 → E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i : Fin 4, (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp (G i) (G i)

private theorem fourGradientDirichlet_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (G : Fin 4 → E →L[ℝ] F) (u v : E) :
    fourGradientDirichlet G u v = ∑ i : Fin 4, inner ℝ (G i u) (G i v) := by
  simp only [fourGradientDirichlet, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]

section AbstractSolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

private def fourGradientSolution (G : Fin 4 → E →L[ℝ] F) (V : E →L[ℝ] F)
    (h : IsCoercive (fourGradientDirichlet G)) : F →L[ℝ] E :=
  h.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp V.adjoint

private theorem fourGradientSolution_weak (G : Fin 4 → E →L[ℝ] F) (V : E →L[ℝ] F)
    (h : IsCoercive (fourGradientDirichlet G)) (f : F) (v : E) :
    (∑ i : Fin 4, inner ℝ (G i (fourGradientSolution G V h f)) (G i v)) =
      inner ℝ f (V v) := by
  rw [← fourGradientDirichlet_apply, ← h.continuousLinearEquivOfBilin_apply]
  change inner ℝ (h.continuousLinearEquivOfBilin
    (h.continuousLinearEquivOfBilin.symm (V.adjoint f))) v = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact V.adjoint_inner_left v f

private theorem fourGradientSolution_unique (G : Fin 4 → E →L[ℝ] F) (V : E →L[ℝ] F)
    (h : IsCoercive (fourGradientDirichlet G)) (f : F) (u : E)
    (hu : ∀ v : E, (∑ i : Fin 4, inner ℝ (G i u) (G i v)) = inner ℝ f (V v)) :
    u = fourGradientSolution G V h f := by
  apply h.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [h.continuousLinearEquivOfBilin_apply, h.continuousLinearEquivOfBilin_apply,
    fourGradientDirichlet_apply, fourGradientDirichlet_apply,
    hu, fourGradientSolution_weak]

end AbstractSolution

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

local instance scalarCoercive_h1Space (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1 d) := Submodule.normedSpace (𝕜 := ℝ) (scalarH1 d)

local instance scalarCoercive_meanZeroSpace (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1MeanZero d) :=
  Submodule.normedSpace (𝕜 := ℝ) (scalarH1MeanZero d)

local instance scalarCoercive_h1Inner (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1 d) := Submodule.innerProductSpace _

local instance scalarCoercive_meanZeroInner (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1MeanZero d) := Submodule.innerProductSpace _

/-- The estimate needed here, stated solely for actual smooth mean-zero
scalars.  The geometric Poincaré theorem supplies this hypothesis. -/
def SmoothScalarPoincare (d : ParallelMetricData g μ) (K : ℝ) : Prop :=
  ∀ a : SmoothScalar (M := M), (∫ e, a.val e.base ∂μ) = 0 →
    ‖smoothScalarValueL2 g μ a‖ ^ 2 ≤
      K * ∑ i : Fin 4, ‖smoothScalarGradientL2 d i a‖ ^ 2

/-- Center the value coordinate before taking closure.  This avoids needing
an independently chosen smooth mean-zero approximation. -/
theorem scalarH1_centered_poincare (d : ParallelMetricData g μ) {K : ℝ}
    (hP : SmoothScalarPoincare d K) (u : scalarH1 d) :
    ‖scalarH1Value d u - scalarH1Mean d u • scalarL2One g μ‖ ^ 2 ≤
      K * ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  let p₀ : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none
  let pᵢ (i : Fin 4) : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)
  let m : ScalarJetL2 g μ →L[ℝ] ℝ := (innerSL ℝ (scalarL2One g μ)).comp p₀
  let S : Set (ScalarJetL2 g μ) := {v |
    ‖p₀ v - m v • scalarL2One g μ‖ ^ 2 ≤ K * ∑ i : Fin 4, ‖pᵢ i v‖ ^ 2}
  have hclosed : IsClosed S := isClosed_le
    ((p₀.continuous.sub (m.continuous.smul continuous_const)).norm.pow 2)
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => (pᵢ i).continuous.norm.pow 2)))
  have hsub : range (smoothScalarFirstJet d) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    change ‖scalarH1Value d (smoothScalarToH1 d a) -
      scalarH1Mean d (smoothScalarToH1 d a) • scalarL2One g μ‖ ^ 2 ≤
      K * ∑ i : Fin 4, ‖scalarH1Gradient d i (smoothScalarToH1 d a)‖ ^ 2
    rw [← scalarH1Value_subtractMean, ← smoothScalarSubtractMean_toH1]
    simpa only [scalarH1Value_smooth, scalarH1Gradient_smooth,
      smoothScalarGradientL2_subtractMean] using
      hP (smoothScalarSubtractMean (μ := μ) a) (smoothScalarSubtractMean_mean_zero d a)
  exact (hclosed.closure_subset_iff.mpr hsub) u.property

theorem scalarH1_poincare (d : ParallelMetricData g μ) {K : ℝ}
    (hP : SmoothScalarPoincare d K) (u : scalarH1 d)
    (hu : scalarH1Mean d u = 0) :
    ‖scalarH1Value d u‖ ^ 2 ≤ K * ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  simpa only [hu, zero_smul, sub_zero] using scalarH1_centered_poincare d hP u

theorem scalarH1_norm_sq (d : ParallelMetricData g μ) (u : scalarH1 d) :
    ‖u‖ ^ 2 = ‖scalarH1Value d u‖ ^ 2 +
      ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  calc
    ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = _ := by rw [scalarH1_inner]; simp only [real_inner_self_eq_norm_sq]

/-- Restrict the scalar value map to the mean-zero Hilbert subspace. -/
def scalarMeanZeroValue (d : ParallelMetricData g μ) :
    scalarH1MeanZero d →L[ℝ] ScalarL2 g μ :=
  (scalarH1Value d).comp (scalarH1MeanZero d).subtypeL

/-- Restrict each of the four actual scalar derivatives to that subspace. -/
def scalarMeanZeroGradient (d : ParallelMetricData g μ) (i : Fin 4) :
    scalarH1MeanZero d →L[ℝ] ScalarL2 g μ :=
  (scalarH1Gradient d i).comp (scalarH1MeanZero d).subtypeL

/-- The bounded Dirichlet bilinear form on the actual mean-zero space. -/
def scalarMeanZeroDirichlet (d : ParallelMetricData g μ) :
    scalarH1MeanZero d →L[ℝ] scalarH1MeanZero d →L[ℝ] ℝ :=
  fourGradientDirichlet (E := scalarH1MeanZero d) (F := ScalarL2 g μ)
    (scalarMeanZeroGradient d)

theorem scalarMeanZeroDirichlet_apply (d : ParallelMetricData g μ)
    (u v : scalarH1MeanZero d) :
    scalarMeanZeroDirichlet d u v =
      ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u.val) (scalarH1Gradient d i v.val) := by
  exact @fourGradientDirichlet_apply (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroSpace d) _ _ (scalarMeanZeroGradient d) u v

theorem scalarMeanZeroDirichlet_self (d : ParallelMetricData g μ)
    (u : scalarH1MeanZero d) :
    scalarMeanZeroDirichlet d u u = ∑ i : Fin 4, ‖scalarH1Gradient d i u.val‖ ^ 2 := by
  rw [scalarMeanZeroDirichlet_apply]
  simp only [real_inner_self_eq_norm_sq]

/-- The Poincaré estimate controls the full first-jet norm on the mean-zero
subspace; the coercivity constant is exactly `1 / (K + 1)`. -/
theorem scalarMeanZeroDirichlet_coercive (d : ParallelMetricData g μ)
    {K : ℝ} (hK : 0 < K) (hP : SmoothScalarPoincare d K) :
    @IsCoercive (scalarH1MeanZero d) _ (scalarCoercive_meanZeroSpace d)
      (scalarMeanZeroDirichlet d) := by
  have hK₁ : 0 < K + 1 := by linarith
  refine ⟨1 / (K + 1), one_div_pos.mpr hK₁, ?_⟩
  intro u
  have hu := scalarH1_poincare d hP u.val u.property
  have hn := scalarH1_norm_sq d u.val
  have hbound : ‖u‖ ^ 2 ≤ (K + 1) *
      (∑ i : Fin 4, ‖scalarH1Gradient d i u.val‖ ^ 2) := by
    change ‖u.val‖ ^ 2 ≤ _
    nlinarith only [hu, hn]
  rw [scalarMeanZeroDirichlet_self]
  have heq : (1 / (K + 1)) * ‖u‖ * ‖u‖ = ‖u‖ ^ 2 / (K + 1) := by ring
  rw [heq]
  exact (div_le_iff₀ hK₁).mpr (by simpa only [mul_comm] using hbound)

/-- The unique mean-zero weak solution, as a continuous operator on `L²`.
Its sign convention is the positive Dirichlet operator `-Δ`. -/
def scalarMeanZeroWeakPoisson (d : ParallelMetricData g μ) {K : ℝ}
    (hK : 0 < K) (hP : SmoothScalarPoincare d K) :
    ScalarL2 g μ →L[ℝ] scalarH1MeanZero d :=
  @fourGradientSolution (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroInner d) (scalarH1MeanZero_complete d) _ _ _
    (scalarMeanZeroGradient d) (scalarMeanZeroValue d)
    (scalarMeanZeroDirichlet_coercive d hK hP)

theorem scalarMeanZeroWeakPoisson_weak (d : ParallelMetricData g μ) {K : ℝ}
    (hK : 0 < K) (hP : SmoothScalarPoincare d K) (f : ScalarL2 g μ)
    (v : scalarH1MeanZero d) :
    (∑ i : Fin 4, inner ℝ
      (scalarH1Gradient d i (scalarMeanZeroWeakPoisson d hK hP f).val)
      (scalarH1Gradient d i v.val)) = inner ℝ f (scalarH1Value d v.val) := by
  exact @fourGradientSolution_weak (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroInner d) (scalarH1MeanZero_complete d) _ _ _
    (scalarMeanZeroGradient d) (scalarMeanZeroValue d)
    (scalarMeanZeroDirichlet_coercive d hK hP) f v

theorem scalarMeanZeroWeakPoisson_unique (d : ParallelMetricData g μ) {K : ℝ}
    (hK : 0 < K) (hP : SmoothScalarPoincare d K) (f : ScalarL2 g μ)
    (u : scalarH1MeanZero d)
    (hu : ∀ v : scalarH1MeanZero d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u.val) (scalarH1Gradient d i v.val)) =
        inner ℝ f (scalarH1Value d v.val)) :
    u = scalarMeanZeroWeakPoisson d hK hP f := by
  exact @fourGradientSolution_unique (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroInner d) (scalarH1MeanZero_complete d) _ _ _
    (scalarMeanZeroGradient d) (scalarMeanZeroValue d)
    (scalarMeanZeroDirichlet_coercive d hK hP) f u hu

theorem scalarMeanZeroWeakPoisson_existsUnique (d : ParallelMetricData g μ) {K : ℝ}
    (hK : 0 < K) (hP : SmoothScalarPoincare d K) (f : ScalarL2 g μ) :
    ∃! u : scalarH1MeanZero d, ∀ v : scalarH1MeanZero d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u.val) (scalarH1Gradient d i v.val)) =
        inner ℝ f (scalarH1Value d v.val) :=
  ⟨scalarMeanZeroWeakPoisson d hK hP f, scalarMeanZeroWeakPoisson_weak d hK hP f,
    fun u hu => scalarMeanZeroWeakPoisson_unique d hK hP f u hu⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported smooth extension of the power on a positive
bounded interval. This is used only after the weak solution is positive. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter Metric
open scoped _root_.Topology ContDiff NNReal

noncomputable section

private def positivePowerInner (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : ℝ) where
  rIn := a / 4
  rOut := a / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private def positivePowerOuter (B : ℝ) (hB : 0 ≤ B) : ContDiffBump (0 : ℝ) where
  rIn := B + 1
  rOut := B + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

private def positivePowerExtension (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (t : ℝ) : ℝ :=
  positivePowerOuter B hB t * (1 - positivePowerInner a ha t) * t ^ q

private theorem positivePowerExtension_smooth (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    ContDiff ℝ ∞ (positivePowerExtension a B q ha hB) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hone := (positivePowerInner a ha).eventuallyEq_one
    filter_upwards [hone] with s hs
    simp only [positivePowerExtension, hs, Pi.one_apply, sub_self, mul_zero, zero_mul]
  · exact (((positivePowerOuter B hB).contDiff.contDiffAt.mul
      (contDiffAt_const.sub (positivePowerInner a ha).contDiff.contDiffAt)).mul
        (contDiffAt_id.rpow_const_of_ne ht))

private theorem positivePowerExtension_compact (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    HasCompactSupport (positivePowerExtension a B q ha hB) :=
  ((positivePowerOuter B hB).hasCompactSupport.mul_right).mul_right

private theorem positivePowerExtension_eq (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    {t : ℝ} (hat : a ≤ t) (htB : t ≤ B) :
    positivePowerExtension a B q ha hB t = t ^ q := by
  have ht : 0 < t := ha.trans_le hat
  have hinner : positivePowerInner a ha t = 0 := by
    apply ContDiffBump.zero_of_le_dist
    change a / 2 ≤ dist t 0
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have houter : positivePowerOuter B hB t = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist t 0 ≤ B + 1
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  simp only [positivePowerExtension, hinner, houter, sub_zero, one_mul]

private theorem positivePowerExtension_deriv (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    {t : ℝ} (hat : a ≤ t) (htB : t ≤ B) :
    deriv (positivePowerExtension a B q ha hB) t = q * t ^ (q - 1) := by
  have ht : 0 < t := ha.trans_le hat
  have he : positivePowerExtension a B q ha hB =ᶠ[𝓝 t] (fun s : ℝ => s ^ q) := by
    filter_upwards [Ioo_mem_nhds (show a / 2 < t by linarith)
      (show t < B + 1 by linarith)] with s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hi : positivePowerInner a ha s = 0 := by
      apply ContDiffBump.zero_of_le_dist
      change a / 2 ≤ dist s 0
      rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact hs.1.le
    have ho : positivePowerOuter B hB s = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      change dist s 0 ≤ B + 1
      rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact hs.2.le
    simp only [positivePowerExtension, hi, ho, sub_zero, one_mul]
  exact ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).congr_of_eventuallyEq he).deriv

/-- The extension is smooth on all of R, vanishes at zero, and has bounded
first derivative. On the positive interval it is exactly the desired power. -/
theorem scalar_positive_power_extension (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ φ 0 = 0 ∧
      (∃ D : ℝ≥0, ∀ t, |deriv φ t| ≤ D) ∧
      ∀ t ∈ Icc a B, φ t = t ^ q ∧ deriv φ t = q * t ^ (q - 1) := by
  let φ := positivePowerExtension a B q ha hB
  have hφ : ContDiff ℝ ∞ φ := positivePowerExtension_smooth a B q ha hB
  have hc : HasCompactSupport φ := positivePowerExtension_compact a B q ha hB
  have hd := (hφ.continuous_deriv (by simp)).bounded_above_of_compact_support hc.deriv
  obtain ⟨D, hD⟩ := hd
  refine ⟨φ, hφ, hc, ?_, ⟨⟨max D 0, le_max_right _ _⟩, ?_⟩, ?_⟩
  · have hone : positivePowerInner a ha 0 = 1 :=
      (positivePowerInner a ha).one_of_mem_closedBall (mem_closedBall_self (by
        change 0 ≤ a / 4
        positivity))
    simp only [φ, positivePowerExtension, hone, sub_self, mul_zero, zero_mul]
  · intro t
    exact (show |deriv φ t| ≤ D by simpa only [Real.norm_eq_abs] using hD t).trans (le_max_left _ _)
  · intro t ht
    exact ⟨positivePowerExtension_eq a B q ha hB ht.1 ht.2,
      positivePowerExtension_deriv a B q ha hB ht.1 ht.2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual first-jet completion.  This identifies
the variational equation with the distributional scalar Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem smoothScalarDirichlet_laplacian_pairing (d : ParallelMetricData g μ)
    (a b : SmoothScalar (M := M)) :
    smoothScalarDirichlet d a b =
      -(inner ℝ (smoothScalarValueL2 g μ a) (smoothScalarLaplacianL2 (μ := μ) b)) := by
  have h := smoothScalarShiftedRhs_pairing d b a
  rw [smoothScalarShiftedRhs, inner_sub_left,
    smoothScalarDirichlet_symm d b a,
    real_inner_comm (smoothScalarValueL2 g μ a)
      (smoothScalarLaplacianL2 (μ := μ) b)] at h
  linarith

theorem scalarH1_green (d : ParallelMetricData g μ) (u : scalarH1 d)
    (b : SmoothScalar (M := M)) :
    (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (smoothScalarGradientL2 d i b)) =
      -(inner ℝ (scalarH1Value d u) (smoothScalarLaplacianL2 (μ := μ) b)) := by
  let p₀ : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none
  let pᵢ (i : Fin 4) : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)
  let S : Set (ScalarJetL2 g μ) := {v |
    (∑ i : Fin 4, inner ℝ (pᵢ i v) (smoothScalarGradientL2 d i b)) =
      -(inner ℝ (p₀ v) (smoothScalarLaplacianL2 (μ := μ) b))}
  have hclosed : IsClosed S := isClosed_eq
    (continuous_finsetSum _ (fun i _ => (pᵢ i).continuous.inner continuous_const))
    (p₀.continuous.inner continuous_const).neg
  have hsub : range (smoothScalarFirstJet d) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact smoothScalarDirichlet_laplacian_pairing d a b
  exact (hclosed.closure_subset_iff.mpr hsub) u.property

/-- The first-jet completion has no nonzero element with zero scalar value:
Green's identity determines every derivative coordinate. -/
theorem scalarH1Value_injective (d : ParallelMetricData g μ) :
    Function.Injective (scalarH1Value d) := by
  intro u v huv
  apply scalarH1_eq_of_smooth_tests d
  intro b
  rw [scalarH1_inner, scalarH1_inner]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth]
  rw [scalarH1_green d u b, scalarH1_green d v b, huv]

theorem scalarH1_eq_smooth_of_value (d : ParallelMetricData g μ)
    (u : scalarH1 d) (a : SmoothScalar (M := M))
    (hu : scalarH1Value d u = smoothScalarValueL2 g μ a) :
    u = smoothScalarToH1 d a :=
  scalarH1Value_injective d hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Sobolev energy as a genuine Hilbert norm.  Only the four
first-derivative coordinates are rescaled; the value coordinate is unchanged. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff BigOperators

noncomputable section

private def scalarJetWeight : Option (Fin 4) → ℝ
  | none => 1
  | some _ => Real.sqrt (1 / 2)

private theorem scalarJetWeight_ne_zero (j : Option (Fin 4)) : scalarJetWeight j ≠ 0 := by
  cases j with
  | none => norm_num [scalarJetWeight]
  | some i => exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))

private def scalarWeightEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Option (Fin 4)) : E ≃L[ℝ] E where
  toFun u := scalarJetWeight j • u
  invFun u := (scalarJetWeight j)⁻¹ • u
  left_inv u := inv_smul_smul₀ (scalarJetWeight_ne_zero j) u
  right_inv u := smul_inv_smul₀ (scalarJetWeight_ne_zero j) u
  map_add' u v := smul_add _ _ _
  map_smul' r u := by simp only [RingHom.id_apply, smul_smul]; rw [mul_comm]
  continuous_toFun := continuous_const_smul _
  continuous_invFun := continuous_const_smul _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- Invertible diagonal rescaling of the actual scalar first jet. -/
def scalarWeightedJetEquiv (g : SmoothMetric M) (μ : Measure (FrameBundle g)) :
    ScalarJetL2 g μ ≃L[ℝ] ScalarJetL2 g μ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin 4) => ScalarL2 g μ)).trans
    ((ContinuousLinearEquiv.piCongrRight fun j => scalarWeightEquiv (ScalarL2 g μ) j).trans
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Option (Fin 4) => ScalarL2 g μ)).symm)

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
@[simp] theorem scalarWeightedJetEquiv_none (u : ScalarJetL2 g μ) :
    scalarWeightedJetEquiv g μ u none = u none := by
  change (1 : ℝ) • u none = u none
  exact one_smul _ _

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
@[simp] theorem scalarWeightedJetEquiv_some (u : ScalarJetL2 g μ) (i : Fin 4) :
    scalarWeightedJetEquiv g μ u (some i) = Real.sqrt (1 / 2) • u (some i) := rfl

/-- The closed image of actual smooth first jets, with the Sobolev energy norm. -/
def scalarWeightedH1 (d : ParallelMetricData g μ) : Submodule ℝ (ScalarJetL2 g μ) :=
  (scalarH1 d).map (scalarWeightedJetEquiv g μ).toLinearMap

theorem scalarWeightedH1_closed (d : ParallelMetricData g μ) :
    IsClosed (scalarWeightedH1 d : Set (ScalarJetL2 g μ)) := by
  rw [scalarWeightedH1, Submodule.map_coe]
  exact (scalarWeightedJetEquiv g μ).isClosed_image.mpr
    (Submodule.isClosed_topologicalClosure _)

instance scalarWeightedH1_complete (d : ParallelMetricData g μ) :
    CompleteSpace (scalarWeightedH1 d) :=
  (scalarWeightedH1_closed d).isComplete.completeSpace_coe

/-- The weighted energy space is continuously linearly equivalent to actual H¹. -/
def scalarWeightedH1Equiv (d : ParallelMetricData g μ) :
    scalarH1 d ≃L[ℝ] scalarWeightedH1 d :=
  (scalarWeightedJetEquiv g μ).submoduleMap (scalarH1 d)

/-- Continuous recovery of the original first jet, including its value. -/
def scalarWeightedH1ToH1 (d : ParallelMetricData g μ) :
    scalarWeightedH1 d →L[ℝ] scalarH1 d :=
  (scalarWeightedH1Equiv d).symm.toContinuousLinearMap

@[simp] theorem scalarWeightedH1ToH1_equiv (d : ParallelMetricData g μ) (u : scalarH1 d) :
    scalarWeightedH1ToH1 d (scalarWeightedH1Equiv d u) = u :=
  (scalarWeightedH1Equiv d).symm_apply_apply u

/-- The exact weighted inner product, on arbitrary completed scalar jets. -/
theorem scalarWeightedH1_inner (d : ParallelMetricData g μ) (u v : scalarH1 d) :
    inner ℝ (scalarWeightedH1Equiv d u) (scalarWeightedH1Equiv d v) =
      inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
        (1 / 2 : ℝ) * ∑ i : Fin 4,
          inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
  change (∑ j : Option (Fin 4),
    inner ℝ (scalarWeightedJetEquiv g μ u.val j)
      (scalarWeightedJetEquiv g μ v.val j)) = _
  rw [Fintype.sum_option]
  simp only [scalarWeightedJetEquiv_none, scalarWeightedJetEquiv_some,
    inner_smul_left, inner_smul_right, conj_trivial]
  have hs : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = (1 / 2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  change inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
    (∑ i : Fin 4, Real.sqrt (1 / 2) *
      (Real.sqrt (1 / 2) * inner ℝ (scalarH1Gradient d i u)
        (scalarH1Gradient d i v))) = _
  simp only [← mul_assoc, hs, Finset.mul_sum]

theorem scalarWeightedH1_norm_sq (d : ParallelMetricData g μ) (u : scalarH1 d) :
    ‖scalarWeightedH1Equiv d u‖ ^ 2 = ‖scalarH1Value d u‖ ^ 2 +
      (1 / 2 : ℝ) * ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, scalarWeightedH1_inner]
  simp only [real_inner_self_eq_norm_sq]

/-- A smooth function, regarded as an element of the weighted Hilbert space. -/
def smoothScalarToWeightedH1 (d : ParallelMetricData g μ) :
    SmoothScalar (M := M) →ₗ[ℝ] scalarWeightedH1 d where
  toFun a := scalarWeightedH1Equiv d (smoothScalarToH1 d a)
  map_add' a b := by
    rw [← map_add]
    congr 1
    exact Subtype.ext ((smoothScalarFirstJet d).map_add a b)
  map_smul' r a := by
    rw [← map_smul]
    congr 1
    exact Subtype.ext ((smoothScalarFirstJet d).map_smul r a)

@[simp] theorem scalarWeightedH1ToH1_smooth (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) :
    scalarWeightedH1ToH1 d (smoothScalarToWeightedH1 d a) = smoothScalarToH1 d a :=
  scalarWeightedH1ToH1_equiv d _

theorem smoothScalarToWeightedH1_dense (d : ParallelMetricData g μ) :
    DenseRange (smoothScalarToWeightedH1 d) := by
  have hd : DenseRange (fun a : SmoothScalar (M := M) => smoothScalarToH1 d a) := by
    change Dense (range (fun a : SmoothScalar (M := M) => smoothScalarToH1 d a))
    rw [Topology.IsInducing.subtypeVal.dense_iff]
    intro u
    apply closure_mono (s := range (smoothScalarFirstJet d)) ?_ u.property
    rintro v ⟨a, rfl⟩
    exact ⟨smoothScalarToH1 d a, ⟨a, rfl⟩, rfl⟩
  exact (scalarWeightedH1Equiv d).surjective.denseRange.comp hd
    (scalarWeightedH1Equiv d).continuous

section Canonical

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarWeighted_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

/-- On smooth scalars the Hilbert norm is exactly the Sobolev quotient denominator. -/
theorem smoothScalarToWeightedH1_norm_sq (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    ‖smoothScalarToWeightedH1 d a‖ ^ 2 =
      (∫ x, a.val x ^ 2 ∂normalizedVolume g) + smoothScalarDirichlet d a a / 2 := by
  rw [show smoothScalarToWeightedH1 d a =
    scalarWeightedH1Equiv d (smoothScalarToH1 d a) from rfl, scalarWeightedH1_norm_sq]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth]
  have hv : ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 =
      ∫ x, a.val x ^ 2 ∂normalizedVolume g := by
    rw [← scalarBasePullback_smooth g o a, (scalarBasePullback g o).norm_map,
      ← real_inner_self_eq_norm_sq]
    change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ)))
      (ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ))) = _
    rw [ContinuousMap.inner_toLp]
    simp only [conj_trivial, pow_two]
    rfl
  rw [hv]
  simp only [smoothScalarDirichlet, real_inner_self_eq_norm_sq]
  ring

end Canonical
end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite tensor estimates for the chart localization of two-forms.
The bounds involve the actual value and covariant energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def tensorTransportWeight (n : ℕ) (P : Mat4) : ℝ :=
  ∑ a : Fin n → Fin 4, ∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)|

theorem tensorTransportWeight_nonneg (n : ℕ) (P : Mat4) :
    0 ≤ tensorTransportWeight n P :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem tensorTransportWeight_continuous (n : ℕ) : Continuous (tensorTransportWeight n) := by
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (continuous_finsetProd _ (fun i _ =>
    (continuous_apply (a i)).comp (continuous_apply (b i)))).abs

theorem frameTensor_abs_le_weight {n : ℕ} (P : Mat4) (T : CovariantCoordinates n)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ a, |T a| ≤ C) (a : Fin n → Fin 4) :
    |frameTensor P T a| ≤ tensorTransportWeight n P * C := by
  calc
    _ ≤ ∑ b : Fin n → Fin 4, |(∏ i, P (b i) (a i)) * T b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)| * C := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hT b) (abs_nonneg _)
    _ = (∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)|) * C :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      unfold tensorTransportWeight
      exact Finset.single_le_sum (f := fun a : Fin n → Fin 4 =>
        ∑ b : Fin n → Fin 4, |∏ i, P (b i) (a i)|)
        (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (∏ i, P (b i) (a i))))
        (Finset.mem_univ a)

theorem tensor_component_sq_le {n : ℕ} (T : CovariantCoordinates n) (a : Fin n → Fin 4) :
    |T a| ^ 2 ≤ frameTensorSquareNorm T := by
  rw [sq_abs]
  simpa only [frameTensorSquareNorm, frameTensorPairing, pow_two] using
    (Finset.single_le_sum (fun b _ => sq_nonneg (T b)) (Finset.mem_univ a))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartTransport (g : SmoothMetric M) (c : M) (z : FourSpace) : Mat4 :=
  (chartGramMatrix g c 1 z)ᵀ * metricInChart g c z

theorem twoFormChartTransport_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (twoFormChartTransport g c) (chartAt FourSpace c).target := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j z hz
  change ContinuousWithinAt (fun w => ∑ k,
    chartGramMatrix g c 1 w k i * metricInChart g c w k j) _ z
  exact (ContDiffAt.sum (fun k _ =>
    (chartGramMatrix_contDiffAt g c 1 z hz k i).mul
      (metricInChart_contDiffAt g c z hz k j))).continuousAt.continuousWithinAt

theorem twoFormCoordinates_abs_le (u : M → TwoFormFour) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 2 → Fin 4) :
    |twoFormCoordinates o u c z a| ≤
      2 * tensorTransportWeight 2 (twoFormChartTransport g c z) *
        ‖u ((chartAt FourSpace c).symm z)‖ := by
  rw [twoFormCoordinates_from_chart o u c 1 (by simp) z hz]
  have hn : ‖twoFormChartValue o u c 1 (by simp) z‖ =
      ‖u ((chartAt FourSpace c).symm z)‖ := by
    simp only [twoFormChartValue, dite_eq_left hz]
    exact twoFormFrameValue_norm o u _
  have hbound (b : Fin 2 → Fin 4) :
      |twoFormTensor (twoFormChartValue o u c 1 (by simp) z) b| ≤
        2 * ‖u ((chartAt FourSpace c).symm z)‖ := by
    have hb := tensor_component_sq_le
      (twoFormTensor (twoFormChartValue o u c 1 (by simp) z)) b
    rw [twoFormTensor_norm, hn] at hb
    nlinarith [abs_nonneg (twoFormTensor (twoFormChartValue o u c 1 (by simp) z) b),
      norm_nonneg (u ((chartAt FourSpace c).symm z))]
  have h := frameTensor_abs_le_weight (twoFormChartTransport g c z) _
    (2 * ‖u ((chartAt FourSpace c).symm z)‖) (by positivity) hbound a
  exact h.trans_eq (by ring)

theorem TwoFormSmooth.gramCovariantCoordinates {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormFramedCovariantDerivative o u (chartGramSection g c 1 (by simp) ⟨z, hz⟩) =
      frameTensor (chartGramMatrix g c 1 z) (twoFormCovariantCoordinates o u c z) := by
  let x := (chartAt FourSpace c).symm z
  have ht := hu.covariant_transition c x z hz (mem_chart_source FourSpace x)
  rw [chartTransitionMatrix_to_center c z hz] at ht
  change twoFormCovariantCoordinates o u c z = frameTensor (chartInverseMatrix c z)
    (twoFormCovariantCoordinates o u x (chartAt FourSpace x x)) at ht
  change frameTensor (chartInverseMatrix c z * chartGramMatrix g c 1 z)
    (twoFormCovariantCoordinates o u x (chartAt FourSpace x x)) = _
  rw [frameTensor_mul, ← ht]

theorem TwoFormSmooth.covariantCoordinates_abs_le {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 3 → Fin 4) :
    |twoFormCovariantCoordinates o u c z a| ≤
      2 * tensorTransportWeight 3 (twoFormChartTransport g c z) *
        Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z)) := by
  let e := chartGramSection g c 1 (by simp) ⟨z, hz⟩
  have he : e.base = (chartAt FourSpace c).symm z := rfl
  have hnorm : frameTensorSquareNorm (twoFormFramedCovariantDerivative o u e) =
      2 * twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z) := by
    have h := twoFormCovariantPairing_eq_frame o u u e
    change twoFormCovariantPairing o u u e.base =
      (1 / 2 : ℝ) * frameTensorSquareNorm (twoFormFramedCovariantDerivative o u e) at h
    rw [he] at h
    linarith
  have hback : twoFormCovariantCoordinates o u c z =
      frameTensor (twoFormChartTransport g c z) (twoFormFramedCovariantDerivative o u e) := by
    rw [hu.gramCovariantCoordinates c z hz, ← frameTensor_mul]
    have h := chartGramMatrix_normalizes g c 1 (by simp) ⟨z, hz⟩
    change (chartGramMatrix g c 1 z)ᵀ * metricInChart g c z *
      chartGramMatrix g c 1 z = 1 at h
    change twoFormChartTransport g c z * chartGramMatrix g c 1 z = 1 at h
    rw [mul_eq_one_comm.mp h, frameTensor_one]
  have hbound (b : Fin 3 → Fin 4) : |twoFormFramedCovariantDerivative o u e b| ≤
      2 * Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z)) := by
    have hb := tensor_component_sq_le (twoFormFramedCovariantDerivative o u e) b
    rw [hnorm] at hb
    have hs := Real.sq_sqrt
      (twoFormCovariantPairing_self_nonneg o u ((chartAt FourSpace c).symm z))
    nlinarith [abs_nonneg (twoFormFramedCovariantDerivative o u e b), Real.sqrt_nonneg
      (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))]
  rw [hback]
  have h := frameTensor_abs_le_weight (twoFormChartTransport g c z) _
    (2 * Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z)))
    (by positivity) hbound a
  exact h.trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual covariant derivative retains the alternating two-form slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem twoFormFramedValue_skew (u : M → TwoFormFour) (e : FrameBundle g) (j k : Fin 4) :
    twoFormFramedValue o u e ![k,j] = -twoFormFramedValue o u e ![j,k] := by
  rw [twoFormFramedValue_eq]
  exact congrArg (fun A : Mat4 => A j k) (twoFormMatrix_skew (twoFormFrameValue o u e))

theorem TwoFormSmooth.framedCovariant_skew (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) (i j k : Fin 4) :
    twoFormFramedCovariantDerivative o u e ![i,k,j] =
      -twoFormFramedCovariantDerivative o u e ![i,j,k] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e :=
    actualParallelMetricData_zero g (canonicalFrameMeasure g o)
      (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hk := hu.framedValue_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![k,j]
  have hj := (hu.framedValue_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k]).neg
  have heq : (fun t => -(twoFormFramedValue o u (γ t) ![j,k])) =
      fun t => twoFormFramedValue o u (γ t) ![k,j] := by
    funext t
    exact (twoFormFramedValue_skew u (γ t) j k).symm
  change HasDerivAt (fun t => -(twoFormFramedValue o u (γ t) ![j,k]))
    (-twoFormFramedCovariantDerivative o u (γ 0) (Fin.cons i ![j,k])) 0 at hj
  rw [heq] at hj
  have h := hk.unique hj
  rw [hzero] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed integration by parts turns the first-order cross terms into
the actual curvature action on two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem smoothTwoForm_cross_curvature (hRic : RicciThree g) (u v : smoothTwoForms o) :
    (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
        twoFormFramedCovariantDerivative o v.val e ![j,j,k] ∂canonicalFrameMeasure g o) -
    (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
        twoFormFramedCovariantDerivative o v.val e ![j,i,k] ∂canonicalFrameMeasure g o) =
    ∑ i, ∑ j, ∑ k, ∫ e, twoFormFramedValue o u.val e ![i,k] *
      tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
        (twoFormFramedValue o v.val e) ![j,k] ∂canonicalFrameMeasure g o := by
  let μ := canonicalFrameMeasure g o
  let A := fun i j k => ∫ e, twoFormFramedValue o u.val e ![i,k] *
    twoFormFramedSecondDerivative o v.val e ![i,j,j,k] ∂μ
  let B := fun i j k => ∫ e, twoFormFramedValue o u.val e ![i,k] *
    twoFormFramedSecondDerivative o v.val e ![j,i,j,k] ∂μ
  let C := fun i j k => ∫ e, twoFormFramedValue o u.val e ![i,k] *
    tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
      (twoFormFramedValue o v.val e) ![j,k] ∂μ
  have hint (a : Fin 2 → Fin 4) (b : Fin 4 → Fin 4) :
      Integrable (fun e => twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o v.val e b) μ :=
    (((continuous_apply a).comp u.property.continuous_framedValue).mul
      ((continuous_apply b).comp v.property.continuous_framedSecondDerivative)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hAB (i j k : Fin 4) : A i j k - B i j k = -C i j k := by
    change (∫ e, _ ∂μ) - (∫ e, _ ∂μ) = -(∫ e, _ ∂μ)
    rw [← integral_sub (hint ![i,k] ![i,j,j,k]) (hint ![i,k] ![j,i,j,k]), ← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with e
    have hc := v.property.framed_commutator e i j ![j,k]
    change twoFormFramedSecondDerivative o v.val e ![i,j,j,k] -
      twoFormFramedSecondDerivative o v.val e ![j,i,j,k] = _ at hc
    rw [← mul_sub, hc, mul_neg]
  have hfirst : (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
      twoFormFramedCovariantDerivative o v.val e ![j,j,k] ∂μ) =
        -(∑ i, ∑ j, ∑ k, A i j k) := by
    have h (i j k : Fin 4) : (∫ e,
        twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
        twoFormFramedCovariantDerivative o v.val e ![j,j,k] ∂μ) = -A i j k :=
      smoothTwoForm_mixed_green hRic u v i j ![i,k] ![j,k]
    simp only [h, Finset.sum_neg_distrib]
  have hsecond : (∑ i, ∑ j, ∑ k, ∫ e,
      twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
      twoFormFramedCovariantDerivative o v.val e ![j,i,k] ∂μ) =
        -(∑ i, ∑ j, ∑ k, B i j k) := by
    rw [Finset.sum_comm]
    have h (i j k : Fin 4) : (∫ e,
        twoFormFramedCovariantDerivative o u.val e ![j,i,k] *
        twoFormFramedCovariantDerivative o v.val e ![i,j,k] ∂μ) = -B i j k :=
      smoothTwoForm_mixed_green hRic u v j i ![i,k] ![j,k]
    simp only [h, Finset.sum_neg_distrib]
  change _ - _ = ∑ i, ∑ j, ∑ k, C i j k
  rw [hfirst, hsecond]
  have hs : (∑ i, ∑ j, ∑ k, A i j k) - (∑ i, ∑ j, ∑ k, B i j k) =
      -(∑ i, ∑ j, ∑ k, C i j k) := by
    simp only [← Finset.sum_sub_distrib]
    simp_rw [hAB, Finset.sum_neg_distrib]
  linarith only [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The H1 pairing against a smooth two-form extends to the actual L2
completion by the rough Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormGreenLinear (v : SmoothL2TwoForm o) : SmoothL2TwoForm o →ₗ[ℝ] ℝ where
  toFun u := smoothTwoFormL2Inner (u : smoothTwoForms o) v +
    smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v
  map_add' u w := by
    exact (congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_add (u : smoothTwoForms o) w v)
      (smoothTwoFormCovariantEnergy_add (u : smoothTwoForms o) w v)).trans
      (add_add_add_comm _ _ _ _)
  map_smul' r u := by
    exact (congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_smul r (u : smoothTwoForms o) v)
      (smoothTwoFormCovariantEnergy_smul r (u : smoothTwoForms o) v)).trans
      (mul_add r _ _).symm

theorem smoothTwoFormGreenLinear_bound (hRic : RicciThree g)
    (v : SmoothL2TwoForm o) (u : SmoothL2TwoForm o) :
    ‖smoothTwoFormGreenLinear v u‖ ≤
      (‖v‖ + ‖smoothTwoFormTensorTraceL2 v‖) * ‖u‖ := by
  have hL2 : |smoothTwoFormL2Inner (u : smoothTwoForms o) v| ≤
      ‖u‖ * ‖v‖ :=
    abs_real_inner_le_norm u v
  have hE := smoothTwoFormCovariantEnergy_L2_bound hRic u v
  change |smoothTwoFormL2Inner (u : smoothTwoForms o) v +
    smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v| ≤ _
  calc
    _ ≤ |smoothTwoFormL2Inner (u : smoothTwoForms o) v| +
      |smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v| := abs_add_le _ _
    _ ≤ ‖u‖ * ‖v‖ +
      ‖u‖ * ‖smoothTwoFormTensorTraceL2 v‖ := add_le_add hL2 hE
    _ = _ := by ring

def smoothTwoFormGreenDual (hRic : RicciThree g) (v : SmoothL2TwoForm o) :
    SmoothL2TwoForm o →L[ℝ] ℝ :=
  (smoothTwoFormGreenLinear v).mkContinuous
    (‖v‖ + ‖smoothTwoFormTensorTraceL2 v‖)
    (smoothTwoFormGreenLinear_bound hRic v)

def twoFormGreenDual (hRic : RicciThree g) (v : SmoothL2TwoForm o) :
    TwoFormL2 o →L[ℝ] ℝ :=
  (smoothTwoFormGreenDual hRic v).fromCompletion

theorem twoFormGreenDual_smooth (hRic : RicciThree g) (v : SmoothL2TwoForm o)
    (u : SmoothL2TwoForm o) :
    twoFormGreenDual hRic v (smoothTwoFormToL2 u) =
      smoothTwoFormL2Inner (u : smoothTwoForms o) v +
        smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem twoFormH1_inner_smooth (hRic : RicciThree g) (u : TwoFormH1 o)
    (v : SmoothH1TwoForm o) :
    inner ℝ u (smoothTwoFormToH1 v) =
      twoFormGreenDual hRic (smoothH1ToL2 v) (twoFormH1ToL2 u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (continuous_id.inner continuous_const)
      ((twoFormGreenDual hRic (smoothH1ToL2 v)).continuous.comp
        twoFormH1ToL2.continuous)) ?_
  intro w
  change inner ℝ (smoothTwoFormToH1 w) (smoothTwoFormToH1 v) =
    twoFormGreenDual hRic (smoothH1ToL2 v) (twoFormH1ToL2 (smoothTwoFormToH1 w))
  rw [twoFormH1ToL2_smooth, twoFormGreenDual_smooth]
  exact UniformSpace.Completion.inner_coe w v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Realize the actual L2 completion inside square-integrable tensors on
the canonical frame bundle. The adjoint reconstructs L2 sections from
finite-regularity frame tensors without assuming they are smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def smoothTwoFormTensorLinear : SmoothL2TwoForm o →ₗ[ℝ]
    Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) where
  toFun u := smoothTwoFormTensorValueL2 (u : smoothTwoForms o)
  map_add' u v := by
    have he : smoothTwoFormEuclideanValue ((u + v : SmoothL2TwoForm o) : smoothTwoForms o) =
        smoothTwoFormEuclideanValue (u : smoothTwoForms o) +
          smoothTwoFormEuclideanValue (v : smoothTwoForms o) := by
      ext e a
      simp only [ContinuousMap.add_apply, PiLp.add_apply]
      change twoFormFramedValue o ((u : smoothTwoForms o).val + (v : smoothTwoForms o).val) e a =
        twoFormFramedValue o (u : smoothTwoForms o).val e a +
          twoFormFramedValue o (v : smoothTwoForms o).val e a
      rw [twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormFrameValue_add]
      exact congrFun (twoFormTensorLinear.map_add _ _) a
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_add]
    rfl
  map_smul' r u := by
    have he : smoothTwoFormEuclideanValue ((r • u : SmoothL2TwoForm o) : smoothTwoForms o) =
        r • smoothTwoFormEuclideanValue (u : smoothTwoForms o) := by
      ext e a
      simp only [ContinuousMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
      change twoFormFramedValue o (r • (u : smoothTwoForms o).val) e a =
        r * twoFormFramedValue o (u : smoothTwoForms o).val e a
      rw [twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormFrameValue_smul]
      exact congrFun (twoFormTensorLinear.map_smul r _) a
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_smul]
    rfl

def smoothTwoFormTensorL2 : SmoothL2TwoForm o →L[ℝ]
    Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  (smoothTwoFormTensorLinear (o := o)).mkContinuous 2
    (fun u => smoothTwoFormTensorValueL2_norm_le u)

def twoFormTensorL2 : TwoFormL2 o →L[ℝ]
    Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  (smoothTwoFormTensorL2 (o := o)).fromCompletion

theorem twoFormTensorL2_smooth (u : SmoothL2TwoForm o) :
    twoFormTensorL2 (smoothTwoFormToL2 u) = smoothTwoFormTensorValueL2 (u : smoothTwoForms o) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

theorem twoFormTensorL2_norm_sq (u : TwoFormL2 o) :
    ‖twoFormTensorL2 u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq ((twoFormTensorL2.continuous.norm).pow 2)
      (continuous_const.mul (continuous_norm.pow 2))) ?_
  intro v
  change ‖twoFormTensorL2 (smoothTwoFormToL2 v)‖ ^ 2 = 2 * ‖smoothTwoFormToL2 v‖ ^ 2
  rw [twoFormTensorL2_smooth]
  calc
    _ = 2 * smoothTwoFormL2Inner (v : smoothTwoForms o) v :=
      smoothTwoFormTensorValueL2_norm_sq (v : smoothTwoForms o)
    _ = _ := by
      change 2 * inner ℝ v v = 2 * ‖smoothTwoFormToL2 v‖ ^ 2
      rw [smoothTwoFormToL2.norm_map, real_inner_self_eq_norm_sq]

theorem twoFormTensorL2_inner (u v : TwoFormL2 o) :
    inner ℝ (twoFormTensorL2 u) (twoFormTensorL2 v) = 2 * inner ℝ u v := by
  have h := norm_add_sq_real (twoFormTensorL2 u) (twoFormTensorL2 v)
  rw [← map_add, twoFormTensorL2_norm_sq, twoFormTensorL2_norm_sq,
    twoFormTensorL2_norm_sq] at h
  nlinarith [norm_add_sq_real u v]

def twoFormFromTensorL2 : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) →L[ℝ] TwoFormL2 o :=
  (1 / 2 : ℝ) • twoFormTensorL2.adjoint

theorem twoFormFromTensorL2_pairing (F : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o))
    (u : TwoFormL2 o) :
    inner ℝ (twoFormFromTensorL2 F) u = (1 / 2 : ℝ) * inner ℝ F (twoFormTensorL2 u) := by
  simp only [twoFormFromTensorL2, smul_apply,
    real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

theorem twoFormFromTensorL2_left_inverse (u : TwoFormL2 o) :
    twoFormFromTensorL2 (twoFormTensorL2 u) = u := by
  apply ext_inner_right ℝ
  intro v
  rw [twoFormFromTensorL2_pairing, twoFormTensorL2_inner]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence for the two regularized moments in the Weyl
gap argument. All bounds are uniform in the smoothing parameter. -/
namespace PositiveEinsteinFour.Geometry
open MeasureTheory Filter Set
open scoped _root_.Topology
noncomputable section

def weylGapEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem weylGapEpsilon_pos (n : ℕ) : 0 < weylGapEpsilon n := by
  unfold weylGapEpsilon
  positivity

theorem weylGapEpsilon_le_one (n : ℕ) : weylGapEpsilon n ≤ 1 := by
  unfold weylGapEpsilon
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem weylGapEpsilon_tendsto : Tendsto weylGapEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_weyl_regularized_power_tendsto (v w : C(Ω, ℝ))
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun n => ∫ x, w x * (v x ^ 2 + weylGapEpsilon n ^ 2) ^ p ∂μ) atTop
      (𝓝 (∫ x, w x * (v x ^ 2) ^ p ∂μ)) := by
  have hpow : Continuous (fun x : Ω => (v x ^ 2 + 1) ^ p) :=
    ((v.continuous.pow 2).add continuous_const).rpow_const (fun _ => Or.inr hp)
  apply tendsto_integral_of_dominated_convergence (fun x => |w x| * (v x ^ 2 + 1) ^ p)
  · intro n
    exact (w.continuous.mul (((v.continuous.pow 2).add continuous_const).rpow_const
      (fun _ => Or.inr hp))).aestronglyMeasurable
  · exact (w.continuous.abs.mul hpow).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) p)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.rpow_le_rpow (by positivity) _ hp
    have h0 := weylGapEpsilon_pos n
    have h1 := weylGapEpsilon_le_one n
    nlinarith
  · filter_upwards [] with x
    have ht : Tendsto (fun n => v x ^ 2 + weylGapEpsilon n ^ 2) atTop (𝓝 (v x ^ 2)) := by
      simpa using (tendsto_const_nhds (x := v x ^ 2)).add (weylGapEpsilon_tendsto.pow 2)
    exact tendsto_const_nhds.mul (ht.rpow_const (Or.inr hp))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal differential of the actual exponential is the global
Jacobi matrix. The initial velocity is varied in its actual frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_frame_endpoint_time (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (t : ℝ) (ht : 0 < t) (v : FourSpace) (hv : v ≠ 0) :
    (radialCoordinateFlow g o c d t
      (chartAt FourSpace c e.base, frameMomentumMap g c e v)).1 =
      chartAt FourSpace d (frameExponential g o e (t • v)) := by
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c (r, unitTangentTurn e q) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  rw [← hstate, radialCoordinateFlow_at_state g o c d t _ he]
  change chartAt FourSpace d (unitTangentFlowMap g o (r.val * t) (unitTangentTurn e q)).base = _
  rw [← hvr, smul_smul]
  have h := frameExponential_radial g o e q ⟨t * r.val, mul_pos ht r.property⟩
  simpa only [unitGeodesic, mul_comm] using congrArg (chartAt FourSpace d) h.symm

omit [T2Space M] [CompactSpace M] in
theorem frameMomentumMap_apply (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) :
    frameMomentumMap g c e v = WithLp.toLp 2
      (metricInChart g c (chartAt FourSpace c e.base) *ᵥ
        (frameChartMatrix g c e *ᵥ WithLp.ofLp v)) := by
  let Q := (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap
  have hcol (i : Fin 4) : Q (coordinateVector i) =
      WithLp.toLp 2 (fun j => frameChartMatrix g c e j i) := by
    change chartForwardOperator c e.base (e.frame.map (coordinateVector i)) = _
    rw [e.frame.map_coordinateVector]
    exact (frameChart_column_eq_derivative g c e i he).symm
  have hQ : Q v = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ WithLp.ofLp v) := by
    have hsum : (∑ i, (WithLp.ofLp v) i • coordinateVector i) = v :=
      sum_coordinateVector (WithLp.ofLp v)
    conv_lhs => rw [← hsum]
    rw [map_sum]
    simp only [map_smul, hcol]
    ext j
    simp [Matrix.mulVec, dotProduct, mul_comm]
  change Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (metricInChart g c (chartAt FourSpace c e.base)) (Q v) = _
  rw [hQ]
  rfl

omit [T2Space M] [CompactSpace M] in
theorem frameUnitRadialState_cotangent (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    unitRadialCotangentState g c (frameUnitRadialState e) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e (coordinateVector 0)) := by
  rw [frameMomentumMap_apply g c e he]
  change (chartAt FourSpace c e.base, 1 • WithLp.toLp 2
    (metricInChart g c (chartAt FourSpace c e.base) *ᵥ
      (fun i => frameChartMatrix g c e i 0))) = _
  rw [one_smul]
  congr 2
  simp [coordinateVector]
  rfl

theorem frameExponential_rescaled_hasFDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (d : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    HasFDerivAt (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      ((ContinuousLinearMap.fst ℝ FourSpace FourSpace).comp
        ((fderiv ℝ (radialCoordinateFlow g o e.base d t)
          (unitRadialCotangentState g e.base (frameUnitRadialState e))).comp
          ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))))
      (coordinateVector 0) := by
  have hc : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  have hD := ((radialFlowContDiffAt_all_time g o t (frameUnitRadialState e) e.base d hc
    (by simpa only [frameUnitRadialState_flow g o e he t, unitTangentOfFrame] using hd)).differentiableAt
      (by simp)).hasFDerivAt
  rw [frameUnitRadialState_cotangent g e.base e hc] at hD
  have hinit : HasFDerivAt
      (fun v : FourSpace => (chartAt FourSpace e.base e.base, frameMomentumMap g e.base e v))
      ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))
      (coordinateVector 0) :=
    (hasFDerivAt_const _ _).prodMk (frameMomentumMap g e.base e).hasFDerivAt
  have hcomp := (hD.comp (coordinateVector 0) hinit).fst
  have hv : coordinateVector (0 : Fin 4) ≠ 0 := by
    intro h
    have hh := congrArg (fun v : FourSpace => v 0) h
    norm_num [coordinateVector] at hh
  have heq : (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      =ᶠ[𝓝 (coordinateVector 0)]
      (fun v => (radialCoordinateFlow g o e.base d t
        (chartAt FourSpace e.base e.base, frameMomentumMap g e.base e v)).1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hv] with v hv
    exact (radialCoordinateFlow_frame_endpoint_time g o e.base d e hc t ht v hv).symm
  have h := hcomp.congr_of_eventuallyEq heq
  rw [← frameUnitRadialState_cotangent g e.base e hc] at h
  exact h

variable [T3Space M]

/-- Varying the initial unit velocity in a normal frame direction gives
exactly the matrix Jacobi solution at time `t`. -/
theorem frameExponential_rescaled_normal_differential (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source)
    (w : Fin 3 → ℝ) :
    (fun i : Fin 3 => ((frameChartMatrix g d (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ
      WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e (t • v))) (coordinateVector 0)
          (WithLp.toLp 2 (Fin.cons 0 w)))) i.succ) =
      (actualJacobiSolution g hRic e).J t *ᵥ w := by
  let a := frameNormalInitialVariation g e w
  have hc : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  have ha : ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))
      (WithLp.toLp 2 (Fin.cons 0 w)) = a := by
    change (0, frameMomentumMap g e.base e (WithLp.toLp 2 (Fin.cons 0 w))) = a
    rw [frameMomentumMap_apply g e.base e hc]
    rfl
  rw [(frameExponential_rescaled_hasFDerivAt g o d e he t ht hd).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ha]
  have hchart := actualNormalVariationPosition_eq_chart g o d e he a t hd
  change actualNormalVariationPosition g o e a t = fun i =>
    ((frameChartMatrix g d (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ
      WithLp.ofLp (frameGeodesicCoordinateVariation g o d e a t).1) i.succ at hchart
  rw [frameGeodesicCoordinateVariation_fst g o d e he a t hd] at hchart
  exact hchart.symm.trans (actualNormalVariation_eq_jacobi g o hRic e he w t).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first positive singular time of the actual Jacobi matrix is attained.
Normalizing by time removes the initial zero; compactness then gives a
positive first zero, and the trace-three comparison bounds it by π. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

private theorem actual_normalizedJacobi_continuous (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    Continuous (normalizedJacobi (actualJacobiSolution g hRic e).J) := by
  let d := actualJacobiSolution g hRic e
  apply continuous_iff_continuousAt.mpr
  intro s
  change ContinuousAt (dslope d.J 0) s
  by_cases hs : s = 0
  · subst s
    exact continuousAt_dslope_same.mpr (d.position_derivative 0).differentiableAt
  · exact (continuousAt_dslope_of_ne hs).mpr d.continuous_J.continuousAt

theorem exists_actualFirstConjugateTime (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ∃ c : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      ¬ IsUnit ((actualJacobiSolution g hRic e).J c) ∧
      ∀ s, 0 < s → s < c → IsUnit ((actualJacobiSolution g hRic e).J s) := by
  let d := actualJacobiSolution g hRic e
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0
  let S : Set ℝ := Icc 0 (Real.pi + 1) ∩ {s | (normalizedJacobi d.J s).det = 0}
  have hS : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_eq
      (actual_normalizedJacobi_continuous g hRic e).matrix_det continuous_const)
  have hSnonempty : S.Nonempty := by
    obtain ⟨s, hs, hsbound, hsing⟩ :=
      actualJacobi_exists_singular_of_pi_lt g hRic e (Real.pi + 1) (by linarith)
    have hz : (d.J s).det = 0 := by
      by_contra hne
      exact hsing ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
    refine ⟨s, ⟨⟨hs.le, hsbound⟩, ?_⟩⟩
    change (normalizedJacobi d.J s).det = 0
    rw [normalizedJacobi_pos d.initial_position hs.ne', Matrix.det_smul,
      Fintype.card_fin, hz, mul_zero]
  obtain ⟨c, hc⟩ := hS.exists_isLeast hSnonempty
  have hcpos : 0 < c := by
    have hcne : c ≠ 0 := by
      intro hzero
      have hz := hc.1.2
      change (normalizedJacobi d.J c).det = 0 at hz
      rw [hzero, normalizedJacobi_zero hd0, Matrix.det_one] at hz
      norm_num at hz
    exact lt_of_le_of_ne hc.1.1.1 (Ne.symm hcne)
  have hbefore : ∀ s, 0 < s → s < c → IsUnit (d.J s) := by
    intro s hs hsc
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hsS : s ∈ S := by
      refine ⟨⟨hs.le, hsc.le.trans hc.1.1.2⟩, ?_⟩
      change (normalizedJacobi d.J s).det = 0
      rw [normalizedJacobi_pos d.initial_position hs.ne', Matrix.det_smul,
        Fintype.card_fin, hz, mul_zero]
    exact (not_le_of_gt hsc) (hc.2 hsS)
  have hcbound : c ≤ Real.pi := by
    by_contra hnot
    have hπc : Real.pi < c := lt_of_not_ge hnot
    have ht : Real.pi < (Real.pi + c) / 2 := by linarith
    have htc : (Real.pi + c) / 2 < c := by linarith
    have hle := actualJacobi_le_pi_of_preconjugate g hRic e ((Real.pi + c) / 2)
      (fun s hs hst => hbefore s hs (hst.trans_lt htc))
    exact (not_le_of_gt ht) hle
  have hczero : (d.J c).det = 0 := by
    have hz := hc.1.2
    change (normalizedJacobi d.J c).det = 0 at hz
    rw [normalizedJacobi_pos d.initial_position hcpos.ne', Matrix.det_smul,
      Fintype.card_fin] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (inv_ne_zero hcpos.ne'))
  refine ⟨c, hcpos, hcbound, ?_, hbefore⟩
  intro hu
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hczero

def actualFirstConjugateTime (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : ℝ :=
  Classical.choose (exists_actualFirstConjugateTime g hRic e)

theorem actualFirstConjugateTime_pos (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : 0 < actualFirstConjugateTime g hRic e :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).1

theorem actualFirstConjugateTime_le_pi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : actualFirstConjugateTime g hRic e ≤ Real.pi :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).2.1

theorem actualFirstConjugateTime_singular (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ¬ IsUnit ((actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e)) :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).2.2.1

theorem actualJacobi_isUnit_before_firstConjugate (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (s : ℝ)
    (hs : 0 < s) (hsc : s < actualFirstConjugateTime g hRic e) :
    IsUnit ((actualJacobiSolution g hRic e).J s) :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).2.2.2 s hs hsc

theorem actualJacobi_preconjugate_iff_lt (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    (∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) ↔
      t < actualFirstConjugateTime g hRic e := by
  constructor
  · intro hp
    by_contra hnot
    exact actualFirstConjugateTime_singular g hRic e
      (hp _ (actualFirstConjugateTime_pos g hRic e) (le_of_not_gt hnot))
  · intro ht s hs hst
    exact actualJacobi_isUnit_before_firstConjugate g hRic e s hs (hst.trans_lt ht)

theorem actualJacobi_det_pos_before_firstConjugate (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (s : ℝ)
    (hs : 0 < s) (hsc : s < actualFirstConjugateTime g hRic e) :
    0 < ((actualJacobiSolution g hRic e).J s).det :=
  actualJacobi_det_pos_of_preconjugate g hRic e s hs
    ((actualJacobi_preconjugate_iff_lt g hRic e s).mpr hsc)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full actual variation in a parallel frame. The radial component
has zero acceleration and the normal component is the Jacobi system. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameGeodesic_full_variation (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (geodesicFramePosition g c (parallelFrameFlowMap g 0 · e)
      (frameGeodesicCoordinateVariation g o c e a))
      (geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t) t ∧
    HasDerivAt (geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
      (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a))
      (-(Fin.cons 0 ((1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) *ᵥ
        geodesicNormalPosition g c (parallelFrameFlowMap g 0 · e)
          (frameGeodesicCoordinateVariation g o c e a) t))) t := by
  apply actual_geodesic_frame_variation g c (parallelFrameFlowMap g 0 · e)
    (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t hc
  · exact frameGeodesicCoordinateCurve_position g o c e he t
  · exact frameGeodesicCoordinateCurve_velocity g o c e he t hc
  · exact frameGeodesicCoordinateCurve_hasDerivAt g o c e he t hc
  · exact frameGeodesicCoordinateVariation_hasDerivAt g o c e he a t hc
  · have h := parallelFrameCurveAt_fixedChart g c (parallelFrameFlowMap g 0 · e) t 0
      (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt hc
      (parallelFrameFlowMap_primitive g 0 e t)
    have hE := (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t h
    rw [frameGeodesicCoordinateCurve_position g o c e he t,
      frameGeodesicCoordinateCurve_velocity g o c e he t hc]
    exact fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j

def actualFullVariationPosition (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : Fin 4 → ℝ :=
  radialVariationInFrame g o e.base (parallelFrameFlowMap g 0 t e).base
    (frameUnitRadialState e) t (parallelFrameFlowMap g 0 t e) a

def actualFullVariationVelocity (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (a : CotangentCoordinates) : ℝ → Fin 4 → ℝ :=
  deriv (actualFullVariationPosition g o e a)

theorem actualFullVariationPosition_eq_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualFullVariationPosition g o e a t =
      geodesicFramePosition g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateVariation g o c e a) t := by
  have hb : (parallelFrameFlowMap g 0 t e).base =
      (unitTangentRadialFlow g o t (frameUnitRadialState e)).2.base :=
    (congrArg UnitTangentBundle.base (frameUnitRadialState_flow g o e he t)).symm
  have h := radialVariationInFrame_chart_independent g o e.base
    (parallelFrameFlowMap g 0 t e).base c (frameUnitRadialState e) t
    (parallelFrameFlowMap g 0 t e) a (mem_chart_source FourSpace e.base) hb
    (mem_chart_source FourSpace _) hc
  change actualFullVariationPosition g o e a t =
    (frameChartMatrix g c (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ WithLp.ofLp
      (frameGeodesicCoordinateVariation g o c e a t).1
  rw [frameGeodesicCoordinateVariation_fst g o c e he a t hc]
  exact h

theorem actualFullVariationPosition_eventually_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualFullVariationPosition g o e a =ᶠ[𝓝 t]
      geodesicFramePosition g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateVariation g o c e a) := by
  have hnear := ((continuous_frameBase g).comp
    (parallelFrameFlowMap_curve_continuous g 0 e)).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
  filter_upwards [hnear] with s hs
  exact actualFullVariationPosition_eq_chart g o c e he a s hs

theorem actualFullVariationPosition_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ) :
    HasDerivAt (actualFullVariationPosition g o e a)
      (actualFullVariationVelocity g o e a t) t := by
  let c := (parallelFrameFlowMap g 0 t e).base
  have hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have h := (frameGeodesic_full_variation g o c e he a t hc).1.congr_of_eventuallyEq
    (actualFullVariationPosition_eventually_chart g o c e he a t hc)
  exact h.differentiableAt.hasDerivAt

theorem actualFullVariationVelocity_eq_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualFullVariationVelocity g o e a t =
      geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t := by
  exact ((frameGeodesic_full_variation g o c e he a t hc).1.congr_of_eventuallyEq
    (actualFullVariationPosition_eventually_chart g o c e he a t hc)).deriv

theorem actualFullVariationVelocity_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ) :
    HasDerivAt (actualFullVariationVelocity g o e a)
      (-(Fin.cons 0 ((1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) *ᵥ
        (fun i => actualFullVariationPosition g o e a t i.succ)))) t := by
  let c := (parallelFrameFlowMap g 0 t e).base
  have hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have hnear := ((continuous_frameBase g).comp
    (parallelFrameFlowMap_curve_continuous g 0 e)).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
  have heq : actualFullVariationVelocity g o e a =ᶠ[𝓝 t]
      geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) := by
    filter_upwards [hnear] with s hs
    exact actualFullVariationVelocity_eq_chart g o c e he a s hs
  have h := (frameGeodesic_full_variation g o c e he a t hc).2.congr_of_eventuallyEq heq
  rw [actualFullVariationPosition_eq_chart g o c e he a t hc]
  exact h

def frameFullInitialVariation (g : SmoothMetric M) (e : FrameBundle g)
    (w : Fin 4 → ℝ) : CotangentCoordinates :=
  (0, WithLp.toLp 2
    (metricInChart g e.base (chartAt FourSpace e.base e.base) *ᵥ
      (frameChartMatrix g e.base e *ᵥ w)))

theorem actualFullVariation_initial (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (w : Fin 4 → ℝ) :
    actualFullVariationPosition g o e (frameFullInitialVariation g e w) 0 = 0 ∧
      actualFullVariationVelocity g o e (frameFullInitialVariation g e w) 0 = w := by
  let a := frameFullInitialVariation g e w
  let p := unitRadialCotangentState g e.base (frameUnitRadialState e)
  have hc : (parallelFrameFlowMap g 0 0 e).base ∈ (chartAt FourSpace e.base).source := by
    rw [parallelFrameFlowMap_zero]
    exact mem_chart_source FourSpace e.base
  have hp : p.1 ∈ (chartAt FourSpace e.base).target :=
    (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hzero : frameKineticCurve g o e.base e 0 = p := by
    change unitRadialCotangentState g e.base
      (unitTangentRadialFlow g o 0 (frameUnitRadialState e)) = p
    rw [unitTangentRadialFlow_zero]
  have hvar : frameKineticVariation g o e.base e a 0 = a := by
    change fderiv ℝ (radialCoordinateFlow g o e.base e.base 0) p a = a
    rw [radialCoordinateFlow_self_zero_fderiv g o e.base (frameUnitRadialState e)
      (mem_chart_source FourSpace e.base)]
    rfl
  have hZ : frameGeodesicCoordinateVariation g o e.base e a 0 =
      fderiv ℝ (kineticVelocityCoordinates g e.base) p
        (0, WithLp.toLp 2 (metricInChart g e.base p.1 *ᵥ
          (frameChartMatrix g e.base (parallelFrameFlowMap g 0 0 e) *ᵥ w))) := by
    change fderiv ℝ (kineticVelocityCoordinates g e.base) (frameKineticCurve g o e.base e 0)
      (frameKineticVariation g o e.base e a 0) = _
    rw [hzero, hvar, parallelFrameFlowMap_zero]
    rfl
  have h := kinetic_frame_initial_data g e.base (parallelFrameFlowMap g 0 · e)
    (frameGeodesicCoordinateCurve g o e.base e)
    (frameGeodesicCoordinateVariation g o e.base e a) p w 0 hc hp hZ
  rw [actualFullVariationPosition_eq_chart g o e.base e he a 0 hc,
    actualFullVariationVelocity_eq_chart g o e.base e he a 0 hc]
  exact h

variable [T3Space M]

theorem actualFullVariation_eq_jacobi (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (w : Fin 4 → ℝ) (t : ℝ) :
    actualFullVariationPosition g o e (frameFullInitialVariation g e w) t =
        jacobiBlockMatrix t ((actualJacobiSolution g hRic e).J t) *ᵥ w ∧
      actualFullVariationVelocity g o e (frameFullInitialVariation g e w) t =
        jacobiBlockMatrix 1 ((actualJacobiSolution g hRic e).V t) *ᵥ w := by
  let a := frameFullInitialVariation g e w
  have hinit := actualFullVariation_initial g o e he w
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  have hzero : (0 : ℝ) ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  exact Jacobi.full_jacobi_eq_mulVec (actualJacobiSolution g hRic e) K (hK e)
    (actualFullVariationPosition g o e a) (actualFullVariationVelocity g o e a)
    w _ _ hzero hinit.1 hinit.2
    (fun s _ => actualFullVariationPosition_hasDerivAt g o e he a s)
    (fun s _ => actualFullVariationVelocity_hasDerivAt g o e he a s) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The divergence of an actual smooth one-form is a smooth scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def oneFormDivergence (g : SmoothMetric M) (u : smoothCovariantFields M 1) (x : M) : ℝ :=
  ∑ i, ∑ j, (chartMetric g x)⁻¹ i j * covariantFieldDerivative g u.val x ![i,j]

theorem oneFormDivergence_eq_frame (u : smoothCovariantFields M 1) (e : FrameBundle g) :
    oneFormDivergence g u e.base =
      ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i] := by
  simp only [oneFormDivergence, covariantFieldFramed_eq]
  rw [frameTensor_trace_two, e.frame.matrix_mul_transpose]

theorem oneFormDivergence_coordinates (u : smoothCovariantFields M 1)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    oneFormDivergence g u ((chartAt FourSpace c).symm z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        covariantFieldCoordinates (covariantFieldDerivative g u.val) c z ![i,j] := by
  have h := oneFormDivergence_eq_frame u (chartGramSection g c 1 (by simp) ⟨z,hz⟩)
  simp_rw [covariantFieldFramed_chart] at h
  rw [frameTensor_trace_two, chartGramMatrix_mul_transpose g c z hz] at h
  exact h

theorem oneFormDivergence_smooth (u : smoothCovariantFields M 1) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (oneFormDivergence g u) := by
  intro c
  have hz := mem_chart_target FourSpace c
  have hchart : ContDiffAt ℝ ∞ (fun z => ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
      covariantFieldCoordinates (covariantFieldDerivative g u.val) c z ![i,j])
      (chartAt FourSpace c c) := by
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (metricInChart_inv_contDiffAt g c _ hz
      (metricInChart_posDef g c _ hz).det_pos.ne' i j).mul
        (u.property.derivative (g := g) c _ hz ![i,j])
  have h := hchart.contMDiffAt.comp c
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      (mem_chart_source FourSpace c))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c)] with x hx
  have he := oneFormDivergence_coordinates (g := g) u c (chartAt FourSpace c x)
    ((chartAt FourSpace c).map_source hx)
  simpa only [Function.comp_apply, (chartAt FourSpace c).left_inv hx] using he

def smoothOneFormDivergence (g : SmoothMetric M) : smoothCovariantFields M 1 →ₗ[ℝ] SmoothScalar (M := M) where
  toFun u := ⟨oneFormDivergence g u, oneFormDivergence_smooth u⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    have hd := congrFun (covariantFieldDerivative_add (g := g) u v) x
    change (∑ i, ∑ j, (chartMetric g x)⁻¹ i j *
      covariantFieldDerivative g (u + v).val x ![i,j]) = _
    rw [hd]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rfl
  map_smul' r u := by
    apply Subtype.ext
    funext x
    have hd := congrFun (covariantFieldDerivative_smul (g := g) r u) x
    change (∑ i, ∑ j, (chartMetric g x)⁻¹ i j *
      covariantFieldDerivative g (r • u).val x ![i,j]) =
        r * (∑ i, ∑ j, (chartMetric g x)⁻¹ i j * covariantFieldDerivative g u.val x ![i,j])
    rw [hd]
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ r, ← Finset.mul_sum]

theorem oneFormDivergence_differential (f : SmoothScalar (M := M)) (e : FrameBundle g) :
    oneFormDivergence g (smoothScalarDifferential g f) e.base = scalarLaplacian g f.val e := by
  rw [oneFormDivergence_eq_frame]
  apply Finset.sum_congr rfl
  intro i _
  exact smoothScalarDifferential_derivative f e i i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual exterior derivative of one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoCovariantAlternation_pairing (D A : CovariantCoordinates 2)
    (hA : ∀ i j, A ![j,i] = -A ![i,j]) :
    frameTensorPairing (twoCovariantAlternation D) A =
      2 * ∑ i, ∑ j, D ![i,j] * A ![i,j] := by
  have hsplit : frameTensorPairing (twoCovariantAlternation D) A =
      (∑ i, ∑ j, D ![i,j] * A ![i,j]) - (∑ i, ∑ j, D ![j,i] * A ![i,j]) := by
    unfold frameTensorPairing
    simp only [sum_tensor_indices_cons, Fintype.sum_unique]
    change (∑ i, ∑ j, twoCovariantAlternation D ![i,j] * A ![i,j]) = _
    simp only [twoCovariantAlternation_apply, sub_mul, Finset.sum_sub_distrib]
  have hs : (∑ i, ∑ j, D ![j,i] * A ![i,j]) = -(∑ i, ∑ j, D ![i,j] * A ![i,j]) := by
    rw [Finset.sum_comm]
    have hi (i j : Fin 4) : D ![i,j] * A ![j,i] = -(D ![i,j] * A ![i,j]) := by
      rw [hA i j, mul_neg]
    simp only [hi, Finset.sum_neg_distrib]
  rw [hs] at hsplit
  linarith only [hsplit]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormExterior_framed_tensor (u : smoothCovariantFields M 1)
    (e : FrameBundle g) :
    twoFormFramedValue o (smoothOneFormExterior (o := o) u).val e =
      twoCovariantAlternation (covariantFieldFramed g (covariantFieldDerivative g u.val) e) := by
  funext a
  have ha : a = ![a 0,a 1] := by ext i; fin_cases i <;> rfl
  rw [ha]
  exact (smoothOneFormExterior_framed u e _ _).trans (twoCovariantAlternation_apply _ _ _).symm

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormExterior_frame_pairing (u : smoothCovariantFields M 1)
    (v : smoothTwoForms o) (e : FrameBundle g) :
    inner ℝ (twoFormFrameValue o (smoothOneFormExterior (o := o) u).val e)
      (twoFormFrameValue o v.val e) =
      ∑ i, ∑ j, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
        twoFormFramedValue o v.val e ![i,j] := by
  have hp := twoCovariantAlternation_pairing
    (covariantFieldFramed g (covariantFieldDerivative g u.val) e)
    (twoFormFramedValue o v.val e) (twoFormFramedValue_skew v.val e)
  rw [← smoothOneFormExterior_framed_tensor (o := o) u e, twoFormFramedValue_eq,
    twoFormFramedValue_eq, twoFormTensor_pairing] at hp
  rw [← twoFormFramedValue_eq o v.val e] at hp
  linarith only [hp]

theorem smoothOneForm_direction_green (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (v : smoothTwoForms o) (i j : Fin 4) :
    (∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
      twoFormFramedValue o v.val e ![i,j] ∂canonicalFrameMeasure g o) =
      -(∫ e, covariantFieldFramed g u.val e ![j] *
        twoFormFramedCovariantDerivative o v.val e ![i,i,j] ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![j],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedValue o v.val e ![i,j],
    (continuous_apply _).comp v.property.continuous_framedValue⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o v.val e ![i,i,j],
    (continuous_apply _).comp v.property.continuous_framedCovariantDerivative⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![j]
  · intro t e
    exact v.property.framedValue_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![i,j]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive smooth approximations of the absolute value, with the exact
value error and contraction of the scalar Dirichlet energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def smoothScalarAbsRegularized (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    SmoothScalar (M := M) := by
  refine ⟨fun x => Real.sqrt (a.val x ^ 2 + ε ^ 2), ?_⟩
  intro x
  exact (Real.contDiffAt_sqrt (ne_of_gt (add_pos_of_nonneg_of_pos
    (sq_nonneg _) (sq_pos_of_pos hε)))).comp_contMDiffAt
      (f := fun x : M => a.val x ^ 2 + ε ^ 2)
      ((a.property.pow 2).add contMDiff_const).contMDiffAt

omit [IsManifold I4 ∞ M] in
theorem smoothScalarAbsRegularized_pos (a : SmoothScalar (M := M))
    (ε : ℝ) (hε : 0 < ε) (x : M) :
    0 < (smoothScalarAbsRegularized a ε hε).val x :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))

omit [IsManifold I4 ∞ M] in
theorem smoothScalarAbsRegularized_sq (a : SmoothScalar (M := M))
    (ε : ℝ) (hε : 0 < ε) (x : M) :
    (smoothScalarAbsRegularized a ε hε).val x ^ 2 = a.val x ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit [IsManifold I4 ∞ M] in
theorem smoothScalarAbsRegularized_error (a : SmoothScalar (M := M))
    (ε : ℝ) (hε : 0 < ε) (x : M) :
    |(smoothScalarAbsRegularized a ε hε).val x - (|a.val x|)| ≤ ε := by
  have hlo : |a.val x| ≤ (smoothScalarAbsRegularized a ε hε).val x := by
    change |a.val x| ≤ Real.sqrt (a.val x ^ 2 + ε ^ 2)
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε, sq_abs (a.val x)])
  have hup : (smoothScalarAbsRegularized a ε hε).val x ≤ |a.val x| + ε := by
    apply (sq_le_sq₀ (smoothScalarAbsRegularized_pos a ε hε x).le (by positivity)).mp
    rw [smoothScalarAbsRegularized_sq]
    nlinarith [abs_nonneg (a.val x), sq_abs (a.val x)]
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem smoothScalarAbsRegularized_gradient {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε)
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarAbsRegularized a ε hε).val e i =
      (a.val e.base / (smoothScalarAbsRegularized a ε hε).val e.base) *
        scalarGradient g a.val e i := by
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let b := smoothScalarAbsRegularized a ε hε
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  have hp : 0 < a.val e.base ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have houter : HasDerivAt (fun r : ℝ => Real.sqrt (r ^ 2 + ε ^ 2))
      (a.val e.base / b.val e.base) (a.val e.base) := by
    convert (Real.hasDerivAt_sqrt hp.ne').comp (a.val e.base)
      (((hasDerivAt_id (a.val e.base)).pow 2).add_const (ε ^ 2)) using 1
    · rfl
    · change a.val e.base / Real.sqrt (a.val e.base ^ 2 + ε ^ 2) = _
      simp only [id_eq]
      ring
  have hd := sa.derivativeValue i 0 f
  rw [hf] at hd
  have hb := sb.derivativeValue i 0 f
  rw [hf] at hb
  have hc := HasDerivAt.comp
    (h₂ := fun r : ℝ => Real.sqrt (r ^ 2 + ε ^ 2))
    (h := fun t : ℝ => a.val (((d.toMetricGreenData.flow i).map t) f).base)
    0 (by simpa only [hf] using houter) hd
  exact hb.unique hc

theorem smoothScalarAbsRegularized_gradient_sq_le {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε)
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarAbsRegularized a ε hε).val e i ^ 2 ≤
      scalarGradient g a.val e i ^ 2 := by
  have hr := smoothScalarAbsRegularized_pos a ε hε e.base
  have hc : (a.val e.base / (smoothScalarAbsRegularized a ε hε).val e.base) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (sq_pos_of_pos hr), smoothScalarAbsRegularized_sq]
    linarith [sq_nonneg ε]
  rw [smoothScalarAbsRegularized_gradient d, mul_pow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg (scalarGradient g a.val e i))

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance scalarAbs_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarAbs_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem smoothScalarAbsRegularized_dirichlet_le {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    smoothScalarDirichlet d (smoothScalarAbsRegularized a ε hε)
      (smoothScalarAbsRegularized a ε hε) ≤ smoothScalarDirichlet d a a := by
  rw [smoothScalarDirichlet_eq_integral, smoothScalarDirichlet_eq_integral]
  apply integral_mono
  · exact (continuous_finsetSum _ (fun i _ =>
      (actual_scalarGradient_continuous g (smoothScalarAbsRegularized a ε hε).property i).mul
        (actual_scalarGradient_continuous g (smoothScalarAbsRegularized a ε hε).property i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_finsetSum _ (fun i _ =>
      (actual_scalarGradient_continuous g a.property i).mul
        (actual_scalarGradient_continuous g a.property i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro e
    apply Finset.sum_le_sum
    intro i _
    simpa only [pow_two] using smoothScalarAbsRegularized_gradient_sq_le d a ε hε e i

theorem smoothScalarAbsRegularized_energy_le {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    ‖smoothScalarToWeightedH1 d (smoothScalarAbsRegularized a ε hε)‖ ^ 2 ≤
      ‖smoothScalarToWeightedH1 d a‖ ^ 2 + ε ^ 2 := by
  rw [smoothScalarToWeightedH1_norm_sq o d, smoothScalarToWeightedH1_norm_sq o d]
  have hi : Integrable (fun x : M => a.val x ^ 2) (normalizedVolume g) :=
    (a.property.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, (smoothScalarAbsRegularized a ε hε).val x ^ 2 ∂normalizedVolume g) =
      (∫ x, a.val x ^ 2 ∂normalizedVolume g) + ε ^ 2 := by
    simp only [smoothScalarAbsRegularized_sq]
    rw [integral_add hi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [he]
  linarith [smoothScalarAbsRegularized_dirichlet_le o d a ε hε]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The base L² representative of an intrinsic H¹ scalar is a bounded
linear map, obtained from the closed image of base pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance h1Base_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

private def scalarH1BaseValueFun (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    Lp ℝ 2 (normalizedVolume g) :=
  Classical.choose (scalarH1_base_representative g o d u)

private theorem scalarH1BaseValueFun_spec (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    scalarBasePullback g o (scalarH1BaseValueFun g o d u) = scalarH1Value d u :=
  Classical.choose_spec (scalarH1_base_representative g o d u)

def scalarH1BaseValue (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  LinearMap.mkContinuous
    { toFun := scalarH1BaseValueFun g o d
      map_add' := fun u v => by
        apply (scalarBasePullback g o).injective
        rw [map_add, scalarH1BaseValueFun_spec, scalarH1BaseValueFun_spec,
          scalarH1BaseValueFun_spec, map_add]
      map_smul' := fun r u => by
        apply (scalarBasePullback g o).injective
        rw [map_smul, scalarH1BaseValueFun_spec, scalarH1BaseValueFun_spec, map_smul]
        rfl }
    1 (fun u => by
      change ‖scalarH1BaseValueFun g o d u‖ ≤ 1 * ‖u‖
      rw [one_mul, ← (scalarBasePullback g o).norm_map, scalarH1BaseValueFun_spec]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [scalarH1_norm_sq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

theorem scalarH1BaseValue_spec (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    scalarBasePullback g o (scalarH1BaseValue g o d u) = scalarH1Value d u :=
  scalarH1BaseValueFun_spec g o d u

theorem scalarH1BaseValue_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d)
    (b : Lp ℝ 2 (normalizedVolume g)) (hb : scalarBasePullback g o b = scalarH1Value d u) :
    scalarH1BaseValue g o d u = b := by
  apply (scalarBasePullback g o).injective
  exact (scalarH1BaseValue_spec g o d u).trans hb.symm

theorem scalarH1BaseValue_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    scalarH1BaseValue g o d (smoothScalarToH1 d a) = smoothScalarBaseL2 g a := by
  apply scalarH1BaseValue_eq
  exact scalarBasePullback_smooth g o a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L² tail absorption in the rational Brezis--Kato estimate.  All
constants are independent of the rational truncation parameter. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped _root_.Topology ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local instance katoTail_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance katoTail_realFour : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 4) := ⟨by norm_num⟩

def scalarKatoTail (V : X → ℝ) (n : ℕ) (x : X) : ℝ := max (V x - n) 0

theorem scalarKatoTail_memLp {V : X → ℝ} (hV : MemLp V 2 μ) (n : ℕ) :
    MemLp (scalarKatoTail V n) 2 μ := by
  have hc : Continuous (fun r : ℝ => max (r - (n : ℝ)) 0) := by fun_prop
  apply hV.of_le (hc.comp_aestronglyMeasurable hV.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (by linarith [le_abs_self (V x), Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg _)

theorem scalarKatoTail_small {V : X → ℝ} (hV : MemLp V 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) < ε := by
  have hd := tendsto_integral_of_dominated_convergence (fun x => V x ^ 2)
    (fun n => (scalarKatoTail_memLp hV n).aestronglyMeasurable.pow 2)
    hV.integrable_sq (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : scalarKatoTail V n x ≤ |V x| :=
        max_le (by linarith [le_abs_self (V x), Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg _)
      change scalarKatoTail V n x ^ 2 ≤ V x ^ 2
      simpa only [scalarKatoTail, sq_abs] using
        (sq_le_sq₀ (le_max_right _ _) (abs_nonneg _)).2 hb)
    (f := fun _ => (0 : ℝ)) (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_gt (V x)
      change Tendsto (fun n => scalarKatoTail V n x ^ 2) atTop (𝓝 0)
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hv : V x ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
      simp only [scalarKatoTail, max_eq_right (sub_nonpos.mpr hv), zero_pow (by decide : 2 ≠ 0)])
  have hs : Tendsto (fun n => Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [integral_zero, Real.sqrt_zero, Function.comp_def] using!
      Real.continuous_sqrt.continuousAt.tendsto.comp hd
  obtain ⟨n, hn⟩ := (hs.eventually (gt_mem_nhds hε)).exists
  exact ⟨n, hn⟩

theorem scalarLp_four_norm_sq (f : Lp ℝ 4 μ) :
    ‖f‖ ^ 2 = Real.sqrt (∫ x, f x ^ 4 ∂μ) := by
  have hfn := scalarLp_norm_sq_eq_moment (μ := μ) (p := 4) (by norm_num)
  rw [show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by norm_num] at hfn
  have h := hfn f
  have hi : (∫ x, |f x| ^ (4 : ℝ) ∂μ) = ∫ x, f x ^ 4 ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change |f x| ^ (4 : ℝ) = f x ^ 4
      rw [Real.rpow_ofNat, ← abs_pow, abs_of_nonneg (show 0 ≤ f x ^ 4 by positivity)]
  rw [hi, show (2 : ℝ) / 4 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at h
  exact h

theorem scalarKato_square_memLp {f : X → ℝ} (hf : MemLp f 4 μ) :
    MemLp (fun x => f x ^ 2) 2 μ := by
  have h := hf.norm_rpow_div 2
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  have he : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  simpa only [he] using h

/-- The multiplication estimate used for the tail, in ordinary real integrals. -/
theorem scalarKato_tail_pairing {V W : X → ℝ} (hV : MemLp V 2 μ)
    (hW : MemLp W 4 μ) (n : ℕ) :
    (∫ x, scalarKatoTail V n x * W x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) *
        Real.sqrt (∫ x, W x ^ 4 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => le_max_right (V x - (n : ℝ)) 0)
    (Eventually.of_forall fun x => sq_nonneg (W x))
    (by
      rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
      change MemLp (scalarKatoTail V n) 2 μ
      exact scalarKatoTail_memLp hV n)
    (by
      rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
      exact scalarKato_square_memLp hW)
  simpa only [scalarKatoTail, ENNReal.ofReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow,
    show (fun x => (W x ^ 2) ^ 2) = (fun x => W x ^ 4) by funext x; ring] using h

/-- A fixed Sobolev estimate and the tested energy bound imply the eighth
moment.  The potential only needs its genuine L² integrability. -/
theorem scalarKato_memLp_eight_of_energy [IsFiniteMeasure μ] {f V : X → ℝ}
    (hf : MemLp f 4 μ) (hV : MemLp V 2 μ) {C : ℝ} (hC : 0 < C)
    (hW : ∀ lam : ℝ, 0 < lam → MemLp (fun x => scalarKatoSquare lam (f x)) 4 μ)
    (henergy : ∀ lam : ℝ, 0 < lam →
      Real.sqrt (∫ x, scalarKatoSquare lam (f x) ^ 4 ∂μ) ≤ C *
        ((∫ x, f x ^ 4 ∂μ) +
          4 * ∫ x, V x * scalarKatoSquare lam (f x) ^ 2 ∂μ)) :
    MemLp f 8 μ := by
  let A := ∫ x, f x ^ 4 ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => by positivity
  obtain ⟨n, hn⟩ := scalarKatoTail_small hV (show 0 < 1 / (8 * C) by positivity)
  let D := 2 * C * (1 + 4 * n) * A
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply scalarKato_memLp_eight_of_bound hf.aestronglyMeasurable
    (C := ENNReal.ofReal (D + 1)) ENNReal.ofReal_ne_top
  intro lam hlam
  let W := fun x => scalarKatoSquare lam (f x)
  have hi4 : Integrable (fun x => f x ^ 4) μ := by
    have h := hf.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)
    have he : (fun x => ‖f x‖ ^ 4) = (fun x => f x ^ 4) := by
      funext x
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
    rwa [he] at h
  have hW2 := scalarKato_square_memLp (hW lam hlam)
  have hvw : Integrable (fun x => V x * W x ^ 2) μ := hV.integrable_mul hW2
  have htw : Integrable (fun x => scalarKatoTail V n x * W x ^ 2) μ :=
    (scalarKatoTail_memLp hV n).integrable_mul hW2
  have hi2 : Integrable (fun x => W x ^ 2) μ := hW2.integrable (by norm_num)
  have hpair : (∫ x, V x * W x ^ 2 ∂μ) ≤
      (n : ℝ) * A + Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) *
        Real.sqrt (∫ x, W x ^ 4 ∂μ) := by
    calc
      _ ≤ ∫ x, (n : ℝ) * W x ^ 2 + scalarKatoTail V n x * W x ^ 2 ∂μ := by
        apply integral_mono hvw ((hi2.const_mul _).add htw)
        intro x
        have hv : V x ≤ (n : ℝ) + scalarKatoTail V n x := by
          dsimp [scalarKatoTail]
          linarith [le_max_left (V x - (n : ℝ)) 0]
        change V x * W x ^ 2 ≤ (n : ℝ) * W x ^ 2 + scalarKatoTail V n x * W x ^ 2
        nlinarith [sq_nonneg (W x)]
      _ = (n : ℝ) * (∫ x, W x ^ 2 ∂μ) +
          ∫ x, scalarKatoTail V n x * W x ^ 2 ∂μ := by
        rw [integral_add (hi2.const_mul _) htw, integral_const_mul]
      _ ≤ (n : ℝ) * A + Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) *
          Real.sqrt (∫ x, W x ^ 4 ∂μ) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
          exact integral_mono hi2 hi4 (fun x => scalarKatoSquare_sq_le hlam (f x))
        · exact scalarKato_tail_pairing hV (hW lam hlam) n
  have hx := henergy lam hlam
  have hX : 0 ≤ Real.sqrt (∫ x, W x ^ 4 ∂μ) := Real.sqrt_nonneg _
  have hsmall : 4 * C * Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) < 1 / 2 := by
    apply (lt_div_iff₀ (show 0 < 8 * C by positivity)).mp at hn
    nlinarith
  have hb : Real.sqrt (∫ x, W x ^ 4 ∂μ) ≤ D := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hpair (show 0 ≤ 4 * C by positivity),
      mul_le_mul_of_nonneg_right hsmall.le hX]
  let w : Lp ℝ 4 μ := (hW lam hlam).toLp W
  have he : w =ᵐ[μ] W := MemLp.coeFn_toLp _
  have hnorm : ‖w‖ ^ 2 ≤ D := by
    rw [scalarLp_four_norm_sq]
    have hi : (∫ x, w x ^ 4 ∂μ) = ∫ x, W x ^ 4 ∂μ :=
      integral_congr_ae (he.fun_comp fun r : ℝ => r ^ 4)
    rwa [hi]
  have hnw : ‖w‖ ≤ D + 1 := by nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - 1)]
  have hen : eLpNorm W 4 μ = ENNReal.ofReal ‖w‖ := by
    rw [← eLpNorm_congr_ae he, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w)]
  rw [hen]
  exact ENNReal.ofReal_le_ofReal hnw

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact weak minimum principle in the actual H1 space. A smooth
bounded monotone test detects every negative value without presupposing
pointwise second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
private theorem scalarWeakMinimum_inner (a b : ScalarL2 g μ) :
    inner ℝ a b = ∫ e, a e * b e ∂μ := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]

/-- Strict negativity of the weak Laplacian wherever the scalar value is
negative forces nonnegativity almost everywhere. -/
theorem scalarH1_nonneg_of_negative_source (d : ParallelMetricData g μ)
    (u : scalarH1 d) (F : ScalarL2 g μ)
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (hneg : ∀ᵐ e ∂μ, scalarH1Value d u e < 0 → F e < 0) :
    ∀ᵐ e ∂μ, 0 ≤ scalarH1Value d u e := by
  obtain ⟨D, hD⟩ := scalarNegativeTest_deriv_bound
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists_of_deriv_bound d
    scalarNegativeTest scalarNegativeTest_smooth scalarNegativeTest_zero hD u
  have hG (i : Fin 4) : 0 ≤ inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
    rw [scalarWeakMinimum_inner]
    apply integral_nonneg_of_ae
    filter_upwards [hgrad i] with e he
    change 0 ≤ scalarH1Gradient d i u e * scalarH1Gradient d i v e
    rw [he]
    have h := scalarNegativeTest_deriv_nonneg (scalarH1Value d u e)
    convert mul_nonneg h (sq_nonneg (scalarH1Gradient d i u e)) using 1
    ring
  have hp : ∀ᵐ e ∂μ, 0 ≤ F e * scalarH1Value d v e := by
    filter_upwards [hneg, hv] with e he hve
    rw [hve]
    by_cases hu : scalarH1Value d u e < 0
    · exact mul_nonneg_of_nonpos_of_nonpos (he hu).le (scalarNegativeTest_nonpos _)
    · rw [scalarNegativeTest_eq_zero (le_of_not_gt hu), mul_zero]
  have hint : Integrable (fun e => F e * scalarH1Value d v e) μ :=
    (Lp.memLp F).integrable_mul (Lp.memLp (scalarH1Value d v))
  have hi : (∫ e, F e * scalarH1Value d v e ∂μ) = 0 := by
    have h := heq v
    rw [scalarWeakMinimum_inner] at h
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hG i)
    have hpos := integral_nonneg_of_ae hp
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hp hint).mp hi
  filter_upwards [hneg, hv, hz] with e he hve hze
  by_contra hu
  have hu' : scalarH1Value d u e < 0 := lt_of_not_ge hu
  have hpos := mul_pos_of_neg_of_neg (he hu') (scalarNegativeTest_neg hu')
  rw [hve] at hze
  exact (ne_of_gt hpos) hze

/-- Subtracting a smooth barrier preserves the weak equation, with its
actual geometric Laplacian subtracted from the source. -/
theorem scalarH1_sub_smooth_weak_equation (d : ParallelMetricData g μ)
    (u : scalarH1 d) (F : ScalarL2 g μ)
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (b : SmoothScalar (M := M)) (ε : ℝ) (v : scalarH1 d) :
    (∑ i : Fin 4, inner ℝ
      (scalarH1Gradient d i (u - ε • smoothScalarToH1 d b)) (scalarH1Gradient d i v)) =
        -(inner ℝ (F - ε • smoothScalarLaplacianL2 (μ := μ) b) (scalarH1Value d v)) := by
  have hb := scalarH1_green d v b
  simp only [map_sub, map_smul, scalarH1Gradient_smooth,
    inner_sub_left, real_inner_smul_left, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [heq]
  have hs : (∑ i : Fin 4, inner ℝ (smoothScalarGradientL2 d i b)
      (scalarH1Gradient d i v)) = -(inner ℝ (smoothScalarLaplacianL2 (μ := μ) b)
      (scalarH1Value d v)) := by
    simpa only [real_inner_comm] using hb
  rw [hs]
  ring

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M]

/-- A continuous base representative which is nonnegative almost everywhere
on the canonical frames is nonnegative at every base point. -/
theorem scalar_continuous_base_nonneg_of_frame_ae (g : SmoothMetric M)
    (o : FrameOrientation g) (u : M → ℝ) (hu : Continuous u)
    (hae : ∀ᵐ e ∂canonicalFrameMeasure g o, 0 ≤ u e.base) : ∀ x, 0 ≤ u x := by
  let := normalizedVolume_isOpenPosMeasure g
  have hb : ∀ᵐ x ∂normalizedVolume g, 0 ≤ u x := by
    rw [← (canonicalFrameMeasure_base g o).map_eq]
    exact (ae_map_iff (canonicalFrameMeasure_base g o).measurable.aemeasurable
      (isClosed_le continuous_const hu).measurableSet).mpr hae
  have heq : (fun x => min (u x) 0) =ᵐ[normalizedVolume g] fun _ => (0 : ℝ) := by
    filter_upwards [hb] with x hx
    exact min_eq_right hx
  have hfun := Measure.eq_of_ae_eq heq (hu.min continuous_const) continuous_const
  intro x
  exact min_eq_right_iff.mp (congrFun hfun x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse-metric contraction preserves actual smooth covariant fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem covariantMetricTraceField_coordinates (T : M → CovariantCoordinates 3)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantFieldCoordinates (covariantMetricTraceField g T) c z =
      covariantMetricTraceThree (metricInChart g c z)⁻¹ (covariantFieldCoordinates T c z) := by
  have h := covariantMetricTraceField_framed T (chartGramSection g c 1 (by simp) ⟨z,hz⟩)
  rw [covariantFieldFramed_chart, covariantFieldFramed_chart,
    covariantMetricTraceThree_frame, chartGramMatrix_mul_transpose g c z hz] at h
  have hi := congrArg (frameTensor ((chartGramMatrix g c 1 z)ᵀ * metricInChart g c z)) h
  simp only [← frameTensor_mul] at hi
  rw [mul_eq_one_comm.mp (chartGramMatrix_normalizes g c 1 (by simp) ⟨z,hz⟩),
    frameTensor_one, frameTensor_one] at hi
  exact hi

theorem CovariantFieldSmooth.metricTrace {T : M → CovariantCoordinates 3}
    (hT : CovariantFieldSmooth T) : CovariantFieldSmooth (covariantMetricTraceField g T) := by
  intro c z hz a
  have hs : ContDiffAt ℝ ∞ (fun w =>
      covariantMetricTraceThree (metricInChart g c w)⁻¹ (covariantFieldCoordinates T c w) a) z := by
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (metricInChart_inv_contDiffAt g c z hz
      (metricInChart_posDef g c z hz).det_pos.ne' i j).mul
      (hT c z hz (Fin.cons i (Fin.cons j a)))
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact congrFun (covariantMetricTraceField_coordinates T c w hw) a

def smoothCovariantMetricTrace (T : smoothCovariantFields M 3) : smoothCovariantFields M 1 :=
  ⟨covariantMetricTraceField g T.val, T.property.metricTrace⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact chart control of ordinary derivatives by the actual two-form
H1 energy. The connection coefficients are bounded only on the chosen
compact chart set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def tensorSlotWeight (n : ℕ) (P : Mat4) : ℝ :=
  ∑ a : Fin n → Fin 4, ∑ s : Fin n, ∑ b : Fin 4, |P b (a s)|

theorem tensorSlotWeight_nonneg (n : ℕ) (P : Mat4) : 0 ≤ tensorSlotWeight n P :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

theorem tensorSlotWeight_continuous (n : ℕ) : Continuous (tensorSlotWeight n) := by
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro s _
  apply continuous_finsetSum
  intro b _
  exact ((continuous_apply (a s)).comp (continuous_apply b)).abs

theorem tensorSlotAction_abs_le_weight {n : ℕ} (P : Mat4) (T : CovariantCoordinates n)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ a, |T a| ≤ C) (a : Fin n → Fin 4) :
    |tensorSlotAction P T a| ≤ tensorSlotWeight n P * C := by
  calc
    _ ≤ ∑ s : Fin n, |∑ b : Fin 4, P b (a s) * T (Function.update a s b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin n, ∑ b : Fin 4, |P b (a s)| * C := by
      apply Finset.sum_le_sum
      intro s _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hT _) (abs_nonneg _)
    _ = (∑ s : Fin n, ∑ b : Fin 4, |P b (a s)|) * C := by
      simp only [Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      unfold tensorSlotWeight
      exact Finset.single_le_sum (f := fun a : Fin n → Fin 4 =>
        ∑ s : Fin n, ∑ b : Fin 4, |P b (a s)|)
        (fun a _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun b _ =>
          abs_nonneg (P b (a s))))) (Finset.mem_univ a)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartConnectionWeight (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  ∑ i : Fin 4, tensorSlotWeight 2 (connectionMatrix g c i z)

def twoFormChartControl (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  2 * tensorTransportWeight 2 (twoFormChartTransport g c z) +
  2 * tensorTransportWeight 3 (twoFormChartTransport g c z) +
  2 * twoFormChartConnectionWeight g c z * tensorTransportWeight 2 (twoFormChartTransport g c z)

theorem twoFormChartControl_nonneg (g : SmoothMetric M) (c : M) (z : FourSpace) :
    0 ≤ twoFormChartControl g c z := by
  have hw : 0 ≤ twoFormChartConnectionWeight g c z :=
    Finset.sum_nonneg (fun _ _ => tensorSlotWeight_nonneg _ _)
  have h₂ := tensorTransportWeight_nonneg 2 (twoFormChartTransport g c z)
  have h₃ := tensorTransportWeight_nonneg 3 (twoFormChartTransport g c z)
  unfold twoFormChartControl
  positivity

theorem twoFormChartControl_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (twoFormChartControl g c) (chartAt FourSpace c).target := by
  have hc : ContinuousOn (twoFormChartConnectionWeight g c) (chartAt FourSpace c).target := by
    apply continuousOn_finsetSum
    intro i _
    apply (tensorSlotWeight_continuous 2).comp_continuousOn
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_pi.mpr
    intro k z hz
    exact (christoffel_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
      j i k).continuousAt.continuousWithinAt
  have h₂ := (tensorTransportWeight_continuous 2).comp_continuousOn
    (twoFormChartTransport_continuousOn g c)
  have h₃ := (tensorTransportWeight_continuous 3).comp_continuousOn
    (twoFormChartTransport_continuousOn g c)
  exact ((continuousOn_const.mul h₂).add (continuousOn_const.mul h₃)).add
    ((continuousOn_const.mul hc).mul h₂)

theorem TwoFormSmooth.coordinate_partial_control {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) (a : Fin 2 → Fin 4) :
    |partialDeriv (fun w => twoFormCoordinates o u c w a) i z| ≤
      twoFormChartControl g c z * (‖u ((chartAt FourSpace c).symm z)‖ +
        Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))) := by
  let V := ‖u ((chartAt FourSpace c).symm z)‖
  let E := Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))
  let A := 2 * tensorTransportWeight 3 (twoFormChartTransport g c z)
  let B := 2 * twoFormChartConnectionWeight g c z *
    tensorTransportWeight 2 (twoFormChartTransport g c z)
  have hV : 0 ≤ V := norm_nonneg _
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hA : 0 ≤ A := mul_nonneg (by norm_num) (tensorTransportWeight_nonneg _ _)
  have hB : 0 ≤ B := by
    dsimp [B, twoFormChartConnectionWeight]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ => tensorSlotWeight_nonneg _ _)))
      (tensorTransportWeight_nonneg _ _)
  have hs := tensorSlotAction_abs_le_weight (connectionMatrix g c i z)
    (twoFormCoordinates o u c z)
    (2 * tensorTransportWeight 2 (twoFormChartTransport g c z) * V)
    (mul_nonneg (mul_nonneg (by norm_num) (tensorTransportWeight_nonneg _ _)) hV)
    (twoFormCoordinates_abs_le u c z hz) a
  have hi : tensorSlotWeight 2 (connectionMatrix g c i z) ≤
      twoFormChartConnectionWeight g c z :=
    Finset.single_le_sum (fun j _ => tensorSlotWeight_nonneg 2 (connectionMatrix g c j z))
      (Finset.mem_univ i)
  have hs' : |tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a| ≤ B * V :=
    hs.trans ((mul_le_mul_of_nonneg_right hi
      (mul_nonneg (mul_nonneg (by norm_num) (tensorTransportWeight_nonneg _ _)) hV)).trans_eq
        (by dsimp [B]; ring))
  have heq : partialDeriv (fun w => twoFormCoordinates o u c w a) i z =
      twoFormCovariantCoordinates o u c z (Fin.cons i a) +
        tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a := by
    unfold twoFormCovariantCoordinates
    rw [covariantDerivative_direction]
    change _ = (partialDeriv (fun w => twoFormCoordinates o u c w a) i z -
      tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a) + _
    ring
  rw [heq]
  calc
    _ ≤ |twoFormCovariantCoordinates o u c z (Fin.cons i a)| +
      |tensorSlotAction (connectionMatrix g c i z) (twoFormCoordinates o u c z) a| := abs_add_le _ _
    _ ≤ A * E + B * V := add_le_add (hu.covariantCoordinates_abs_le c z hz _) hs'
    _ ≤ A * (V + E) + B * (V + E) := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hV) hA)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE) hB)
    _ ≤ twoFormChartControl g c z * (V + E) := by
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ (add_nonneg hV hE)
      change A + B ≤ _ + A + B
      linarith [mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (tensorTransportWeight_nonneg 2 (twoFormChartTransport g c z))]

theorem twoFormChart_compact_control (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : M → TwoFormFour), TwoFormSmooth o u →
      ∀ z ∈ K, (∀ a, |twoFormCoordinates o u c z a| ≤ C * ‖u ((chartAt FourSpace c).symm z)‖) ∧
        ∀ i a, |partialDeriv (fun w => twoFormCoordinates o u c w a) i z| ≤
          C * (‖u ((chartAt FourSpace c).symm z)‖ +
            Real.sqrt (twoFormCovariantPairing o u u ((chartAt FourSpace c).symm z))) := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn
    ((twoFormChartControl_continuousOn g c).mono hKt)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun u hu z hz => ?_⟩
  have hbound : twoFormChartControl g c z ≤ max C 0 :=
    (le_abs_self _).trans ((hC _ ⟨z, hz, rfl⟩).trans (le_max_left _ _))
  refine ⟨fun a => (twoFormCoordinates_abs_le u c z (hKt hz) a).trans ?_, fun i a =>
    (hu.coordinate_partial_control c z (hKt hz) i a).trans
      (mul_le_mul_of_nonneg_right hbound (by positivity))⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply le_trans _ hbound
  unfold twoFormChartControl
  have hw : 0 ≤ twoFormChartConnectionWeight g c z :=
    Finset.sum_nonneg (fun _ _ => tensorSlotWeight_nonneg _ _)
  have h₂ := tensorTransportWeight_nonneg 2 (twoFormChartTransport g c z)
  have h₃ := tensorTransportWeight_nonneg 3 (twoFormChartTransport g c z)
  have hp := mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hw) h₂
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reverse chart norm control. This recovers the intrinsic two-form
value from its finitely many compact coordinate components. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem twoForm_norm_le_tensor_sum (u : TwoFormFour) :
    ‖u‖ ≤ ∑ a : Fin 2 → Fin 4, |twoFormTensor u a| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun a : Fin 2 → Fin 4 => |twoFormTensor u a|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hs
  have hn := twoFormTensor_norm u
  simp only [frameTensorSquareNorm, frameTensorPairing, ← pow_two] at hn
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mp
  nlinarith [sq_nonneg ‖u‖]

theorem frameTensor_sum_abs_le {n : ℕ} (P : Mat4) (T : CovariantCoordinates n) :
    (∑ a : Fin n → Fin 4, |frameTensor P T a|) ≤
      (Fintype.card (Fin n → Fin 4) : ℝ) * tensorTransportWeight n P *
        ∑ b : Fin n → Fin 4, |T b| := by
  have hsum : 0 ≤ ∑ b : Fin n → Fin 4, |T b| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc
    _ ≤ ∑ _a : Fin n → Fin 4, tensorTransportWeight n P * ∑ b : Fin n → Fin 4, |T b| :=
      Finset.sum_le_sum (fun a _ => frameTensor_abs_le_weight P T _ hsum
        (fun b => Finset.single_le_sum (fun c _ => abs_nonneg (T c)) (Finset.mem_univ b)) a)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartReverseControl (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  (Fintype.card (Fin 2 → Fin 4) : ℝ) * tensorTransportWeight 2 (chartGramMatrix g c 1 z)

theorem twoFormChartReverseControl_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (twoFormChartReverseControl g c) (chartAt FourSpace c).target := by
  apply continuousOn_const.mul
  apply (tensorTransportWeight_continuous 2).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j z hz
  exact (chartGramMatrix_contDiffAt g c 1 z hz i j).continuousAt.continuousWithinAt

theorem twoForm_chart_reverse_value (u : M → TwoFormFour) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (r : ℝ) :
    |r| * ‖u ((chartAt FourSpace c).symm z)‖ ≤ twoFormChartReverseControl g c z *
      ∑ a : Fin 2 → Fin 4, |r * twoFormCoordinates o u c z a| := by
  have h := twoForm_norm_le_tensor_sum (twoFormChartValue o u c 1 (by simp) z)
  rw [twoFormChartValue_norm o u c 1 (by simp) z hz,
    twoFormChartValue_tensor o u c 1 (by simp) z hz] at h
  have hb := h.trans (frameTensor_sum_abs_le (chartGramMatrix g c 1 z) (twoFormCoordinates o u c z))
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg r)
  calc
    _ ≤ |r| * (twoFormChartReverseControl g c z * ∑ a : Fin 2 → Fin 4, |twoFormCoordinates o u c z a|) := hm
    _ = _ := by simp only [abs_mul, ← Finset.mul_sum]; ring

theorem twoForm_chart_reverse_bound (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : M → TwoFormFour) (z : FourSpace), z ∈ K → ∀ r : ℝ,
      |r| * ‖u ((chartAt FourSpace c).symm z)‖ ≤
        C * ∑ a : Fin 2 → Fin 4, |r * twoFormCoordinates o u c z a| := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn
    ((twoFormChartReverseControl_continuousOn g c).mono hKt)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun u z hz r => ?_⟩
  have hbound : twoFormChartReverseControl g c z ≤ max C 0 :=
    (le_abs_self _).trans ((hC _ ⟨z, hz, rfl⟩).trans (le_max_left _ _))
  exact (twoForm_chart_reverse_value (o := o) u c z (hKt hz) r).trans
    (mul_le_mul_of_nonneg_right hbound (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual L2 sections obtained from continuous frame tensors, together
with their exact pairings against smooth two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem twoFormFromTensorL2_norm_le (F : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o)) :
    ‖twoFormFromTensorL2 F‖ ≤ ‖F‖ := by
  let w := twoFormFromTensorL2 F
  have hT : ‖twoFormTensorL2 w‖ ≤ 2 * ‖w‖ := by
    nlinarith [twoFormTensorL2_norm_sq w, norm_nonneg w, norm_nonneg (twoFormTensorL2 w)]
  have hi := (le_abs_self (inner ℝ F (twoFormTensorL2 w))).trans
    (abs_real_inner_le_norm F (twoFormTensorL2 w))
  have hb := mul_le_mul_of_nonneg_left hT (norm_nonneg F)
  have he : ‖w‖ ^ 2 = (1 / 2 : ℝ) * inner ℝ F (twoFormTensorL2 w) := by
    rw [← real_inner_self_eq_norm_sq]
    exact twoFormFromTensorL2_pairing F w
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ ‖F‖
    rw [hw]
    exact norm_nonneg _
  · have hwpos := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    change ‖w‖ ≤ ‖F‖
    nlinarith

def twoFormFromContinuousTensor : C(FrameBundle g, TwoTensorEuclidean) →L[ℝ] TwoFormL2 o :=
  (twoFormFromTensorL2 (o := o)).comp (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ)

theorem twoFormFromContinuousTensor_pairing (F : C(FrameBundle g, TwoTensorEuclidean))
    (v : SmoothL2TwoForm o) :
    inner ℝ (twoFormFromContinuousTensor F) (smoothTwoFormToL2 v) =
      (1 / 2 : ℝ) * ∫ e, inner ℝ (F e) (smoothTwoFormEuclideanValue (v : smoothTwoForms o) e)
        ∂canonicalFrameMeasure g o := by
  change inner ℝ (twoFormFromTensorL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F))
    (smoothTwoFormToL2 v) = _
  rw [twoFormFromTensorL2_pairing, twoFormTensorL2_smooth]
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
      (smoothTwoFormEuclideanValue (v : smoothTwoForms o))] with e hF hv
  rw [hF]
  exact congrArg (inner ℝ (F e)) hv

theorem twoFormFromContinuousTensor_smooth (v : SmoothL2TwoForm o) :
    twoFormFromContinuousTensor (smoothTwoFormEuclideanValue (v : smoothTwoForms o)) =
      smoothTwoFormToL2 v := by
  change twoFormFromTensorL2 (smoothTwoFormTensorValueL2 (v : smoothTwoForms o)) = _
  rw [← twoFormTensorL2_smooth]
  exact twoFormFromTensorL2_left_inverse _

theorem twoFormFromContinuousTensor_norm_le (F : C(FrameBundle g, TwoTensorEuclidean)) :
    ‖twoFormFromContinuousTensor (o := o) F‖ ≤ ‖F‖ := by
  apply (twoFormFromTensorL2_norm_le _).trans
  have hnorm : ‖(ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ :
      C(FrameBundle g, TwoTensorEuclidean) →L[ℝ] Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o))‖
      ≤ 1 := by
    simpa [measureUnivNNReal] using
      ContinuousMap.toLp_norm_le (𝕜 := ℝ) (E := TwoTensorEuclidean) (p := 2)
        (canonicalFrameMeasure g o)
  exact (ContinuousLinearMap.le_opNorm _ F).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg F)).trans_eq (one_mul _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior-derivative and codifferential energy of a smooth
two-form, and its integrated Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem integral_frame_sum_three (μ : Measure (FrameBundle g))
    (F : Fin 4 → Fin 4 → Fin 4 → FrameBundle g → ℝ)
    (hF : ∀ i j k, Integrable (F i j k) μ) :
    (∫ e, ∑ i, ∑ j, ∑ k, F i j k e ∂μ) = ∑ i, ∑ j, ∑ k, ∫ e, F i j k e ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hF i j k)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hF i j k)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_finsetSum _ (fun k _ => hF i j k)

def smoothTwoFormDeRhamEnergy (u : smoothTwoForms o) : ℝ :=
  ∫ e, twoFormDeRhamQuadratic (fun i j k =>
    twoFormFramedCovariantDerivative o u.val e ![i,j,k]) ∂canonicalFrameMeasure g o

theorem smoothTwoFormDeRhamEnergy_nonneg (u : smoothTwoForms o) :
    0 ≤ smoothTwoFormDeRhamEnergy u :=
  integral_nonneg (fun _ => twoFormDeRhamQuadratic_nonneg _)

theorem smoothTwoForm_derivative_product_integrable (u v : smoothTwoForms o)
    (a b : Fin 3 → Fin 4) :
    Integrable (fun e => twoFormFramedCovariantDerivative o u.val e a *
      twoFormFramedCovariantDerivative o v.val e b) (canonicalFrameMeasure g o) :=
  (((continuous_apply a).comp u.property.continuous_framedCovariantDerivative).mul
    ((continuous_apply b).comp v.property.continuous_framedCovariantDerivative)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem smoothTwoFormDeRhamEnergy_cross (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = smoothTwoFormCovariantEnergy u u +
      (∑ i, ∑ j, ∑ k, ∫ e,
        twoFormFramedCovariantDerivative o u.val e ![i,i,k] *
        twoFormFramedCovariantDerivative o u.val e ![j,j,k] ∂canonicalFrameMeasure g o) -
      (∑ i, ∑ j, ∑ k, ∫ e,
        twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
        twoFormFramedCovariantDerivative o u.val e ![j,i,k] ∂canonicalFrameMeasure g o) := by
  let μ := canonicalFrameMeasure g o
  let D := fun e i j k => twoFormFramedCovariantDerivative o u.val e ![i,j,k]
  let A := fun e => ∑ i, ∑ j, ∑ k, D e i j k * D e i j k
  let B := fun e => ∑ i, ∑ j, ∑ k, D e i i k * D e j j k
  let C := fun e => ∑ i, ∑ j, ∑ k, D e i j k * D e j i k
  have hi (a b : Fin 3 → Fin 4) := smoothTwoForm_derivative_product_integrable u u a b
  have hA : Integrable A μ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi ![i,j,k] ![i,j,k]
  have hB : Integrable B μ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi ![i,i,k] ![j,j,k]
  have hC : Integrable C μ := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hi ![i,j,k] ![j,i,k]
  have he : smoothTwoFormDeRhamEnergy u = ∫ e, (1 / 2 : ℝ) * A e + B e - C e ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with e
    simpa only [D, A, B, C, pow_two] using
      twoFormDeRhamQuadratic_eq (D e) (u.property.framedCovariant_skew hRic e)
  have hAB : Integrable (fun e => (1 / 2 : ℝ) * A e + B e) μ :=
    (hA.const_mul (1 / 2 : ℝ)).add hB
  rw [he, integral_sub hAB hC,
    integral_add (hA.const_mul (1 / 2 : ℝ)) hB, integral_const_mul]
  have ha : smoothTwoFormCovariantEnergy u u = (1 / 2 : ℝ) * ∫ e, A e ∂μ :=
    smoothTwoFormCovariantEnergy_eq_frame u u
  rw [← ha]
  congr 2
  · exact integral_frame_sum_three μ _ (fun i j k => hi ![i,i,k] ![j,j,k])
  · exact integral_frame_sum_three μ _ (fun i j k => hi ![i,j,k] ![j,i,k])

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual H1 completion embeds injectively in L2. The rough Green
identity makes the derivative graph closable; no injectivity premise is
imposed on the completion map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormH1_eq_zero_of_value_eq_zero (hRic : RicciThree g)
    (u : TwoFormH1 o) (hu : twoFormH1ToL2 u = 0) : u = 0 := by
  have htest (v : SmoothH1TwoForm o) : inner ℝ u (smoothTwoFormToH1 v) = 0 := by
    rw [twoFormH1_inner_smooth hRic, hu, map_zero]
  have hall : ∀ v : TwoFormH1 o, inner ℝ u v = 0 := by
    have heq : (fun v : TwoFormH1 o => inner ℝ u v) = fun _ => 0 :=
      (smoothTwoFormToH1_dense (o := o)).equalizer
        (continuous_const.inner continuous_id) continuous_const (funext htest)
    intro v
    exact congrFun heq v
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hall u)

theorem twoFormH1ToL2_injective (hRic : RicciThree g) :
    Function.Injective (twoFormH1ToL2 (o := o)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply twoFormH1_eq_zero_of_value_eq_zero hRic
  rw [map_sub, huv, sub_self]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rough trace retains the alternating two-form slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.framedSecond_skew (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) (i j k l : Fin 4) :
    twoFormFramedSecondDerivative o u e ![i,j,l,k] =
      -twoFormFramedSecondDerivative o u e ![i,j,k,l] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hk := hu.framedCovariant_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,l,k]
  have hj := (hu.framedCovariant_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k,l]).neg
  have heq : (fun t => -(twoFormFramedCovariantDerivative o u (γ t) ![j,k,l])) =
      fun t => twoFormFramedCovariantDerivative o u (γ t) ![j,l,k] := by
    funext t
    exact (hu.framedCovariant_skew hRic (γ t) j k l).symm
  change HasDerivAt (fun t => -(twoFormFramedCovariantDerivative o u (γ t) ![j,k,l]))
    (-twoFormFramedSecondDerivative o u (γ 0) (Fin.cons i ![j,k,l])) 0 at hj
  rw [heq] at hj
  have h := hk.unique hj
  rw [hzero] at h
  exact h

theorem TwoFormSmooth.roughTrace_skew (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) (j k : Fin 4) :
    twoFormFramedRoughTrace o u e ![k,j] = -twoFormFramedRoughTrace o u e ![j,k] := by
  change (∑ i, twoFormFramedSecondDerivative o u e ![i,i,k,j]) =
    -(∑ i, twoFormFramedSecondDerivative o u e ![i,i,j,k])
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => hu.framedSecond_skew hRic e i i j k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality in the Weyl norm gap forces its continuous norm to be one.
The equality argument uses only the two limiting scalar moments. -/
namespace PositiveEinsteinFour.Geometry
open MeasureTheory Filter Set
open scoped _root_.Topology
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [PreconnectedSpace Ω]
  [Nonempty Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]

theorem weyl_gap_equality_constant (v : C(Ω, ℝ)) (hv : ∀ x, 0 ≤ v x)
    (hnorm : (∫ x, v x ^ 2 ∂μ) = 1)
    (hgap : Real.sqrt (∫ x, ((v x ^ 2) ^ (1 / 3 : ℝ)) ^ 2 ∂μ) ≤
      ∫ x, v x * (v x ^ 2) ^ (1 / 3 : ℝ) ∂μ) : ∀ x, v x = 1 := by
  let u : C(Ω, ℝ) := ⟨fun x => (v x ^ 2) ^ (1 / 3 : ℝ),
    (v.continuous.pow 2).rpow_const (fun _ => Or.inr (by norm_num))⟩
  let A := ∫ x, u x ^ 2 ∂μ
  let c := Real.sqrt A
  have hi (f : C(Ω, ℝ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hun (x : Ω) : 0 ≤ u x := Real.rpow_nonneg (sq_nonneg _) _
  have hA : 0 ≤ A := integral_nonneg (fun x => sq_nonneg (u x))
  have hc : c ^ 2 = A := Real.sq_sqrt hA
  have hcs : (∫ x, v x * u x ∂μ) ≤ c := by
    have hvLp : MemLp (fun x => v x) (ENNReal.ofReal (2 : ℝ)) μ :=
      v.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have huLp : MemLp (fun x => u x) (ENNReal.ofReal (2 : ℝ)) μ :=
      u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall hv) (Filter.Eventually.of_forall hun)
      hvLp huLp
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hnorm, Real.sqrt_one, one_mul] using h
  have hI : (∫ x, v x * u x ∂μ) = c := le_antisymm hcs hgap
  have hz : (∫ x, (c * v x - u x) ^ 2 ∂μ) = 0 := by
    calc
      _ = c ^ 2 * (∫ x, v x ^ 2 ∂μ) -
          2 * c * (∫ x, v x * u x ∂μ) + ∫ x, u x ^ 2 ∂μ := by
        have hpoint : (fun x => (c * v x - u x) ^ 2) =
            fun x => c ^ 2 * v x ^ 2 - (2 * c) * (v x * u x) + u x ^ 2 := by
          funext x; ring
        have hvI : Integrable (fun x => v x ^ 2) μ :=
          (v.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have huI : Integrable (fun x => u x ^ 2) μ :=
          (u.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hvuI : Integrable (fun x => v x * u x) μ :=
          (v.continuous.mul u.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [hpoint]
        calc
          _ = (∫ x, c ^ 2 * v x ^ 2 - (2 * c) * (v x * u x) ∂μ) +
              ∫ x, u x ^ 2 ∂μ :=
            integral_add ((hvI.const_mul (c ^ 2)).sub (hvuI.const_mul (2 * c))) huI
          _ = ((∫ x, c ^ 2 * v x ^ 2 ∂μ) -
              ∫ x, (2 * c) * (v x * u x) ∂μ) + ∫ x, u x ^ 2 ∂μ :=
            congrArg (fun z => z + ∫ x, u x ^ 2 ∂μ)
              (integral_sub (hvI.const_mul (c ^ 2)) (hvuI.const_mul (2 * c)))
          _ = _ := by rw [integral_const_mul, integral_const_mul]

      _ = 0 := by
        rw [hnorm, hI]
        change c ^ 2 * 1 - 2 * c * c + A = 0
        nlinarith only [hc]
  have hrel (x : Ω) : c * v x = u x := by
    have hcont : Continuous (fun x => (c * v x - u x) ^ 2) :=
      ((continuous_const.mul v.continuous).sub u.continuous).pow 2
    by_contra h
    have hp := integral_pos_of_integrable_nonneg_nonzero (μ := μ) hcont
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun x => sq_nonneg (c * v x - u x))
      (pow_ne_zero 2 (sub_ne_zero.mpr h))
    linarith
  have hfinite : (range v).Finite := by
    apply (Set.toFinite ({0, 1 / c ^ 3} : Set ℝ)).subset
    rintro _ ⟨x,rfl⟩
    by_cases hx : v x = 0
    · simp [hx]
    · have hu : u x ^ 3 = v x ^ 2 := by
        dsimp only [u, ContinuousMap.coe_mk]
        rw [← Real.rpow_mul_natCast (sq_nonneg _)]
        norm_num
      rw [← hrel x] at hu
      have hf : v x ^ 2 * (c ^ 3 * v x - 1) = 0 := by nlinarith only [hu]
      have he : c ^ 3 * v x = 1 := sub_eq_zero.mp
        ((mul_eq_zero.mp hf).resolve_left (pow_ne_zero 2 hx))
      have hc0 : c ^ 3 ≠ 0 := by intro h; rw [h,zero_mul] at he; norm_num at he
      have hx' : v x = 1 / c ^ 3 := (eq_div_iff hc0).mpr (by linarith only [he])
      simp [hx']
  have hsub : (range v).Subsingleton := by
    by_contra h
    exact hfinite.not_infinite ((isPreconnected_range v.continuous).infinite_of_nontrivial
      (not_subsingleton_iff.mp h))
  let x₀ : Ω := Classical.choice inferInstance
  have hconst (x : Ω) : v x = v x₀ := hsub ⟨x,rfl⟩ ⟨x₀,rfl⟩
  have hsquare : v x₀ ^ 2 = 1 := by simpa only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul] using hnorm
  intro x
  rw [hconst]
  nlinarith [hv x₀]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential differential and its metric Jacobian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_rescaled_full_differential (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source)
    (w : Fin 4 → ℝ) :
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ
      WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e (t • v))) (coordinateVector 0) (WithLp.toLp 2 w)) =
      jacobiBlockMatrix t ((actualJacobiSolution g hRic e).J t) *ᵥ w := by
  let a := frameFullInitialVariation g e w
  have hc : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  have ha : ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))
      (WithLp.toLp 2 w) = a := by
    change (0, frameMomentumMap g e.base e (WithLp.toLp 2 w)) = a
    rw [frameMomentumMap_apply g e.base e hc]
    rfl
  rw [(frameExponential_rescaled_hasFDerivAt g o d e he t ht hd).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ha]
  have hchart := actualFullVariationPosition_eq_chart g o d e he a t hd
  change actualFullVariationPosition g o e a t =
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ WithLp.ofLp
      (frameGeodesicCoordinateVariation g o d e a t).1 at hchart
  rw [frameGeodesicCoordinateVariation_fst g o d e he a t hd] at hchart
  exact hchart.symm.trans (actualFullVariation_eq_jacobi g o hRic e he w t).1

theorem frameExponential_rescaled_fderiv (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      (coordinateVector 0) = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
          jacobiBlockMatrix t ((actualJacobiSolution g hRic e).J t)) := by
  let E := frameChartMatrix g d (parallelFrameFlowMap g 0 t e)
  have hE : IsUnit E.det := Matrix.isUnit_det_of_left_inverse
    (frameChartMatrix_normalizes g d (parallelFrameFlowMap g 0 t e) hd)
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun w : Fin 4 → ℝ => E *ᵥ w)
    (frameExponential_rescaled_full_differential g o hRic d e he t ht hd (WithLp.ofLp v))
  change E *ᵥ (E⁻¹ *ᵥ WithLp.ofLp (fderiv ℝ
    (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      (coordinateVector 0) v)) = _ at h
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec] at h
  apply (WithLp.ofLp_injective 2)
  exact h.trans (Matrix.mulVec_mulVec (WithLp.ofLp v) E _)

private theorem jacobiBlockMatrix_rescale (t : ℝ) (ht : t ≠ 0) (J : Jacobi.NormalMatrix) :
    t⁻¹ • jacobiBlockMatrix t J = jacobiBlockMatrix 1 (t⁻¹ • J) := by
  ext i j
  change t⁻¹ * jacobiBlockMatrix t J i j = jacobiBlockMatrix 1 (t⁻¹ • J) i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [jacobiBlockMatrix, ht]

/-- The actual exponential differential at `t e₀`, written using the
parallel frame at its endpoint. -/
theorem frameExponential_hasFDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    HasFDerivAt (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e v))
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
        jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)))
      (t • coordinateVector 0) := by
  let E := frameChartMatrix g d (parallelFrameFlowMap g 0 t e)
  let J := (actualJacobiSolution g hRic e).J t
  have hres := (frameExponential_rescaled_hasFDerivAt g o d e he t ht hd).differentiableAt.hasFDerivAt
  rw [frameExponential_rescaled_fderiv g o hRic d e he t ht hd] at hres
  have hres' : HasFDerivAt
      (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix t J))
      (t⁻¹ • (t • coordinateVector 0)) := by
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hres
  have hs : HasFDerivAt (fun v : FourSpace => t⁻¹ • v)
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) (t • coordinateVector 0) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).hasFDerivAt
  have h := hres'.comp (t • coordinateVector 0) hs
  have heq : (fun v : FourSpace => chartAt FourSpace d
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace d (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hD : (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix t J)).comp
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix 1 (t⁻¹ • J)) := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
      ← map_smul, ← Matrix.mul_smul, jacobiBlockMatrix_rescale t ht.ne']
  change HasFDerivAt (fun v : FourSpace => chartAt FourSpace d
      (frameExponential g o e (t • (t⁻¹ • v))))
      ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix t J)).comp
        (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace)) (t • coordinateVector 0) at h
  rw [heq, hD] at h
  exact h

theorem frameExponential_metric_jacobian (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    chartVolumeDensity g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *
      |LinearMap.det (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e v)) (t • coordinateVector 0)).toLinearMap| =
        |((actualJacobiSolution g hRic e).J t).det / t ^ 3| := by
  rw [(frameExponential_hasFDerivAt g o hRic d e he t ht hd).fderiv]
  exact jacobiBlockMatrix_scaled_linear_density g d (parallelFrameFlowMap g 0 t e) hd
    t ((actualJacobiSolution g hRic e).J t)

theorem frameExponential_metric_jacobian_preconjugate (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    chartVolumeDensity g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *
      |LinearMap.det (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e v)) (t • coordinateVector 0)).toLinearMap| =
        (actualRegularJacobi g hRic e t).truncatedDensity / t ^ 3 := by
  rw [frameExponential_metric_jacobian g o hRic d e he t ht hd, abs_div,
    actualJacobi_abs_det_eq_truncatedDensity g hRic e t ht hpre, abs_of_pos (pow_pos ht 3)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual first conjugate time is measurable and lower semicontinuous.
Joint continuity of the normalized Jacobi matrix follows by averaging its
jointly continuous velocity, including at time zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

/-- Measurability of the preconjugate set implies measurability of the first conjugate time. -/
theorem actualFirstConjugateTime_measurable (g : SmoothMetric M) (hRic : RicciThree g) :
    Measurable (actualFirstConjugateTime g hRic) := by
  apply measurable_of_Ioi
  intro t
  have heq : actualFirstConjugateTime g hRic ⁻¹' Ioi t =
      (fun e : FrameBundle g => (t, e)) ⁻¹' preconjugateSet (actualJacobiMatrix g hRic) := by
    ext e
    exact (actualJacobi_preconjugate_iff_lt g hRic e t).symm
  rw [heq]
  exact (measurableSet_preconjugate _ (actualJacobiJ_joint_continuous g hRic)).preimage
    (measurable_const.prodMk measurable_id)

def actualNormalizedJacobiMatrix (g : SmoothMetric M) (hRic : RicciThree g)
    (p : ℝ × FrameBundle g) : NormalMatrix :=
  normalizedJacobi (actualJacobiSolution g hRic p.2).J p.1

theorem actualNormalizedJacobiMatrix_zero (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : actualNormalizedJacobiMatrix g hRic (0, e) = 1 := by
  apply normalizedJacobi_zero
  simpa only [MatrixJacobiSolution.initial_velocity] using
    (actualJacobiSolution g hRic e).position_derivative 0

theorem actualNormalizedJacobiMatrix_eq_average (g : SmoothMetric M)
    (hRic : RicciThree g) (t : ℝ) (e : FrameBundle g) :
    actualNormalizedJacobiMatrix g hRic (t, e) =
      ∫ r in (0 : ℝ)..1, (actualJacobiSolution g hRic e).V (t * r) := by
  let d := actualJacobiSolution g hRic e
  by_cases ht : t = 0
  · subst t
    simp only [actualNormalizedJacobiMatrix_zero, zero_mul,
      intervalIntegral.integral_const, sub_zero, one_smul]
    exact (actualJacobiSolution g hRic e).initial_velocity.symm
  · have hd (r : ℝ) : HasDerivAt (fun r => d.J (t * r)) (t • d.V (t * r)) r := by
      simpa only [Function.comp_def, mul_one] using
        (d.position_derivative (t * r)).scomp r ((hasDerivAt_id r).const_mul t)
    have hc : Continuous (fun r => t • d.V (t * r)) := by
      have hv := d.continuous_V.comp
        ((continuous_const : Continuous (fun _ : ℝ => t)).mul continuous_id)
      simpa only [Pi.mul_apply, Function.comp_def, id_eq] using! hv.const_smul t
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
      (hc.intervalIntegrable 0 1)
    simp only [mul_one, mul_zero, d.initial_position, sub_zero,
      intervalIntegral.integral_smul] at hFTC
    change normalizedJacobi d.J t = _
    rw [normalizedJacobi_pos d.initial_position ht, ← hFTC, smul_smul,
      inv_mul_cancel₀ ht, one_smul]

theorem actualNormalizedJacobiMatrix_continuous (g : SmoothMetric M)
    (hRic : RicciThree g) : Continuous (actualNormalizedJacobiMatrix g hRic) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hc : Continuous (fun p : (ℝ × FrameBundle g) × ℝ =>
      (actualJacobiSolution g hRic p.1.2).V (p.1.1 * p.2)) :=
    (actualJacobiV_joint_continuous g hRic).comp
      (((continuous_fst.comp continuous_fst).mul continuous_snd).prodMk
        (continuous_snd.comp continuous_fst))
  have hi : Continuous (fun p : ℝ × FrameBundle g =>
      ∫ r in Icc (0 : ℝ) 1, (actualJacobiSolution g hRic p.2).V (p.1 * r)) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  convert hi using 1
  funext p
  rw [actualNormalizedJacobiMatrix_eq_average, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]

private theorem actualNormalizedJacobiMatrix_isUnit_iff (g : SmoothMetric M)
    (hRic : RicciThree g) (t : ℝ) (e : FrameBundle g) (ht : t ≠ 0) :
    IsUnit (actualNormalizedJacobiMatrix g hRic (t, e)) ↔
      IsUnit ((actualJacobiSolution g hRic e).J t) := by
  have hfactor : t⁻¹ ^ 3 ≠ 0 := pow_ne_zero 3 (inv_ne_zero ht)
  simp only [actualNormalizedJacobiMatrix,
    normalizedJacobi_pos (actualJacobiSolution g hRic e).initial_position ht,
    Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Fintype.card_fin,
    isUnit_iff_ne_zero, ne_eq, mul_eq_zero, hfactor, false_or]

theorem actualFirstConjugateTime_lowerSemicontinuous (g : SmoothMetric M)
    (hRic : RicciThree g) : LowerSemicontinuous (actualFirstConjugateTime g hRic) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  let F : Icc (0 : ℝ) t × FrameBundle g → NormalMatrix := fun p =>
    actualNormalizedJacobiMatrix g hRic (p.1.val, p.2)
  have hF : Continuous F := (actualNormalizedJacobiMatrix_continuous g hRic).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hz : IsClosed {p : Icc (0 : ℝ) t × FrameBundle g | (F p).det = 0} :=
    isClosed_eq hF.matrix_det continuous_const
  have hclosed := isClosedMap_snd_of_compactSpace _ hz
  have hopen : IsOpen {e : FrameBundle g | ∀ r : Icc (0 : ℝ) t, IsUnit (F (r, e))} := by
    have heq : {e : FrameBundle g | ∀ r : Icc (0 : ℝ) t, IsUnit (F (r, e))} =
        (Prod.snd '' {p : Icc (0 : ℝ) t × FrameBundle g | (F p).det = 0})ᶜ := by
      ext e
      simp only [mem_ofPred_eq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
        mem_compl_iff, mem_image, Prod.exists]
      aesop
    rw [heq]
    exact hclosed.isOpen_compl
  have heq : actualFirstConjugateTime g hRic ⁻¹' Ioi t =
      {e : FrameBundle g | ∀ r : Icc (0 : ℝ) t, IsUnit (F (r, e))} := by
    ext e
    rw [mem_preimage, mem_Ioi, ← actualJacobi_preconjugate_iff_lt]
    constructor
    · intro hp r
      by_cases hr : r.val = 0
      · change IsUnit (actualNormalizedJacobiMatrix g hRic (r.val, e))
        rw [hr, actualNormalizedJacobiMatrix_zero]
        exact isUnit_one
      · apply (actualNormalizedJacobiMatrix_isUnit_iff g hRic r.val e hr).mpr
        exact hp r.val (lt_of_le_of_ne r.property.1 (Ne.symm hr)) r.property.2
    · intro hp s hs hst
      exact (actualNormalizedJacobiMatrix_isUnit_iff g hRic s e hs.ne').mp
        (hp ⟨s, hs.le, hst⟩)
  rwa [heq]

/-- Positive times strictly before the first conjugate time form an open
subset of the actual radial parameter space. -/
theorem actual_preconjugate_radial_isOpen (g : SmoothMetric M) (hRic : RicciThree g) :
    IsOpen {p : ℝ × FrameBundle g |
      0 < p.1 ∧ p.1 < actualFirstConjugateTime g hRic p.2} := by
  have hc := (actualFirstConjugateTime_lowerSemicontinuous g hRic).isClosed_epigraph
  have ho : IsOpen {p : ℝ × FrameBundle g |
      p.1 < actualFirstConjugateTime g hRic p.2} := by
    simpa only [preimage_ofPred_eq, compl_ofPred, not_le] using
      (hc.preimage (continuous_snd.prodMk continuous_fst)).isOpen_compl
  exact (isOpen_lt continuous_const continuous_fst).inter ho

end
end PositiveEinsteinFour.Geometry
end


section

/-! A conjugate point supplies a nonzero actual normal Jacobi field with
zero endpoint positions and nonzero terminal covariant velocity.  The last
assertion follows from uniqueness of the linear ODE, anchored at that endpoint. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

theorem MatrixJacobiSolution.kernel_intersection_eq_zero {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K)
    (c : ℝ) (w : Fin 3 → ℝ) (hJ : d.J c *ᵥ w = 0) (hV : d.V c *ᵥ w = 0) :
    w = 0 := by
  let B : NormalMatrix := fun i _ => w i
  let γ : ℝ → JacobiState := fun s => (d.J s * B, d.V s * B)
  let A : ℝ → JacobiState →L[ℝ] JacobiState := fun s => jacobiStateOperator (R s)
  let T : ℝ := |c| + 1
  have hbound (s : ℝ) : ‖A s‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  have hγ : LinearCurveOn A γ (Ioo (-T) T) := by
    intro s _
    have hp := (d.position_derivative s).mul_const B
    have hv := (d.velocity_derivative s).mul_const B
    simpa only [γ, A, jacobiStateOperator_apply, neg_mul, Matrix.mul_assoc] using
      hp.prodMk hv
  have hzero : LinearCurveOn A (fun _ => 0) (Ioo (-T) T) := by
    intro s _
    simpa only [map_zero] using hasDerivAt_const s (0 : JacobiState)
  have hmulzero (Q : NormalMatrix) (hQ : Q *ᵥ w = 0) : Q * B = 0 := by
    ext i j
    change (Q *ᵥ w) i = 0
    exact congrFun hQ i
  have hinit : γ c = 0 := by
    change (d.J c * B, d.V c * B) = (0, 0)
    rw [hmulzero _ hJ, hmulzero _ hV]
  have hc : c ∈ Ioo (-T) T := by
    dsimp [T]
    constructor <;> linarith [neg_abs_le c, le_abs_self c]
  have h0 : (0 : ℝ) ∈ Ioo (-T) T := by
    dsimp [T]
    constructor <;> linarith [abs_nonneg c]
  have heq := linear_curve_eqOn_interval A (1 + K) hbound hγ hzero hc hinit
  have hB : B = 0 := by
    simpa only [γ, d.initial_velocity, Matrix.one_mul, Prod.snd_zero] using
      congrArg Prod.snd (heq h0)
  funext i
  exact congrArg (fun Q : NormalMatrix => Q i 0) hB

theorem MatrixJacobiSolution.velocity_ne_zero_of_kernel {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K)
    (c : ℝ) (w : Fin 3 → ℝ) (hw : w ≠ 0) (hJ : d.J c *ᵥ w = 0) :
    d.V c *ᵥ w ≠ 0 := by
  intro hV
  exact hw (d.kernel_intersection_eq_zero K hK c w hJ hV)

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_actualJacobi_conjugate_vector (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : ℝ)
    (hc : ¬ IsUnit ((actualJacobiSolution g hRic e).J c)) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ (actualJacobiSolution g hRic e).J c *ᵥ w = 0 ∧
      (actualJacobiSolution g hRic e).V c *ᵥ w ≠ 0 := by
  have hdet : ((actualJacobiSolution g hRic e).J c).det = 0 := by
    by_contra hne
    exact hc ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
  obtain ⟨w, hw, hJ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  exact ⟨w, hw, hJ,
    (actualJacobiSolution g hRic e).velocity_ne_zero_of_kernel K (hK e) c w hw hJ⟩

theorem exists_actualFirstConjugate_vector (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      (actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e) *ᵥ w = 0 ∧
      (actualJacobiSolution g hRic e).V (actualFirstConjugateTime g hRic e) *ᵥ w ≠ 0 :=
  exists_actualJacobi_conjugate_vector g hRic e _
    (actualFirstConjugateTime_singular g hRic e)

/-- The conjugate vector is realized by the derivative of the geodesic flow. -/
theorem exists_actualConjugateNormalVariation (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (c : ℝ)
    (hc : ¬ IsUnit ((actualJacobiSolution g hRic e).J c)) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      actualNormalVariationPosition g o e (frameNormalInitialVariation g e w) 0 = 0 ∧
      actualNormalVariationVelocity g o e (frameNormalInitialVariation g e w) 0 = w ∧
      actualNormalVariationPosition g o e (frameNormalInitialVariation g e w) c = 0 ∧
      actualNormalVariationVelocity g o e (frameNormalInitialVariation g e w) c ≠ 0 := by
  obtain ⟨w, hw, hJ, hV⟩ := exists_actualJacobi_conjugate_vector g hRic e c hc
  have h0 := actualNormalVariation_initial g o e he w
  have h := actualNormalVariation_eq_jacobi g o hRic e he w c
  exact ⟨w, hw, h0.1, h0.2, h.1.trans hJ, fun hz => hV (h.2.symm.trans hz)⟩

theorem exists_actualFirstConjugateNormalVariation (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      actualNormalVariationPosition g o e (frameNormalInitialVariation g e w) 0 = 0 ∧
      actualNormalVariationVelocity g o e (frameNormalInitialVariation g e w) 0 = w ∧
      actualNormalVariationPosition g o e (frameNormalInitialVariation g e w)
        (actualFirstConjugateTime g hRic e) = 0 ∧
      actualNormalVariationVelocity g o e (frameNormalInitialVariation g e w)
        (actualFirstConjugateTime g hRic e) ≠ 0 :=
  exists_actualConjugateNormalVariation g o hRic e he _
    (actualFirstConjugateTime_singular g hRic e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A radial determinant cutoff at or before the first conjugate point is
bounded by the actual truncated Jacobi density.  The endpoint contributes
zero, and the first conjugate time bounds the support by `[0, π]`. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_det_firstConjugate_eq_zero (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ((actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e)).det = 0 := by
  by_contra hdet
  apply actualFirstConjugateTime_singular g hRic e
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)

theorem actualRegularJacobi_truncatedDensity_firstConjugate (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (r : ℝ) :
    (actualRegularJacobi g hRic e r).truncatedDensity =
      if r < actualFirstConjugateTime g hRic e then
        ((actualJacobiSolution g hRic e).J r).det else 0 := by
  classical
  simp only [RegularJacobi.truncatedDensity, actualRegularJacobi_J,
    actualJacobi_preconjugate_iff_lt]

theorem actualJacobi_cutoff_le_truncatedDensity (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b r : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) (hr : 0 < r) :
    (if r ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0) ≤
      ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity := by
  classical
  by_cases hrb : r ≤ b
  · rw [ite_eq_left hrb]
    rcases lt_or_eq_of_le (hrb.trans hb) with hrc | hrc
    · rw [actualJacobi_abs_det_eq_truncatedDensity g hRic e r hr
        ((actualJacobi_preconjugate_iff_lt g hRic e r).mpr hrc)]
    · subst r
      rw [actualJacobi_det_firstConjugate_eq_zero, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  · rw [ite_eq_right hrb]
    exact zero_le

theorem actualJacobi_cutoff_le_truncatedIndicator (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b r : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) (hr : 0 < r) :
    (if r ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0) ≤
      (Icc (0 : ℝ) Real.pi).indicator
        (fun s => ENNReal.ofReal (actualRegularJacobi g hRic e s).truncatedDensity) r := by
  classical
  by_cases hrπ : r ≤ Real.pi
  · rw [Set.indicator_of_mem (show r ∈ Icc (0 : ℝ) Real.pi from ⟨hr.le, hrπ⟩)]
    exact actualJacobi_cutoff_le_truncatedDensity g hRic e b r hb hr
  · have hrb : ¬ r ≤ b := fun h => hrπ
      ((h.trans hb).trans (actualFirstConjugateTime_le_pi g hRic e))
    rw [ite_eq_right hrb]
    exact zero_le

theorem actualJacobi_cutoff_lintegral_le (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det|
        else 0) ∂((volume : Measure ℝ).comap Subtype.val)) ≤
      ∫⁻ r in Icc (0 : ℝ) Real.pi,
        ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity := by
  classical
  let f : ℝ → ℝ≥0∞ := fun r =>
    if r ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  let h : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity
  change (∫⁻ r : Ioi (0 : ℝ), f r.val ∂((volume : Measure ℝ).comap Subtype.val)) ≤ _
  rw [lintegral_subtype_comap measurableSet_Ioi f]
  calc
    (∫⁻ r in Ioi (0 : ℝ), f r) ≤
        ∫⁻ r in Ioi (0 : ℝ), (Icc (0 : ℝ) Real.pi).indicator h r := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact actualJacobi_cutoff_le_truncatedIndicator g hRic e b r hb hr
    _ ≤ ∫⁻ r, (Icc (0 : ℝ) Real.pi).indicator h r :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ r in Icc (0 : ℝ) Real.pi, h r := lintegral_indicator measurableSet_Icc h

theorem actualJacobi_truncatedDensity_integrableOn (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (a b : ℝ) :
    IntegrableOn (fun r => (actualRegularJacobi g hRic e r).truncatedDensity) (Icc a b) := by
  have hdet : Continuous (fun r => ((actualJacobiSolution g hRic e).J r).det) :=
    (actualJacobiSolution g hRic e).continuous_J.matrix_det
  have hm : Measurable (fun r => (actualRegularJacobi g hRic e r).truncatedDensity) := by
    have h : Measurable (fun r => if r < actualFirstConjugateTime g hRic e then
        ((actualJacobiSolution g hRic e).J r).det else 0) :=
      Measurable.ite measurableSet_Iio hdet.measurable measurable_const
    simpa only [actualRegularJacobi_truncatedDensity_firstConjugate] using h
  apply hdet.abs.integrableOn_Icc.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro r
  rw [actualRegularJacobi_truncatedDensity_firstConjugate]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using abs_nonneg (((actualJacobiSolution g hRic e).J r).det)

theorem actualJacobi_cutoff_lintegral_le_integral (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b : ℝ)
    (hb : b ≤ actualFirstConjugateTime g hRic e) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ b then ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det|
        else 0) ∂((volume : Measure ℝ).comap Subtype.val)) ≤
      ENNReal.ofReal (∫ r in Icc (0 : ℝ) Real.pi,
        (actualRegularJacobi g hRic e r).truncatedDensity) := by
  have hnonneg : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) Real.pi)),
      0 ≤ (actualRegularJacobi g hRic e r).truncatedDensity := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr.1
  rw [ofReal_integral_eq_lintegral_ofReal
    (actualJacobi_truncatedDensity_integrableOn g hRic e 0 Real.pi) hnonneg]
  exact actualJacobi_cutoff_lintegral_le g hRic e b hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed radial frame lies over the actual exponential map,
by uniqueness of the metric Hamiltonian trajectories. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.kinetic_eq {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (K : KineticLocalFlow g c (p.1, 0)) (hT : K.time ≤ F.time)
    (v : FourSpace) (hv : (v, p) ∈ closedBall (0, p) F.radius)
    (hK : heatRadialCotangentState g c v p ∈ ball (p.1, 0) K.radius)
    (t : ℝ) (ht : t ∈ Ioo (-K.time) K.time) :
    K.map (heatRadialCotangentState g c v p, t) =
      heatRadialCotangentState g c v (F.map ((v, p), t)).2 := by
  have he := K.eq_on _ hK
    (fun s => heatRadialCotangentState g c v (F.map ((v, p), s)).2)
    (by rw [F.initial (v, p) hv])
    (fun s hs => F.cotangent_derivative (v, p) hv s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  exact he ht

variable [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem heatRadialCotangentState_frame (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) :
    heatRadialCotangentState g c v (frameCoordinateState g c e) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
  rw [frameMomentumMap_apply g c e he v]
  rfl

theorem heatRadialFrameEndpoint_exponential (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (F : HeatRadialFrameFlow g c (frameCoordinateState g c e))
    (K : KineticLocalFlow g c (chartAt FourSpace c e.base, 0))
    (hT : K.time ≤ F.time) (t : ℝ) (ht : t ∈ Ioo (-K.time) K.time) (ht0 : 0 < t) :
    (fun v => (heatRadialFrameEndpoint F t v).1) =ᶠ[𝓝 0]
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
  let p := frameCoordinateState g c e
  have hFinit : ∀ᶠ v : FourSpace in 𝓝 0, (v, p) ∈ closedBall (0, p) F.radius := by
    have hc : Continuous (fun v : FourSpace => (v, p)) := continuous_id.prodMk continuous_const
    exact hc.continuousAt.preimage_mem_nhds (closedBall_mem_nhds (0, p) F.radius_pos)
  have hKinit : ∀ᶠ v : FourSpace in 𝓝 0,
      heatRadialCotangentState g c v p ∈ ball (p.1, 0) K.radius := by
    have hc : Continuous (fun v => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) :=
      continuous_const.prodMk (frameMomentumMap g c e).continuous
    have hc0 : ContinuousAt (fun v =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 := hc.continuousAt
    have hh := hc0.preimage_mem_nhds
      (by simpa only [map_zero] using
        ball_mem_nhds (chartAt FourSpace c e.base, (0 : FourSpace)) K.radius_pos)
    filter_upwards [hh] with v hv
    change heatRadialCotangentState g c v (frameCoordinateState g c e) ∈ _
    rw [heatRadialCotangentState_frame g c e he v]
    exact hv
  have hraw : ∀ᶠ v : FourSpace in 𝓝 0,
      (F.map ((v, p), t)).2.1 = chartAt FourSpace c (frameExponential g o e (t • v)) := by
    filter_upwards [hFinit, hKinit,
      frameExponential_chart_eventually_kinetic g o c e he K t ht ht0] with v hv hKv hexp
    have h := congrArg Prod.fst (F.kinetic_eq K hT v hv hKv t ht)
    rw [heatRadialCotangentState_frame g c e he v] at h
    exact h.symm.trans hexp.symm
  have hs : Tendsto (fun v : FourSpace => t⁻¹ • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun v : FourSpace => t⁻¹ • v) :=
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).continuous
    have h := (show ContinuousAt (fun v : FourSpace => t⁻¹ • v) 0 from hc.continuousAt).tendsto
    simpa only [smul_zero] using h
  filter_upwards [hs.eventually hraw] with v hv
  change (F.map ((t⁻¹ • v, p), t)).2.1 = _
  rw [hv, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Once positivity is known, real powers preserve the actual H1 closure.
A compact positive range permits the bounded smooth chain rule at every
real exponent, including negative exponents used in the rigidity argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarH1_power_of_positive_range (d : ParallelMetricData g μ)
    (u : scalarH1 d) (q a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hu : ∀ᵐ e ∂μ, scalarH1Value d u e ∈ Icc a B) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => (scalarH1Value d u e) ^ q) ∧
      ∀ i, (scalarH1Gradient d i v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => q * (scalarH1Value d u e) ^ (q - 1) * scalarH1Gradient d i u e) := by
  obtain ⟨φ, hφ, _, hzero, ⟨D, hD⟩, hext⟩ := scalar_positive_power_extension a B q ha hB
  obtain ⟨v, hv, hd⟩ := scalarH1_compose_exists_of_deriv_bound d φ hφ hzero hD u
  refine ⟨v, ?_, fun i => ?_⟩
  · filter_upwards [hv, hu] with e he hr
    exact he.trans (hext _ hr).1
  · filter_upwards [hd i, hu] with e he hr
    rw [he, (hext _ hr).2]

section CompactRange

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

theorem scalar_positive_continuous_range (f : X → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) :
    ∃ a B : ℝ, 0 < a ∧ 0 ≤ B ∧ ∀ x, f x ∈ Icc a B := by
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨x₁, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨f x₀, f x₁, hpos x₀, (hpos x₁).le,
    fun x => ⟨hmin (mem_univ x), hmax (mem_univ x)⟩⟩

end CompactRange

variable [CompactSpace M] [Nonempty M]

theorem scalarH1_power_of_positive_continuous (d : ParallelMetricData g μ)
    (u : scalarH1 d) (f : M → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hrep : (scalarH1Value d u : FrameBundle g → ℝ) =ᵐ[μ] fun e => f e.base)
    (q : ℝ) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ] (fun e => (f e.base) ^ q) ∧
      ∀ i, (scalarH1Gradient d i v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => q * (f e.base) ^ (q - 1) * scalarH1Gradient d i u e) := by
  obtain ⟨a, B, ha, hB, hr⟩ := scalar_positive_continuous_range f hf hpos
  have hu : ∀ᵐ e ∂μ, scalarH1Value d u e ∈ Icc a B := by
    filter_upwards [hrep] with e he
    rw [he]
    exact hr e.base
  obtain ⟨v, hv, hd⟩ := scalarH1_power_of_positive_range d u q a B ha hB hu
  refine ⟨v, ?_, fun i => ?_⟩
  · filter_upwards [hv, hrep] with e he hr
    simpa only [hr] using he
  · filter_upwards [hd i, hrep] with e he hr
    simpa only [hr] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Barrier comparison for the actual H1 solution with a continuous base
representative. Only the barrier is required to be smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance weakBarrier_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem scalarH1_barrier_comparison (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (F : ScalarL2 g (canonicalFrameMeasure g o))
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base)
    (b : SmoothScalar (M := M)) {ε c₀ : ℝ} (hε : 0 < ε) (hc₀ : 0 ≤ c₀)
    (hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, F e ≤ c₀ * f e.base)
    (hb : ∀ e : FrameBundle g, f e.base < ε * b.val e.base →
      c₀ * b.val e.base < scalarLaplacian g b.val e) :
    ∀ x, ε * b.val x ≤ f x := by
  let v := u - ε • smoothScalarToH1 d b
  let G := F - ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b
  have hv : scalarH1Value d v =ᵐ[canonicalFrameMeasure g o]
      fun e => f e.base - ε * b.val e.base := by
    dsimp only [v]
    rw [map_sub, map_smul, scalarH1Value_smooth]
    filter_upwards [Lp.coeFn_sub (scalarH1Value d u) (ε • smoothScalarValueL2 g
      (canonicalFrameMeasure g o) b),
      Lp.coeFn_smul ε (smoothScalarValueL2 g (canonicalFrameMeasure g o) b),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
        (smoothScalarValue g b), hrep] with e he hsm hbe hue
    change (ε • smoothScalarValueL2 g (canonicalFrameMeasure g o) b) e =
      ε * smoothScalarValueL2 g (canonicalFrameMeasure g o) b e at hsm
    change smoothScalarValueL2 g (canonicalFrameMeasure g o) b e = b.val e.base at hbe
    rw [he]
    change scalarH1Value d u e - (ε • smoothScalarValueL2 g
      (canonicalFrameMeasure g o) b) e = _
    rw [hsm, hbe, hue]
  have hG : G =ᵐ[canonicalFrameMeasure g o]
      fun e => F e - ε * scalarLaplacian g b.val e := by
    filter_upwards [Lp.coeFn_sub F (ε • smoothScalarLaplacianL2
      (μ := canonicalFrameMeasure g o) b),
      Lp.coeFn_smul ε (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b),
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
        (smoothScalarLaplacianField g b)] with e he hsm hbe
    change (F - ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b) e = _
    change (ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b) e =
      ε * smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b e at hsm
    change smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b e =
      scalarLaplacian g b.val e at hbe
    rw [he]
    change F e - (ε • smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) b) e = _
    rw [hsm, hbe]
  have hn : ∀ᵐ e ∂canonicalFrameMeasure g o, scalarH1Value d v e < 0 → G e < 0 := by
    filter_upwards [hv, hG, hsource] with e hve hGe he
    rw [hve, hGe]
    intro hn
    have hbar := mul_lt_mul_of_pos_left (hb e (sub_neg.mp hn)) hε
    have hcn := mul_nonpos_of_nonneg_of_nonpos hc₀ hn.le
    nlinarith
  have hae := scalarH1_nonneg_of_negative_source d v G
    (fun z => scalarH1_sub_smooth_weak_equation d u F heq b ε z) hn
  have ha : ∀ᵐ e ∂canonicalFrameMeasure g o, 0 ≤ f e.base - ε * b.val e.base := by
    filter_upwards [hae, hv] with e he hv
    rwa [hv] at he
  have hpoint := scalar_continuous_base_nonneg_of_frame_ae g o
    (fun x => f x - ε * b.val x) (hf.sub (continuous_const.mul b.property.continuous)) ha
  intro x
  exact sub_nonneg.mp (hpoint x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The traced second covariant derivative is an actual smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormTraceLinear : CovariantCoordinates 4 →ₗ[ℝ] CovariantCoordinates 2 where
  toFun T v := ∑ i, T (Fin.cons i (Fin.cons i v))
  map_add' T U := by funext v; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r T := by funext v; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

def twoFormTraceExtract : CovariantCoordinates 4 →L[ℝ] TwoFormFour :=
  ((twoFormExtractLinear.comp twoTensorMatrixLinear).comp twoFormTraceLinear).toContinuousLinearMap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormRoughTraceField (o : FrameOrientation g) (u : M → TwoFormFour) : M → TwoFormFour :=
  fun x => twoFormExtract (twoTensorMatrixLinear (twoFormFramedRoughTrace o u ⟨x, o.frame x⟩))

theorem TwoFormSmooth.secondGram_contDiffAt {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun w => frameTensor (chartGramMatrix g c S w)
      (twoFormSecondCovariantCoordinates o u c w)) z := by
  apply contDiffAt_pi.mpr
  intro a
  unfold frameTensor
  exact ContDiffAt.sum (fun b _ =>
    (contDiffAt_prod (fun k _ => chartGramMatrix_contDiffAt g c S z hz (b k) (a k))).mul
      (hu.secondCovariant_contDiffAt c z hz b))

theorem TwoFormSmooth.framedSecond_chart {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    twoFormFramedSecondDerivative o u (chartGramSection g c S hS z) =
      frameTensor (chartGramMatrix g c S z) (twoFormSecondCovariantCoordinates o u c z) := by
  have hc := hu.secondCovariant_transition c ((chartAt FourSpace c).symm z) z z.property
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  rw [hc, ← frameTensor_mul]
  rfl

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem TwoFormSmooth.roughTraceField_frame (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) :
    twoFormFrameValue o (twoFormRoughTraceField o u) e =
      twoFormExtract (twoTensorMatrixLinear (twoFormFramedRoughTrace o u e)) := by
  let T := twoFormFramedRoughTrace o u ⟨e.base, o.frame e.base⟩
  have hT : twoFormTensor (twoFormExtract (twoTensorMatrixLinear T)) = T :=
    twoFormTensor_extract T (hu.roughTrace_skew hRic _)
  apply twoFormTensor_injective
  change twoFormTensor (twoFormFrameAction ((o.frame e.base).changeMatrix e.frame)
    (twoFormExtract (twoTensorMatrixLinear T))) = _
  rw [twoFormTensor_frameAction, hT]
  rw [twoFormTensor_extract _ (hu.roughTrace_skew hRic e)]
  exact (twoFormFramedRoughTrace_change u (o.frame e.base) e.frame).symm

theorem TwoFormSmooth.roughTrace (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : TwoFormSmooth o (twoFormRoughTraceField o u) := by
  intro c S hS U _hU hUt _hp
  let F := fun z : FourSpace => twoFormTraceExtract
    (frameTensor (chartGramMatrix g c S z) (twoFormSecondCovariantCoordinates o u c z))
  have hF : ContDiffOn ℝ ∞ F U := by
    intro z hz
    exact (twoFormTraceExtract.contDiff.comp_contDiffAt z
      (hu.secondGram_contDiffAt c S z (hUt hz))).contDiffWithinAt
  apply hF.congr
  intro z hz
  rw [twoFormChartValue, dite_eq_left (hUt hz), hu.roughTraceField_frame hRic]
  have he := hu.framedSecond_chart c S hS ⟨z, hUt hz⟩
  exact congrArg twoFormTraceExtract he

def smoothTwoFormRoughTrace (hRic : RicciThree g) (u : smoothTwoForms o) : smoothTwoForms o :=
  ⟨twoFormRoughTraceField o u.val, u.property.roughTrace hRic⟩

theorem TwoFormSmooth.framedValue_roughTrace (hRic : RicciThree g)
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (e : FrameBundle g) :
    twoFormFramedValue o (twoFormRoughTraceField o u) e =
      twoFormFramedRoughTrace o u e := by
  rw [twoFormFramedValue_eq, hu.roughTraceField_frame hRic,
    twoFormTensor_extract _ (hu.roughTrace_skew hRic e)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated Weitzenböck identity for the actual smooth two-forms
on a closed Einstein four-manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem smoothTwoForm_frame_inner_integrable (u v : smoothTwoForms o) :
    Integrable (fun e => inner ℝ (twoFormFrameValue o u.val e)
      (twoFormFrameValue o v.val e)) (canonicalFrameMeasure g o) := by
  have hc : Continuous (fun e => (1 / 2 : ℝ) * frameTensorPairing
      (twoFormFramedValue o u.val e) (twoFormFramedValue o v.val e)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro a _
    exact ((continuous_apply a).comp u.property.continuous_framedValue).mul
      ((continuous_apply a).comp v.property.continuous_framedValue)
  have he : (fun e => inner ℝ (twoFormFrameValue o u.val e) (twoFormFrameValue o v.val e)) =
      fun e => (1 / 2 : ℝ) * frameTensorPairing
        (twoFormFramedValue o u.val e) (twoFormFramedValue o v.val e) := by
    funext e
    rw [twoFormFramedValue_eq, twoFormFramedValue_eq, twoFormTensor_pairing]
    ring
  rw [he]
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem smoothTwoForm_Weitzenbock (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = smoothTwoFormCovariantEnergy u u +
      6 * smoothTwoFormL2Inner u u - 2 * smoothTwoFormL2Inner (smoothTwoFormCurvature u) u := by
  let μ := canonicalFrameMeasure g o
  let F := fun i j k (e : FrameBundle g) => twoFormFramedValue o u.val e ![i,k] *
    tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
      (twoFormFramedValue o u.val e) ![j,k]
  have hi (a : Fin 2 → Fin 4) (b : Fin 4 → Fin 4) :
      Integrable (fun e => twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o u.val e b) μ :=
    (((continuous_apply a).comp u.property.continuous_framedValue).mul
      ((continuous_apply b).comp u.property.continuous_framedSecondDerivative)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hF (i j k : Fin 4) : Integrable (F i j k) μ := by
    apply ((hi ![i,k] ![i,j,j,k]).sub (hi ![i,k] ![j,i,j,k])).neg.congr
    filter_upwards [] with e
    have hc := u.property.framed_commutator e i j ![j,k]
    change twoFormFramedSecondDerivative o u.val e ![i,j,j,k] -
      twoFormFramedSecondDerivative o u.val e ![j,i,j,k] = _ at hc
    dsimp [F]
    rw [← mul_sub, hc]
    ring
  have hC := smoothTwoForm_cross_curvature hRic u u
  change _ - _ = ∑ i, ∑ j, ∑ k, ∫ e, F i j k e ∂μ at hC
  rw [← integral_frame_sum_three μ F hF] at hC
  have h0 := smoothTwoForm_frame_inner_integrable u u
  have h1 := smoothTwoForm_frame_inner_integrable (smoothTwoFormCurvature u) u
  change Integrable (fun e => inner ℝ
    (twoFormFrameValue o (twoFormCurvatureField o u.val) e)
    (twoFormFrameValue o u.val e)) μ at h1
  simp_rw [twoFormCurvatureField_frame] at h1
  have hf : (fun e => ∑ i, ∑ j, ∑ k, F i j k e) = fun e =>
      6 * inner ℝ (twoFormFrameValue o u.val e) (twoFormFrameValue o u.val e) -
        2 * inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
          (twoFormFrameValue o u.val e)) (twoFormFrameValue o u.val e) := by
    funext e
    exact twoFormMetricCurvature_slot_sum hRic u.val e
  rw [hf, integral_sub (h0.const_mul 6) (h1.const_mul 2), integral_const_mul,
    integral_const_mul, ← smoothTwoFormL2Inner_eq_frame u u,
    ← smoothTwoFormCurvatureInner_eq_frame u u] at hC
  rw [smoothTwoFormDeRhamEnergy_cross hRic u]
  linarith only [hC]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential endpoint is jointly C1 in a nonzero normal
vector and its initial coordinate frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatRadialCotangentState_contDiffAt (g : SmoothMetric M) (c : M)
    (z : HeatRadialFrameSpace) (hz : z.2.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => heatRadialCotangentState g c w.1 w.2) z := by
  apply contDiffAt_snd.fst.prodMk
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.contDiff.contDiffAt.comp
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => ∑ j : Fin 4,
    metricInChart g c w.2.1 i j * ∑ k : Fin 4, w.2.2 j k * w.1 k) z
  apply ContDiffAt.sum
  intro j _
  apply ((metricInChart_contDiffAt g c z.2.1 hz i j).of_le (by simp)).comp z
    contDiffAt_snd.fst |>.mul
  apply ContDiffAt.sum
  intro k _
  have hE : ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => w.2.2 j k) z := by fun_prop
  have hV : ContDiffAt ℝ 1 (fun w : HeatRadialFrameSpace => w.1 k) z :=
    by fun_prop
  exact hE.mul hV

variable [T2Space M] [CompactSpace M]

def exponentialFamilyCoordinates (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (z : HeatRadialFrameSpace) : FourSpace :=
  (radialCoordinateFlow g o c d 1 (heatRadialCotangentState g c z.1 z.2)).1

theorem exponentialFamilyCoordinates_frame (g : SmoothMetric M)
    (o : FrameOrientation g) (c d : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) (hv : v ≠ 0) :
    exponentialFamilyCoordinates g o c d (v, frameCoordinateState g c e) =
      chartAt FourSpace d (frameExponential g o e v) := by
  unfold exponentialFamilyCoordinates
  rw [heatRadialCotangentState_frame g c e he]
  exact radialCoordinateFlow_frame_endpoint g o c d e he v hv

theorem exponentialFamilyCoordinates_contDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c d : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) (hv : v ≠ 0)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 1 (exponentialFamilyCoordinates g o c d) (v, frameCoordinateState g c e) := by
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  let p : PositiveRadius × UnitTangentBundle g := (r, unitTangentTurn e q)
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c p =
      heatRadialCotangentState g c v (frameCoordinateState g c e) := by
    rw [heatRadialCotangentState_frame g c e he]
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  have hout : (unitTangentRadialFlow g o 1 p).2.base = frameExponential g o e v := by
    change (unitTangentFlowMap g o (r.val * 1) (unitTangentTurn e q)).base = _
    rw [mul_one, ← hvr, frameExponential_radial]
    rfl
  have hcore := radialFlowContDiffAt_all_time g o 1 p c d he (by rwa [hout])
  rw [hstate] at hcore
  exact (hcore.comp (v, frameCoordinateState g c e)
    (heatRadialCotangentState_contDiffAt g c _ ((chartAt FourSpace c).map_source he))).fst

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed exponential is a C1 manifold map and satisfies the
radial Gauss identity, as a consequence of its actual differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_contMDiff (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : ContMDiff I4 I4 1 (frameExponential g o e) := by
  intro v
  let c := frameExponential g o e v
  have hc : frameExponential g o e v ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have hchart := frameExponential_chart_contDiffAt g o c e v hc
  have hinv : ContMDiffAt I4 I4 1 (chartAt FourSpace c).symm
      (chartAt FourSpace c (frameExponential g o e v)) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      ((chartAt FourSpace c).map_source hc)
  have h := hinv.comp v hchart.contMDiffAt
  apply h.congr_of_eventuallyEq
  have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds hc)
  filter_upwards [hnear] with w hw
  exact ((chartAt FourSpace c).left_inv hw).symm

theorem frameExponential_first_ray (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    frameExponential g o e (t • coordinateVector 0) = (parallelFrameFlowMap g 0 t e).base := by
  have hu : unitTangentTurn e firstDirection = unitTangentOfFrame e := by
    apply unitTangent_ext (u := unitTangentTurn e firstDirection) (v := unitTangentOfFrame e) rfl
    exact (e.frame.turn_first firstDirection).trans (e.frame.map_coordinateVector 0)
  have h := frameExponential_radial g o e firstDirection ⟨t, ht⟩
  change frameExponential g o e (t • coordinateVector 0) =
    unitGeodesic g o (unitTangentTurn e firstDirection) t at h
  rw [hu, unitGeodesic, unitTangentFlowMap_of_frame g o t e he] at h
  exact h

private theorem normalized_frame_pairing (E G : Mat4) (hE : Eᵀ * G * E = 1)
    (u v : Fin 4 → ℝ) : (E *ᵥ u) ⬝ᵥ (G *ᵥ (E *ᵥ v)) = u ⬝ᵥ v := by
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec E u (G *ᵥ (E *ᵥ v))]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]

/-- In output coordinates, the exponential differential has radial inner
product exactly equal to the initial radial component. -/
theorem frameExponential_chart_gauss (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source)
    (w : FourSpace) :
    (fun i => frameChartMatrix g d (parallelFrameFlowMap g 0 t e) i 0) ⬝ᵥ
      (metricInChart g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *ᵥ
        WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
          (frameExponential g o e v)) (t • coordinateVector 0) w)) = w 0 := by
  let E := frameChartMatrix g d (parallelFrameFlowMap g 0 t e)
  let G := metricInChart g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base)
  let B := jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)
  have hE : Eᵀ * G * E = 1 := frameChartMatrix_normalizes g d (parallelFrameFlowMap g 0 t e) hd
  rw [(frameExponential_hasFDerivAt g o hRic d e he t ht hd).fderiv]
  change (fun i => E i 0) ⬝ᵥ (G *ᵥ ((E * B) *ᵥ WithLp.ofLp w)) = w 0
  have hcol : (fun i => E i 0) = E *ᵥ Pi.single 0 1 := (Matrix.mulVec_single_one E 0).symm
  rw [hcol, ← Matrix.mulVec_mulVec, normalized_frame_pairing E G hE]
  change (Pi.single 0 1 : Fin 4 → ℝ) ⬝ᵥ (B *ᵥ WithLp.ofLp w) = w 0
  rw [show B = jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t) from rfl,
    jacobiBlockMatrix_mulVec]
  simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-frame covariance of the actual Jacobi solution, and hence of
its truncated determinant.  Both orientations of a normal frame are allowed. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

private theorem normal_conjugate_mul (V A B : NormalMatrix) (hV : V * Vᵀ = 1) :
    (Vᵀ * A * V) * (Vᵀ * B * V) = Vᵀ * (A * B) * V := by
  calc
    _ = Vᵀ * A * (V * Vᵀ) * B * V := by noncomm_ring
    _ = _ := by rw [hV]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem matrixJacobi_conjugate {R S : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (f : MatrixJacobiSolution S)
    (V : NormalMatrix) (hV : Vᵀ * V = 1)
    (hS : ∀ t, S t = Vᵀ * R t * V)
    (K : ℝ≥0) (hK : ∀ t, ‖S t‖ ≤ K) (t : ℝ) :
    f.J t = Vᵀ * d.J t * V ∧ f.V t = Vᵀ * d.V t * V := by
  let γ : ℝ → JacobiState := fun s => (f.J s, f.V s)
  let η : ℝ → JacobiState := fun s => (Vᵀ * d.J s * V, Vᵀ * d.V s * V)
  have hγ (s : ℝ) : HasDerivAt γ (jacobiStateOperator (S s) (γ s)) s :=
    (f.position_derivative s).prodMk (f.velocity_derivative s)
  have hη (s : ℝ) : HasDerivAt η (jacobiStateOperator (S s) (η s)) s := by
    have hp := ((d.position_derivative s).const_mul Vᵀ).mul_const V
    have hv := ((d.velocity_derivative s).const_mul Vᵀ).mul_const V
    have heq : Vᵀ * (-(R s * d.J s)) * V =
        -(S s * (Vᵀ * d.J s * V)) := by
      rw [hS s, normal_conjugate_mul V (R s) (d.J s) (mul_eq_one_comm.mp hV)]
      simp only [Matrix.mul_neg, Matrix.neg_mul]
    rw [heq] at hv
    exact hp.prodMk hv
  have hbound (s : ℝ) : ‖jacobiStateOperator (S s)‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  have hinit : γ 0 = η 0 := by
    simp only [γ, η, f.initial_position, f.initial_velocity, d.initial_position,
      d.initial_velocity, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, hV]
  have h := congrFun (global_linear_solution_unique _ (1 + K) hbound hγ hη hinit) t
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem normal_conjugate_det (V A : NormalMatrix) (hV : Vᵀ * V = 1) :
    (Vᵀ * A * V).det = A.det := by
  have hdet := congrArg Matrix.det hV
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    V.det * A.det * V.det = (V.det * V.det) * A.det := by ring
    _ = A.det := by rw [hdet, one_mul]

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped Manifold ContDiff _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem orthogonal_first_row (Q : OrthogonalFour)
    (hQ : ∀ i, Q.val i 0 = (1 : Mat4) i 0) (j : Fin 4) :
    Q.val 0 j = if (0 : Fin 4) = j then 1 else 0 := by
  have h := congrArg (fun A : Mat4 => A 0 j) Q.property
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, hQ, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

private theorem frameJacobi_normalRestriction {g : SmoothMetric M} (e : FrameBundle g) :
    1 + frameCurvatureField g e = normalRestriction e.frame.matrix
      (directionalCurvatureMatrix (curvatureCoordinates g e.base
        (chartAt FourSpace e.base e.base)) (fun a => e.frame.matrix a 0)) := by
  cases e with
  | mk c E =>
    rw [frameCurvatureField_normalRestriction]
    abel

theorem frameJacobi_rotate_normal (g : SmoothMetric M) (e : FrameBundle g)
    (Q : OrthogonalFour) (hQ : ∀ i, Q.val i 0 = (1 : Mat4) i 0) :
    1 + frameCurvatureField g (e.rotate Q) =
      (normalChange Q.val)ᵀ * (1 + frameCurvatureField g e) * normalChange Q.val := by
  have hcol : (fun i => (e.frame.matrix * Q.val) i 0) =
      (fun i => e.frame.matrix i 0) := by
    funext i
    simp only [Matrix.mul_apply, hQ, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [frameJacobi_normalRestriction, frameJacobi_normalRestriction]
  change normalRestriction (e.frame.matrix * Q.val)
      (directionalCurvatureMatrix (curvatureCoordinates g e.base
        (chartAt FourSpace e.base e.base)) (fun i => (e.frame.matrix * Q.val) i 0)) = _
  rw [hcol]
  exact normalRestriction_conjugate _ _ _ (orthogonal_first_row Q hQ)

variable [T3Space M] [CompactSpace M]

theorem actualJacobi_rotate_normal (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (Q : OrthogonalFour)
    (hQ : ∀ i, Q.val i 0 = (1 : Mat4) i 0) (t : ℝ) :
    (actualJacobiSolution g hRic (e.rotate Q)).J t =
        (normalChange Q.val)ᵀ * (actualJacobiSolution g hRic e).J t * normalChange Q.val ∧
    (actualJacobiSolution g hRic (e.rotate Q)).V t =
        (normalChange Q.val)ᵀ * (actualJacobiSolution g hRic e).V t * normalChange Q.val := by
  have hV : (normalChange Q.val)ᵀ * normalChange Q.val = 1 :=
    normalChange_orthogonal Q.val Q.property (fun i => by simpa only [Matrix.one_apply] using hQ i)
  have hR (s : ℝ) : actualJacobiCurvature g (e.rotate Q) s =
      (normalChange Q.val)ᵀ * actualJacobiCurvature g e s * normalChange Q.val := by
    unfold actualJacobiCurvature
    rw [← parallelFrameFlowMap_rotate g 0 Q hQ s e]
    exact frameJacobi_rotate_normal g _ Q hQ
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  exact matrixJacobi_conjugate (actualJacobiSolution g hRic e)
    (actualJacobiSolution g hRic (e.rotate Q)) (normalChange Q.val) hV hR K (hK _) t

theorem actualJacobi_det_rotate_normal (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (Q : OrthogonalFour)
    (hQ : ∀ i, Q.val i 0 = (1 : Mat4) i 0) (t : ℝ) :
    ((actualJacobiSolution g hRic (e.rotate Q)).J t).det =
      ((actualJacobiSolution g hRic e).J t).det := by
  rw [(actualJacobi_rotate_normal g hRic e Q hQ t).1]
  exact normal_conjugate_det _ _ (normalChange_orthogonal Q.val Q.property
    (fun i => by simpa only [Matrix.one_apply] using hQ i))

theorem actualJacobi_truncatedDensity_rotate_normal (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (Q : OrthogonalFour)
    (hQ : ∀ i, Q.val i 0 = (1 : Mat4) i 0) (t : ℝ) :
    (actualRegularJacobi g hRic (e.rotate Q) t).truncatedDensity =
      (actualRegularJacobi g hRic e t).truncatedDensity := by
  classical
  simp only [RegularJacobi.truncatedDensity, actualRegularJacobi_J,
    Matrix.isUnit_iff_isUnit_det, actualJacobi_det_rotate_normal g hRic e Q hQ]

omit [T3Space M] [CompactSpace M] in
private theorem frame_eq_of_matrix_eq {g : SmoothMetric M} {c : M}
    (e f : OrthonormalFrame g c) (h : e.matrix = f.matrix) : e = f := by
  cases e with
  | mk E hE =>
    cases f with
    | mk F hF =>
      dsimp only at h
      subst F
      rfl

omit [T3Space M] [CompactSpace M] in
private theorem frame_rotate_change {g : SmoothMetric M} {c : M}
    (e f : OrthonormalFrame g c) :
    (FrameBundle.mk c e).rotate ⟨e.changeMatrix f, e.changeMatrix_orthogonal f⟩ =
      (FrameBundle.mk c f) := by
  apply congrArg (FrameBundle.mk c)
  exact frame_eq_of_matrix_eq _ _ (e.mul_changeMatrix f)

theorem actualJacobi_truncatedDensity_directionInvariant (g : SmoothMetric M)
    (hRic : RicciThree g) (t : ℝ) :
    DirectionInvariant (fun e => (actualRegularJacobi g hRic e t).truncatedDensity) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ hbase hfirst
  dsimp only at hbase
  subst d
  let Q : OrthogonalFour := ⟨e.changeMatrix f, e.changeMatrix_orthogonal f⟩
  have hQ (i : Fin 4) : Q.val i 0 = (1 : Mat4) i 0 := by
    simpa only [Q, Matrix.one_apply] using e.changeMatrix_first f hfirst i
  have h := actualJacobi_truncatedDensity_rotate_normal g hRic (FrameBundle.mk c e) Q hQ t
  rw [frame_rotate_change] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual normal Jacobi equation.
The quadratic term uses the Euclidean coordinate pairing. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def normalIndexDensity (R : NormalMatrix) (y z : Fin 3 → ℝ) : ℝ :=
  z ⬝ᵥ z - (R *ᵥ y) ⬝ᵥ y

theorem normalIndexDensity_eq_euclidean (R : NormalMatrix) (y z : Fin 3 → ℝ) :
    normalIndexDensity R y z = ‖WithLp.toLp 2 z‖ ^ 2 - (R *ᵥ y) ⬝ᵥ y := by
  rw [normalIndexDensity, EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, pow_two]

private def mulVecRightLinear (w : Fin 3 → ℝ) :
    NormalMatrix →ₗ[ℝ] (Fin 3 → ℝ) :=
  (Matrix.mulVecBilin ℝ ℝ).flip w

private theorem hasDerivAt_mulVec_right (A : ℝ → NormalMatrix) (A' : NormalMatrix)
    (w : Fin 3 → ℝ) (s : ℝ) (hA : HasDerivAt A A' s) :
    HasDerivAt (fun r => A r *ᵥ w) (A' *ᵥ w) s :=
  (mulVecRightLinear w).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hA

theorem MatrixJacobiSolution.field_position_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => d.J r *ᵥ w) (d.V s *ᵥ w) s :=
  hasDerivAt_mulVec_right d.J (d.V s) w s (d.position_derivative s)

theorem MatrixJacobiSolution.field_velocity_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (fun r => d.V r *ᵥ w) (-(R s *ᵥ (d.J s *ᵥ w))) s := by
  simpa only [Matrix.neg_mulVec, Matrix.mulVec_mulVec] using
    hasDerivAt_mulVec_right d.V (-(R s * d.J s)) w s (d.velocity_derivative s)

theorem normalJacobi_pairing_hasDerivAt (R : NormalMatrix)
    (y z : ℝ → Fin 3 → ℝ) (s : ℝ)
    (hy : HasDerivAt y (z s) s) (hz : HasDerivAt z (-(R *ᵥ y s)) s) :
    HasDerivAt (fun r => y r ⬝ᵥ z r) (normalIndexDensity R (y s) (z s)) s := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hy i).mul (hasDerivAt_pi.mp hz i))
  have heq : (∑ i, (z s i * z s i + y s i * (-(R *ᵥ y s)) i)) =
      normalIndexDensity R (y s) (z s) := by
    rw [Finset.sum_add_distrib]
    change z s ⬝ᵥ z s + y s ⬝ᵥ (-(R *ᵥ y s)) =
      z s ⬝ᵥ z s - (R *ᵥ y s) ⬝ᵥ y s
    rw [dotProduct_neg, dotProduct_comm (y s) (R *ᵥ y s)]
    simp only [sub_eq_add_neg]
  rw [heq] at hd
  simpa only [dotProduct, Pi.mul_apply] using hd

theorem MatrixJacobiSolution.index_integral_eq_boundary {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ) (a b : ℝ) :
    (∫ s in a..b, normalIndexDensity (R s) (d.J s *ᵥ w) (d.V s *ᵥ w)) =
      (d.J b *ᵥ w) ⬝ᵥ (d.V b *ᵥ w) - (d.J a *ᵥ w) ⬝ᵥ (d.V a *ᵥ w) := by
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    (mulVecRightLinear w).toContinuousLinearMap.continuous.comp d.continuous_J
  have hz : Continuous (fun s => d.V s *ᵥ w) :=
    (mulVecRightLinear w).toContinuousLinearMap.continuous.comp d.continuous_V
  have hr : Continuous (fun s => R s *ᵥ (d.J s *ᵥ w)) := by
    have hh := (mulVecRightLinear w).toContinuousLinearMap.continuous.comp
      (hR.mul d.continuous_J)
    change Continuous (fun s => (R s * d.J s) *ᵥ w) at hh
    simpa only [Matrix.mulVec_mulVec] using hh
  have hcont : Continuous (fun s => normalIndexDensity (R s) (d.J s *ᵥ w) (d.V s *ᵥ w)) := by
    unfold normalIndexDensity dotProduct
    fun_prop
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hcont.intervalIntegrable a b)
  intro s _
  exact normalJacobi_pairing_hasDerivAt (R s) _ _ s
    (d.field_position_hasDerivAt w s) (d.field_velocity_hasDerivAt w s)

theorem MatrixJacobiSolution.index_integral_zero_of_kernel {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ) (c : ℝ)
    (hc : d.J c *ᵥ w = 0) :
    (∫ s in (0 : ℝ)..c, normalIndexDensity (R s) (d.J s *ᵥ w) (d.V s *ᵥ w)) = 0 := by
  rw [d.index_integral_eq_boundary hR w 0 c, hc, d.initial_position]
  simp

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_index_integral_eq_boundary (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (w : Fin 3 → ℝ) (a b : ℝ) :
    (∫ s in a..b, normalIndexDensity (actualJacobiCurvature g e s)
      ((actualJacobiSolution g hRic e).J s *ᵥ w)
      ((actualJacobiSolution g hRic e).V s *ᵥ w)) =
      ((actualJacobiSolution g hRic e).J b *ᵥ w) ⬝ᵥ
        ((actualJacobiSolution g hRic e).V b *ᵥ w) -
      ((actualJacobiSolution g hRic e).J a *ᵥ w) ⬝ᵥ
        ((actualJacobiSolution g hRic e).V a *ᵥ w) :=
  (actualJacobiSolution g hRic e).index_integral_eq_boundary
    (actualJacobiCurvature_continuous g hRic e) w a b

theorem exists_actualFirstConjugate_zero_index (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      (actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e) *ᵥ w = 0 ∧
      (actualJacobiSolution g hRic e).V (actualFirstConjugateTime g hRic e) *ᵥ w ≠ 0 ∧
      (∫ s in (0 : ℝ)..actualFirstConjugateTime g hRic e,
        normalIndexDensity (actualJacobiCurvature g e s)
          ((actualJacobiSolution g hRic e).J s *ᵥ w)
          ((actualJacobiSolution g hRic e).V s *ᵥ w)) = 0 := by
  obtain ⟨w, hw, hJ, hV⟩ := exists_actualFirstConjugate_vector g hRic e
  exact ⟨w, hw, hJ, hV, (actualJacobiSolution g hRic e).index_integral_zero_of_kernel
    (actualJacobiCurvature_continuous g hRic e) w _ hJ⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common chart interval works for every direction and every nearby
initial frame. Compactness is used only for the unit direction sphere. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem unitGeodesic_common_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ δ > (0 : ℝ),
      ∀ e' ∈ U, ∀ q : Directions, ∀ s ∈ Ioo (-δ) δ,
        unitGeodesic g o (unitTangentTurn e' q) s ∈ (chartAt FourSpace c).source := by
  let b : (ℝ × FrameBundle g) × Directions → M :=
    fun z => unitGeodesic g o (unitTangentTurn z.1.2 z.2) z.1.1
  have hb : Continuous b := by
    have harg : Continuous (fun z : (ℝ × FrameBundle g) × Directions =>
        (z.1.1, unitTangentTurn z.1.2 z.2)) :=
      continuous_fst.fst.prodMk
        (continuous_unitTangentTurn.comp (continuous_fst.snd.prodMk continuous_snd))
    exact (continuous_unitTangentBase g).comp ((unitTangentFlowMap_continuous g o).comp harg)
  have hz : ({((0 : ℝ), e)} : Set (ℝ × FrameBundle g)) ×ˢ (univ : Set Directions) ⊆
      b ⁻¹' (chartAt FourSpace c).source := by
    rintro ⟨p, q⟩ ⟨hp, _⟩
    have hp' : p = (0, e) := hp
    subst p
    simpa [b, unitGeodesic_turn_zero] using he
  obtain ⟨T, V, hT, _, h0, hV, hTV⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_univ ((chartAt FourSpace c).open_source.preimage hb) hz
  have ht : T ∈ 𝓝 ((0 : ℝ), e) := hT.mem_nhds (h0 rfl)
  obtain ⟨I, U, hI, h0I, hU, heU, hIU⟩ := mem_nhds_prod_iff'.mp ht
  obtain ⟨δ, hδ, hδI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds h0I)
  refine ⟨U, hU, heU, δ, hδ, ?_⟩
  intro e' he' q s hs
  have hsI : s ∈ I := hδI (by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr hs)
  exact hTV (show ((s, e'), q) ∈ T ×ˢ V from
    ⟨hIU (show (s, e') ∈ I ×ˢ U from ⟨hsI, he'⟩), hV (mem_univ q)⟩)

theorem frameExponential_common_source (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
      ∀ e' ∈ U, ∀ v ∈ ball (0 : FourSpace) r,
        frameExponential g o e' v ∈ (chartAt FourSpace c).source := by
  obtain ⟨U, hU, heU, r, hr, hchart⟩ := unitGeodesic_common_chart g o c e he
  refine ⟨U, hU, heU, r, hr, ?_⟩
  intro e' he' v hv
  have hvnorm : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hv
  by_cases hv0 : v = 0
  · subst v
    rw [frameExponential_zero]
    have hh := hchart e' he' firstDirection 0 (by constructor <;> linarith)
    simpa only [unitGeodesic_turn_zero] using hh
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv0⟩
    let q := (euclideanPolarHomeomorph w).1
    let ρ := (euclideanPolarHomeomorph w).2
    have hρ : 0 < ρ.val := ρ.property
    have hρnorm : ρ.val = ‖v‖ := homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    have hvr : ρ.val • q.val = v := congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
    have hh := frameExponential_radial g o e' q ρ
    rw [hvr] at hh
    rw [hh]
    exact hchart e' he' q ρ.val ⟨by linarith, hρnorm ▸ hvnorm⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Restricting the same kinetic flow to nearby initial points preserves
its time interval and every variational identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}

def KineticLocalFlow.recenter (K : KineticLocalFlow g c p)
    (q : CotangentCoordinates) (hq : q ∈ ball p K.radius) :
    KineticLocalFlow g c q := by
  let r := (K.radius - dist q p) / 2
  have hr : 0 < r := half_pos (sub_pos.mpr hq)
  have hsub : ball q r ⊆ ball p K.radius :=
    ball_subset_ball' (by dsimp [r]; linarith [show dist q p < K.radius from hq])
  exact {
    radius := r
    radius_pos := hr
    time := K.time
    time_pos := K.time_pos
    map := K.map
    variation := K.variation
    continuous_map := K.continuous_map.mono (fun z hz => ⟨hsub hz.1, hz.2⟩)
    continuous_variation := K.continuous_variation.mono (fun z hz => ⟨hsub hz.1, hz.2⟩)
    initial := fun z hz => K.initial z (hsub hz)
    initial_variation := fun z hz => K.initial_variation z (hsub hz)
    inside := fun z hz t ht => K.inside z (hsub hz) t ht
    time_derivative := fun z hz t ht => K.time_derivative z (hsub hz) t ht
    variation_derivative := fun z hz t ht => K.variation_derivative z (hsub hz) t ht
    joint_derivative := fun z hz t ht => K.joint_derivative z (hsub hz) t ht }

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth orthonormal frames over the actual normal exponential
chart, constructed by radial parallel transport through zero velocity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def HeatRadialFrameFlow.restrictTime {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p) (δ : ℝ)
    (hδ : 0 < δ) (hle : δ ≤ F.time) : HeatRadialFrameFlow g c p where
  radius := F.radius
  radius_pos := F.radius_pos
  time := δ
  time_pos := hδ
  map := F.map
  continuous := F.continuous.mono (fun q hq => ⟨hq.1,
    ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩)
  initial := F.initial
  in_chart := fun q hq t ht => F.in_chart q hq t
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  derivative := fun q hq t ht => F.derivative q hq t
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  regular := F.regular

variable [T2Space M] [CompactSpace M]

theorem exists_heatRadialNormalFrame_flow (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (n : ℕ) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e), ∃ t > (0 : ℝ),
      t ∈ Ioo (-F.time) F.time ∧ ContDiffAt ℝ n (heatRadialFrameEndpoint F t) 0 ∧
      (fun v => (heatRadialFrameEndpoint F t v).1) =ᶠ[𝓝 0]
        (fun v => chartAt FourSpace c (frameExponential g o e v)) ∧
      ∀ᶠ v in 𝓝 (0 : FourSpace),
        (heatRadialFrameEndpoint F t v).1 ∈ (chartAt FourSpace c).target ∧
        (heatRadialFrameEndpoint F t v).2ᵀ *
          metricInChart g c (heatRadialFrameEndpoint F t v).1 *
          (heatRadialFrameEndpoint F t v).2 = 1 := by
  let p := frameCoordinateState g c e
  have hp : p.1 ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source he
  obtain ⟨F₀⟩ := exists_heatRadialFrameFlow g c p hp
  obtain ⟨K₀⟩ := exists_kineticLocalFlow g c (p.1, 0) hp
  let δ := min F₀.time K₀.time
  have hδ : 0 < δ := lt_min F₀.time_pos K₀.time_pos
  let F := F₀.restrictTime δ hδ (min_le_left _ _)
  let K := K₀.restrictTime δ hδ (min_le_right _ _)
  obtain ⟨t, ht, htI, hFt⟩ := F.exists_pos_slice n
  let A : FourSpace → HeatRadialFrameSpace := fun v => (t⁻¹ • v, p)
  let P := heatRadialFrameEndpoint F t
  have hL : ContDiff ℝ ∞ (fun v : FourSpace => t⁻¹ • v) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff
  have hA : ContDiff ℝ ∞ A := hL.prodMk contDiff_const
  have hA0 : A 0 = (0, p) := by simp [A]
  have hFt' : ContDiffAt ℝ n (fun q => F.map (q, t)) (A 0) := by
    simpa only [hA0] using hFt
  have hP : ContDiffAt ℝ n P 0 :=
    (ContDiffAt.comp (f := A) (g := fun q => F.map (q, t)) 0 hFt'
      (hA.contDiffAt.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))).snd
  refine ⟨F, t, ht, htI, hP, ?_, ?_⟩
  · exact heatRadialFrameEndpoint_exponential g o c e he F K le_rfl t htI ht
  · have hnear : ∀ᶠ v in 𝓝 (0 : FourSpace), A v ∈ closedBall (0, p) F.radius :=
      hA.continuous.continuousAt.preimage_mem_nhds (by
        rw [hA0]
        exact closedBall_mem_nhds (0, p) F.radius_pos)
    filter_upwards [hnear] with v hv
    refine ⟨F.in_chart (A v) hv t htI, ?_⟩
    exact (F.gram (A v) hv t htI).trans (frameChartMatrix_normalizes g c e he)

theorem exists_heatRadialNormalFrame (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (n : ℕ) :
    ∃ P : FourSpace → CoordinateFrameSpace,
      ContDiffAt ℝ n P 0 ∧ P 0 = frameCoordinateState g c e ∧
      (fun v => (P v).1) =ᶠ[𝓝 0] (fun v => chartAt FourSpace c (frameExponential g o e v)) ∧
      ∀ᶠ v in 𝓝 (0 : FourSpace), (P v).1 ∈ (chartAt FourSpace c).target ∧
        (P v).2ᵀ * metricInChart g c (P v).1 * (P v).2 = 1 := by
  obtain ⟨F, t, ht, htI, hreg, hbase, hGram⟩ :=
    exists_heatRadialNormalFrame_flow g o c e he n
  exact ⟨heatRadialFrameEndpoint F t, hreg, heatRadialFrameEndpoint_zero F t htI,
    hbase, hGram⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rough Green identity with its actual smooth trace section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_roughTrace_green (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v =
      -smoothTwoFormL2Inner u (smoothTwoFormRoughTrace hRic v) := by
  rw [smoothTwoForm_rough_green hRic, smoothTwoFormL2Inner_eq_frame]
  have he : (fun e : FrameBundle g =>
      frameTensorPairing (twoFormFramedValue o u.val e)
        (twoFormFramedRoughTrace o v.val e)) =
      fun e => 2 * inner ℝ (twoFormFrameValue o u.val e)
        (twoFormFrameValue o (smoothTwoFormRoughTrace hRic v).val e) := by
    funext e
    rw [← v.property.framedValue_roughTrace hRic e, twoFormFramedValue_eq,
      twoFormFramedValue_eq, twoFormTensor_pairing]
    rfl
  rw [he, integral_const_mul]
  ring

theorem smoothTwoForm_roughTrace_green_left (hRic : RicciThree g)
    (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v =
      -smoothTwoFormL2Inner (smoothTwoFormRoughTrace hRic u) v := by
  rw [smoothTwoFormCovariantEnergy_comm, smoothTwoForm_roughTrace_green hRic,
    smoothTwoFormL2Inner_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial differential and Gauss identities for the actual
exponential, expressed in the metric rather than in an output chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartBackwardOperator_center (x : M) :
    chartBackwardOperator x (chartAt FourSpace x x) =
      ContinuousLinearMap.id ℝ FourSpace := by
  have h := chartBackward_forward x x (mem_chart_source FourSpace x)
  rwa [chartForwardOperator_center, ContinuousLinearMap.comp_id] at h

theorem metricInChart_center_pairing (g : SmoothMetric M) (x : M)
    (u v : Fin 4 → ℝ) :
    u ⬝ᵥ (metricInChart g x (chartAt FourSpace x x) *ᵥ v) =
      g.inner x (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [metricInChart_pairing]
  change g.inner ((chartAt FourSpace x).symm (chartAt FourSpace x x))
    (chartBackwardOperator x (chartAt FourSpace x x) (WithLp.toLp 2 u))
    (chartBackwardOperator x (chartAt FourSpace x x) (WithLp.toLp 2 v)) = _
  rw [(chartAt FourSpace x).left_inv (mem_chart_source FourSpace x),
    chartBackwardOperator_center]
  rfl

theorem metric_inner_abs_le (g : SmoothMetric M) (x : M) (u v : TangentSpace I4 x) :
    |g.inner x u v| ≤ metricTangentNorm g x u * metricTangentNorm g x v := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact abs_real_inner_le_norm u v

variable [T3Space M] [CompactSpace M]

theorem frameExponential_center_fderiv (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) :
    fderiv ℝ (fun w : FourSpace => chartAt FourSpace (frameExponential g o e v)
      (frameExponential g o e w)) v = mfderiv I4 I4 (frameExponential g o e) v := by
  let x := frameExponential g o e v
  have hc : MDifferentiableAt I4 I4 (chartAt FourSpace x) x :=
    (mdifferentiable_chart (I := I4) x).mdifferentiableAt (mem_chart_source FourSpace x)
  have he := (frameExponential_contMDiff g o e).mdifferentiable one_ne_zero v
  have h := mfderiv_comp v hc he
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun w => chartAt FourSpace x (frameExponential g o e w)) v =
    (chartForwardOperator x x).comp (mfderiv I4 I4 (frameExponential g o e) v) at h
  rw [chartForwardOperator_center] at h
  simpa only [ContinuousLinearMap.id_comp] using! h

theorem frameExponential_gauss_first (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (w : FourSpace) :
    g.inner (parallelFrameFlowMap g 0 t e).base
      ((parallelFrameFlowMap g 0 t e).frame.vector 0)
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) w) = w 0 := by
  let d := (parallelFrameFlowMap g 0 t e).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hx : frameExponential g o e (t • coordinateVector 0) = d :=
    frameExponential_first_ray g o e he t ht
  have hD := frameExponential_center_fderiv g o e (t • coordinateVector 0)
  rw [hx] at hD
  have hcol := frameChart_column_eq_derivative g d (parallelFrameFlowMap g 0 t e) 0 hd
  rw [chartForwardOperator_center] at hcol
  have hp := metricInChart_center_pairing g d
    (fun i => frameChartMatrix g d (parallelFrameFlowMap g 0 t e) i 0)
    (WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
      (frameExponential g o e v)) (t • coordinateVector 0) w))
  rw [WithLp.toLp_ofLp, hcol, hD] at hp
  have hg := frameExponential_chart_gauss g o hRic d e he t ht hd w
  rw [hD] at hg
  exact hp.symm.trans hg

theorem frameExponential_radial_differential_first (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) (coordinateVector 0) =
      (parallelFrameFlowMap g 0 t e).frame.vector 0 := by
  let d := (parallelFrameFlowMap g 0 t e).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hx : frameExponential g o e (t • coordinateVector 0) = d :=
    frameExponential_first_ray g o e he t ht
  have hD := frameExponential_center_fderiv g o e (t • coordinateVector 0)
  rw [hx] at hD
  rw [← hD, (frameExponential_hasFDerivAt g o hRic d e he t ht hd).fderiv]
  have hcol := frameChart_column_eq_derivative g d (parallelFrameFlowMap g 0 t e) 0 hd
  rw [chartForwardOperator_center] at hcol
  change WithLp.toLp 2 ((_ * _) *ᵥ WithLp.ofLp (coordinateVector 0)) = _
  rw [← Matrix.mulVec_mulVec, jacobiBlockMatrix_mulVec]
  have hb : (Fin.cons (1 * (coordinateVector 0 : FourSpace) 0)
      ((t⁻¹ • (actualJacobiSolution g hRic e).J t) *ᵥ
        (fun i => (coordinateVector 0 : FourSpace) i.succ)) : Fin 4 → ℝ) = Pi.single 0 1 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateVector]
    exact congrFun (Matrix.mulVec_zero (t⁻¹ • (actualJacobiSolution g hRic e).J t)) j
  rw [hb, Matrix.mulVec_single_one]
  exact hcol

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential is a local coordinate chart along every radial
geodesic strictly before its first conjugate point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_preconjugate_isUnit (g : SmoothMetric M)
    (hRic : RicciThree g) (d : M) (e : FrameBundle g) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    IsUnit (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
        jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))) := by
  have hE := Matrix.isUnit_det_of_left_inverse
    (frameChartMatrix_normalizes g d (parallelFrameFlowMap g 0 t e) hd)
  have hJ := (Matrix.isUnit_iff_isUnit_det _).mp
    (actualJacobi_isUnit_before_firstConjugate g hRic e t ht htc)
  have hB : IsUnit (jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [jacobiBlockMatrix_scaled_det]
    exact isUnit_iff_ne_zero.mpr (div_ne_zero hJ.ne_zero (pow_ne_zero _ ht.ne'))
  have hA := ((Matrix.isUnit_iff_isUnit_det _).mpr hE).mul hB
  exact hA.map (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)).toMonoidHom

/-- A local exponential chart centered at any positive preconjugate time. -/
theorem frameExponential_preconjugate_localChart (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      t • coordinateVector 0 ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  let d := (parallelFrameFlowMap g 0 t e).base
  let x := t • coordinateVector 0
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hx : frameExponential g o e x = d := frameExponential_first_ray g o e he t ht
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL : IsUnit L := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hxsrc : frameExponential g o e x ∈ (chartAt FourSpace d).source := hx ▸ hd
  have hcont := frameExponential_chart_contDiffAt g o d e x hxsrc
  have hder : HasFDerivAt (fun v => chartAt FourSpace d (frameExponential g o e v)) L x :=
    frameExponential_hasFDerivAt g o hRic d e he t ht hd
  have hf : HasStrictFDerivAt
      (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e v))
      (E : FourSpace →L[ℝ] FourSpace) x := by
    rw [hE]
    exact hcont.hasStrictFDerivAt' hder one_ne_zero
  let C := hf.toOpenPartialHomeomorph _
  let U := (frameExponential g o e) ⁻¹' (chartAt FourSpace d).source
  have hU : IsOpen U := (chartAt FourSpace d).open_source.preimage
    (frameExponential_continuous g o e)
  let D := (C.trans (chartAt FourSpace d).symm).restrOpen U hU
  refine ⟨D, ?_, ?_⟩
  · change x ∈ (C.trans (chartAt FourSpace d).symm).source ∩ U
    refine ⟨⟨hf.mem_toOpenPartialHomeomorph_source, ?_⟩, hxsrc⟩
    exact (chartAt FourSpace d).map_source hxsrc
  · intro v hv
    change (chartAt FourSpace d).symm
      (chartAt FourSpace d (frameExponential g o e v)) = frameExponential g o e v
    exact (chartAt FourSpace d).left_inv hv.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential commutes with oriented orthogonal changes of its initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameRotate_map (g : SmoothMetric M) (e : FrameBundle g) (Q : OrthogonalFour)
    (v : FourSpace) :
    (e.rotate Q).frame.map v =
      e.frame.map (orthogonalEuclideanIsometry Q.val Q.property v) := by
  ext i
  change ((e.frame.matrix * Q.val) *ᵥ WithLp.ofLp v) i =
    (e.frame.matrix *ᵥ (Q.val *ᵥ WithLp.ofLp v)) i
  rw [Matrix.mulVec_mulVec]

theorem unitTangentTurn_vector (g : SmoothMetric M) (e : FrameBundle g) (q : Directions) :
    (unitTangentTurn e q).vector = e.frame.map q.val := e.frame.turn_first q

theorem unitTangentTurn_base (g : SmoothMetric M) (e : FrameBundle g) (q : Directions) :
    (unitTangentTurn e q).base = e.base := rfl

theorem frameRotate_base (g : SmoothMetric M) (e : FrameBundle g) (Q : OrthogonalFour) :
    (e.rotate Q).base = e.base := rfl

theorem orthogonalDirection_val (Q : OrthogonalFour) (q : Directions) :
    (orthogonalDirection Q.val Q.property q).val =
      orthogonalEuclideanIsometry Q.val Q.property q.val := rfl

theorem orientedDirection_val (Q : OrientedOrthogonalFour) (q : Directions) :
    (orientedDirection Q q).val =
      orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property q.val := rfl

theorem unitTangentTurn_rotate (g : SmoothMetric M) (e : FrameBundle g)
    (Q : OrientedOrthogonalFour) (q : Directions) :
    unitTangentTurn (e.rotate (orientedToOrthogonal Q)) q =
      unitTangentTurn e (orientedDirection Q q) := by
  calc
    _ = unitTangentOfFrame ((e.rotate (orientedToOrthogonal Q)).rotate
        (orientedToOrthogonal (directionOrientedMatrix q))) := rfl
    _ = unitTangentOfFrame (e.rotate (orientedToOrthogonal (Q * directionOrientedMatrix q))) :=
      congrArg unitTangentOfFrame (frameRotate_mul e Q (directionOrientedMatrix q))
    _ = unitTangentTurn e (orientedDirection (Q * directionOrientedMatrix q) firstDirection) :=
      (unitTangentTurn_first e (Q * directionOrientedMatrix q)).symm
    _ = unitTangentTurn e (orientedDirection Q q) := by
      rw [orientedDirection_mul, orientedDirection_completion]

variable [T2Space M] [CompactSpace M]

theorem frameExponential_rotate (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (Q : OrientedOrthogonalFour) (v : FourSpace) :
    frameExponential g o (e.rotate (orientedToOrthogonal Q)) v =
      frameExponential g o e (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property v) := by
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property
  by_cases hv : v = 0
  · subst v
    rw [map_zero, frameExponential_zero, frameExponential_zero]
    rfl
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
    let q := (euclideanPolarHomeomorph w).1
    let r := (euclideanPolarHomeomorph w).2
    let q' := orientedDirection Q q
    have hvr : r.val • q.val = v :=
      congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
    calc
      _ = frameExponential g o (e.rotate (orientedToOrthogonal Q)) (r.val • q.val) := by rw [hvr]
      _ = unitGeodesic g o (unitTangentTurn (e.rotate (orientedToOrthogonal Q)) q) r.val :=
        frameExponential_radial g o (e.rotate (orientedToOrthogonal Q)) q r
      _ = unitGeodesic g o (unitTangentTurn e q') r.val := by
        rw [unitTangentTurn_rotate g e Q q]
      _ = frameExponential g o e (r.val • q'.val) := (frameExponential_radial g o e q' r).symm
      _ = frameExponential g o e (L v) := by
        rw [← hvr, map_smul]
        congr 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! A zero-ended, piecewise smooth negative-index variation after a conjugate
point.  The action is written as the sum on the two smooth pieces. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def normalIndexPairing (R : NormalMatrix) (y z h k : Fin 3 → ℝ) : ℝ :=
  z ⬝ᵥ k - (R *ᵥ y) ⬝ᵥ h

theorem normalIndexDensity_sub_smul (R : NormalMatrix) (hR : R.IsSymm)
    (y z h k : Fin 3 → ℝ) (ε : ℝ) :
    normalIndexDensity R (y - ε • h) (z - ε • k) =
      normalIndexDensity R y z - 2 * ε * normalIndexPairing R y z h k +
        ε ^ 2 * normalIndexDensity R h k := by
  have hmix : (R *ᵥ h) ⬝ᵥ y = (R *ᵥ y) ⬝ᵥ h := by
    rw [dotProduct_comm (R *ᵥ h) y, hR.dotProduct_mulVec_comm,
      dotProduct_comm h (R *ᵥ y)]
  simp only [normalIndexDensity, normalIndexPairing, Matrix.mulVec_sub,
    Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [hmix, dotProduct_comm k z]
  ring

theorem normalIndexDensity_smul (R : NormalMatrix) (y z : Fin 3 → ℝ) (ε : ℝ) :
    normalIndexDensity R (ε • y) (ε • z) = ε ^ 2 * normalIndexDensity R y z := by
  simp only [normalIndexDensity, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_normalIndexDensity {R : ℝ → NormalMatrix}
    {y z : ℝ → Fin 3 → ℝ} (hR : Continuous R) (hy : Continuous y) (hz : Continuous z) :
    Continuous (fun s => normalIndexDensity (R s) (y s) (z s)) :=
  (hz.dotProduct hz).sub ((hR.matrix_mulVec hy).dotProduct hy)

theorem continuous_normalIndexPairing {R : ℝ → NormalMatrix}
    {y z h k : ℝ → Fin 3 → ℝ} (hR : Continuous R) (hy : Continuous y)
    (hz : Continuous z) (hh : Continuous h) (hk : Continuous k) :
    Continuous (fun s => normalIndexPairing (R s) (y s) (z s) (h s) (k s)) :=
  (hz.dotProduct hk).sub ((hR.matrix_mulVec hy).dotProduct hh)

theorem normalJacobi_mixed_pairing_hasDerivAt (R : NormalMatrix)
    (y z h k : ℝ → Fin 3 → ℝ) (s : ℝ)
    (hz : HasDerivAt z (-(R *ᵥ y s)) s) (hh : HasDerivAt h (k s) s) :
    HasDerivAt (fun r => z r ⬝ᵥ h r)
      (normalIndexPairing R (y s) (z s) (h s) (k s)) s := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hz i).mul (hasDerivAt_pi.mp hh i))
  have heq : (∑ i, ((-(R *ᵥ y s)) i * h s i + z s i * k s i)) =
      normalIndexPairing R (y s) (z s) (h s) (k s) := by
    rw [Finset.sum_add_distrib]
    change (-(R *ᵥ y s)) ⬝ᵥ h s + z s ⬝ᵥ k s =
      z s ⬝ᵥ k s - (R *ᵥ y s) ⬝ᵥ h s
    rw [neg_dotProduct]
    ring
  rw [heq] at hd
  simpa only [dotProduct, Pi.mul_apply] using hd

theorem MatrixJacobiSolution.index_pairing_integral {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ)
    (h k : ℝ → Fin 3 → ℝ) (hh : ∀ s, HasDerivAt h (k s) s)
    (hk : Continuous k) (a b : ℝ) :
    (∫ s in a..b, normalIndexPairing (R s) (d.J s *ᵥ w) (d.V s *ᵥ w) (h s) (k s)) =
      (d.V b *ᵥ w) ⬝ᵥ h b - (d.V a *ᵥ w) ⬝ᵥ h a := by
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_position_hasDerivAt w s).continuousAt
  have hz : Continuous (fun s => d.V s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_velocity_hasDerivAt w s).continuousAt
  have hhcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun s => (hh s).continuousAt
  have hint : IntervalIntegrable (fun s => normalIndexPairing (R s)
      (d.J s *ᵥ w) (d.V s *ᵥ w) (h s) (k s)) volume a b :=
    (continuous_normalIndexPairing hR hy hz hhcont hk).intervalIntegrable a b
  have hderiv (s : ℝ) : HasDerivAt (fun r => (d.V r *ᵥ w) ⬝ᵥ h r)
      (normalIndexPairing (R s) (d.J s *ᵥ w) (d.V s *ᵥ w) (h s) (k s)) s :=
    normalJacobi_mixed_pairing_hasDerivAt (R s)
      (fun r => d.J r *ᵥ w) (fun r => d.V r *ᵥ w) h k s
      (d.field_velocity_hasDerivAt w s) (hh s)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hint

theorem index_integral_sub_smul {R : ℝ → NormalMatrix}
    {y z h k : ℝ → Fin 3 → ℝ} (hR : Continuous R)
    (hsym : ∀ s, (R s).IsSymm) (hy : Continuous y) (hz : Continuous z)
    (hh : Continuous h) (hk : Continuous k) (ε a b : ℝ) :
    (∫ s in a..b, normalIndexDensity (R s) (y s - ε • h s) (z s - ε • k s)) =
      (∫ s in a..b, normalIndexDensity (R s) (y s) (z s)) -
        2 * ε * (∫ s in a..b, normalIndexPairing (R s) (y s) (z s) (h s) (k s)) +
        ε ^ 2 * (∫ s in a..b, normalIndexDensity (R s) (h s) (k s)) := by
  have hi : IntervalIntegrable (fun s => normalIndexDensity (R s) (y s) (z s)) volume a b :=
    (continuous_normalIndexDensity hR hy hz).intervalIntegrable a b
  have hm : IntervalIntegrable (fun s => normalIndexPairing (R s) (y s) (z s) (h s) (k s))
      volume a b := (continuous_normalIndexPairing hR hy hz hh hk).intervalIntegrable a b
  have hh' : IntervalIntegrable (fun s => normalIndexDensity (R s) (h s) (k s)) volume a b :=
    (continuous_normalIndexDensity hR hh hk).intervalIntegrable a b
  simp_rw [normalIndexDensity_sub_smul _ (hsym _) ]
  rw [intervalIntegral.integral_add (hi.sub (hm.const_mul _)) (hh'.const_mul _),
    intervalIntegral.integral_sub hi (hm.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

def indexEndpointBump (c b : ℝ) (v : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  (s * (b - s) / (c * (b - c))) • v

def indexEndpointBumpDerivative (c b : ℝ) (v : Fin 3 → ℝ) (s : ℝ) : Fin 3 → ℝ :=
  ((b - 2 * s) / (c * (b - c))) • v

theorem indexEndpointBump_hasDerivAt (c b : ℝ) (v : Fin 3 → ℝ) (s : ℝ) :
    HasDerivAt (indexEndpointBump c b v) (indexEndpointBumpDerivative c b v s) s := by
  have hd : HasDerivAt (fun r : ℝ => r * (b - r) / (c * (b - c)))
      ((b - 2 * s) / (c * (b - c))) s := by
    convert ((hasDerivAt_id s).mul ((hasDerivAt_const s b).sub
      (hasDerivAt_id s))).div_const (c * (b - c)) using 1
    · funext r
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    · simp only [Pi.sub_apply, id_eq]
      ring
  exact hd.smul_const v

theorem indexEndpointBump_continuous (c b : ℝ) (v : Fin 3 → ℝ) :
    Continuous (indexEndpointBump c b v) :=
  continuous_iff_continuousAt.mpr fun s => (indexEndpointBump_hasDerivAt c b v s).continuousAt

theorem indexEndpointBumpDerivative_continuous (c b : ℝ) (v : Fin 3 → ℝ) :
    Continuous (indexEndpointBumpDerivative c b v) := by
  unfold indexEndpointBumpDerivative
  fun_prop

theorem indexEndpointBump_values {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (v : Fin 3 → ℝ) :
    indexEndpointBump c b v 0 = 0 ∧ indexEndpointBump c b v c = v ∧
      indexEndpointBump c b v b = 0 := by
  simp [indexEndpointBump, ne_of_gt hc, ne_of_gt (sub_pos.mpr hcb)]

/-- The action on the two smooth pieces of the zero-extended conjugate field
minus the explicit endpoint bump. -/
def conjugateIndexAction {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε : ℝ) : ℝ :=
  let h := indexEndpointBump c b (d.V c *ᵥ w)
  let k := indexEndpointBumpDerivative c b (d.V c *ᵥ w)
  (∫ s in (0 : ℝ)..c, normalIndexDensity (R s) (d.J s *ᵥ w - ε • h s)
    (d.V s *ᵥ w - ε • k s)) +
  (∫ s in c..b, normalIndexDensity (R s) (-(ε • h s)) (-(ε • k s)))

theorem MatrixJacobiSolution.conjugateIndexAction_eq {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (hsym : ∀ s, (R s).IsSymm)
    (w : Fin 3 → ℝ) {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hJ : d.J c *ᵥ w = 0) (ε : ℝ) :
    conjugateIndexAction d w c b ε =
      ε ^ 2 * (∫ s in (0 : ℝ)..b, normalIndexDensity (R s)
        (indexEndpointBump c b (d.V c *ᵥ w) s)
        (indexEndpointBumpDerivative c b (d.V c *ᵥ w) s)) -
      2 * ε * ((d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w)) := by
  let h := indexEndpointBump c b (d.V c *ᵥ w)
  let k := indexEndpointBumpDerivative c b (d.V c *ᵥ w)
  have hh := indexEndpointBump_continuous c b (d.V c *ᵥ w)
  have hk := indexEndpointBumpDerivative_continuous c b (d.V c *ᵥ w)
  have hi := continuous_normalIndexDensity hR hh hk
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_position_hasDerivAt w s).continuousAt
  have hz : Continuous (fun s => d.V s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_velocity_hasDerivAt w s).continuousAt
  have hvalues := indexEndpointBump_values hc hcb (d.V c *ᵥ w)
  have hcross := d.index_pairing_integral hR w h k
    (indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w)) hk 0 c
  change (∫ s in (0 : ℝ)..c, normalIndexPairing (R s) (d.J s *ᵥ w)
    (d.V s *ᵥ w) (h s) (k s)) = _ at hcross
  have hcross' : (∫ s in (0 : ℝ)..c, normalIndexPairing (R s) (d.J s *ᵥ w)
      (d.V s *ᵥ w) (h s) (k s)) = (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) := by
    simpa only [h, hvalues.1, hvalues.2.1, dotProduct_zero, sub_zero] using hcross
  change (∫ s in (0 : ℝ)..c, normalIndexDensity (R s) (d.J s *ᵥ w - ε • h s)
      (d.V s *ᵥ w - ε • k s)) +
    (∫ s in c..b, normalIndexDensity (R s) (-(ε • h s)) (-(ε • k s))) = _
  rw [index_integral_sub_smul hR hsym hy hz hh hk,
    d.index_integral_zero_of_kernel hR w c hJ, hcross']
  have hright : (∫ s in c..b, normalIndexDensity (R s) (-(ε • h s)) (-(ε • k s))) =
      ε ^ 2 * (∫ s in c..b, normalIndexDensity (R s) (h s) (k s)) := by
    simp_rw [← neg_smul, normalIndexDensity_smul, neg_sq]
    exact intervalIntegral.integral_const_mul _ _
  rw [hright, ← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable 0 c) (hi.intervalIntegrable c b)]
  ring

private theorem exists_positive_quadratic_negative {n : ℝ} (hn : 0 < n) (D : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 * D - 2 * ε * n < 0 := by
  let ε := n / (|D| + 1)
  have hd : 0 < |D| + 1 := by positivity
  have he : 0 < ε := div_pos hn hd
  have heq : ε * (|D| + 1) = n := by
    dsimp [ε]
    exact div_mul_cancel₀ n (ne_of_gt hd)
  have hbound : ε * D ≤ ε * |D| := mul_le_mul_of_nonneg_left (le_abs_self D) he.le
  have hsmall : ε * D < n := by nlinarith
  refine ⟨ε, he, ?_⟩
  nlinarith [mul_lt_mul_of_pos_left hsmall he, mul_pos he hn]

theorem MatrixJacobiSolution.exists_negative_conjugate_index {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (hsym : ∀ s, (R s).IsSymm)
    (w : Fin 3 → ℝ) {c b : ℝ} (hc : 0 < c) (hcb : c < b)
    (hJ : d.J c *ᵥ w = 0) (hV : d.V c *ᵥ w ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ conjugateIndexAction d w c b ε < 0 := by
  have hn : 0 < (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) := by
    have hnonneg : 0 ≤ (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg ((d.V c *ᵥ w) i))
    have hne : (d.V c *ᵥ w) ⬝ᵥ (d.V c *ᵥ w) ≠ 0 := by
      intro hzero
      exact hV (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨ε, hε, hneg⟩ := exists_positive_quadratic_negative hn
    (∫ s in (0 : ℝ)..b, normalIndexDensity (R s)
      (indexEndpointBump c b (d.V c *ᵥ w) s)
      (indexEndpointBumpDerivative c b (d.V c *ᵥ w) s))
  refine ⟨ε, hε, ?_⟩
  rwa [d.conjugateIndexAction_eq hR hsym w hc hcb hJ]

def conjugateIndexVariation {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε s : ℝ) : Fin 3 → ℝ :=
  (if s ≤ c then d.J s *ᵥ w else 0) - ε • indexEndpointBump c b (d.V c *ᵥ w) s

theorem MatrixJacobiSolution.conjugateIndexVariation_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ)
    (hJ : d.J c *ᵥ w = 0) : Continuous (conjugateIndexVariation d w c b ε) := by
  have hy : Continuous (fun s => d.J s *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun s => (d.field_position_hasDerivAt w s).continuousAt
  have hp : Continuous (fun s => if s ≤ c then d.J s *ᵥ w else 0) :=
    hy.if_le continuous_const continuous_id continuous_const (fun s hs => by simpa [hs] using hJ)
  exact hp.sub ((indexEndpointBump_continuous c b (d.V c *ᵥ w)).const_smul ε)

theorem MatrixJacobiSolution.conjugateIndexVariation_endpoints {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) {c b : ℝ}
    (hc : 0 < c) (hcb : c < b) (ε : ℝ) :
    conjugateIndexVariation d w c b ε 0 = 0 ∧
      conjugateIndexVariation d w c b ε b = 0 := by
  simp [conjugateIndexVariation, indexEndpointBump, d.initial_position,
    hc.le, not_le.mpr hcb]

theorem MatrixJacobiSolution.conjugateIndexVariation_left_derivative {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε s : ℝ) (hs : s < c) :
    HasDerivAt (conjugateIndexVariation d w c b ε)
      (d.V s *ᵥ w - ε • indexEndpointBumpDerivative c b (d.V c *ᵥ w) s) s := by
  apply ((d.field_position_hasDerivAt w s).sub
    ((indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w) s).const_smul ε)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hs] with r hr
  simp only [conjugateIndexVariation, ite_eq_left hr.le, Pi.sub_apply, Pi.smul_apply]

theorem MatrixJacobiSolution.conjugateIndexVariation_right_derivative {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε s : ℝ) (hs : c < s) :
    HasDerivAt (conjugateIndexVariation d w c b ε)
      (-(ε • indexEndpointBumpDerivative c b (d.V c *ᵥ w) s)) s := by
  apply (((indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w) s).const_smul ε).neg).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with r hr
  simp only [conjugateIndexVariation, ite_eq_right (not_le.mpr hr), zero_sub,
    Pi.neg_apply, Pi.smul_apply]

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_actualFirstConjugate_negative_index (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) (b : ℝ)
    (hb : actualFirstConjugateTime g hRic e < b) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      conjugateIndexAction (actualJacobiSolution g hRic e) w
        (actualFirstConjugateTime g hRic e) b ε < 0 := by
  obtain ⟨w, hw, hJ, hV⟩ := exists_actualFirstConjugate_vector g hRic e
  obtain ⟨ε, hε, hneg⟩ := (actualJacobiSolution g hRic e).exists_negative_conjugate_index
    (actualJacobiCurvature_continuous g hRic e)
    (actualJacobiCurvature_symmetric g e) w
    (actualFirstConjugateTime_pos g hRic e) hb hJ hV
  exact ⟨w, hw, ε, hε, hneg⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The index density in an actual metric chart equals the normal Euclidean
Jacobi index density when evaluated in a parallel orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem jacobiMetricPair_frame (G E : Mat4) (hE : Eᵀ * G * E = 1)
    (u v : JacobiCoordinateVector) :
    jacobiMetricPair G (E *ᵥ u) (E *ᵥ v) = u ⬝ᵥ v := by
  rw [← jacobiMetricPair_left_product, ← jacobiMetricPair_right_product, hE]
  simp only [jacobiMetricPair, Matrix.one_mulVec]

theorem normal_lift_dotProduct (u v : Fin 3 → ℝ) :
    (Fin.cons (0 : ℝ) u : Fin 4 → ℝ) ⬝ᵥ Fin.cons 0 v = u ⬝ᵥ v := by
  rw [dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add, dotProduct]

theorem hasDerivAt_normal_lift (a : ℝ → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (t : ℝ) (ha : HasDerivAt a b t) :
    HasDerivAt (fun s => (Fin.cons (0 : ℝ) (a s) : Fin 4 → ℝ)) (Fin.cons 0 b) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hasDerivAt_const t 0
  · exact hasDerivAt_pi.mp ha j

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_normal_curvature_vector (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    jacobiCurvature (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
        (fun i j => matrixPartial (connectionMatrix g c j) i (chartAt FourSpace c e.base))
        (frameChartMatrix g c e *ᵥ Fin.cons 0 a) (fun i => frameChartMatrix g c e i 0) *ᵥ
          (fun i => frameChartMatrix g c e i 0) =
      frameChartMatrix g c e *ᵥ Fin.cons 0 ((1 + frameCurvatureField g e) *ᵥ a) := by
  let E := frameChartMatrix g c e
  have hdet : IsUnit E.det :=
    Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g c e he)
  have h := congrArg (fun v => E *ᵥ v)
    (frameChart_normal_jacobi_curvature g c e he (Fin.cons 0 a))
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  simpa only [actual_jacobiCurvature_eq, jacobiCurvatureCombination, Fin.cons_succ] using h

/-- Only the ordinary-to-covariant derivative relation is needed in addition
to the actual frame and curvature. -/
theorem actual_coordinateIndexDensity_normal (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (a b : Fin 3 → ℝ) (w : JacobiCoordinateVector)
    (hw : w + jacobiConnection
        (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
        (fun i => frameChartMatrix g c e i 0) *ᵥ
          (frameChartMatrix g c e *ᵥ Fin.cons 0 a) =
      frameChartMatrix g c e *ᵥ Fin.cons 0 b) :
    coordinateIndexDensity (metricInChart g c (chartAt FourSpace c e.base))
        (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
        (fun i j => matrixPartial (connectionMatrix g c j) i (chartAt FourSpace c e.base))
        (fun i => frameChartMatrix g c e i 0) (frameChartMatrix g c e *ᵥ Fin.cons 0 a) w =
      normalIndexDensity (1 + frameCurvatureField g e) a b := by
  unfold coordinateIndexDensity
  rw [hw, frameChart_normal_curvature_vector g c e he,
    jacobiMetricPair_frame _ _ (frameChartMatrix_normalizes g c e he),
    jacobiMetricPair_frame _ _ (frameChartMatrix_normalizes g c e he),
    normal_lift_dotProduct, normal_lift_dotProduct]
  rfl

/-- Parallel-frame differentiation supplies the preceding derivative relation
from ordinary derivatives of the actual field. -/
theorem actual_parallel_normal_index (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (a : ℝ → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (w : JacobiCoordinateVector) (t : ℝ)
    (he : (e t).base ∈ (chartAt FourSpace c).source)
    (hE : ∀ i j, HasDerivAt (fun s => frameChartMatrix g c (e s) i j)
      (-(jacobiConnection
        (fun k => connectionMatrix g c k (chartAt FourSpace c (e t).base))
        (fun k => frameChartMatrix g c (e t) k 0) * frameChartMatrix g c (e t)) i j) t)
    (ha : HasDerivAt a b t)
    (hY : HasDerivAt (fun s => frameChartMatrix g c (e s) *ᵥ Fin.cons 0 (a s)) w t) :
    coordinateIndexDensity (metricInChart g c (chartAt FourSpace c (e t).base))
        (fun i => connectionMatrix g c i (chartAt FourSpace c (e t).base))
        (fun i j => matrixPartial (connectionMatrix g c j) i (chartAt FourSpace c (e t).base))
        (fun i => frameChartMatrix g c (e t) i 0)
        (frameChartMatrix g c (e t) *ᵥ Fin.cons 0 (a t)) w =
      normalIndexDensity (1 + frameCurvatureField g (e t)) (a t) b := by
  apply actual_coordinateIndexDensity_normal g c (e t) he
  exact parallel_frame_covariant_derivative (fun s => frameChartMatrix g c (e s))
    (fun s => Fin.cons 0 (a s)) _ (Fin.cons 0 b) w t hE
    (hasDerivAt_normal_lift a b t ha) hY

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential maps of all nearby frames agree with one
kinetic flow on a common velocity ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem KineticLocalFlow.common_exponential_endpoint (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (K : KineticLocalFlow g c (chartAt FourSpace c e.base, 0)) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ ε > (0 : ℝ),
      ∀ e' ∈ U, e'.base ∈ (chartAt FourSpace c).source ∧
        ∀ v : FourSpace, ‖v‖ < ε → ∀ t ∈ Ioo (-K.time) K.time, 0 < t →
          (K.map ((chartAt FourSpace c e'.base, frameMomentumMap g c e' v), t)).1 =
            chartAt FourSpace c (frameExponential g o e' (t • v)) := by
  obtain ⟨U₀, hU₀, he₀, δ, hδ, hchart⟩ := unitGeodesic_common_chart g o c e he
  let p := frameCoordinateState g c e
  obtain ⟨r, hr, hdomain⟩ := heatRadialCotangentState_common_domain g c p
    ((chartAt FourSpace c).map_source he) K.radius K.radius_pos
  have hcoord : {e' : FrameBundle g | frameCoordinateState g c e' ∈ ball p r} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g c e he).preimage_mem_nhds (ball_mem_nhds _ hr)
  have hsource : {e' : FrameBundle g | e'.base ∈ (chartAt FourSpace c).source} ∈ 𝓝 e :=
    (continuous_frameBase g).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds he)
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU₀.mem_nhds he₀) (Filter.inter_mem hcoord hsource))
  let ε := min r (δ / (K.time + 1))
  have htpos : 0 < K.time + 1 := by linarith [K.time_pos]
  have hε : 0 < ε := lt_min hr (div_pos hδ htpos)
  refine ⟨U, hU, heU, ε, hε, ?_⟩
  intro e' he'
  obtain ⟨he'₀, hq, he'c⟩ := hsub he'
  refine ⟨he'c, ?_⟩
  intro v hv t ht ht0
  have hinit : (chartAt FourSpace c e'.base, frameMomentumMap g c e' v) ∈
      ball (chartAt FourSpace c e.base, 0) K.radius := by
    have hh := hdomain v (hv.trans_le (min_le_left _ _)) (frameCoordinateState g c e') hq
    rw [heatRadialCotangentState_frame g c e' he'c v] at hh
    exact hh
  by_cases hv0 : v = 0
  · subst v
    have hbase : chartAt FourSpace c e'.base ∈ (chartAt FourSpace c).target :=
      (chartAt FourSpace c).map_source he'c
    have heq := K.eq_on _ (by simpa only [map_zero] using hinit)
      (fun _ => (chartAt FourSpace c e'.base, (0 : FourSpace))) rfl
      (fun s _ => by
        rw [kineticHamiltonianField_zero_momentum g c _ hbase]
        exact hasDerivAt_const s _)
    simpa only [map_zero, smul_zero, frameExponential_zero] using congrArg Prod.fst (heq ht)
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv0⟩
    let q := (euclideanPolarHomeomorph w).1
    let ρ := (euclideanPolarHomeomorph w).2
    have hρ : 0 < ρ.val := ρ.property
    have hρnorm : ρ.val = ‖v‖ := homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    have hvr : ρ.val • q.val = v := congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
    have hsmall : ρ.val * (K.time + 1) < δ := by
      rw [hρnorm]
      exact (lt_div_iff₀ htpos).mp (hv.trans_le (min_le_right _ _))
    have hstay (s : ℝ) (hs : s ∈ Ioo (-K.time) K.time) :
        unitGeodesic g o (unitTangentTurn e' q) (ρ.val * s) ∈ (chartAt FourSpace c).source := by
      apply hchart e' he'₀ q (ρ.val * s)
      have hsabs : |s| < K.time := abs_lt.mpr hs
      apply abs_lt.mp
      rw [abs_mul, abs_of_pos hρ]
      nlinarith [abs_nonneg s]
    have hsol (s : ℝ) (hs : s ∈ Ioo (-K.time) K.time) :=
      hasDerivAt_unitTangentRadial_cotangent g o c
        (⟨ρ.val, hρ⟩, unitTangentTurn e' q) s (hstay s hs)
    have heq := K.eq_on _ hinit
      (fun s => unitCotangentState g c ρ.val (unitTangentFlowMap g o (ρ.val * s) (unitTangentTurn e' q)))
      (by simpa only [mul_zero, unitTangentFlowMap_zero, hvr] using
        unitCotangentState_turn g c e' he'c ρ.val q) hsol
    have hexp : frameExponential g o e' (t • v) =
        unitGeodesic g o (unitTangentTurn e' q) (ρ.val * t) := by
      rw [← hvr, smul_smul]
      simpa only [mul_comm] using frameExponential_radial g o e' q ⟨t * ρ.val, mul_pos ht0 hρ⟩
    rw [hexp]
    exact congrArg Prod.fst (heq ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scaling the initial direction scales time in the radial frame ODE. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatRadialDirectionScale (r : ℝ) (q : HeatRadialFrameSpace) : HeatRadialFrameSpace :=
  (r • q.1, q.2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatRadialFrameField_scale (g : SmoothMetric M) (c : M) (r : ℝ)
    (q : HeatRadialFrameSpace) :
    heatRadialFrameField g c (heatRadialDirectionScale r q) =
      (0, r • (heatRadialFrameField g c q).2) := by
  have hv : heatRadialFrameVelocity (heatRadialDirectionScale r q) =
      r • heatRadialFrameVelocity q := by
    exact Matrix.mulVec_smul _ _ _
  have hC : heatRadialFrameConnection g c (heatRadialDirectionScale r q) =
      r • heatRadialFrameConnection g c q := by
    change (∑ i : Fin 4, heatRadialFrameVelocity (heatRadialDirectionScale r q) i •
      connectionMatrix g c i q.2.1) = r • ∑ i : Fin 4,
        heatRadialFrameVelocity q i • connectionMatrix g c i q.2.1
    rw [hv, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_smul, smul_eq_mul]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext i
    change heatRadialFrameVelocity (heatRadialDirectionScale r q) i =
      r * heatRadialFrameVelocity q i
    rw [hv]
    rfl
  · change -(heatRadialFrameConnection g c (heatRadialDirectionScale r q) * q.2.2) =
      r • -(heatRadialFrameConnection g c q * q.2.2)
    rw [hC, smul_mul_assoc, smul_neg]

theorem hasDerivAt_heatRadialDirectionScale (g : SmoothMetric M) (c : M)
    (α : ℝ → HeatRadialFrameSpace) (r t : ℝ)
    (hα : HasDerivAt α (heatRadialFrameField g c (α (r * t))) (r * t)) :
    HasDerivAt (fun s => heatRadialDirectionScale r (α (r * s)))
      (heatRadialFrameField g c (heatRadialDirectionScale r (α (r * t)))) t := by
  have h : HasDerivAt (fun s => α (r * s))
      (r • heatRadialFrameField g c (α (r * t))) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hα.scomp t ((hasDerivAt_id t).const_mul r)
  have hv : HasDerivAt (fun s => r • (α (r * s)).1) 0 t := by
    have hd : HasDerivAt (fun s => (α (r * s)).1) 0 t := by
      have hd' : HasDerivAt (fun s => (α (r * s)).1)
          ((r • heatRadialFrameField g c (α (r * t))).1) t := h.fst
      change HasDerivAt (fun s => (α (r * s)).1) (r • (0 : FourSpace)) t at hd'
      simpa only [smul_zero] using hd'
    simpa only [smul_zero] using! hd.const_smul r
  have hp : HasDerivAt (fun s => (α (r * s)).2)
      (r • (heatRadialFrameField g c (α (r * t))).2) t := by
    simpa only [Prod.smul_snd] using! h.snd
  rw [heatRadialFrameField_scale]
  exact hv.prodMk hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single jointly regular radial frame family over nearby centers.
Its slices lie over the actual exponential maps by kinetic uniqueness. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_heatRadialNormalFamily (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧ ∃ r > (0 : ℝ),
        (∀ z ∈ ball (0, frameCoordinateState g c e) r,
          ContDiffAt ℝ 12 (heatRadialFrameFamily F t) z ∧
          (heatRadialFrameFamily F t z).1 ∈ (chartAt FourSpace c).target ∧
          (heatRadialFrameFamily F t z).2ᵀ *
              metricInChart g c (heatRadialFrameFamily F t z).1 *
              (heatRadialFrameFamily F t z).2 =
            z.2.2ᵀ * metricInChart g c z.2.1 * z.2.2) ∧
        ∀ e' : FrameBundle g, e'.base ∈ (chartAt FourSpace c).source →
          frameCoordinateState g c e' ∈ ball (frameCoordinateState g c e) r →
          (heatRadialFrameFamily F t (0, frameCoordinateState g c e') =
            frameCoordinateState g c e') ∧
          (fun v => (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1)
            =ᶠ[𝓝 0] (fun v => chartAt FourSpace c (frameExponential g o e' v)) := by
  let p := frameCoordinateState g c e
  have hp : p.1 ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source he
  obtain ⟨F₀⟩ := exists_heatRadialFrameFlow g c p hp
  obtain ⟨K₀⟩ := exists_kineticLocalFlow g c (p.1, 0) hp
  let δ := min F₀.time K₀.time
  have hδ : 0 < δ := lt_min F₀.time_pos K₀.time_pos
  let F := F₀.restrictTime δ hδ (min_le_left _ _)
  let K := K₀.restrictTime δ hδ (min_le_right _ _)
  obtain ⟨t, ht, htI, R, hR, hfamily⟩ := F.exists_joint_frame_family
  let r := min R (min F.radius K.radius) / 2
  have hr : 0 < r := half_pos (lt_min hR (lt_min F.radius_pos K.radius_pos))
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hR
    (lt_min F.radius_pos K.radius_pos)))).trans (min_le_left _ _)
  have hrF : r ≤ F.radius := (half_le_self (le_of_lt (lt_min hR
    (lt_min F.radius_pos K.radius_pos)))).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hrK : r ≤ K.radius := (half_le_self (le_of_lt (lt_min hR
    (lt_min F.radius_pos K.radius_pos)))).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨F, t, ht, htI, r, hr, ?_, ?_⟩
  · intro z hz
    obtain ⟨hreg, _, hc, hg⟩ := hfamily z (ball_subset_ball hrR hz)
    exact ⟨hreg, hc, hg⟩
  · intro e' he' he'r
    let q := frameCoordinateState g c e'
    have hq : ((0 : FourSpace), q) ∈ ball (0, p) F.radius := by
      have hh : dist q p < F.radius := (show dist q p < r from he'r).trans_le hrF
      change max (dist (0 : FourSpace) 0) (dist q p) < F.radius
      simpa only [dist_self, max_eq_right dist_nonneg] using hh
    have hk : (q.1, (0 : FourSpace)) ∈ ball (p.1, 0) K.radius := by
      have hh : dist q.1 p.1 < K.radius :=
        (show dist q.1 p.1 ≤ dist q p from le_max_left _ _).trans_lt
          ((show dist q p < r from he'r).trans_le hrK)
      simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hh
    refine ⟨heatRadialFrameFamily_zero F q (ball_subset_closedBall hq) t htI, ?_⟩
    exact heatRadialFrameEndpoint_exponential g o c e' he'
      (F.recenter q hq) (K.recenter (q.1, 0) hk) le_rfl t htI ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gauss' lemma in every initial direction and the resulting radial speed bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix
open scoped Manifold ContDiff _root_.Topology InnerProductSpace

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_rotate_mfderiv (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (Q : OrientedOrthogonalFour) (v w : FourSpace) :
    mfderiv I4 I4 (frameExponential g o (e.rotate (orientedToOrthogonal Q))) v w =
      mfderiv I4 I4 (frameExponential g o e)
        (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property v)
        (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property w) := by
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  have hL : HasFDerivAt (fun w : FourSpace => L w) (L : FourSpace →L[ℝ] FourSpace) v :=
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have he := (frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (L v)
  have h := congrArg (fun A => A w) (mfderiv_comp v he hL.differentiableAt.mdifferentiableAt)
  have heq : frameExponential g o (e.rotate (orientedToOrthogonal Q)) =
      (fun w : FourSpace => frameExponential g o e (L w)) :=
    funext (frameExponential_rotate g o e Q)
  have hDL : mfderiv I4 I4 (fun z : FourSpace => L z) v w = L w := by
    rw [mfderiv_eq_fderiv, hL.fderiv]
    rfl
  change mfderiv I4 I4 (fun z => frameExponential g o e (L z)) v w =
    mfderiv I4 I4 (frameExponential g o e) (L v)
      (mfderiv I4 I4 (fun z : FourSpace => L z) v w) at h
  rw [← heq, hDL] at h
  exact h

theorem directionRotation_first (q : Directions) :
    orthogonalEuclideanIsometry (orientedToOrthogonal (directionOrientedMatrix q)).val
      (orientedToOrthogonal (directionOrientedMatrix q)).property (coordinateVector 0) = q.val := by
  ext i
  change (directionFrameMatrix q *ᵥ Pi.single 0 1) i = q.val i
  rw [Matrix.mulVec_single_one]
  exact directionFrameMatrix_zero q i

/-- Gauss' lemma for every unit radial direction, derived from the actual
Jacobi differential and the proved orthogonal change of initial frame. -/
theorem frameExponential_gauss (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (t : ℝ) (ht : 0 < t) (w : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w) = ⟪q.val, w⟫_ℝ := by
  let Q := directionOrientedMatrix q
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have htq : L (t • coordinateVector 0) = t • q.val := by rw [map_smul, hfirst]
  have hD (w : FourSpace) :
      mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) w =
        mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L w) := by
    have h := frameExponential_rotate_mfderiv g o e Q (t • coordinateVector 0) w
    change mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) w =
      mfderiv I4 I4 (frameExponential g o e) (L (t • coordinateVector 0)) (L w) at h
    rwa [htq] at h
  have hrad := frameExponential_radial_differential_first g o hRic f hf t ht
  rw [hD] at hrad
  change mfderiv I4 I4 (frameExponential g o e) (t • q.val)
    (L (coordinateVector 0)) = _ at hrad
  rw [hfirst] at hrad
  have hx : frameExponential g o e (t • q.val) = (parallelFrameFlowMap g 0 t f).base := by
    rw [← htq, ← frameExponential_rotate g o e Q]
    exact frameExponential_first_ray g o f hf t ht
  have h := frameExponential_gauss_first g o hRic f hf t ht (L.symm w)
  rw [hD] at h
  change g.inner (parallelFrameFlowMap g 0 t f).base
    ((parallelFrameFlowMap g 0 t f).frame.vector 0)
    (mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L (L.symm w))) = _ at h
  rw [L.apply_symm_apply] at h
  have hinner := L.inner_map_map (coordinateVector 0) (L.symm w)
  rw [hfirst, L.apply_symm_apply] at hinner
  have hzero : ⟪(coordinateVector 0 : FourSpace), L.symm w⟫_ℝ = (L.symm w) 0 := by
    simp [PiLp.inner_apply, coordinateVector]
  let u : FourSpace := mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val
  let z : FourSpace := mfderiv I4 I4 (frameExponential g o e) (t • q.val) w
  change u = (parallelFrameFlowMap g 0 t f).frame.vector 0 at hrad
  change g.inner (frameExponential g o e (t • q.val)) u z = _
  rw [hrad, hx]
  exact h.trans (hinner.trans hzero).symm

theorem frameExponential_radial_norm (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (t : ℝ) (ht : 0 < t) :
    metricTangentNorm g (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val) = 1 := by
  rw [metricTangentNorm_eq_sqrt, frameExponential_gauss g o hRic e he q t ht q.val,
    real_inner_self_eq_norm_sq, q.property, one_pow, Real.sqrt_one]

theorem frameExponential_radial_pairing_le (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (t : ℝ) (ht : 0 < t) (w : FourSpace) :
    |⟪q.val, w⟫_ℝ| ≤ metricTangentNorm g (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w) := by
  have h := metric_inner_abs_le g (frameExponential g o e (t • q.val))
    (mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val)
    (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w)
  rw [frameExponential_gauss g o hRic e he q t ht w,
    frameExponential_radial_norm g o hRic e he q t ht, one_mul] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local inverses of the actual exponential are C1 wherever its actual
coordinate derivative is invertible. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_chart_local_inverse_contMDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (d : M) (x : FourSpace)
    (C : OpenPartialHomeomorph FourSpace M) (hx : x ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hd : frameExponential g o e x ∈ (chartAt FourSpace d).source)
    (hL : IsUnit (fderiv ℝ (fun v : FourSpace =>
      chartAt FourSpace d (frameExponential g o e v)) x)) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e x) := by
  let F := fun v : FourSpace => chartAt FourSpace d (frameExponential g o e v)
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = fderiv ℝ F x := hL.unit_spec
  have hcont : ContDiffAt ℝ 1 F x := frameExponential_chart_contDiffAt g o d e x hd
  have hder : HasFDerivAt F (E : FourSpace →L[ℝ] FourSpace) x := by
    rw [hE]
    exact (hcont.differentiableAt one_ne_zero).hasFDerivAt
  let hf := hcont.hasStrictFDerivAt' hder one_ne_zero
  let H := fun z : FourSpace => C.symm ((chartAt FourSpace d).symm z)
  have hleft : ∀ᶠ v in 𝓝 x, H (F v) = v := by
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)
    filter_upwards [C.open_source.mem_nhds hx, hnear] with v hv hvc
    change C.symm ((chartAt FourSpace d).symm
      (chartAt FourSpace d (frameExponential g o e v))) = v
    rw [(chartAt FourSpace d).left_inv hvc, ← hC hv]
    exact C.left_inv hv
  have heq := hf.localInverse_unique hleft
  have hcontH : ContDiffAt ℝ 1 H (F x) :=
    (hcont.to_localInverse hder one_ne_zero).congr_of_eventuallyEq heq
  have hchart : ContMDiffAt I4 I4 1 (chartAt FourSpace d) (frameExponential g o e x) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hd
  have h := hcontH.contMDiffAt.comp (frameExponential g o e x) hchart
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace d).open_source.mem_nhds hd] with y hy
  change C.symm y = C.symm ((chartAt FourSpace d).symm (chartAt FourSpace d y))
  rw [(chartAt FourSpace d).left_inv hy]

theorem frameExponential_local_inverse_contMDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (x : FourSpace)
    (C : OpenPartialHomeomorph FourSpace M) (hx : x ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hL : IsUnit (fderiv ℝ (fun v : FourSpace =>
      chartAt FourSpace (frameExponential g o e x) (frameExponential g o e v)) x)) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e x) :=
  frameExponential_chart_local_inverse_contMDiffAt g o e _ x C hx hC
    (mem_chart_source FourSpace _) hL

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first variation of the squared radial length of a genuine local
inverse branch of the exponential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology RealInnerProductSpace
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_exponential_log_first_variation (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (d : M) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    ∃ C : OpenPartialHomeomorph FourSpace FourSpace,
      (C : FourSpace → FourSpace) = (fun v => chartAt FourSpace d (frameExponential g o e v)) ∧
      t • coordinateVector 0 ∈ C.source ∧
      ∀ a : FourSpace, HasDerivAt
        (fun ε : ℝ => ‖C.symm (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base + ε • a)‖ ^ 2)
        (2 * t * ((fun i => frameChartMatrix g d (parallelFrameFlowMap g 0 t e) i 0) ⬝ᵥ
          (metricInChart g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *ᵥ WithLp.ofLp a))) 0 := by
  let v : FourSpace := t • coordinateVector 0
  let F : FourSpace → FourSpace := fun x => chartAt FourSpace d (frameExponential g o e x)
  let z : FourSpace := chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base
  have hz : F v = z := congrArg (chartAt FourSpace d) (frameExponential_first_ray g o e he t ht)
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hder : HasFDerivAt F (A : FourSpace →L[ℝ] FourSpace) v := by
    rw [hA]
    exact frameExponential_hasFDerivAt g o hRic d e he t ht hd
  have hs : HasStrictFDerivAt F (A : FourSpace →L[ℝ] FourSpace) v :=
    (frameExponential_chart_contDiffAt g o d e v
      ((frameExponential_first_ray g o e he t ht).symm ▸ hd)).hasStrictFDerivAt' hder one_ne_zero
  let C := hs.toOpenPartialHomeomorph F
  have hC : (C : FourSpace → FourSpace) = F := rfl
  have hvC : v ∈ C.source := hs.mem_toOpenPartialHomeomorph_source
  have hInv : HasFDerivAt C.symm (A.symm : FourSpace →L[ℝ] FourSpace) z := by
    rw [← hz]
    exact hs.to_localInverse.hasFDerivAt
  have hInv0 : C.symm z = v := by rw [← hz]; exact C.left_inv hvC
  refine ⟨C,hC,hvC,?_⟩
  intro a
  have hline : HasDerivAt (fun ε : ℝ => z + ε • a) a 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add z
  have hbranch : HasDerivAt (fun ε : ℝ => C.symm (z + ε • a)) (A.symm a) 0 := by
    have hh : HasFDerivAt C.symm (A.symm : FourSpace →L[ℝ] FourSpace) (z + (0 : ℝ) • a) := by
      simpa only [zero_smul,add_zero] using hInv
    exact hh.comp_hasDerivAt 0 hline
  have hnorm := hbranch.norm_sq
  have hgauss := frameExponential_chart_gauss g o hRic d e he t ht hd (A.symm a)
  rw [hder.fderiv] at hgauss
  change _ ⬝ᵥ (_ *ᵥ WithLp.ofLp (A (A.symm a))) = _ at hgauss
  rw [A.apply_symm_apply] at hgauss
  have hinner : inner ℝ v (A.symm a) = t * (A.symm a) 0 := by
    rw [show v = t • coordinateVector 0 from rfl,real_inner_smul_left]
    change t * inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : FourSpace) (A.symm a) = _
    rw [EuclideanSpace.inner_single_left]
    simp only [conj_trivial,one_mul]
  simpa only [zero_smul,add_zero,hInv0,hinner,← hgauss,mul_assoc] using hnorm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Globally C1 extensions of the two smooth pieces of the conjugate-point
test field.  The extensions agree at the conjugate point, so a chart partition
can treat each side separately without differentiating at the corner. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix MeasureTheory Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

def conjugateLeftField {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  d.J t *ᵥ w - ε • indexEndpointBump c b (d.V c *ᵥ w) t

def conjugateLeftRate {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  d.V t *ᵥ w - ε • indexEndpointBumpDerivative c b (d.V c *ᵥ w) t

def conjugateRightField {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  -(ε • indexEndpointBump c b (d.V c *ᵥ w) t)

def conjugateRightRate {R : ℝ → NormalMatrix} (d : MatrixJacobiSolution R)
    (w : Fin 3 → ℝ) (c b ε t : ℝ) : Fin 3 → ℝ :=
  -(ε • indexEndpointBumpDerivative c b (d.V c *ᵥ w) t)

theorem conjugateLeftField_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε t : ℝ) :
    HasDerivAt (conjugateLeftField d w c b ε) (conjugateLeftRate d w c b ε t) t := by
  exact (d.field_position_hasDerivAt w t).sub
    ((indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w) t).const_smul ε)

theorem conjugateRightField_hasDerivAt {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε t : ℝ) :
    HasDerivAt (conjugateRightField d w c b ε) (conjugateRightRate d w c b ε t) t := by
  exact ((indexEndpointBump_hasDerivAt c b (d.V c *ᵥ w) t).const_smul ε).neg

theorem conjugateLeftRate_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    Continuous (conjugateLeftRate d w c b ε) := by
  have hV : Continuous (fun t => d.V t *ᵥ w) :=
    continuous_iff_continuousAt.mpr fun t => (d.field_velocity_hasDerivAt w t).continuousAt
  exact hV.sub ((indexEndpointBumpDerivative_continuous c b (d.V c *ᵥ w)).const_smul ε)

theorem conjugateRightRate_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    Continuous (conjugateRightRate d w c b ε) :=
  ((indexEndpointBumpDerivative_continuous c b (d.V c *ᵥ w)).const_smul ε).neg

theorem conjugateLeftField_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    Continuous (conjugateLeftField d w c b ε) :=
  continuous_iff_continuousAt.mpr fun t =>
    (conjugateLeftField_hasDerivAt d w c b ε t).continuousAt

theorem conjugateRightField_continuous {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    Continuous (conjugateRightField d w c b ε) :=
  continuous_iff_continuousAt.mpr fun t =>
    (conjugateRightField_hasDerivAt d w c b ε t).continuousAt

theorem conjugateLeftField_contDiff {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    ContDiff ℝ 1 (conjugateLeftField d w c b ε) := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t =>
    (conjugateLeftField_hasDerivAt d w c b ε t).differentiableAt, ?_⟩
  have heq : deriv (conjugateLeftField d w c b ε) = conjugateLeftRate d w c b ε :=
    funext fun t => (conjugateLeftField_hasDerivAt d w c b ε t).deriv
  rw [heq]
  exact conjugateLeftRate_continuous d w c b ε

theorem conjugateRightField_contDiff {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    ContDiff ℝ 1 (conjugateRightField d w c b ε) := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t =>
    (conjugateRightField_hasDerivAt d w c b ε t).differentiableAt, ?_⟩
  have heq : deriv (conjugateRightField d w c b ε) = conjugateRightRate d w c b ε :=
    funext fun t => (conjugateRightField_hasDerivAt d w c b ε t).deriv
  rw [heq]
  exact conjugateRightRate_continuous d w c b ε

theorem conjugateBranches_agree {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ)
    (hJ : d.J c *ᵥ w = 0) :
    conjugateLeftField d w c b ε c = conjugateRightField d w c b ε c := by
  simp only [conjugateLeftField, conjugateRightField, hJ, zero_sub]

theorem conjugateBranches_endpoints {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    conjugateLeftField d w c b ε 0 = 0 ∧ conjugateRightField d w c b ε b = 0 := by
  simp [conjugateLeftField, conjugateRightField, indexEndpointBump, d.initial_position]

theorem conjugateLeftField_eq_variation {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε t : ℝ) (ht : t ≤ c) :
    conjugateLeftField d w c b ε t = conjugateIndexVariation d w c b ε t := by
  simp only [conjugateLeftField, conjugateIndexVariation, ite_eq_left ht]

theorem conjugateRightField_eq_variation {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε t : ℝ)
    (hJ : d.J c *ᵥ w = 0) (ht : c ≤ t) :
    conjugateRightField d w c b ε t = conjugateIndexVariation d w c b ε t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simp only [conjugateRightField, conjugateIndexVariation, le_refl, ite_true, hJ, zero_sub]
  · simp only [conjugateRightField, conjugateIndexVariation, ite_eq_right (not_le.mpr h), zero_sub]

theorem conjugateBranches_integrals {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (w : Fin 3 → ℝ) (c b ε : ℝ) :
    (∫ t in (0 : ℝ)..c, normalIndexDensity (R t)
      (conjugateLeftField d w c b ε t) (conjugateLeftRate d w c b ε t)) +
    (∫ t in c..b, normalIndexDensity (R t)
      (conjugateRightField d w c b ε t) (conjugateRightRate d w c b ε t)) =
      conjugateIndexAction d w c b ε := rfl

theorem conjugateBranches_index_integrable {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (hR : Continuous R) (w : Fin 3 → ℝ)
    (c b ε r s : ℝ) :
    IntervalIntegrable (fun t => normalIndexDensity (R t)
      (conjugateLeftField d w c b ε t) (conjugateLeftRate d w c b ε t)) volume r s ∧
    IntervalIntegrable (fun t => normalIndexDensity (R t)
      (conjugateRightField d w c b ε t) (conjugateRightRate d w c b ε t)) volume r s := by
  exact ⟨(continuous_normalIndexDensity hR
    (conjugateLeftField_continuous d w c b ε)
    (conjugateLeftRate_continuous d w c b ε)).intervalIntegrable r s,
    (continuous_normalIndexDensity hR
    (conjugateRightField_continuous d w c b ε)
    (conjugateRightRate_continuous d w c b ε)).intervalIntegrable r s⟩

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Normal fields along the actual parallel-frame flow.  Their ordinary
coordinate derivatives and their index densities are derived from the
constructed horizontal ODE, rather than supplied as extra field identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def normalChartField (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (a : ℝ → Fin 3 → ℝ) (t : ℝ) : JacobiCoordinateVector :=
  frameChartMatrix g c (parallelFrameFlowMap g 0 t e) *ᵥ Fin.cons 0 (a t)

def normalChartFrameRate (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (t : ℝ) : Mat4 :=
  (parallelFrameVectorField g c 0
    (frameCoordinateState g c (parallelFrameFlowMap g 0 t e))).2

def normalChartFieldRate (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (a b : ℝ → Fin 3 → ℝ) (t : ℝ) : JacobiCoordinateVector :=
  normalChartFrameRate g c e t *ᵥ Fin.cons 0 (a t) +
    frameChartMatrix g c (parallelFrameFlowMap g 0 t e) *ᵥ Fin.cons 0 (b t)

theorem normalChartFrame_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => frameChartMatrix g c (parallelFrameFlowMap g 0 s e))
      (normalChartFrameRate g c e t) t := by
  have h := parallelFrameCurveAt_fixedChart g c (parallelFrameFlowMap g 0 · e) t 0
    (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt hc
    (parallelFrameFlowMap_primitive g 0 e t)
  exact (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t h

theorem normalChartFieldRate_eq (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (t : ℝ) :
    normalChartFieldRate g c e a b t =
      frameChartMatrix g c (parallelFrameFlowMap g 0 t e) *ᵥ Fin.cons 0 (b t) -
        jacobiConnection
          (fun i => connectionMatrix g c i (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
          (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0) *ᵥ
            normalChartField g c e a t := by
  simp only [normalChartFieldRate, normalChartFrameRate, normalChartField,
    parallelFrameVectorField, parallelFrameConnection, frameCoordinateState,
    jacobiConnection, Matrix.neg_mulVec, Matrix.mulVec_mulVec, sub_eq_add_neg]
  exact add_comm _ _

theorem normalChartField_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : HasDerivAt a (b t) t) :
    HasDerivAt (normalChartField g c e a) (normalChartFieldRate g c e a b t) t := by
  have hE := normalChartFrame_hasDerivAt g c e t hc
  have hentries (i j : Fin 4) : HasDerivAt
      (fun s => frameChartMatrix g c (parallelFrameFlowMap g 0 s e) i j)
      (-(jacobiConnection
        (fun k => connectionMatrix g c k (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
        (fun k => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) k 0) *
          frameChartMatrix g c (parallelFrameFlowMap g 0 t e)) i j) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j
  rw [normalChartFieldRate_eq]
  exact hasDerivAt_parallel_frameVector _ _ _ _ t hentries
    (hasDerivAt_normal_lift a (b t) t ha)

theorem normalChartField_toLp_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : HasDerivAt a (b t) t) :
    HasDerivAt (fun s => WithLp.toLp 2 (normalChartField g c e a s))
      (WithLp.toLp 2 (normalChartFieldRate g c e a b t)) t := by
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt t (normalChartField_hasDerivAt g c e a b t hc ha)
  simpa only [Function.comp_def] using! h

theorem normalChartField_change (g : SmoothMetric M) (c d : M)
    (e : FrameBundle g) (a : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    normalChartField g d e a t =
      chartTransitionMatrix c d (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base) *ᵥ
        normalChartField g c e a t := by
  unfold normalChartField
  rw [Matrix.mulVec_mulVec, frameChartMatrix_change g c d _ hc hd]

private theorem continuousOn_normal_lift (a : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (ha : ContinuousOn a S) :
    ContinuousOn (fun s => (Fin.cons (0 : ℝ) (a s) : Fin 4 → ℝ)) S := by
  apply continuousOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuousOn_const
  · exact continuousOn_pi.mp ha j

private theorem continuousOn_matrixVector {S : Set ℝ} {A : ℝ → Mat4}
    {a : ℝ → JacobiCoordinateVector} (hA : ContinuousOn A S) (ha : ContinuousOn a S) :
    ContinuousOn (fun t => A t *ᵥ a t) S := by
  apply continuousOn_pi.mpr
  intro i
  unfold Matrix.mulVec dotProduct
  apply continuousOn_finsetSum
  intro j _
  exact (continuousOn_pi.mp (continuousOn_pi.mp hA i) j).mul (continuousOn_pi.mp ha j)

theorem normalChartFrame_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (fun t => frameChartMatrix g c (parallelFrameFlowMap g 0 t e)) S := by
  intro t ht
  exact (normalChartFrame_hasDerivAt g c e t (hc t ht)).continuousAt.continuousWithinAt

theorem normalChartFrameRate_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (normalChartFrameRate g c e) S := by
  intro t ht
  have hs : ContinuousAt (fun s : ℝ =>
      frameCoordinateState g c (parallelFrameFlowMap g 0 s e)) t :=
    (frameCoordinateState_continuousAt g c (parallelFrameFlowMap g 0 t e)
      (hc t ht)).comp (f := fun s : ℝ => parallelFrameFlowMap g 0 s e)
        (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt
  have hp : (frameCoordinateState g c (parallelFrameFlowMap g 0 t e)).1 ∈
      (chartAt FourSpace c).target := (chartAt FourSpace c).map_source (hc t ht)
  have hV : ContinuousAt (fun s : ℝ => parallelFrameVectorField g c 0
      (frameCoordinateState g c (parallelFrameFlowMap g 0 s e))) t :=
    (parallelFrameVectorField_contDiffAt g c 0 _ hp).continuousAt.comp
      (f := fun s : ℝ => frameCoordinateState g c (parallelFrameFlowMap g 0 s e)) hs
  exact hV.snd.continuousWithinAt

theorem normalChartField_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a S) : ContinuousOn (normalChartField g c e a) S :=
  continuousOn_matrixVector (normalChartFrame_continuousOn g c e S hc)
    (continuousOn_normal_lift a S ha)

theorem normalChartFieldRate_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (normalChartFieldRate g c e a b) S :=
  (continuousOn_matrixVector (normalChartFrameRate_continuousOn g c e S hc)
    (continuousOn_normal_lift a S ha)).add
    (continuousOn_matrixVector (normalChartFrame_continuousOn g c e S hc)
      (continuousOn_normal_lift b S hb))

/-- The actual coordinate index is the matrix index for every prescribed
normal value and normal derivative; the ordinary derivative is constructed. -/
theorem normalChartField_index (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (a b : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    chartEnergyIndexDensity g c (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
      (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0)
      (normalChartField g c e a t) (normalChartFieldRate g c e a b t) =
    normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t) := by
  apply actual_coordinateIndexDensity_normal g c (parallelFrameFlowMap g 0 t e) hc
  rw [normalChartFieldRate_eq]
  exact sub_add_cancel _ _

theorem normalChartField_index_continuousOn (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t =>
      chartEnergyIndexDensity g c (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
        (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0)
        (normalChartField g c e a t) (normalChartFieldRate g c e a b t)) S := by
  have hR : Continuous (fun t =>
      (1 : NormalMatrix) + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) :=
    continuous_const.add ((actual_frameCurvature_continuous g hRic).comp
      (parallelFrameFlowMap_curve_continuous g 0 e))
  have hN : ContinuousOn (fun t => normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t)) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hb.domRestrict.dotProduct hb.domRestrict).sub
      (((hR.comp continuous_subtype_val).matrix_mulVec ha.domRestrict).dotProduct ha.domRestrict)
  apply hN.congr
  intro t ht
  exact normalChartField_index g c e a b t (hc t ht)

theorem normalChartField_index_intervalIntegrable (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (s t : ℝ)
    (hc : ∀ r ∈ uIcc s t,
      (parallelFrameFlowMap g 0 r e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a (uIcc s t)) (hb : ContinuousOn b (uIcc s t)) :
    IntervalIntegrable (fun r =>
      chartEnergyIndexDensity g c (chartAt FourSpace c (parallelFrameFlowMap g 0 r e).base)
        (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 r e) i 0)
        (normalChartField g c e a r) (normalChartFieldRate g c e a b r))
      MeasureTheory.volume s t :=
  (normalChartField_index_continuousOn g hRic c e a b (uIcc s t) hc ha hb).intervalIntegrable

end
end PositiveEinsteinFour.Geometry
end


section

/-! Common geometric domain for normal-frame slices over an open set of
actual frames. Exponential agreement holds throughout the same ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem HeatRadialFrameFlow.kinetic_eq_from {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    {a : CotangentCoordinates} (K : KineticLocalFlow g c a) (hT : K.time ≤ F.time)
    (v : FourSpace) (q : CoordinateFrameSpace)
    (hv : (v, q) ∈ closedBall (0, p) F.radius)
    (hK : heatRadialCotangentState g c v q ∈ ball a K.radius)
    (t : ℝ) (ht : t ∈ Ioo (-K.time) K.time) :
    K.map (heatRadialCotangentState g c v q, t) =
      heatRadialCotangentState g c v (F.map ((v, q), t)).2 := by
  exact K.eq_on _ hK
    (fun s => heatRadialCotangentState g c v (F.map ((v, q), s)).2)
    (by rw [F.initial (v, q) hv])
    (fun s hs => F.cotangent_derivative (v, q) hv s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩) ht

theorem exists_heatRadialFrameCommonDomain (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, e'.base ∈ (chartAt FourSpace c).source ∧
          ∀ v ∈ ball (0 : FourSpace) r,
            ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (v, frameCoordinateState g c e') ∧
            (t⁻¹ • v, frameCoordinateState g c e') ∈ closedBall (0, frameCoordinateState g c e) F.radius ∧
            (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1 ∈ (chartAt FourSpace c).target ∧
            (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).2ᵀ *
              metricInChart g c (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1 *
                (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).2 = 1 ∧
            (heatRadialFrameFamily F t (v, frameCoordinateState g c e')).1 =
              chartAt FourSpace c (frameExponential g o e' v) := by
  let p := frameCoordinateState g c e
  have hp : p.1 ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source he
  obtain ⟨F₀⟩ := exists_heatRadialFrameFlow g c p hp
  obtain ⟨K₀⟩ := exists_kineticLocalFlow g c (p.1, 0) hp
  let δ := min F₀.time K₀.time
  have hδ : 0 < δ := lt_min F₀.time_pos K₀.time_pos
  let F := F₀.restrictTime δ hδ (min_le_left _ _)
  let K := K₀.restrictTime δ hδ (min_le_right _ _)
  obtain ⟨t, ht, htI, R, hR, hfamily⟩ := F.exists_joint_frame_family
  obtain ⟨V, hV, heV, ε, hε, hendpoint⟩ := K.common_exponential_endpoint g o c e he
  obtain ⟨S, hS, hdomain⟩ := heatRadialCotangentState_common_domain g c p hp K.radius K.radius_pos
  have hcoord : {e' : FrameBundle g | frameCoordinateState g c e' ∈ ball p (min R S)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g c e he).preimage_mem_nhds
      (ball_mem_nhds _ (lt_min hR hS))
  obtain ⟨U, hUV, hU, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hV.mem_nhds heV) hcoord)
  let r := min R (t * min ε S) / 2
  have hr : 0 < r := half_pos (lt_min hR (mul_pos ht (lt_min hε hS)))
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hR (mul_pos ht (lt_min hε hS))))).trans
    (min_le_left _ _)
  have hrT : r ≤ t * min ε S := (half_le_self (le_of_lt (lt_min hR (mul_pos ht (lt_min hε hS))))).trans
    (min_le_right _ _)
  refine ⟨F, t, ht, htI, U, hU, heU, r, hr, ?_⟩
  intro e' he'
  obtain ⟨he'V, hclose⟩ := hUV he'
  obtain ⟨he'c, he'endpoint⟩ := hendpoint e' he'V
  refine ⟨he'c, ?_⟩
  intro v hv
  let q := frameCoordinateState g c e'
  have hvnorm : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hv
  have hzR : (v, q) ∈ ball (0, p) R := by
    change max (dist v 0) (dist q p) < R
    exact max_lt (by simpa only [dist_zero_right] using hvnorm.trans_le hrR)
      ((show dist q p < min R S from hclose).trans_le (min_le_left _ _))
  obtain ⟨hreg, hFinit, hc, hg⟩ := hfamily (v, q) hzR
  have hscaled : ‖t⁻¹ • v‖ < min ε S := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_lt_iff₀ ht).mpr (hvnorm.trans_le hrT)
  have hKinit : heatRadialCotangentState g c (t⁻¹ • v) q ∈ ball (p.1, 0) K.radius :=
    hdomain _ (hscaled.trans_le (min_le_right _ _)) q
      ((show dist q p < min R S from hclose).trans_le (min_le_right _ _))
  have hkin := congrArg Prod.fst (F.kinetic_eq_from K le_rfl (t⁻¹ • v) q hFinit hKinit t htI)
  have hexp := he'endpoint (t⁻¹ • v) (hscaled.trans_le (min_le_left _ _)) t htI ht
  rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at hexp
  rw [heatRadialCotangentState_frame g c e' he'c] at hkin
  refine ⟨hreg, hFinit, hc, hg.trans (frameChartMatrix_normalizes g c e' he'c), ?_⟩
  exact hkin.symm.trans hexp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial scaling identifies the endpoint derivative with the actual
horizontal frame field. This is the radial parallel-transport identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.scaling_eventually {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (v : FourSpace) (hv : (v, p) ∈ ball (0, p) F.radius)
    (t : ℝ) (ht : 0 < t) (htF : t < F.time) :
    ∀ᶠ r : ℝ in 𝓝 1,
      F.map ((r • v, p), t) = heatRadialDirectionScale r (F.map ((v, p), r * t)) := by
  let ε := (F.time + t) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [F.time_pos]
  have htε : t < ε := by dsimp [ε]; linarith
  have hεF : ε < F.time := by dsimp [ε]; linarith
  let G := F.restrictTime ε hε hεF.le
  have hbase : ∀ᶠ r : ℝ in 𝓝 1, (r • v, p) ∈ ball (0, p) F.radius := by
    have hc : Continuous (fun r : ℝ => (r • v, p)) :=
      (continuous_id.smul continuous_const).prodMk continuous_const
    have hc1 : ContinuousAt (fun r : ℝ => (r • v, p)) 1 := hc.continuousAt
    exact hc1.preimage_mem_nhds (by
      simpa only [one_smul] using! isOpen_ball.mem_nhds hv)
  have htime : ∀ᶠ r : ℝ in 𝓝 1, r * ε < F.time := by
    have hc : Continuous (fun r : ℝ => r * ε) := continuous_id.mul continuous_const
    have hc1 : ContinuousAt (fun r : ℝ => r * ε) 1 := hc.continuousAt
    exact hc1.preimage_mem_nhds (by
      simpa only [one_mul] using isOpen_Iio.mem_nhds hεF)
  filter_upwards [hbase, htime, eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)]
    with r hrbase hrtime hrpos
  have hsol (s : ℝ) (hs : s ∈ Ioo (-G.time) G.time) :
      HasDerivAt (fun u => heatRadialDirectionScale r (F.map ((v, p), r * u)))
        (heatRadialFrameField g c (heatRadialDirectionScale r (F.map ((v, p), r * s)))) s := by
    apply hasDerivAt_heatRadialDirectionScale g c (fun u => F.map ((v, p), u)) r s
    apply F.derivative (v, p) (ball_subset_closedBall hv)
    change -ε < s ∧ s < ε at hs
    constructor
    · have hh := mul_lt_mul_of_pos_left hs.1 hrpos
      nlinarith
    · have hh := mul_lt_mul_of_pos_left hs.2 hrpos
      nlinarith
  have hzero : heatRadialDirectionScale r (F.map ((v, p), r * 0)) = (r • v, p) := by
    rw [mul_zero, F.initial (v, p) (ball_subset_closedBall hv)]
    rfl
  exact G.eq_on (r • v, p) (ball_subset_closedBall hrbase) _ hzero hsol
    ⟨by change -ε < t; linarith, htε⟩

theorem heatRadialFrameEndpoint_radial_derivative {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (t : ℝ) (ht : 0 < t) (htF : t < F.time) (x : FourSpace)
    (hx : (t⁻¹ • x, p) ∈ ball (0, p) F.radius)
    (hP : DifferentiableAt ℝ (heatRadialFrameEndpoint F t) x) :
    fderiv ℝ (heatRadialFrameEndpoint F t) x x =
      (heatRadialFrameField g c (x, heatRadialFrameEndpoint F t x)).2 := by
  let v := t⁻¹ • x
  let q : HeatRadialFrameSpace := (v, p)
  have htI : t ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], htF⟩
  have heq : (fun r : ℝ => heatRadialFrameEndpoint F t (r • x)) =ᶠ[𝓝 1]
      (fun r => (F.map (q, r * t)).2) := by
    filter_upwards [F.scaling_eventually v hx t ht htF] with r hr
    have hi : t⁻¹ • (r • x) = r • v := by simp only [v, smul_smul, mul_comm]
    change (F.map ((t⁻¹ • (r • x), p), t)).2 = _
    rw [hi, hr]
    rfl
  have hs : HasDerivAt (fun r : ℝ => r • x) x 1 := by
    have h := (ContinuousLinearMap.toSpanSingleton ℝ x).hasFDerivAt.comp_hasDerivAt
      1 (hasDerivAt_id 1)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      Function.comp_def, id_eq] using! h
  have hleft : HasDerivAt (fun r : ℝ => heatRadialFrameEndpoint F t (r • x))
      (fderiv ℝ (heatRadialFrameEndpoint F t) x x) 1 := by
    have hPx : HasFDerivAt (heatRadialFrameEndpoint F t)
        (fderiv ℝ (heatRadialFrameEndpoint F t) x) ((1 : ℝ) • x) := by
      simpa only [one_smul] using hP.hasFDerivAt
    exact hPx.comp_hasDerivAt 1 hs
  have hright : HasDerivAt (fun r : ℝ => (F.map (q, r * t)).2)
      (t • (heatRadialFrameField g c (F.map (q, t))).2) 1 := by
    have hd : HasDerivAt (fun s => (F.map (q, s)).2)
        (heatRadialFrameField g c (F.map (q, t))).2 t :=
      (F.derivative q (ball_subset_closedBall hx) t htI).snd
    have hd' : HasDerivAt (fun s => (F.map (q, s)).2)
        (heatRadialFrameField g c (F.map (q, t))).2 (id 1 * t) := by
      simpa only [id_eq, one_mul] using hd
    have h := hd'.scomp 1
      ((hasDerivAt_id 1).mul_const t)
    simpa only [one_mul, one_mul, id_eq, Function.comp_def] using! h
  have hd := hleft.unique (hright.congr_of_eventuallyEq heq)
  rw [hd]
  have hdir : (F.map (q, t)).1 = t⁻¹ • x := F.direction q (ball_subset_closedBall hx) t htI
  have hscale : heatRadialDirectionScale t (F.map (q, t)) =
      (x, heatRadialFrameEndpoint F t x) := by
    apply Prod.ext
    · change t • (F.map (q, t)).1 = x
      rw [hdir, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    · rfl
  exact (congrArg Prod.snd (heatRadialFrameField_scale g c t (F.map (q, t)))).symm.trans
    (congrArg (fun z => (heatRadialFrameField g c z).2) hscale)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric speed of an actual C1 curve is continuous. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metric_curve_speed_continuous (g : SmoothMetric M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ) :
    Continuous (fun t => metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1)) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ => (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hv : Continuous (fun t =>
      (⟨γ t, mfderiv 𝓘(ℝ, ℝ) I4 γ t 1⟩ : TangentBundle I4 M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hinput.continuous
  have hi := hv.inner_bundle hv
  have hs := Real.continuous_sqrt.comp hi
  change Continuous (fun t => Real.sqrt (g.inner (γ t)
    (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1))) at hs
  simpa only [metricTangentNorm_eq_sqrt] using hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonzero parallel normal field has strictly negative index on every
positive-length geodesic segment in positive sectional curvature. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix SectionalPlane MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_normal_curvature_positive (hsec : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((1 + frameCurvatureField g e) *ᵥ v) := by
  have heq : v ⬝ᵥ ((1 + frameCurvatureField g e) *ᵥ v) =
      sectionalValue (frameCurvature g e.base e.frame)
        (normalCoordinates v) (coordinateVector 0) := by
    simpa only [star_trivial] using frameJacobiMatrix_quadratic e v
  rw [heq]
  have hu : normalCoordinates v ≠ 0 := normalCoordinates_ne_zero hv
  have hz : coordinateVector (0 : Fin 4) ≠ 0 := by
    intro he
    have h := congrArg (fun w : FourSpace => w 0) he
    norm_num [coordinateVector] at h
  have hlin : LinearIndependent ℝ ![normalCoordinates v, coordinateVector 0] := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i
      · exact hu
      · exact hz
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact normalCoordinates_orthogonal v
      · change inner ℝ (coordinateVector 0) (normalCoordinates v) = 0
        rw [real_inner_comm]
        exact normalCoordinates_orthogonal v
      · exact False.elim (hij rfl)
  rw [sectionalValue_frame]
  exact e.frame.sectional_pos hsec _ _ hlin

variable [T3Space M] [CompactSpace M]

theorem parallel_normal_index_negative (hRic : RicciThree g) (hsec : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (v : Fin 3 → ℝ) (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) v 0) < 0 := by
  have hc : Continuous (fun t => normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) v 0) := by
    apply continuous_normalIndexDensity
    · exact actualJacobiCurvature_continuous g hRic e
    · exact continuous_const
    · exact continuous_const
  have hn (t : ℝ) : normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) v 0 < 0 := by
    rw [normalIndexDensity]
    simp only [dotProduct_zero,zero_sub]
    rw [dotProduct_comm]
    exact neg_neg_of_pos (actual_normal_curvature_positive hsec _ v hv)
  simpa only [intervalIntegral.integral_zero] using
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      hc.continuousOn continuousOn_const (fun t _ => (hn t).le)
      ⟨a,⟨le_rfl,hab.le⟩,hn a⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The inverse radial first variation in the actual metric at the endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_center_inner (g : SmoothMetric M) (d : M) (E : FrameBundle g)
    (hd : E.base = d) (a : FourSpace) :
    (fun i => frameChartMatrix g d E i 0) ⬝ᵥ
      (metricInChart g d (chartAt FourSpace d d) *ᵥ WithLp.ofLp a) =
      g.inner d (E.frame.vector 0) a := by
  cases E with
  | mk x F =>
    change x = d at hd
    subst x
    have hcol := frameChart_column_eq_derivative g d (⟨d,F⟩ : FrameBundle g) 0
      (mem_chart_source FourSpace d)
    rw [chartForwardOperator_center] at hcol
    have hp := metricInChart_center_pairing g d
      (fun i => frameChartMatrix g d (⟨d,F⟩ : FrameBundle g) i 0) (WithLp.ofLp a)
    rw [hcol,WithLp.toLp_ofLp] at hp
    exact hp

variable [T3Space M] [CompactSpace M]

theorem exists_exponential_log_center (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (d : M) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hd : (parallelFrameFlowMap g 0 t e).base = d) :
    ∃ C : OpenPartialHomeomorph FourSpace FourSpace,
      (C : FourSpace → FourSpace) = (fun v => chartAt FourSpace d (frameExponential g o e v)) ∧
      t • coordinateVector 0 ∈ C.source ∧
      ∀ a : FourSpace, HasDerivAt
        (fun ε : ℝ => ‖C.symm (chartAt FourSpace d d + ε • a)‖ ^ 2)
        (2 * t * g.inner d ((parallelFrameFlowMap g 0 t e).frame.vector 0) a) 0 := by
  obtain ⟨C,hC,hv,hder⟩ := exists_exponential_log_first_variation g o hRic e he d t ht htc
    (hd ▸ mem_chart_source FourSpace d)
  refine ⟨C,hC,hv,?_⟩
  intro a
  have h := hder a
  rw [hd,frameChart_center_inner g d _ hd a] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The open polar parameter domain before the first conjugate point, and
actual local exponential charts in all of its directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def framePolarDomain (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : Set (Directions × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < actualFirstConjugateTime g hRic
    (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))}

theorem framePolarDomain_isOpen (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : IsOpen (framePolarDomain g hRic e) := by
  have hframe : Continuous (fun p : Directions × ℝ =>
      e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1))) :=
    (continuous_frameRotate g).comp (continuous_const.prodMk
      (continuous_orientedToOrthogonal.comp
        (continuous_directionOrientedMatrix.comp continuous_fst)))
  exact (actual_preconjugate_radial_isOpen g hRic).preimage
    (continuous_snd.prodMk hframe)

theorem framePolarDomain_time_le_pi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (p : Directions × ℝ) (hp : p ∈ framePolarDomain g hRic e) :
    p.2 < Real.pi :=
  hp.2.trans_le (actualFirstConjugateTime_le_pi g hRic _)

theorem frameExponential_polar_localChart (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : Directions) (t : ℝ)
    (hp : (q, t) ∈ framePolarDomain g hRic e) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      t • q.val ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hf : e.rotate (orientedToOrthogonal Q) ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  obtain ⟨C, hx, hC⟩ := frameExponential_preconjugate_localChart g o hRic
    (e.rotate (orientedToOrthogonal Q)) hf t hp.1 hp.2
  let D := L.symm.toHomeomorph.toOpenPartialHomeomorph.trans C
  have hinv : L.symm (t • q.val) = t • coordinateVector 0 := by
    rw [← hfirst, map_smul, L.symm_apply_apply]
  refine ⟨D, ?_, ?_⟩
  · change t • q.val ∈ Set.univ ∩ L.symm ⁻¹' C.source
    refine ⟨Set.mem_univ _, ?_⟩
    change L.symm (t • q.val) ∈ C.source
    rw [hinv]
    exact hx
  · intro v hv
    change C (L.symm v) = frameExponential g o e v
    have h := hC hv.2
    change C (L.symm v) = frameExponential g o (e.rotate (orientedToOrthogonal Q)) (L.symm v) at h
    rw [frameExponential_rotate g o e Q] at h
    change C (L.symm v) = frameExponential g o e (L (L.symm v)) at h
    rwa [L.apply_symm_apply] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth approximations to radial distance have differential bounded by
the actual metric speed after applying the exponential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular
open scoped Manifold ContDiff _root_.Topology InnerProductSpace

noncomputable section

def smoothRadialNorm (ε : ℝ) (v : FourSpace) : ℝ := Real.sqrt (‖v‖ ^ 2 + ε ^ 2)

theorem smoothRadialNorm_pos (ε : ℝ) (hε : 0 < ε) (v : FourSpace) :
    0 < smoothRadialNorm ε v := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem smoothRadialNorm_bounds (ε : ℝ) (hε : 0 < ε) (v : FourSpace) :
    ‖v‖ ≤ smoothRadialNorm ε v ∧ smoothRadialNorm ε v ≤ ‖v‖ + ε := by
  have hsq : smoothRadialNorm ε v ^ 2 = ‖v‖ ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hp := (smoothRadialNorm_pos ε hε v).le
  constructor <;> nlinarith [norm_nonneg v, sq_nonneg ε]

theorem smoothRadialNorm_hasFDerivAt (ε : ℝ) (hε : 0 < ε) (v : FourSpace) :
    HasFDerivAt (smoothRadialNorm ε)
      ((smoothRadialNorm ε v)⁻¹ • innerSL ℝ v) v := by
  have hpos : 0 < ‖v‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have h := ((hasStrictFDerivAt_norm_sq v).hasFDerivAt.add_const (ε ^ 2)).sqrt hpos.ne'
  have hcoef : (1 / (2 * Real.sqrt (‖v‖ ^ 2 + ε ^ 2))) * 2 =
      (Real.sqrt (‖v‖ ^ 2 + ε ^ 2))⁻¹ := by
    field_simp
  have hD : (1 / (2 * Real.sqrt (‖v‖ ^ 2 + ε ^ 2))) • (2 • innerSL ℝ v) =
      (Real.sqrt (‖v‖ ^ 2 + ε ^ 2))⁻¹ • innerSL ℝ v := by
    ext w
    simp only [two_smul, _root_.smul_apply, _root_.add_apply,
      smul_eq_mul]
    change (1 / (2 * Real.sqrt (‖v‖ ^ 2 + ε ^ 2))) * (⟪v, w⟫_ℝ + ⟪v, w⟫_ℝ) =
      (Real.sqrt (‖v‖ ^ 2 + ε ^ 2))⁻¹ * ⟪v, w⟫_ℝ
    rw [← two_mul, ← mul_assoc, hcoef]
  rw [hD] at h
  exact h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem smoothRadialNorm_exponential_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (ε : ℝ) (hε : 0 < ε) (v w : FourSpace) :
    |fderiv ℝ (smoothRadialNorm ε) v w| ≤
      metricTangentNorm g (frameExponential g o e v)
        (mfderiv I4 I4 (frameExponential g o e) v w) := by
  rw [(smoothRadialNorm_hasFDerivAt ε hε v).fderiv]
  change |(smoothRadialNorm ε v)⁻¹ * ⟪v, w⟫_ℝ| ≤ _
  by_cases hv : v = 0
  · subst v
    simp only [inner_zero_left, mul_zero, abs_zero]
    rw [metricTangentNorm_eq_sqrt]
    exact Real.sqrt_nonneg _
  · let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hvq : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hpair := frameExponential_radial_pairing_le g o hRic e he q ‖v‖ hr w
    rw [hvq] at hpair
    have hinner : ⟪v, w⟫_ℝ = ‖v‖ * ⟪q.val, w⟫_ℝ := by
      calc
        _ = ⟪‖v‖ • q.val, w⟫_ℝ := congrArg (fun z => ⟪z, w⟫_ℝ) hvq.symm
        _ = _ := real_inner_smul_left _ _ _
    have hfac : (smoothRadialNorm ε v)⁻¹ * ‖v‖ ≤ 1 := by
      rw [← div_eq_inv_mul]
      exact (div_le_one (smoothRadialNorm_pos ε hε v)).mpr
        (smoothRadialNorm_bounds ε hε v).1
    rw [hinner, ← mul_assoc, abs_mul,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (smoothRadialNorm_pos ε hε v).le)
        (norm_nonneg v))]
    exact (mul_le_of_le_one_left (abs_nonneg _) hfac).trans hpair

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual unit geodesic satisfies the ordinary coordinate geodesic
equation in every fixed chart containing the point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def geodesicChartVelocity (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (t : ℝ) : JacobiCoordinateVector :=
  fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0

theorem geodesicChartVelocity_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (geodesicChartVelocity g c e)
      (-(jacobiConnection
        (fun i => connectionMatrix g c i (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
        (geodesicChartVelocity g c e t) *ᵥ geodesicChartVelocity g c e t)) t := by
  have hE := normalChartFrame_hasDerivAt g c e t hc
  apply hasDerivAt_pi.mpr
  intro i
  have hi := hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) 0
  simpa only [geodesicChartVelocity, normalChartFrameRate, parallelFrameVectorField,
    parallelFrameConnection, frameCoordinateState, jacobiConnection,
    Matrix.neg_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.neg_apply] using hi

theorem geodesicChartPosition_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => chartAt FourSpace c (parallelFrameFlowMap g 0 s e).base)
      (WithLp.toLp 2 (geodesicChartVelocity g c e t)) t :=
  frameGeodesic_chart_derivative g 0 e c t hc

theorem geodesicChart_derivatives (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => chartAt FourSpace c (parallelFrameFlowMap g 0 s e).base)
      (WithLp.toLp 2 (geodesicChartVelocity g c e t)) t ∧
    HasDerivAt (geodesicChartVelocity g c e)
      (-(jacobiConnection
        (fun i => connectionMatrix g c i (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
        (geodesicChartVelocity g c e t) *ᵥ geodesicChartVelocity g c e t)) t :=
  ⟨geodesicChartPosition_hasDerivAt g c e t hc, geodesicChartVelocity_hasDerivAt g c e t hc⟩

theorem geodesicChartPosition_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (fun t => chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base) S :=
  fun t ht => (geodesicChartPosition_hasDerivAt g c e t (hc t ht)).continuousAt.continuousWithinAt

theorem geodesicChartVelocity_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (geodesicChartVelocity g c e) S :=
  fun t ht => (geodesicChartVelocity_hasDerivAt g c e t (hc t ht)).continuousAt.continuousWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal frame satisfies the radial horizontal equation
throughout a neighborhood of zero, with the finite regularity needed for
the heat coefficient construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem exists_heatNormalFrame_transport (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ P : FourSpace → CoordinateFrameSpace,
      ContDiffAt ℝ 12 P 0 ∧ P 0 = frameCoordinateState g c e ∧
      ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
        (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
        (P x).1 ∈ (chartAt FourSpace c).target ∧
        (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
        DifferentiableAt ℝ P x ∧
        fderiv ℝ P x x = (heatRadialFrameField g c (x, P x)).2 := by
  obtain ⟨F, t, ht, htI, hreg, hbase, hgram⟩ :=
    exists_heatRadialNormalFrame_flow g o c e he 12
  let p := frameCoordinateState g c e
  let P := heatRadialFrameEndpoint F t
  let A : FourSpace → HeatRadialFrameSpace := fun x => (t⁻¹ • x, p)
  have hL : Continuous (fun x : FourSpace => t⁻¹ • x) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).continuous
  have hA : Continuous A := hL.prodMk continuous_const
  have hA0 : A 0 = (0, p) := by simp [A]
  have hinit : ∀ᶠ x in 𝓝 (0 : FourSpace), A x ∈ ball (0, p) F.radius :=
    hA.continuousAt.preimage_mem_nhds (by
      rw [hA0]
      exact ball_mem_nhds (0, p) F.radius_pos)
  have hdiff : ∀ᶠ x in 𝓝 (0 : FourSpace), DifferentiableAt ℝ P x := by
    have hh := (hreg.of_le (show (1 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by simp)
    filter_upwards [hh] with x hx
    exact hx.differentiableAt one_ne_zero
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
      (P x).1 ∈ (chartAt FourSpace c).target ∧
      (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
      DifferentiableAt ℝ P x ∧ A x ∈ ball (0, p) F.radius := by
    filter_upwards [hbase, hgram, hdiff, hinit] with x hb hg hd hi
    exact ⟨hb, hg.1, hg.2, hd, hi⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨P, hreg, heatRadialFrameEndpoint_zero F t htI, r, hr, ?_⟩
  intro x hx
  obtain ⟨hb, hc, hg, hd, hi⟩ := hball hx
  exact ⟨hb, hc, hg, hd, heatRadialFrameEndpoint_radial_derivative F t ht htI.2 x hi hd⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating Gauss' lemma bounds the radial displacement of a lifted
C1 curve by the length of its actual exponential image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_curve_derivative (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (α : ℝ → FourSpace) (hα : ContDiff ℝ 1 α) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1 =
      mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t) := by
  have he := (frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (α t)
  have ha := hα.contMDiff.mdifferentiable one_ne_zero t
  have hc := mfderiv_comp_apply t he ha (1 : ℝ)
  have hader : mfderiv 𝓘(ℝ, ℝ) I4 α t 1 = deriv α t := by
    rw [mfderiv_eq_fderiv, (hα.differentiable one_ne_zero t).hasDerivAt.hasFDerivAt.fderiv]
    exact one_smul ℝ _
  exact hc.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) hader)

theorem frameExponential_radial_displacement_le_length (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (α : ℝ → FourSpace) (hα : ContDiff ℝ 1 α)
    (a b : ℝ) (hab : a ≤ b) (hstart : α a = 0) :
    ‖α b‖ ≤ ∫ t in a..b, metricTangentNorm g (frameExponential g o e (α t))
      (mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1) := by
  let β := fun s => frameExponential g o e (α s)
  have hβ : ContMDiff 𝓘(ℝ, ℝ) I4 1 β :=
    (frameExponential_contMDiff g o e).comp hα.contMDiff
  let B := fun t => metricTangentNorm g (β t) (mfderiv 𝓘(ℝ, ℝ) I4 β t 1)
  have hB : IntervalIntegrable B volume a b :=
    (metric_curve_speed_continuous g β hβ).intervalIntegrable a b
  apply le_of_forall_pos_le_add
  intro ε hε
  let F := fun t => smoothRadialNorm ε (α t)
  have hFder (t : ℝ) : HasDerivAt F
      (fderiv ℝ (smoothRadialNorm ε) (α t) (deriv α t)) t := by
    have h := (smoothRadialNorm_hasFDerivAt ε hε (α t)).comp_hasDerivAt t
      (hα.differentiable one_ne_zero t).hasDerivAt
    rw [(smoothRadialNorm_hasFDerivAt ε hε (α t)).fderiv]
    exact h
  have hFc : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hFder t).continuousAt)
  have hFi : DifferentiableOn ℝ F (Ioo a b) := fun t _ =>
    (hFder t).differentiableAt.differentiableWithinAt
  have hbound : ∀ᵐ t, t ∈ Ioo a b → ‖deriv F t‖ ≤ B t := by
    filter_upwards [] with t _
    rw [(hFder t).deriv, Real.norm_eq_abs]
    have h := smoothRadialNorm_exponential_bound g o hRic e he ε hε (α t) (deriv α t)
    have heq : B t = metricTangentNorm g (frameExponential g o e (α t))
        (mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t)) :=
      congrArg (metricTangentNorm g (frameExponential g o e (α t)))
        (frameExponential_curve_derivative g o e α hα t)
    rw [heq]
    exact h
  have hInt := norm_sub_le_integral_of_norm_deriv_le_of_le
    hab hFc.continuousOn hFi hbound hB
  have hfa : F a = ε := by
    simp [F, smoothRadialNorm, hstart, Real.sqrt_sq_eq_abs, abs_of_pos hε]
  have hfb : ‖α b‖ ≤ F b := (smoothRadialNorm_bounds ε hε (α b)).1
  have hs : F b - F a ≤ ∫ t in a..b, B t :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hInt)
  change ‖α b‖ ≤ (∫ t in a..b, B t) + ε
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second variation on a fixed-chart segment of the actual unit
geodesic.  The position, velocity and normal-field derivatives are obtained
from the constructed flow; only the prescribed second jet is differentiated
as input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem normalChartField_second_integral (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ)
    (u q : ℝ → JacobiCoordinateVector) (r s : ℝ)
    (hc : ∀ t ∈ uIcc r s,
      (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ∀ t ∈ uIcc r s, HasDerivAt a (b t) t)
    (hb : ContinuousOn b (uIcc r s))
    (hu : ∀ t ∈ uIcc r s, HasDerivAt u (q t) t)
    (hS : IntervalIntegrable (fun t => chartEnergySecondDensity g c
      (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
      (normalChartField g c e a t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e a b t) (u t) (q t)) volume r s) :
    (∫ t in r..s, chartEnergySecondDensity g c
      (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
      (normalChartField g c e a t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e a b t) (u t) (q t)) =
        (∫ t in r..s, normalIndexDensity
          (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t)) +
        chartEnergyBoundary g c
          (chartAt FourSpace c (parallelFrameFlowMap g 0 s e).base)
          (geodesicChartVelocity g c e s) (normalChartField g c e a s) (u s) -
        chartEnergyBoundary g c
          (chartAt FourSpace c (parallelFrameFlowMap g 0 r e).base)
          (geodesicChartVelocity g c e r) (normalChartField g c e a r) (u r) := by
  have hac : ContinuousOn a (uIcc r s) := fun t ht =>
    (ha t ht).continuousAt.continuousWithinAt
  have hI := normalChartField_index_intervalIntegrable g hRic c e a b r s hc hac hb
  have h := chartEnergySecond_integral g c
    (fun t => chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
    (geodesicChartVelocity g c e) (normalChartField g c e a)
    (normalChartFieldRate g c e a b) u q r s
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
    (fun t ht => geodesicChartPosition_hasDerivAt g c e t (hc t ht))
    (fun t ht => geodesicChartVelocity_hasDerivAt g c e t (hc t ht))
    (fun t ht => normalChartField_hasDerivAt g c e a b t (hc t ht) (ha t ht))
    hu hS hI
  have hindex :
      (∫ t in r..s, chartEnergyIndexDensity g c
        (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
        (geodesicChartVelocity g c e t) (normalChartField g c e a t)
        (normalChartFieldRate g c e a b t)) =
      ∫ t in r..s, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact normalChartField_index g c e a b t (hc t ht)
  rw [hindex] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual pulled-back frame connection has zero radial contraction.
The connection uses the differential of the constructed frame and the
Levi-Civita connection of its base map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalFrameConnection (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (i : Fin 4) (x : FourSpace) : Mat4 :=
  (P x).2⁻¹ * ((fderiv ℝ P x (coordinateVector i)).2 +
    (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      connectionMatrix g c r (P x).1) * (P x).2)

theorem heatNormalFrameConnection_radial (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : fderiv ℝ P x x = (heatRadialFrameField g c (x, P x)).2) :
    (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0 := by
  let D := fderiv ℝ P x
  let V := (P x).2 *ᵥ WithLp.ofLp x
  let C := ∑ r : Fin 4, V r • connectionMatrix g c r (P x).1
  have hdx : D x = (WithLp.toLp 2 V, -(C * (P x).2)) := hP
  have hlin : D x = ∑ i : Fin 4, x i • D (coordinateVector i) := by
    have hx : (∑ i : Fin 4, x i • coordinateVector i) = x :=
      sum_coordinateVector (WithLp.ofLp x)
    calc
      D x = D (∑ i : Fin 4, x i • coordinateVector i) := congrArg D hx.symm
      _ = _ := by rw [map_sum]; simp only [map_smul]
  have hbase : (∑ i : Fin 4, x i • (D (coordinateVector i)).1) = WithLp.toLp 2 V := by
    let L := ContinuousLinearMap.fst ℝ FourSpace Mat4
    have he := congrArg L (hlin.symm.trans hdx)
    simpa only [map_sum, map_smul] using! he
  have hframe : (∑ i : Fin 4, x i • (D (coordinateVector i)).2) = -(C * (P x).2) := by
    let L := ContinuousLinearMap.snd ℝ FourSpace Mat4
    have he := congrArg L (hlin.symm.trans hdx)
    simpa only [map_sum, map_smul] using! he
  have hcoordinate (r : Fin 4) : (∑ i : Fin 4, x i * (D (coordinateVector i)).1 r) = V r := by
    have h := congrArg (fun v : FourSpace => v r) hbase
    simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      WithLp.ofLp_toLp] using h
  let B := fun i : Fin 4 => ∑ r : Fin 4, (D (coordinateVector i)).1 r •
    connectionMatrix g c r (P x).1
  have hB : (∑ i : Fin 4, x i • B i) = C := by
    change (∑ i : Fin 4, x i • ∑ r : Fin 4, (D (coordinateVector i)).1 r •
      connectionMatrix g c r (P x).1) = _
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_smul, hcoordinate]
  change (∑ i : Fin 4, x i • ((P x).2⁻¹ *
    ((D (coordinateVector i)).2 + B i * (P x).2))) = 0
  calc
    _ = ∑ i : Fin 4, (P x).2⁻¹ *
        (x i • (D (coordinateVector i)).2 + (x i • B i) * (P x).2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_smul_comm, smul_add, smul_mul_assoc]
    _ = (P x).2⁻¹ * ((∑ i : Fin 4, x i • (D (coordinateVector i)).2) +
        (∑ i : Fin 4, x i • B i) * (P x).2) := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, mul_add]
    _ = 0 := by rw [hframe, hB]; simp

variable [T2Space M] [CompactSpace M]

theorem exists_heatNormalFrame_radial_connection (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ P : FourSpace → CoordinateFrameSpace,
      ContDiffAt ℝ 12 P 0 ∧ P 0 = frameCoordinateState g c e ∧
      ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
        (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
        (P x).1 ∈ (chartAt FourSpace c).target ∧
        (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
        DifferentiableAt ℝ P x ∧
        (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0 := by
  obtain ⟨P, hP, hP0, r, hr, h⟩ := exists_heatNormalFrame_transport g o c e he
  refine ⟨P, hP, hP0, r, hr, ?_⟩
  intro x hx
  obtain ⟨hb, hc, hg, hd, hrad⟩ := h x hx
  exact ⟨hb, hc, hg, hd, heatNormalFrameConnection_radial g c P x hrad⟩

end
end PositiveEinsteinFour.Geometry
end

end OAI
