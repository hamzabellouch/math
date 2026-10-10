import OAI.Geometry.EinsteinFour.ConnectionPullback
import OAI.Geometry.EinsteinFour.ContinuousFieldDerivative
import OAI.Geometry.EinsteinFour.CurvatureCoordinateSmoothness
import OAI.Geometry.EinsteinFour.CurvatureTensors02
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.HeatRoughTraceAlgebra
import OAI.Geometry.EinsteinFour.MetricInverseCalculus
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMeasure
import OAI.Geometry.EinsteinFour.WeightedConnectionCurvature
import OAI.Geometry.EinsteinFour.WeylEstimates01
import OAI.Geometry.EinsteinFour.WeylEstimates03
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI


section

/-! The radial length bound for lifts defined only on a compact interval.
Endpoint differentiability is unnecessary. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_radial_interval_le (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (α : ℝ → FourSpace) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn α (Icc a b)) (hd : DifferentiableOn ℝ α (Ioo a b))
    (hBi : IntervalIntegrable (fun t => metricTangentNorm g (frameExponential g o e (α t))
      (mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t))) volume a b) :
    ‖α b‖ - ‖α a‖ ≤ ∫ t in a..b,
      metricTangentNorm g (frameExponential g o e (α t))
        (mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t)) := by
  let B := fun t => metricTangentNorm g (frameExponential g o e (α t))
    (mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t))
  apply le_of_forall_pos_le_add
  intro ε hε
  let F := fun t => smoothRadialNorm ε (α t)
  have hR : Continuous (smoothRadialNorm ε) := continuous_iff_continuousAt.mpr
    (fun v => (smoothRadialNorm_hasFDerivAt ε hε v).continuousAt)
  have hFc : ContinuousOn F (Icc a b) := hR.comp_continuousOn hc
  have hFder (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F
      (fderiv ℝ (smoothRadialNorm ε) (α t) (deriv α t)) t := by
    have ha := (hd t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)
    have h := (smoothRadialNorm_hasFDerivAt ε hε (α t)).comp_hasDerivAt t ha.hasDerivAt
    rw [(smoothRadialNorm_hasFDerivAt ε hε (α t)).fderiv]
    exact h
  have hFi : DifferentiableOn ℝ F (Ioo a b) := fun t ht =>
    (hFder t ht).differentiableAt.differentiableWithinAt
  have hbound : ∀ᵐ t, t ∈ Ioo a b → ‖deriv F t‖ ≤ B t := by
    filter_upwards [] with t ht
    rw [(hFder t ht).deriv, Real.norm_eq_abs]
    exact smoothRadialNorm_exponential_bound g o hRic e he ε hε (α t) (deriv α t)
  have hInt := norm_sub_le_integral_of_norm_deriv_le_of_le hab hFc hFi hbound hBi
  have ha : F a ≤ ‖α a‖ + ε := (smoothRadialNorm_bounds ε hε (α a)).2
  have hb : ‖α b‖ ≤ F b := (smoothRadialNorm_bounds ε hε (α b)).1
  have hs : F b - F a ≤ ∫ t in a..b, B t :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hInt)
  change ‖α b‖ - ‖α a‖ ≤ (∫ t in a..b, B t) + ε
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of matrix inversion in the four-dimensional heat
construction, via the actual determinant and adjugate formulas. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff

noncomputable section

theorem heatMatrixDeterminant_contDiffAt (n : ℕ) (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) x) :
    ContDiffAt ℝ n (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

theorem heatMatrixInverse_contDiffAt (n : ℕ) (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) x) (hdet : (A x).det ≠ 0)
    (i j : Fin 4) : ContDiffAt ℝ n (fun y => (A y)⁻¹ i j) x := by
  have hinv : ContDiffAt ℝ n (fun y => ((A y).det)⁻¹) x :=
    (heatMatrixDeterminant_contDiffAt n A x hA).inv hdet
  have hadj : ContDiffAt ℝ n (fun y => (A y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply heatMatrixDeterminant_contDiffAt
    intro r s
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ n
          (fun _ : FourSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) s) x)
    · simpa only [Matrix.updateRow_ne hr] using hA r s
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-coordinate balls with a C1 inverse, constructed from the actual
exponential and the openness of invertible derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_normal_ball (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 1 C.symm C.target := by
  let : CompleteSpace FourSpace := inferInstance
  obtain ⟨D, hzero, hD⟩ := frameExponential_localChart g o e
  let F := fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v)
  have hF : ContDiffAt ℝ 1 F 0 := frameExponential_chart_contDiffAt_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hunit : IsUnit (fderiv ℝ F 0) := by
    have hd := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    rw [hd.hasFDerivAt.fderiv]
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using
      frameMap_isUnit g e
  have hnearE : ∀ᶠ v in 𝓝 (0 : FourSpace),
      fderiv ℝ F v ∈ range ((↑) : (FourSpace ≃L[ℝ] FourSpace) →
        FourSpace →L[ℝ] FourSpace) :=
    (hF.continuousAt_fderiv one_ne_zero).preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds
        ⟨ContinuousLinearEquiv.ofUnit hunit.unit, hunit.unit_spec⟩)
  have hnear : ∀ᶠ v in 𝓝 (0 : FourSpace), IsUnit (fderiv ℝ F v) := by
    filter_upwards [hnearE] with v hv
    obtain ⟨E, hE⟩ := hv
    exact hE ▸ E.toUnit.isUnit
  have hbase : frameExponential g o e 0 ∈ (chartAt FourSpace e.base).source := by
    rw [frameExponential_zero]
    exact mem_chart_source FourSpace e.base
  have hchart := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
    ((chartAt FourSpace e.base).open_source.mem_nhds hbase)
  have hgood : {v : FourSpace | v ∈ D.source ∧
      frameExponential g o e v ∈ (chartAt FourSpace e.base).source ∧
      IsUnit (fderiv ℝ F v)} ∈ 𝓝 0 := by
    filter_upwards [D.open_source.mem_nhds hzero, hchart, hnear] with v hv hc hu
    exact ⟨hv, hc, hu⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let C := D.restrOpen (ball 0 r) isOpen_ball
  have hsource : C.source = ball 0 r := by
    change D.source ∩ ball 0 r = ball 0 r
    exact inter_eq_right.mpr (fun v hv => (hball hv).1)
  have hC : EqOn C (frameExponential g o e) C.source := fun _ hv => hD hv.1
  refine ⟨r, C, hr, hsource, hC, ?_⟩
  intro y hy
  let v := C.symm y
  have hv : v ∈ C.source := C.map_target hy
  have hvg := hball (hsource ▸ hv)
  have heq : frameExponential g o e v = y := (hC hv).symm.trans (C.right_inv hy)
  have hc := frameExponential_chart_local_inverse_contMDiffAt g o e e.base v C hv hC
    hvg.2.1 hvg.2.2
  rw [heq] at hc
  exact hc.contMDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse-metric and density derivatives from metric compatibility.
These local identities will be applied to the actual normal pullback metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatCompatibleMetric_inverse (G : FourSpace → Mat4) (x : FourSpace)
    (hG : ∀ p q, ContDiffAt ℝ 1 (fun y => G y p q) x) (hdet : (G x).det ≠ 0)
    (C : Mat4) (i : Fin 4) (hC : matrixPartial G i x = Cᵀ * G x + G x * C) :
    matrixPartial (fun y => (G y)⁻¹) i x = -(C * (G x)⁻¹) - (G x)⁻¹ * Cᵀ := by
  let H := fun y => (G y)⁻¹
  have hu : IsUnit (G x).det := isUnit_iff_ne_zero.mpr hdet
  have hD := heatMatrixDeterminant_contDiffAt 1 G x hG
  have hn : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    hD.continuousAt.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hdet)
  have he : (fun y => H y * G y) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hn] with y hy
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy)
  have hdH (p q : Fin 4) : DifferentiableAt ℝ (fun y => H y p q) x :=
    (heatMatrixInverse_contDiffAt 1 G x hG hdet p q).differentiableAt one_ne_zero
  have hdG (p q : Fin 4) : DifferentiableAt ℝ (fun y => G y p q) x :=
    (hG p q).differentiableAt one_ne_zero
  have hp := matrixPartial_congr he i
  rw [matrixPartial_mul H G x hdH hdG i, hC] at hp
  have hz : matrixPartial (fun _ : FourSpace => (1 : Mat4)) i x = 0 := by
    ext p q
    simp [matrixPartial, partialDeriv]
  rw [hz] at hp
  have hh := congrArg (fun A : Mat4 => A * H x) hp
  have ha : (matrixPartial H i x * G x + H x * (Cᵀ * G x + G x * C)) * H x =
      matrixPartial H i x + H x * Cᵀ + C * H x := by
    calc
      _ = matrixPartial H i x * (G x * H x) +
          (H x * Cᵀ) * (G x * H x) + (H x * G x) * (C * H x) := by noncomm_ring
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu]; simp
  rw [ha, zero_mul] at hh
  change matrixPartial H i x = -(C * H x) - H x * Cᵀ
  have hh' : matrixPartial H i x = -(H x * Cᵀ + C * H x) :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hh)
  rw [hh']
  abel

theorem heatCompatibleMetric_density (G : FourSpace → Mat4) (x : FourSpace)
    (hG : ∀ p q, ContDiffAt ℝ 1 (fun y => G y p q) x) (hpos : 0 < (G x).det)
    (C : Mat4) (i : Fin 4) (hC : matrixPartial G i x = Cᵀ * G x + G x * C) :
    partialDeriv (fun y => Real.sqrt (G y).det) i x = C.trace * Real.sqrt (G x).det := by
  let γ := fun t : ℝ => x + t • coordinateVector i
  have hγ : HasDerivAt γ (coordinateVector i) 0 := by
    simpa only [γ, one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have hdG (p q : Fin 4) : HasDerivAt (fun t => G (γ t) p q)
      ((Cᵀ * G x + G x * C) p q) 0 := by
    have hf : HasFDerivAt (fun y => G y p q) (fderiv ℝ (fun y => G y p q) x) (γ 0) := by
      rw [hγ0]
      exact (hG p q).differentiableAt one_ne_zero |>.hasFDerivAt
    have hd := hf.comp_hasDerivAt 0 hγ
    have hc := congrArg (fun A : Mat4 => A p q) hC
    change (fderiv ℝ (fun y => G y p q) x) (coordinateVector i) = _ at hc
    simpa only [Function.comp_def, hc] using! hd
  have hd := hasDerivAt_det_of_components (fun t => G (γ t)) (Cᵀ * G x + G x * C) 0 hdG
  rw [hγ0, determinantDifferential_congruence] at hd
  have hs := hd.sqrt (by simpa only [hγ0] using hpos.ne')
  rw [hγ0] at hs
  have hr : (2 * C.trace * (G x).det) / (2 * Real.sqrt (G x).det) =
      C.trace * Real.sqrt (G x).det := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hpos).ne')).mpr
    calc
      _ = 2 * C.trace * (Real.sqrt (G x).det) ^ 2 := by rw [Real.sq_sqrt hpos.le]
      _ = _ := by ring
  rw [hr] at hs
  have hρ := (heatMatrixDeterminant_contDiffAt 1 G x hG).sqrt hpos.ne'
  have hfρ : HasFDerivAt (fun y => Real.sqrt (G y).det)
      (fderiv ℝ (fun y => Real.sqrt (G y).det) x) (γ 0) := by
    rw [hγ0]
    exact hρ.differentiableAt one_ne_zero |>.hasFDerivAt
  have hρc := hfρ.comp_hasDerivAt 0 hγ
  exact hρc.unique hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Spatial derivatives of a jointly regular family. The center and initial
frame are parameters; differentiation here changes only the normal vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyPartial (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (i : Fin 4) (z : HeatRadialFrameSpace) : CoordinateFrameSpace :=
  fderiv ℝ P z (coordinateVector i, 0)

theorem heatFamilyPartial_slice (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    heatFamilyPartial P i z =
      fderiv ℝ (fun x => P (x, z.2)) z.1 (coordinateVector i) := by
  have harg : HasFDerivAt (fun x : FourSpace => (x, z.2))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd : HasFDerivAt (fun x => P (x, z.2))
      ((fderiv ℝ P z).comp ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) z.1 := hP.hasFDerivAt.comp z.1 harg
  exact (congrArg (fun L : FourSpace →L[ℝ] CoordinateFrameSpace =>
    L (coordinateVector i)) hd.fderiv).symm

theorem heatFamilyPartial_contDiffAt (n : ℕ)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z) (i : Fin 4) :
    ContDiffAt ℝ n (heatFamilyPartial P i) z :=
  (hP.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const

theorem heatFamilyMatrixDeterminant_contDiffAt (n : ℕ)
    (A : HeatRadialFrameSpace → Mat4) (z : HeatRadialFrameSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) z) :
    ContDiffAt ℝ n (fun y => (A y).det) z := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

theorem heatFamilyMatrixInverse_contDiffAt (n : ℕ)
    (A : HeatRadialFrameSpace → Mat4) (z : HeatRadialFrameSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) z) (hdet : (A z).det ≠ 0)
    (i j : Fin 4) : ContDiffAt ℝ n (fun y => (A y)⁻¹ i j) z := by
  have hinv : ContDiffAt ℝ n (fun y => ((A y).det)⁻¹) z :=
    (heatFamilyMatrixDeterminant_contDiffAt n A z hA).inv hdet
  have hadj : ContDiffAt ℝ n (fun y => (A y).adjugate i j) z := by
    simp only [Matrix.adjugate_apply]
    apply heatFamilyMatrixDeterminant_contDiffAt
    intro r s
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ n
          (fun _ : HeatRadialFrameSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) s) z)
    · simpa only [Matrix.updateRow_ne hr] using hA r s
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the actual pulled-back normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormalFrameConnection_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target) (hdet : (P x).2.det ≠ 0)
    (i j k : Fin 4) :
    ContDiffAt ℝ n (fun y => heatNormalFrameConnection g c P i y j k) x := by
  have hP0 : ContDiffAt ℝ n P x := hP.of_le (by exact_mod_cast Nat.le_succ n)
  have hE (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 a b) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP0.snd a) b
  have hEi (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2⁻¹ a b) x :=
    heatMatrixInverse_contDiffAt n (fun y => (P y).2) x hE hdet a b
  have hD : ContDiffAt ℝ n (fun y => fderiv ℝ P y (coordinateVector i)) x :=
    (hP.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const
  have hDE (a b : Fin 4) : ContDiffAt ℝ n
      (fun y => (fderiv ℝ P y (coordinateVector i)).2 a b) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hD.snd a) b
  have hDZ (a : Fin 4) : ContDiffAt ℝ n
      (fun y => (fderiv ℝ P y (coordinateVector i)).1 a) x := by
    let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) a
    exact π.contDiff.contDiffAt.comp x hD.fst
  have hΓ (r a b : Fin 4) : ContDiffAt ℝ n
      (fun y => christoffel g c (P y).1 a r b) x := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => christoffel g c z a r b) x
      ((christoffel_contDiffAt g c (P x).1 hx
        (metricInChart_posDef g c (P x).1 hx).det_pos.ne' a r b).of_le (by simp)) hP0.fst
  change ContDiffAt ℝ n (fun y => ∑ l : Fin 4, (P y).2⁻¹ j l *
    ((fderiv ℝ P y (coordinateVector i)).2 l k +
      ∑ a : Fin 4, (∑ r : Fin 4, (fderiv ℝ P y (coordinateVector i)).1 r *
        christoffel g c (P y).1 l r a) * (P y).2 a k)) x
  apply ContDiffAt.sum
  intro l _
  apply (hEi j l).mul
  apply (hDE l k).add
  apply ContDiffAt.sum
  intro a _
  exact (ContDiffAt.sum (fun r _ => (hDZ r).mul (hΓ r l a))).mul (hE a k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gauss' lemma integrated along a C1 interval path. The nonnegative
integral formulation agrees with the definition of Riemannian path length. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_radial_le_lintegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (α : ℝ → FourSpace) (a b : ℝ) (hab : a ≤ b)
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hstart : α a = 0) :
    ENNReal.ofReal ‖α b‖ ≤ ∫⁻ t in Icc a b,
      metricTangentENorm g (frameExponential g o e (α t))
        (mfderiv I4 I4 (frameExponential g o e) (α t) (derivWithin α (Icc a b) t)) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simp only [hstart, norm_zero, ENNReal.ofReal_zero, zero_le]
  let B := ∫⁻ t in Icc a b,
    metricTangentENorm g (frameExponential g o e (α t))
      (mfderiv I4 I4 (frameExponential g o e) (α t) (derivWithin α (Icc a b) t))
  by_cases hB : B = (⊤ : ℝ≥0∞)
  · change ENNReal.ofReal ‖α b‖ ≤ B
    rw [hB]
    exact le_top
  have hreal : ‖α b‖ ≤ B.toReal := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let F := fun t => smoothRadialNorm ε (α t)
    have hR : ContDiff ℝ 1 (smoothRadialNorm ε) :=
      ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun v => by
        have hp : 0 < ‖v‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ‖v‖]
        exact hp.ne')
    have hF : ContDiffOn ℝ 1 F (Icc a b) := hR.comp_contDiffOn hα
    have hd (t : ℝ) (ht : t ∈ Icc a b) : derivWithin F (Icc a b) t =
        fderiv ℝ (smoothRadialNorm ε) (α t) (derivWithin α (Icc a b) t) := by
      have hu := uniqueDiffOn_Icc hab t ht
      have h := (smoothRadialNorm_hasFDerivAt ε hε (α t)).comp_hasDerivWithinAt t
        ((hα.differentiableOn one_ne_zero t ht).hasDerivWithinAt)
      change derivWithin (smoothRadialNorm ε ∘ α) (Icc a b) t = _
      rw [h.derivWithin hu, (smoothRadialNorm_hasFDerivAt ε hε (α t)).fderiv]
    have hb : ∫⁻ t in Icc a b, ‖derivWithin F (Icc a b) t‖ₑ ≤ B := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [hd t ht, metricTangentENorm_eq_ofReal, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs]
      exact smoothRadialNorm_exponential_bound g o hRic e he ε hε (α t)
        (derivWithin α (Icc a b) t)
    have hi := (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF hab.le).trans hb
    have hr : F b - F a ≤ B.toReal := by
      apply le_trans (le_abs_self _)
      apply (ENNReal.ofReal_le_iff_le_toReal hB).mp
      simpa only [Real.enorm_eq_ofReal_abs] using hi
    have ha : F a = ε := by
      simp [F, smoothRadialNorm, hstart, Real.sqrt_sq_eq_abs, abs_of_pos hε]
    have hb' : ‖α b‖ ≤ F b := (smoothRadialNorm_bounds ε hε (α b)).1
    linarith
  exact (ENNReal.ofReal_le_iff_le_toReal hB).mpr hreal

theorem frameExponential_inverse_path_length (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hzero : 0 ∈ C.source) (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target)
    (γ : ℝ → M) (a b : ℝ) (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b))
    (himage : MapsTo γ (Icc a b) C.target) (hstart : γ a = e.base) :
    ENNReal.ofReal ‖C.symm (γ b)‖ ≤
      (let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩;
        Manifold.pathELength I4 γ a b) := by
  let α := C.symm ∘ γ
  have hαm : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 α (Icc a b) := hI.comp hγ himage
  have hα : ContDiffOn ℝ 1 α (Icc a b) := hαm.contDiffOn
  have hCzero : C 0 = e.base := (hC hzero).trans (frameExponential_zero g o e)
  have hαzero : α a = 0 := by
    change C.symm (γ a) = 0
    rw [hstart, ← hCzero]
    exact C.left_inv hzero
  have hEq : EqOn (fun t => frameExponential g o e (α t)) γ (Icc a b) := by
    intro t ht
    have hv := C.map_target (himage ht)
    exact (hC hv).symm.trans (C.right_inv (himage ht))
  have hs := frameExponential_radial_le_lintegral g o hRic e he α a b hab.le hα hαzero
  apply hs.trans_eq
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc hab t ht
  have hcomp := mfderiv_comp_mfderivWithin t
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (α t))
    (hαm.mdifferentiableOn one_ne_zero t ht) hu
  have hD : mfderivWithin 𝓘(ℝ, ℝ) I4
      (fun s => frameExponential g o e (α s)) (Icc a b) t 1 =
      mfderiv I4 I4 (frameExponential g o e) (α t) (derivWithin α (Icc a b) t) := by
    have ha : mfderivWithin 𝓘(ℝ, ℝ) I4 α (Icc a b) t 1 =
        derivWithin α (Icc a b) t := by
      have hf : (fderivWithin ℝ α (Icc a b) t) (1 : ℝ) =
          derivWithin α (Icc a b) t := fderivWithin_derivWithin
      simpa only [mfderivWithin_eq_fderivWithin] using! hf
    have hc := congrArg (fun L : ℝ →L[ℝ]
      TangentSpace I4 (frameExponential g o e (α t)) => L 1) hcomp
    exact hc.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) ha)
  have hspeed := congrArg
    (fun p : TangentBundle I4 M => metricTangentENorm g p.1 p.2)
    (tangentMapWithin_congr hEq (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) ht)
  change metricTangentENorm g (frameExponential g o e (α t))
      (mfderivWithin 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) (Icc a b) t 1) =
    metricTangentENorm g (γ t) (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1) at hspeed
  exact (congrArg (metricTangentENorm g (frameExponential g o e (α t))) hD).symm.trans
    hspeed

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Levi-Civita connection of the common radial-frame family varies
jointly with normal vector, center and initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyConnection (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (i : Fin 4)
    (z : HeatRadialFrameSpace) : Mat4 :=
  (P z).2⁻¹ * ((heatFamilyPartial P i z).2 +
    (∑ r : Fin 4, (heatFamilyPartial P i z).1 r •
      connectionMatrix g c r (P z).1) * (P z).2)

theorem heatFamilyConnection_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    heatFamilyConnection g c P i z =
      heatNormalFrameConnection g c (fun x => P (x, z.2)) i z.1 := by
  simp only [heatFamilyConnection, heatNormalFrameConnection,
    heatFamilyPartial_slice P z hP i]

theorem heatFamilyConnection_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target) (hdet : (P z).2.det ≠ 0)
    (i j k : Fin 4) : ContDiffAt ℝ n (fun y => heatFamilyConnection g c P i y j k) z := by
  have hP0 : ContDiffAt ℝ n P z := hP.of_le (by exact_mod_cast Nat.le_succ n)
  have hE (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP0.snd a) b
  have hEi (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2⁻¹ a b) z :=
    heatFamilyMatrixInverse_contDiffAt n (fun y => (P y).2) z hE hdet a b
  have hD := heatFamilyPartial_contDiffAt n P z hP i
  have hDE (a b : Fin 4) : ContDiffAt ℝ n (fun y => (heatFamilyPartial P i y).2 a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hD.snd a) b
  have hDZ (a : Fin 4) : ContDiffAt ℝ n (fun y => (heatFamilyPartial P i y).1 a) z := by
    let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) a
    exact π.contDiff.contDiffAt.comp z hD.fst
  have hΓ (r a b : Fin 4) : ContDiffAt ℝ n
      (fun y => christoffel g c (P y).1 a r b) z := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun w => christoffel g c w a r b) z
      ((christoffel_contDiffAt g c (P z).1 hz
        (metricInChart_posDef g c (P z).1 hz).det_pos.ne' a r b).of_le (by simp)) hP0.fst
  change ContDiffAt ℝ n (fun y => ∑ l : Fin 4, (P y).2⁻¹ j l *
    ((heatFamilyPartial P i y).2 l k +
      ∑ a : Fin 4, (∑ r : Fin 4, (heatFamilyPartial P i y).1 r *
        christoffel g c (P y).1 l r a) * (P y).2 a k)) z
  apply ContDiffAt.sum
  intro l _
  apply (hEi j l).mul
  apply (hDE l k).add
  apply ContDiffAt.sum
  intro a _
  exact (ContDiffAt.sum (fun r _ => (hDZ r).mul (hΓ r l a))).mul (hE a k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverting the base-coordinate family while retaining the initial
frame as a parameter. The spatial derivative alone supplies invertibility. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyBaseAugment (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) : HeatRadialFrameSpace := ((P z).1, z.2)

theorem heatFamilyBaseAugment_local_inverse
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (q : CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 12 P (0, q)) (A : FourSpace ≃L[ℝ] FourSpace)
    (hA : HasFDerivAt (fun x : FourSpace => (P (x, q)).1) (A : FourSpace →L[ℝ] FourSpace) 0) :
    ∃ H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace,
      (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P ∧
      ((0 : FourSpace), q) ∈ H.source ∧
      ContDiffAt ℝ 12 H.symm (heatFamilyBaseAugment P (0, q)) := by
  let B := (ContinuousLinearMap.fst ℝ FourSpace Mat4).comp
    ((fderiv ℝ P (0, q)).comp (ContinuousLinearMap.inr ℝ FourSpace CoordinateFrameSpace))
  let E : HeatRadialFrameSpace ≃L[ℝ] HeatRadialFrameSpace :=
    (ContinuousLinearEquiv.prodComm ℝ FourSpace CoordinateFrameSpace).trans
      (((ContinuousLinearEquiv.refl ℝ CoordinateFrameSpace).skewProd A B).trans
        (ContinuousLinearEquiv.prodComm ℝ CoordinateFrameSpace FourSpace))
  have hdP := (hP.differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (heatFamilyBaseAugment P)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) (0, q) :=
    hdP.fst.prodMk hasFDerivAt_snd
  have hfirst : HasFDerivAt (fun z : HeatRadialFrameSpace => (P z).1)
      ((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))) (0, q) := hdP.fst
  have harg : HasFDerivAt (fun x : FourSpace => (x, q))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) 0 :=
    (hasFDerivAt_id (0 : FourSpace)).prodMk (hasFDerivAt_const q 0)
  have hs : HasFDerivAt (fun x : FourSpace => (P (x, q)).1)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))).comp
        ((ContinuousLinearMap.id ℝ FourSpace).prod
          (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) 0 := HasFDerivAt.comp (f := fun x : FourSpace => (x, q))
      (g := fun z : HeatRadialFrameSpace => (P z).1) 0 hfirst harg
  have hsame := hs.unique hA
  have hsp (v : FourSpace) : (fderiv ℝ P (0, q) (v, 0)).1 = A v :=
    congrArg (fun L : FourSpace →L[ℝ] FourSpace => L v) hsame
  have hE : (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) =
      (E : HeatRadialFrameSpace →L[ℝ] HeatRadialFrameSpace) := by
    apply ContinuousLinearMap.ext
    intro z
    change ((fderiv ℝ P (0, q) z).1, z.2) = (A z.1 + B z.2, z.2)
    have hz : z = (z.1, (0 : CoordinateFrameSpace)) + ((0 : FourSpace), z.2) := by simp
    apply Prod.ext
    · change (fderiv ℝ P (0, q) z).1 = A z.1 + B z.2
      calc
        (fderiv ℝ P (0, q) z).1 =
            (fderiv ℝ P (0, q) ((z.1, 0) + (0, z.2))).1 := congrArg (fun w : HeatRadialFrameSpace => (fderiv ℝ P (0, q) w).1) hz
        _ = (fderiv ℝ P (0, q) (z.1, 0)).1 +
            (fderiv ℝ P (0, q) (0, z.2)).1 := by rw [map_add]; rfl
        _ = A z.1 + B z.2 := by rw [hsp]; rfl
    · rfl
  rw [hE] at hd
  have hf : ContDiffAt ℝ 12 (heatFamilyBaseAugment P) (0, q) :=
    hP.fst.prodMk contDiffAt_snd
  let H := hf.toOpenPartialHomeomorph (heatFamilyBaseAugment P) hd (by norm_num)
  refine ⟨H, rfl, hf.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_⟩
  exact hf.to_localInverse hd (by norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar differentiation in the normal vector, with the initial frame
held fixed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

def heatFamilyScalarPartial (f : HeatRadialFrameSpace → ℝ) (i : Fin 4)
    (z : HeatRadialFrameSpace) : ℝ := fderiv ℝ f z (coordinateVector i, 0)

theorem heatFamilyScalarPartial_contDiffAt (n : ℕ)
    (f : HeatRadialFrameSpace → ℝ) (z : HeatRadialFrameSpace)
    (hf : ContDiffAt ℝ (n + 1 : ℕ) f z) (i : Fin 4) :
    ContDiffAt ℝ n (heatFamilyScalarPartial f i) z :=
  (hf.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const

theorem heatFamilyScalarPartial_slice (f : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) (hf : DifferentiableAt ℝ f z) (i : Fin 4) :
    heatFamilyScalarPartial f i z = partialDeriv (fun x => f (x, z.2)) i z.1 := by
  have harg : HasFDerivAt (fun x : FourSpace => (x, z.2))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd : HasFDerivAt (fun x => f (x, z.2))
      ((fderiv ℝ f z).comp ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) z.1 := hf.hasFDerivAt.comp z.1 harg
  exact (congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hd.fderiv).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete normal-frame data used by the two-form heat construction.
Every field is obtained from the actual radial frame flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

structure HeatNormalFrameData (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) where
  point : FourSpace → CoordinateFrameSpace
  regular : ContDiffAt ℝ 12 point 0
  initial : point 0 = frameCoordinateState g c e
  radius : ℝ
  radius_pos : 0 < radius
  exponential : ∀ x ∈ ball 0 radius,
    (point x).1 = chartAt FourSpace c (frameExponential g o e x)
  in_chart : ∀ x ∈ ball 0 radius, (point x).1 ∈ (chartAt FourSpace c).target
  orthonormal : ∀ x ∈ ball 0 radius,
    (point x).2ᵀ * metricInChart g c (point x).1 * (point x).2 = 1
  differentiable : ∀ x ∈ ball 0 radius, DifferentiableAt ℝ point x
  radial_connection : ∀ x ∈ ball 0 radius,
    (∑ i : Fin 4, x i • heatNormalFrameConnection g c point i x) = 0
  connection_regular : ∀ i j k : Fin 4,
    ContDiffAt ℝ 11 (fun x => heatNormalFrameConnection g c point i x j k) 0

theorem exists_heatNormalFrameData (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    Nonempty (HeatNormalFrameData g o c e) := by
  obtain ⟨P, hP, hP0, r, hr, h⟩ := exists_heatNormalFrame_radial_connection g o c e he
  obtain ⟨_, hc0, hG0, _, _⟩ := h 0 (mem_ball_self hr)
  have hdet : (P 0).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hG0
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  refine ⟨{
    point := P
    regular := hP
    initial := hP0
    radius := r
    radius_pos := hr
    exponential := fun x hx => (h x hx).1
    in_chart := fun x hx => (h x hx).2.1
    orthonormal := fun x hx => (h x hx).2.2.1
    differentiable := fun x hx => (h x hx).2.2.2.1
    radial_connection := fun x hx => (h x hx).2.2.2.2
    connection_regular := ?_ }⟩
  intro i j k
  exact heatNormalFrameConnection_contDiffAt 11 g c P 0 hP hc0 hdet i j k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four derivatives of the actual inverse normal chart needed to
transport the local parametrix and its cutoff to the manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heat_normal_inverse_four (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (c : M) (x : FourSpace)
    (C : OpenPartialHomeomorph FourSpace M) (hx : x ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hc : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hF : ContDiffAt ℝ 4 (fun v => chartAt FourSpace c (frameExponential g o e v)) x)
    (hL : IsUnit (fderiv ℝ (fun v => chartAt FourSpace c (frameExponential g o e v)) x)) :
    ContMDiffAt I4 I4 4 C.symm (frameExponential g o e x) := by
  let F := fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = fderiv ℝ F x := hL.unit_spec
  have hder : HasFDerivAt F (E : FourSpace →L[ℝ] FourSpace) x := by
    rw [hE]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  let hf := hF.hasStrictFDerivAt' hder (by norm_num)
  let H := fun z : FourSpace => C.symm ((chartAt FourSpace c).symm z)
  have hleft : ∀ᶠ v in 𝓝 x, H (F v) = v := by
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
    filter_upwards [C.open_source.mem_nhds hx, hnear] with v hv hvc
    change C.symm ((chartAt FourSpace c).symm
      (chartAt FourSpace c (frameExponential g o e v))) = v
    rw [(chartAt FourSpace c).left_inv hvc, ← hC hv]
    exact C.left_inv hv
  have heq := hf.localInverse_unique hleft
  have hH : ContDiffAt ℝ 4 H (F x) :=
    (hF.to_localInverse hder (by norm_num)).congr_of_eventuallyEq heq
  have hchart : ContMDiffAt I4 I4 4 (chartAt FourSpace c) (frameExponential g o e x) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hc
  have h := hH.contMDiffAt.comp (frameExponential g o e x) hchart
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_source.mem_nhds hc] with y hy
  change C.symm y = C.symm ((chartAt FourSpace c).symm (chartAt FourSpace c y))
  rw [(chartAt FourSpace c).left_inv hy]

theorem exists_heat_normal_chart_four (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 4 C.symm C.target := by
  obtain ⟨C, hzero, hC⟩ := frameExponential_localChart g o e
  let F := fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v)
  have hFs : ContDiffAt ℝ ∞ F 0 := frameExponential_chart_smoothAt_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hF4 : ∀ᶠ v in 𝓝 (0 : FourSpace), ContDiffAt ℝ 4 F v :=
    (hFs.of_le (show (4 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
  have hunit : IsUnit (fderiv ℝ F 0) := by
    have hd := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    rw [hd.hasFDerivAt.fderiv]
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using frameMap_isUnit g e
  have hu : ∀ᶠ v in 𝓝 (0 : FourSpace), IsUnit (fderiv ℝ F v) := by
    have hnear := (hFs.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).continuousAt_fderiv one_ne_zero
    have h := hnear.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds
      ⟨ContinuousLinearEquiv.ofUnit hunit.unit, hunit.unit_spec⟩)
    filter_upwards [h] with v hv
    obtain ⟨E, hE⟩ := hv
    exact hE ▸ E.toUnit.isUnit
  have hc : ∀ᶠ v in 𝓝 (0 : FourSpace), frameExponential g o e v ∈
      (chartAt FourSpace e.base).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_source.mem_nhds (by
        rw [frameExponential_zero]
        exact mem_chart_source FourSpace e.base))
  have hg : ∀ᶠ v in 𝓝 (0 : FourSpace), v ∈ C.source ∧
      frameExponential g o e v ∈ (chartAt FourSpace e.base).source ∧
      ContDiffAt ℝ 4 F v ∧ IsUnit (fderiv ℝ F v) := by
    filter_upwards [C.open_source.mem_nhds hzero, hc, hF4, hu] with v hv hvc hfv huv
    exact ⟨hv, hvc, hfv, huv⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hg
  let D := C.restrOpen (ball 0 r) isOpen_ball
  have hsource : D.source = ball 0 r :=
    inter_eq_right.mpr (fun v hv => (hball hv).1)
  have hD : EqOn D (frameExponential g o e) D.source := fun _ hv => hC hv.1
  refine ⟨r, D, hr, hsource, hD, ?_⟩
  intro y hy
  let v := D.symm y
  have hv : v ∈ D.source := D.map_target hy
  have hvb := hball (hsource ▸ hv)
  have heq : frameExponential g o e v = y := (hD hv).symm.trans (D.right_inv hy)
  have h := heat_normal_inverse_four g o e e.base v D hv hD hvb.2.1 hvb.2.2.1 hvb.2.2.2
  rw [heq] at h
  exact h.contMDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! The parameter-preserving inverse theorem at an arbitrary normal vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
theorem exponentialFamily_local_inverse
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (v : FourSpace) (q : CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 1 P (v, q)) (A : FourSpace ≃L[ℝ] FourSpace)
    (hA : HasFDerivAt (fun x : FourSpace => (P (x, q)).1) (A : FourSpace →L[ℝ] FourSpace) v) :
    ∃ H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace,
      (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P ∧
      (v, q) ∈ H.source ∧
      ContDiffAt ℝ 1 H.symm (heatFamilyBaseAugment P (v, q)) := by
  let B := (ContinuousLinearMap.fst ℝ FourSpace Mat4).comp
    ((fderiv ℝ P (v, q)).comp (ContinuousLinearMap.inr ℝ FourSpace CoordinateFrameSpace))
  let E : HeatRadialFrameSpace ≃L[ℝ] HeatRadialFrameSpace :=
    (ContinuousLinearEquiv.prodComm ℝ FourSpace CoordinateFrameSpace).trans
      (((ContinuousLinearEquiv.refl ℝ CoordinateFrameSpace).skewProd A B).trans
        (ContinuousLinearEquiv.prodComm ℝ CoordinateFrameSpace FourSpace))
  have hdP := (hP.differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (heatFamilyBaseAugment P)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) (v, q) :=
    hdP.fst.prodMk hasFDerivAt_snd
  have hfirst : HasFDerivAt (fun z : HeatRadialFrameSpace => (P z).1)
      ((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))) (v, q) := hdP.fst
  have harg : HasFDerivAt (fun x : FourSpace => (x, q))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) v :=
    (hasFDerivAt_id v).prodMk (hasFDerivAt_const q v)
  have hs : HasFDerivAt (fun x : FourSpace => (P (x, q)).1)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))).comp
        ((ContinuousLinearMap.id ℝ FourSpace).prod
          (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) v := HasFDerivAt.comp (f := fun x : FourSpace => (x, q))
      (g := fun z : HeatRadialFrameSpace => (P z).1) v hfirst harg
  have hsame := hs.unique hA
  have hsp (w : FourSpace) : (fderiv ℝ P (v, q) (w, 0)).1 = A w :=
    congrArg (fun L : FourSpace →L[ℝ] FourSpace => L w) hsame
  have hE : (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (v, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) =
      (E : HeatRadialFrameSpace →L[ℝ] HeatRadialFrameSpace) := by
    apply ContinuousLinearMap.ext
    intro z
    change ((fderiv ℝ P (v, q) z).1, z.2) = (A z.1 + B z.2, z.2)
    have hz : z = (z.1, (0 : CoordinateFrameSpace)) + ((0 : FourSpace), z.2) := by simp
    apply Prod.ext
    · change (fderiv ℝ P (v, q) z).1 = A z.1 + B z.2
      calc
        (fderiv ℝ P (v, q) z).1 =
            (fderiv ℝ P (v, q) ((z.1, 0) + (0, z.2))).1 := congrArg (fun w : HeatRadialFrameSpace => (fderiv ℝ P (v, q) w).1) hz
        _ = (fderiv ℝ P (v, q) (z.1, 0)).1 +
            (fderiv ℝ P (v, q) (0, z.2)).1 := by rw [map_add]; rfl
        _ = A z.1 + B z.2 := by rw [hsp]; rfl
    · rfl
  rw [hE] at hd
  have hf : ContDiffAt ℝ 1 (heatFamilyBaseAugment P) (v, q) :=
    hP.fst.prodMk contDiffAt_snd
  let H := hf.toOpenPartialHomeomorph (heatFamilyBaseAugment P) hd (by norm_num)
  refine ⟨H, rfl, hf.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_⟩
  exact hf.to_localInverse hd (by norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Short paths cannot leave a normal-coordinate ball. This supplies the
distance lower bound needed for locally minimizing radial geodesics. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Filter Set MeasureTheory Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_short_path_stays (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (r : ℝ) (hr : 0 < r)
    (hball : closedBall 0 r ⊆ C.source)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ) (hstart : γ 0 = e.base)
    (hlen : (let : RiemannianBundle (TangentSpace I4 : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; Manifold.pathELength I4 γ 0 1) < ENNReal.ofReal r) :
    MapsTo γ (Icc 0 1) (C '' closedBall 0 r) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let K := C '' closedBall 0 r
  let U := C '' ball 0 r
  have hzero : (0 : FourSpace) ∈ C.source := hball (mem_closedBall_self hr.le)
  have hCzero : C 0 = e.base := (hC hzero).trans (frameExponential_zero g o e)
  have hKclosed : IsClosed K :=
    ((isCompact_closedBall (0 : FourSpace) r).image_of_continuousOn
      (C.continuousOn.mono hball)).isClosed
  have hUopen : IsOpen U := C.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hball)
  have hUK : U ⊆ K := image_mono ball_subset_closedBall
  have hKtarget : K ⊆ C.target := by
    rintro y ⟨v, hv, rfl⟩
    exact C.map_source (hball hv)
  let A := γ ⁻¹' K
  have hAclosed : IsClosed (A ∩ Icc 0 1) :=
    (hKclosed.preimage hγ.continuous).inter isClosed_Icc
  have hA0 : 0 ∈ A := by
    change γ 0 ∈ K
    exact ⟨0, mem_closedBall_self hr.le, hCzero.trans hstart.symm⟩
  apply hAclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hA0
  intro t ht hprefix
  have hnorm : ‖C.symm (γ t)‖ < r := by
    rcases ht.1.eq_or_lt with rfl | htpos
    · rw [hstart, ← hCzero, C.left_inv hzero, norm_zero]
      exact hr
    · have hbound := frameExponential_inverse_path_length g o hRic e he C hzero hC hI
        γ 0 t htpos hγ.contMDiffOn (fun s hs => hKtarget (hprefix hs)) hstart
      have hlt : ENNReal.ofReal ‖C.symm (γ t)‖ < ENNReal.ofReal r :=
        hbound.trans_lt ((Manifold.pathELength_mono (I := I4) (γ := γ)
          le_rfl ht.2.le).trans_lt hlen)
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hlt
  have htK : γ t ∈ K := hprefix ⟨ht.1, le_rfl⟩
  have htU : γ t ∈ U := ⟨C.symm (γ t), by simpa using hnorm,
    C.right_inv (hKtarget htK)⟩
  exact hγ.continuous.continuousWithinAt (mem_of_superset (hUopen.mem_nhds htU) hUK)

theorem frameExponential_normal_ball_distance_lower (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (r : ℝ) (hr : 0 < r)
    (hball : closedBall 0 r ⊆ C.source) (v : FourSpace) (hv : ‖v‖ < r) :
    ENNReal.ofReal ‖v‖ ≤ metricEDistance g e.base (frameExponential g o e v) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_contra h
  have hlt : Manifold.riemannianEDist I4 e.base (frameExponential g o e v) <
      ENNReal.ofReal ‖v‖ := lt_of_not_ge h
  obtain ⟨γ, hstart, hend, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hrlen : Manifold.pathELength I4 γ 0 1 < ENNReal.ofReal r :=
    hlen.trans (ENNReal.ofReal_lt_ofReal_iff hr |>.mpr hv)
  have hstay := frameExponential_short_path_stays g o hRic e he C hC hI r hr hball
    γ hγ hstart hrlen
  have htarget : MapsTo γ (Icc 0 1) C.target := by
    intro t ht
    obtain ⟨w, hw, hweq⟩ := hstay ht
    rw [← hweq]
    exact C.map_source (hball hw)
  have hzero : (0 : FourSpace) ∈ C.source := hball (mem_closedBall_self hr.le)
  have hbound := frameExponential_inverse_path_length g o hRic e he C hzero hC hI
    γ 0 1 zero_lt_one hγ.contMDiffOn htarget hstart
  have hvsource : v ∈ C.source := hball (by simpa using hv.le)
  have hinverse : C.symm (γ 1) = v := by
    rw [hend, ← hC hvsource]
    exact C.left_inv hvsource
  rw [hinverse] at hbound
  exact (not_lt_of_ge hbound) hlen

/-- The constructed radial geodesics minimize distance near their initial point. -/
theorem frameExponential_locally_minimizing (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ v : FourSpace, ‖v‖ < r →
      metricEDistance g e.base (frameExponential g o e v) = ENNReal.ofReal ‖v‖ := by
  obtain ⟨R, C, hR, hsource, hC, hI⟩ := frameExponential_normal_ball g o e
  refine ⟨R / 2, half_pos hR, fun v hv => le_antisymm (frameExponential_distance g o e v) ?_⟩
  apply frameExponential_normal_ball_distance_lower g o hRic e he C hC hI (R / 2)
    (half_pos hR) _ v hv
  rw [hsource]
  exact closedBall_subset_ball (by linarith)

/-- The metric ball is covered by the actual radial normal coordinates. -/
theorem frameExponential_metric_ball_surj (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (r : ℝ) (hr : 0 < r)
    (hball : closedBall 0 r ⊆ C.source) (y : M)
    (hy : metricEDistance g e.base y < ENNReal.ofReal r) :
    ∃ v : FourSpace, ‖v‖ < r ∧ frameExponential g o e v = y ∧
      metricEDistance g e.base y = ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, hstart, hend, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
  have hstay := frameExponential_short_path_stays g o hRic e he C hC hI r hr hball
    γ hγ hstart hlen
  have htarget : MapsTo γ (Icc 0 1) C.target := by
    intro t ht
    obtain ⟨v, hv, hvγ⟩ := hstay ht
    rw [← hvγ]
    exact C.map_source (hball hv)
  have hzero : (0 : FourSpace) ∈ C.source := hball (mem_closedBall_self hr.le)
  have hb := frameExponential_inverse_path_length g o hRic e he C hzero hC hI
    γ 0 1 zero_lt_one hγ.contMDiffOn htarget hstart
  let v := C.symm y
  have hv : ‖v‖ < r := by
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mp
    simpa only [hend] using hb.trans_lt hlen
  have hyC : y ∈ C.target := by simpa only [hend] using htarget (right_mem_Icc.mpr zero_le_one)
  have hexp : frameExponential g o e v = y :=
    (hC (C.map_target hyC)).symm.trans (C.right_inv hyC)
  refine ⟨v, hv, hexp, ?_⟩
  rw [← hexp]
  exact le_antisymm (frameExponential_distance g o e v)
    (frameExponential_normal_ball_distance_lower g o hRic e he C hC hI r hr hball v hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The initial frame derivative gives a genuine joint inverse and a
common injectivity radius for the actual normal-coordinate family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyBaseAugment_actual_inverse (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 12 P (0, frameCoordinateState g e.base e))
    (hexp : (fun x => (P (x, frameCoordinateState g e.base e)).1) =ᶠ[𝓝 0]
      (fun x => chartAt FourSpace e.base (frameExponential g o e x))) :
    ∃ H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace,
      (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P ∧
      ((0 : FourSpace), frameCoordinateState g e.base e) ∈ H.source ∧
      ContDiffAt ℝ 12 H.symm
        (heatFamilyBaseAugment P (0, frameCoordinateState g e.base e)) := by
  have hL := frameMap_isUnit g e
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = e.frame.map.toContinuousLinearMap := hL.unit_spec
  have hd := (frameExponential_chart_strictDerivative_zero g o e.base e
    (mem_chart_source FourSpace e.base)).hasFDerivAt
  rw [chartForwardOperator_center, ContinuousLinearMap.id_comp] at hd
  have hs : HasFDerivAt (fun x => (P (x, frameCoordinateState g e.base e)).1)
      (A : FourSpace →L[ℝ] FourSpace) 0 := by
    rw [hA]
    exact hd.congr_of_eventuallyEq hexp
  exact heatFamilyBaseAugment_local_inverse P _ hP A hs

theorem heatFamilyBaseAugment_common_injectivity
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (q₀ : CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (h0 : ((0 : FourSpace), q₀) ∈ H.source) :
    ∃ r > (0 : ℝ), ∀ q ∈ ball q₀ r,
      InjOn (fun x : FourSpace => (P (x, q)).1) (ball 0 r) := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0)
  refine ⟨r, hr, ?_⟩
  intro q hq x hx y hy hxy
  have hxH : (x, q) ∈ H.source := hb (show (x, q) ∈ ball (0, q₀) r from by
    change max (dist x 0) (dist q q₀) < r
    exact max_lt hx hq)
  have hyH : (y, q) ∈ H.source := hb (show (y, q) ∈ ball (0, q₀) r from by
    change max (dist y 0) (dist q q₀) < r
    exact max_lt hy hq)
  have hxyH : H (x, q) = H (y, q) := by
    rw [hH]
    exact Prod.ext hxy rfl
  exact congrArg Prod.fst (H.injOn hxH hyH hxyH)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual frame slice of the common flow supplies the
normal-frame data, with exactly the same point function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyFrameData {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (t : ℝ) (ht : 0 < t) (htI : t ∈ Ioo (-F.time) F.time)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hq : ((0 : FourSpace), frameCoordinateState g c e) ∈ ball (0, p) F.radius)
    (hP : ContDiffAt ℝ 12 (fun x => heatRadialFrameFamily F t (x, frameCoordinateState g c e)) 0)
    (hexp : (fun x => (heatRadialFrameFamily F t (x, frameCoordinateState g c e)).1)
      =ᶠ[𝓝 0] (fun x => chartAt FourSpace c (frameExponential g o e x))) :
    ∃ D : HeatNormalFrameData g o c e,
      D.point = fun x => heatRadialFrameFamily F t (x, frameCoordinateState g c e) := by
  let q := frameCoordinateState g c e
  let G := F.recenter q hq
  let P := fun x => heatRadialFrameFamily F t (x, q)
  have hP0 : P 0 = q := heatRadialFrameFamily_zero F q (ball_subset_closedBall hq) t htI
  let A : FourSpace → HeatRadialFrameSpace := fun x => (t⁻¹ • x, q)
  have hA : Continuous A :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).continuous.prodMk continuous_const
  have hA0 : A 0 = (0, q) := by simp [A]
  have hi : ∀ᶠ x in 𝓝 (0 : FourSpace), A x ∈ ball (0, q) G.radius :=
    hA.continuousAt.preimage_mem_nhds (by rw [hA0]; exact ball_mem_nhds _ G.radius_pos)
  have hd : ∀ᶠ x in 𝓝 (0 : FourSpace), DifferentiableAt ℝ P x := by
    filter_upwards [(hP.of_le (show (1 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by simp)] with x hx
    exact hx.differentiableAt one_ne_zero
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (P x).1 = chartAt FourSpace c (frameExponential g o e x) ∧
      (P x).1 ∈ (chartAt FourSpace c).target ∧
      (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 ∧
      DifferentiableAt ℝ P x ∧
      (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0 := by
    filter_upwards [hexp, hi, hd] with x hx hix hdx
    have hclosed := ball_subset_closedBall hix
    have hc : (P x).1 ∈ (chartAt FourSpace c).target := G.in_chart (A x) hclosed t htI
    have hg : (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1 :=
      (G.gram (A x) hclosed t htI).trans (frameChartMatrix_normalizes g c e he)
    have hrad : fderiv ℝ P x x = (heatRadialFrameField g c (x, P x)).2 :=
      heatRadialFrameEndpoint_radial_derivative G t ht htI.2 x hix hdx
    exact ⟨hx, hc, hg, hdx, heatNormalFrameConnection_radial g c P x hrad⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hc0 := (hball (mem_ball_self hr)).2.1
  have hg0 := (hball (mem_ball_self hr)).2.2.1
  have hdet : (P 0).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hg0
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  refine ⟨{
    point := P
    regular := hP
    initial := hP0
    radius := r
    radius_pos := hr
    exponential := fun x hx => (hball hx).1
    in_chart := fun x hx => (hball hx).2.1
    orthonormal := fun x hx => (hball hx).2.2.1
    differentiable := fun x hx => (hball hx).2.2.2.1
    radial_connection := fun x hx => (hball hx).2.2.2.2
    connection_regular := fun i j k => heatNormalFrameConnection_contDiffAt 11 g c P 0 hP hc0 hdet i j k }, rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate differentiation of the base map and frame matrix in the
normal-frame construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatLinearForm_coordinate_expansion (L : FourSpace →L[ℝ] ℝ) (v : FourSpace) :
    L v = ∑ i : Fin 4, v i * L (coordinateVector i) := by
  have hv : (∑ i : Fin 4, v i • coordinateVector i) = v :=
    sum_coordinateVector (WithLp.ofLp v)
  calc
    L v = L (∑ i : Fin 4, v i • coordinateVector i) := congrArg L hv.symm
    _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

theorem heatFrame_matrixPartial (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (i : Fin 4) :
    matrixPartial (fun y => (P y).2) i x = (fderiv ℝ P x (coordinateVector i)).2 := by
  ext j k
  let π₁ : Mat4 →L[ℝ] (Fin 4 → ℝ) := ContinuousLinearMap.proj j
  let π₂ : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  let π : Mat4 →L[ℝ] ℝ := π₂.comp π₁
  have h := π.hasFDerivAt.comp x hP.hasFDerivAt.snd
  have he := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h.fderiv
  exact he

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFrame_metricPartial (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (i : Fin 4) :
    matrixPartial (fun y => metricInChart g c (P y).1) i x =
      (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
        connectionMatrix g c r (P x).1)ᵀ * metricInChart g c (P x).1 +
      metricInChart g c (P x).1 *
        (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
          connectionMatrix g c r (P x).1) := by
  let v := (fderiv ℝ P x (coordinateVector i)).1
  rw [← parallelFrame_metric_rate g c (P x).1 hx v]
  ext j k
  have hg := ((metricInChart_contDiffAt g c (P x).1 hx j k).differentiableAt
    (by simp)).hasFDerivAt
  have h := hg.comp x hP.hasFDerivAt.fst
  have he := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h.fderiv
  change partialDeriv (fun y => metricInChart g c (P y).1 j k) i x = _
  rw [show partialDeriv (fun y => metricInChart g c (P y).1 j k) i x =
      fderiv ℝ (fun z => metricInChart g c z j k) (P x).1 v from he]
  rw [heatLinearForm_coordinate_expansion]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial, partialDeriv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine normal chart supporting a
finite-regularity parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalFrameChart {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 4 C.symm C.target ∧
      C.target ⊆ (chartAt FourSpace c).source ∧
      ContDiffOn ℝ 4 D.point C.source ∧ C.source ⊆ ball 0 D.radius := by
  obtain ⟨r₀, C₀, hr₀, hC₀, hE, hI⟩ := exists_heat_normal_chart_four g o e
  have hc : ∀ᶠ x in 𝓝 (0 : FourSpace),
      frameExponential g o e x ∈ (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds (by rwa [frameExponential_zero]))
  have hreg : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 4 D.point x :=
    (D.regular.of_le (show (4 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ C₀.source ∧
      frameExponential g o e x ∈ (chartAt FourSpace c).source ∧
      ContDiffAt ℝ 4 D.point x ∧ x ∈ ball 0 D.radius := by
    filter_upwards [hC₀ ▸ ball_mem_nhds (0 : FourSpace) hr₀, hc, hreg,
      ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx hcx hpx hdx
    exact ⟨hx, hcx, hpx, hdx⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let C := C₀.restrOpen (ball 0 r) isOpen_ball
  have hs : C.source = ball 0 r := inter_eq_right.mpr (fun x hx => (hball hx).1)
  have hCE : EqOn C (frameExponential g o e) C.source := fun x hx => hE hx.1
  refine ⟨r, C, hr, hs, hCE, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (hI.contMDiffAt (C₀.open_target.mem_nhds hy.1)).contMDiffWithinAt
  · intro y hy
    have hx := C.map_target hy
    have ht := (hball (hs ▸ hx)).2.1
    rw [← hCE hx, C.right_inv hy] at ht
    exact ht
  · intro x hx
    exact (hball (hs ▸ hx)).2.2.1.contDiffWithinAt
  · intro x hx
    exact (hball (hs ▸ hx)).2.2.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported four-times-differentiable scalar coefficients
can be lifted through the actual normal chart and extended by zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M]

def heatNormalScalarLift (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) (x : M) : ℝ := by
  classical
  exact if x ∈ C.target then ψ (C.symm x) else 0

theorem heatNormalScalarLift_on_target (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) {x : M} (hx : x ∈ C.target) :
    heatNormalScalarLift C ψ x = ψ (C.symm x) := by
  simp only [heatNormalScalarLift, ite_eq_left hx]

theorem heatNormalScalarLift_source (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) {x : FourSpace} (hx : x ∈ C.source) :
    heatNormalScalarLift C ψ (C x) = ψ x := by
  rw [heatNormalScalarLift_on_target C ψ (C.map_source hx), C.left_inv hx]

theorem heatNormalScalarLift_support (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) : support (heatNormalScalarLift C ψ) ⊆ C '' tsupport ψ := by
  classical
  intro x hx
  by_cases ht : x ∈ C.target
  · refine ⟨C.symm x, subset_closure ?_, C.right_inv ht⟩
    simpa only [mem_support, heatNormalScalarLift, ite_eq_left ht] using hx
  · exact False.elim (hx (by simp only [heatNormalScalarLift, ite_eq_right ht]))

theorem heatNormalScalarLift_compact [T2Space M]
    (C : OpenPartialHomeomorph FourSpace M) (ψ : FourSpace → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    HasCompactSupport (heatNormalScalarLift C ψ) := by
  have hK : IsCompact (C '' tsupport ψ) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (heatNormalScalarLift_support C ψ) hK.isClosed

variable [ChartedSpace FourSpace M]

theorem heatNormalScalarLift_regular [T2Space M]
    (C : OpenPartialHomeomorph FourSpace M) (ψ : FourSpace → ℝ)
    (hC : ContMDiffOn I4 I4 4 C.symm C.target)
    (hψ : ContDiff ℝ 4 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (heatNormalScalarLift C ψ) := by
  let K := C '' tsupport ψ
  have hK : IsCompact K := hc.image_of_continuousOn (C.continuousOn.mono hs)
  have hKt : K ⊆ C.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.map_source (hs hz)
  intro x
  by_cases hx : x ∈ C.target
  · have h := hψ.contMDiff.contMDiffAt.comp x
      (hC.contMDiffAt (C.open_target.mem_nhds hx))
    apply h.congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hx] with y hy
    exact heatNormalScalarLift_on_target C ψ hy
  · have hxK : x ∉ K := fun hxK => hx (hKt hxK)
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact notMem_support.mp (fun h => hy (heatNormalScalarLift_support C ψ h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonconjugate radial vector has one injective neighborhood that works
for every sufficiently nearby initial frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_common_injective_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
      ∀ f ∈ U, InjOn (frameExponential g o f) (ball (t • coordinateVector 0) r) := by
  let v : FourSpace := t • coordinateVector 0
  let c := e.base
  let d := (parallelFrameFlowMap g 0 t e).base
  have hc : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hvexp : frameExponential g o e v = d := frameExponential_first_ray g o e he t ht
  have hvn : ‖v‖ = t := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit, mul_one]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvn]; exact ht.ne')
  let q := frameCoordinateState g c e
  let P : HeatRadialFrameSpace → CoordinateFrameSpace :=
    fun z => (exponentialFamilyCoordinates g o c d z, 0)
  have hP : ContDiffAt ℝ 1 P (v,q) :=
    (exponentialFamilyCoordinates_contDiffAt g o c d e hc v hv (hvexp ▸ hd)).prodMk contDiffAt_const
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL : IsUnit L := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hder : HasFDerivAt (fun x => (P (x,q)).1) (A : FourSpace →L[ℝ] FourSpace) v := by
    rw [hA]
    have heq : (fun x => (P (x,q)).1) =ᶠ[𝓝 v]
        (fun x => chartAt FourSpace d (frameExponential g o e x)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
      exact exponentialFamilyCoordinates_frame g o c d e hc x hx
    exact (frameExponential_hasFDerivAt g o hRic d e he t ht hd).congr_of_eventuallyEq heq
  obtain ⟨H,hH,hvH,_⟩ := exponentialFamily_local_inverse P v q hP A hder
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds hvH)
  have hframe : {f : FrameBundle g | f.base ∈ (chartAt FourSpace c).source ∧
      frameCoordinateState g c f ∈ ball q R} ∈ 𝓝 e :=
    Filter.inter_mem ((continuous_frameBase g).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc))
      ((frameCoordinateState_continuousAt g c e hc).preimage_mem_nhds (ball_mem_nhds q hR))
  obtain ⟨U,hsub,hU,heU⟩ := mem_nhds_iff.mp hframe
  let r := min R (t / 2)
  have hr : 0 < r := lt_min hR (half_pos ht)
  have hnz (x : FourSpace) (hx : x ∈ ball v r) : x ≠ 0 := by
    intro hzero
    rw [hzero, mem_ball, dist_zero_left, hvn] at hx
    have hh : r ≤ t / 2 := min_le_right _ _
    linarith
  refine ⟨U,hU,heU,r,hr,?_⟩
  intro f hf x hx y hy hxy
  obtain ⟨hfc,hfq⟩ := hsub hf
  have hxH : (x,frameCoordinateState g c f) ∈ H.source := hball (by
    change max (dist x v) (dist (frameCoordinateState g c f) q) < R
    exact max_lt (lt_of_lt_of_le hx (min_le_left _ _)) hfq)
  have hyH : (y,frameCoordinateState g c f) ∈ H.source := hball (by
    change max (dist y v) (dist (frameCoordinateState g c f) q) < R
    exact max_lt (lt_of_lt_of_le hy (min_le_left _ _)) hfq)
  apply congrArg Prod.fst (H.injOn hxH hyH ?_)
  rw [hH]
  dsimp only [heatFamilyBaseAugment]
  apply Prod.ext
  swap
  · rfl
  change exponentialFamilyCoordinates g o c d (x,frameCoordinateState g c f) =
    exponentialFamilyCoordinates g o c d (y,frameCoordinateState g c f)
  rw [exponentialFamilyCoordinates_frame g o c d f hfc x (hnz x hx),
    exponentialFamilyCoordinates_frame g o c d f hfc y (hnz y hy), hxy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Slicing the joint inverse while holding the initial frame fixed gives
an actual open coordinate chart, with an explicit inverse. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilySliceChart (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (q : CoordinateFrameSpace) : OpenPartialHomeomorph FourSpace FourSpace := by
  have he (z : HeatRadialFrameSpace) : H z = ((P z).1, z.2) := congrFun hH z
  have hi (z : HeatRadialFrameSpace) (hz : z ∈ H.target) : (H.symm z).2 = z.2 := by
    have hh := congrArg Prod.snd (H.right_inv hz)
    rw [he] at hh
    exact hh
  have hip (y : FourSpace) (hy : (y, q) ∈ H.target) :
      ((H.symm (y, q)).1, q) = H.symm (y, q) := by
    apply Prod.ext
    · rfl
    · exact (hi (y, q) hy).symm
  exact {
    toFun := fun x => (P (x, q)).1
    invFun := fun y => (H.symm (y, q)).1
    source := {x | (x, q) ∈ H.source}
    target := {y | (y, q) ∈ H.target}
    map_source' := fun x hx => by
      have hh := H.map_source hx
      rw [he] at hh
      exact hh
    map_target' := fun y hy => by
      change ((H.symm (y, q)).1, q) ∈ H.source
      rw [hip y hy]
      exact H.map_target hy
    left_inv' := fun x hx => by
      have hh := congrArg Prod.fst (H.left_inv hx)
      rw [he] at hh
      exact hh
    right_inv' := fun y hy => by
      have hh := congrArg Prod.fst (H.right_inv hy)
      rw [he, ← hip y hy] at hh
      exact hh
    open_source := H.open_source.preimage (continuous_id.prodMk continuous_const)
    open_target := H.open_target.preimage (continuous_id.prodMk continuous_const)
    continuousOn_toFun := by
      have hc : ContinuousOn (fun x : FourSpace => H (x, q)) {x | (x, q) ∈ H.source} :=
        H.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => hx)
      simpa only [hH, heatFamilyBaseAugment] using hc.fst
    continuousOn_invFun :=
      (H.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => hy)).fst }

theorem heatFamilySliceChart_source (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (q : CoordinateFrameSpace) :
    (heatFamilySliceChart P H hH q).source = {x | (x, q) ∈ H.source} := rfl

theorem heatFamilySliceChart_inverse_regular
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (q : CoordinateFrameSpace) (x : FourSpace)
    (hi : ContDiffAt ℝ 4 H.symm ((P (x, q)).1, q)) :
    ContDiffAt ℝ 4 (heatFamilySliceChart P H hH q).symm (P (x, q)).1 := by
  change ContDiffAt ℝ 4 (fun y => (H.symm (y, q)).1) (P (x, q)).1
  exact (ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := H.symm)
    (P (x, q)).1 hi (contDiffAt_id.prodMk contDiffAt_const)).fst

theorem heatFamilySliceChart_uniform
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (q₀ : CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (h0 : ((0 : FourSpace), q₀) ∈ H.source)
    (hP : ContDiffAt ℝ 12 P (0, q₀))
    (hi : ContDiffAt ℝ 12 H.symm (heatFamilyBaseAugment P (0, q₀))) :
    ∃ r > (0 : ℝ), ∀ q ∈ ball q₀ r, ∀ x ∈ ball (0 : FourSpace) r,
      x ∈ (heatFamilySliceChart P H hH q).source ∧
      ContDiffAt ℝ 4 (heatFamilySliceChart P H hH q).symm (P (x, q)).1 := by
  have hp : ContinuousAt (heatFamilyBaseAugment P) (0, q₀) :=
    hP.continuousAt.fst.prodMk continuousAt_snd
  have hreg := hp.tendsto.eventually ((hi.of_le (show (4 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num))
  have hn : ∀ᶠ z in 𝓝 ((0 : FourSpace), q₀), z ∈ H.source ∧
      ContDiffAt ℝ 4 H.symm (heatFamilyBaseAugment P z) :=
    Filter.Eventually.and (H.open_source.mem_nhds h0) hreg
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro q hq x hx
  have hmem : (x, q) ∈ ball ((0 : FourSpace), q₀) r := by
    change max (dist x 0) (dist q q₀) < r
    exact max_lt hx hq
  obtain ⟨hs, hdiff⟩ := hb hmem
  exact ⟨hs, heatFamilySliceChart_inverse_regular P H hH q x hdiff⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant pullback by a moving frame. The frame matrix and the
Jacobian of the base map are kept distinct. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_frameTensor_weighted_sum {n : ℕ} (E : Mat4)
    (c : Fin 4 → ℝ) (T : Fin 4 → CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor E (∑ r, c r • T r) a = ∑ r, c r * frameTensor E (T r) a := by
  have he : (∑ r, c r • T r) = (fun b => ∑ r, c r * T r b) := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, frameTensor_sum]
  simp only [frameTensor_const_mul]

theorem heat_covariantDirection_pullback {n : ℕ}
    (F : FourSpace → FourSpace) (E : FourSpace → Mat4)
    (C D : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hF : DifferentiableAt ℝ F z)
    (hE : ∀ a b, DifferentiableAt ℝ (fun w => E w a b) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (F z)) (i : Fin 4)
    (hC : E z * C i z = matrixPartial E i z +
      (∑ r, jacobianMatrix F z r i • D r (F z)) * E z) :
    tensorCovariantDirection C (fun w => frameTensor (E w) (T (F w))) i z =
      frameTensor (E z) (∑ r, jacobianMatrix F z r i • tensorCovariantDirection D T r (F z)) := by
  have hcomp (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => T (F w) a) z := (hT a).comp z hF
  have hder := tensorPartial_frameTensor E (fun w => T (F w)) z hE hcomp i
  have hchain := tensorPartial_comp F T z hF hT i
  have hvar := frameVariation_connection (E z) (matrixPartial E i z)
    (∑ r, jacobianMatrix F z r i • D r (F z)) (C i z) hC (T (F z))
  have hslot : tensorSlotAction (∑ r, jacobianMatrix F z r i • D r (F z)) (T (F z)) =
      ∑ r, jacobianMatrix F z r i • tensorSlotAction (D r (F z)) (T (F z)) := by
    simp only [tensorSlotAction_sum_matrix, tensorSlotAction_smul_matrix]
  funext a
  have hv := congrFun hvar a
  change tensorPartial (fun w => frameTensor (E w) (T (F w))) i z a -
    tensorSlotAction (C i z) (frameTensor (E z) (T (F z))) a = _
  rw [hder, hchain]
  rw [hslot] at hv
  simp only [Pi.add_apply] at hv ⊢
  rw [heat_frameTensor_weighted_sum] at hv
  rw [heat_frameTensor_weighted_sum, heat_frameTensor_weighted_sum]
  simp only [tensorCovariantDirection, frameTensor_sub, mul_sub, Finset.sum_sub_distrib]
  linarith only [hv]

theorem heatFrame_baseJacobian (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (i r : Fin 4) :
    jacobianMatrix (fun y => (P y).1) x r i =
      (fderiv ℝ P x (coordinateVector i)).1 r := by
  have hp : HasFDerivAt P (fderiv ℝ P x) x := hP.hasFDerivAt
  have hf : HasFDerivAt (fun y => (P y).1)
      ((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P x)) x := hp.fst
  have h := hf.fderiv
  have he := congrArg (fun L : FourSpace →L[ℝ] FourSpace => L (coordinateVector i) r) h
  simpa only [jacobianMatrix] using! he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Convert a two-form amplitude in the constructed parallel frame to
an actual alternating coordinate tensor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalCoordinateTensor {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → TwoFormFour) (x : FourSpace) : CovariantCoordinates 2 :=
  frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))

theorem heatNormalFrame_matrix_nondegenerate {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    {x : FourSpace} (hx : x ∈ ball 0 D.radius) : (D.point x).2.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det (D.orthonormal x hx)
  simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
  norm_num at h

theorem heatNormalCoordinateTensor_regular {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → TwoFormFour) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x) (ha : ContDiffAt ℝ 2 a x)
    (v : Fin 2 → Fin 4) : ContDiffAt ℝ 2 (fun y => heatNormalCoordinateTensor D a y v) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hEi (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2⁻¹ i j) x :=
    heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) x hE
      (heatNormalFrame_matrix_nondegenerate D hx) i j
  have hT : ContDiffAt ℝ 2 (fun y => twoFormTensor (a y)) x :=
    twoFormTensorLinear.toContinuousLinearMap.contDiff.comp_contDiffAt x ha
  change ContDiffAt ℝ 2 (fun y => ∑ b, (∏ k, (D.point y).2⁻¹ (b k) (v k)) *
    twoFormTensor (a y) b) x
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod (fun k _ => hEi (b k) (v k))).mul
    ((ContinuousLinearMap.proj b : CovariantCoordinates 2 →L[ℝ] ℝ).contDiff.comp_contDiffAt x hT)

theorem heatNormalCoordinateTensor_support {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → TwoFormFour) :
    tsupport (heatNormalCoordinateTensor D a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have ha : a x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  simp only [heatNormalCoordinateTensor, ha, show twoFormTensor 0 = 0 from map_zero twoFormTensorLinear]
  funext v
  simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact cutoff inside a genuine normal chart, equal to one on its
inner quarter ball and with four derivatives after lifting to the manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def heatNormalChartBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : FourSpace) where
  rIn := r / 4
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

variable {M : Type*} [TopologicalSpace M]

def heatNormalCutoff (C : OpenPartialHomeomorph FourSpace M) (r : ℝ) (hr : 0 < r) : M → ℝ :=
  heatNormalScalarLift C (heatNormalChartBump r hr)

theorem heatNormalChartBump_support (r : ℝ) (hr : 0 < r)
    (C : OpenPartialHomeomorph FourSpace M) (hC : C.source = ball 0 r) :
    tsupport (heatNormalChartBump r hr : FourSpace → ℝ) ⊆ C.source := by
  rw [hC, (heatNormalChartBump r hr).tsupport_eq]
  exact closedBall_subset_ball (by change r / 2 < r; linarith)

theorem heatNormalCutoff_regular [T2Space M] [ChartedSpace FourSpace M] (C : OpenPartialHomeomorph FourSpace M)
    (r : ℝ) (hr : 0 < r) (hC : C.source = ball 0 r)
    (hInv : ContMDiffOn I4 I4 4 C.symm C.target) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (heatNormalCutoff C r hr) := by
  exact heatNormalScalarLift_regular C _ hInv
    (heatNormalChartBump r hr).contDiff
    (heatNormalChartBump r hr).hasCompactSupport (heatNormalChartBump_support r hr C hC)

theorem heatNormalCutoff_compact [T2Space M] (C : OpenPartialHomeomorph FourSpace M)
    (r : ℝ) (hr : 0 < r) (hC : C.source = ball 0 r) :
    HasCompactSupport (heatNormalCutoff C r hr) :=
  heatNormalScalarLift_compact C _ (heatNormalChartBump r hr).hasCompactSupport
    (heatNormalChartBump_support r hr C hC)

theorem heatNormalCutoff_inner (C : OpenPartialHomeomorph FourSpace M)
    (r : ℝ) (hr : 0 < r) (hC : C.source = ball 0 r)
    {v : FourSpace} (hv : v ∈ closedBall 0 (r / 4)) :
    heatNormalCutoff C r hr (C v) = 1 := by
  have hs : v ∈ C.source := by
    rw [hC]
    exact closedBall_subset_ball (by linarith : r / 4 < r) hv
  rw [heatNormalCutoff, heatNormalScalarLift_source C _ hs]
  exact (heatNormalChartBump r hr).one_of_mem_closedBall hv

theorem heatNormalCutoff_bounds (C : OpenPartialHomeomorph FourSpace M)
    (r : ℝ) (hr : 0 < r) (x : M) :
    0 ≤ heatNormalCutoff C r hr x ∧ heatNormalCutoff C r hr x ≤ 1 := by
  classical
  by_cases hx : x ∈ C.target
  · rw [heatNormalCutoff, heatNormalScalarLift_on_target C _ hx]
    exact ⟨(heatNormalChartBump r hr).nonneg, (heatNormalChartBump r hr).le_one⟩
  · simp only [heatNormalCutoff, heatNormalScalarLift, ite_eq_right hx]
    norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! The same positive radius supports actual normal-frame data for every
frame in one open neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalFrameCommonData (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ F : HeatRadialFrameFlow g c (frameCoordinateState g c e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, e'.base ∈ (chartAt FourSpace c).source ∧
          ∃ D : HeatNormalFrameData g o c e', D.radius = r ∧
            (D.point = fun v => heatRadialFrameFamily F t (v, frameCoordinateState g c e')) ∧
            ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (0, frameCoordinateState g c e') := by
  obtain ⟨F, t, ht, htI, U₀, hU₀, he₀, R, hR, hdata⟩ :=
    exists_heatRadialFrameCommonDomain g o c e he
  let p := frameCoordinateState g c e
  have hnear : {e' : FrameBundle g | frameCoordinateState g c e' ∈ ball p (F.radius / 2)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g c e he).preimage_mem_nhds
      (ball_mem_nhds _ (half_pos F.radius_pos))
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hnear)
  let r := min R (t * (F.radius / 4)) / 2
  have hr : 0 < r := half_pos (lt_min hR (mul_pos ht (by linarith [F.radius_pos])))
  have hrR : r ≤ R := (half_le_self (le_of_lt (lt_min hR
    (mul_pos ht (by linarith [F.radius_pos]))))).trans (min_le_left _ _)
  have hrt : r ≤ t * (F.radius / 4) := (half_le_self (le_of_lt (lt_min hR
    (mul_pos ht (by linarith [F.radius_pos]))))).trans (min_le_right _ _)
  refine ⟨F, t, ht, htI, U, hU, heU, r, hr, ?_⟩
  intro e' he'
  obtain ⟨he'₀, hqnear⟩ := hsub he'
  obtain ⟨he'c, hfields⟩ := hdata e' he'₀
  let q := frameCoordinateState g c e'
  let P := fun v => heatRadialFrameFamily F t (v, q)
  have hqdist : dist q p < F.radius / 2 := hqnear
  have hqF : ((0 : FourSpace), q) ∈ ball (0, p) F.radius := by
    change max (dist (0 : FourSpace) 0) (dist q p) < F.radius
    simpa only [dist_self, max_eq_right dist_nonneg] using
      hqdist.trans (by linarith [F.radius_pos])
  let G := F.recenter q hqF
  have hP0 : P 0 = q := heatRadialFrameFamily_zero F q (ball_subset_closedBall hqF) t htI
  have hP : ContDiffAt ℝ 12 P 0 := by
    have hh := (hfields 0 (mem_ball_self hR)).1
    exact ContDiffAt.comp (f := fun v : FourSpace => (v, q))
      (g := heatRadialFrameFamily F t) 0 hh (contDiffAt_id.prodMk contDiffAt_const)
  have hlocal (v : FourSpace) (hv : v ∈ ball 0 r) :
      (P v).1 ∈ (chartAt FourSpace c).target ∧
      (P v).2ᵀ * metricInChart g c (P v).1 * (P v).2 = 1 ∧
      DifferentiableAt ℝ P v ∧
      (∑ i : Fin 4, v i • heatNormalFrameConnection g c P i v) = 0 ∧
      (P v).1 = chartAt FourSpace c (frameExponential g o e' v) := by
    obtain ⟨hreg, _, hc, hg, hexp⟩ := hfields v (ball_subset_ball hrR hv)
    have hd : DifferentiableAt ℝ P v :=
      (ContDiffAt.comp (f := fun w : FourSpace => (w, q))
        (g := heatRadialFrameFamily F t) v hreg
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
    have hscaled : ‖t⁻¹ • v‖ < F.radius / 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      apply (inv_mul_lt_iff₀ ht).mpr
      exact (show ‖v‖ < r from by simpa only [mem_ball, dist_zero_right] using hv).trans_le hrt
    have hG : (t⁻¹ • v, q) ∈ ball (0, q) G.radius := by
      change max (dist (t⁻¹ • v) 0) (dist q q) < (F.radius - dist (0, q) (0, p)) / 2
      have hdq : dist ((0 : FourSpace), q) (0, p) = dist q p := by
        change max (dist (0 : FourSpace) 0) (dist q p) = dist q p
        simp only [dist_self, max_eq_right dist_nonneg]
      rw [hdq, dist_self, dist_zero_right, max_eq_left (norm_nonneg _)]
      linarith
    have hrad : fderiv ℝ P v v = (heatRadialFrameField g c (v, P v)).2 :=
      heatRadialFrameEndpoint_radial_derivative G t ht htI.2 v hG hd
    exact ⟨hc, hg, hd, heatNormalFrameConnection_radial g c P v hrad, hexp⟩
  have hc0 := (hlocal 0 (mem_ball_self hr)).1
  have hdet : (P 0).2.det ≠ 0 := by
    have hg := congrArg Matrix.det (hlocal 0 (mem_ball_self hr)).2.1
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  refine ⟨he'c, {
    point := P
    regular := hP
    initial := hP0
    radius := r
    radius_pos := hr
    exponential := fun v hv => (hlocal v hv).2.2.2.2
    in_chart := fun v hv => (hlocal v hv).1
    orthonormal := fun v hv => (hlocal v hv).2.1
    differentiable := fun v hv => (hlocal v hv).2.2.1
    radial_connection := fun v hv => (hlocal v hv).2.2.2.1
    connection_regular := fun i j k => heatNormalFrameConnection_contDiffAt 11 g c P 0 hP hc0 hdet i j k
  }, rfl, rfl, (hfields 0 (mem_ball_self hR)).1⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Metric compatibility of the actual radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormalFrameConnection_skew (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hn : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i : Fin 4) :
    (heatNormalFrameConnection g c P i x)ᵀ = -heatNormalFrameConnection g c P i x := by
  let E := fun y => (P y).2
  let H := fun y => metricInChart g c (P y).1
  have hE (r s : Fin 4) : DifferentiableAt ℝ (fun y => E y r s) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hP.snd r) s
  have hH (r s : Fin 4) : DifferentiableAt ℝ (fun y => H y r s) x := by
    exact ((metricInChart_contDiffAt g c (P x).1 hx r s).differentiableAt
      (by simp)).comp x hP.fst
  have hn0 : (E x)ᵀ * H x * E x = 1 := hn.self_of_nhds
  have hdet : (E x).det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hn0
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have heq : (fun y => (E y)ᵀ * (H y * E y)) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hn] with y hy
    simpa only [Matrix.mul_assoc] using hy
  have hzero : matrixPartial (fun y => (E y)ᵀ * (H y * E y)) i x = 0 := by
    rw [matrixPartial_congr heq]
    ext r s
    change fderiv ℝ (fun _ : FourSpace => (1 : Mat4) r s) x (coordinateVector i) = 0
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      (fderiv_const_apply (𝕜 := ℝ) (x := x) ((1 : Mat4) r s))
  have hd := matrixPartial_congruence E H x hE hH i
  rw [hzero] at hd
  have hmatrix : matrixPartial E i x = (fderiv ℝ P x (coordinateVector i)).2 :=
    heatFrame_matrixPartial P x hP i
  have hmetric := heatFrame_metricPartial g c P x hP hx i
  change matrixPartial H i x = _ at hmetric
  rw [hmatrix, hmetric] at hd
  have hc := pulledConnection_metric_compatibility (H x) (E x)
    (fderiv ℝ P x (coordinateVector i)).2
    (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      connectionMatrix g c r (P x).1) (isUnit_iff_ne_zero.mpr hdet)
  rw [hn0, Matrix.mul_one, Matrix.one_mul] at hc
  apply eq_neg_of_add_eq_zero_left
  exact hc.trans hd.symm

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.connection_skew {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (i : Fin 4) :
    (heatNormalFrameConnection g c D.point i x)ᵀ =
      -heatNormalFrameConnection g c D.point i x := by
  apply heatNormalFrameConnection_skew g c D.point x (D.differentiable x hx) (D.in_chart x hx)
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact D.orthonormal y hy

theorem HeatNormalFrameData.connection_as_twoForm {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (i : Fin 4) :
    twoFormMatrix (twoFormExtract (heatNormalFrameConnection g c D.point i x)) =
      heatNormalFrameConnection g c D.point i x :=
  twoFormMatrix_extract _ (D.connection_skew x hx i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal-coordinate tensors define actual continuous tensors
on the intrinsic frame bundle by extension by zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalFrameTensorLift (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 2)
    (e : FrameBundle g) : CovariantCoordinates 2 := by
  classical
  exact if e.base ∈ C.target then
    frameTensor (frameChartMatrix g c e) (T (C.symm e.base)) else 0

theorem heatNormalFrameTensorLift_support (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 2)
    {e : FrameBundle g} (he : heatNormalFrameTensorLift g c C T e ≠ 0) :
    e.base ∈ C '' tsupport T := by
  classical
  by_cases hx : e.base ∈ C.target
  · refine ⟨C.symm e.base, subset_closure ?_, C.right_inv hx⟩
    intro hzero
    apply he
    rw [heatNormalFrameTensorLift, ite_eq_left hx, hzero]
    funext a
    simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · exact False.elim (he (by simp only [heatNormalFrameTensorLift, ite_eq_right hx]))

variable [T2Space M]

theorem heatNormalFrameTensorLift_continuous (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 2)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hT : ContinuousOn T C.source) (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatNormalFrameTensorLift g c C T) := by
  classical
  have hK : IsCompact (C '' tsupport T) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro e
  by_cases he : e.base ∈ C.target
  · have hinv : ContinuousAt (fun f : FrameBundle g => C.symm f.base) e :=
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)).comp
        (continuous_frameBase g).continuousAt
    have hval : ContinuousAt (fun f : FrameBundle g => T (C.symm f.base)) e :=
      (hT.continuousAt (C.open_source.mem_nhds (C.map_target he))).comp
        (f := fun f : FrameBundle g => C.symm f.base) hinv
    have hframe : ContinuousAt (fun f : FrameBundle g =>
        frameTensor (frameChartMatrix g c f) (T (C.symm f.base))) e := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        frameChartMatrix_continuousAt g c e (hCt he) (b k) (a k))).mul
          ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually (C.open_target.mem_nhds he)
    filter_upwards [hnear] with f hf
    change (if f.base ∈ C.target then _ else _) = _
    exact ite_eq_left hf
  · have hxK : e.base ∉ C '' tsupport T := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 2))).congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually
      (hK.isClosed.isOpen_compl.mem_nhds hxK)
    filter_upwards [hnear] with f hf
    exact not_ne_iff.mp (fun h => hf (heatNormalFrameTensorLift_support g c C T h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal-coordinate tensors define actual continuous tensors
on the intrinsic frame bundle by extension by zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalOneFrameLift (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 1)
    (e : FrameBundle g) : CovariantCoordinates 1 := by
  classical
  exact if e.base ∈ C.target then
    frameTensor (frameChartMatrix g c e) (T (C.symm e.base)) else 0

theorem heatNormalOneFrameLift_support (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 1)
    {e : FrameBundle g} (he : heatNormalOneFrameLift g c C T e ≠ 0) :
    e.base ∈ C '' tsupport T := by
  classical
  by_cases hx : e.base ∈ C.target
  · refine ⟨C.symm e.base, subset_closure ?_, C.right_inv hx⟩
    intro hzero
    apply he
    rw [heatNormalOneFrameLift, ite_eq_left hx, hzero]
    funext a
    simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · exact False.elim (he (by simp only [heatNormalOneFrameLift, ite_eq_right hx]))

variable [T2Space M]

theorem heatNormalOneFrameLift_continuous (g : SmoothMetric M) (c : M)
    (C : OpenPartialHomeomorph FourSpace M) (T : FourSpace → CovariantCoordinates 1)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hT : ContinuousOn T C.source) (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatNormalOneFrameLift g c C T) := by
  classical
  have hK : IsCompact (C '' tsupport T) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro e
  by_cases he : e.base ∈ C.target
  · have hinv : ContinuousAt (fun f : FrameBundle g => C.symm f.base) e :=
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)).comp
        (continuous_frameBase g).continuousAt
    have hval : ContinuousAt (fun f : FrameBundle g => T (C.symm f.base)) e :=
      (hT.continuousAt (C.open_source.mem_nhds (C.map_target he))).comp
        (f := fun f : FrameBundle g => C.symm f.base) hinv
    have hframe : ContinuousAt (fun f : FrameBundle g =>
        frameTensor (frameChartMatrix g c f) (T (C.symm f.base))) e := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        frameChartMatrix_continuousAt g c e (hCt he) (b k) (a k))).mul
          ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually (C.open_target.mem_nhds he)
    filter_upwards [hnear] with f hf
    change (if f.base ∈ C.target then _ else _) = _
    exact ite_eq_left hf
  · have hxK : e.base ∉ C '' tsupport T := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 1))).congr_of_eventuallyEq
    have hnear := (continuous_frameBase g).continuousAt.eventually
      (hK.isClosed.isOpen_compl.mem_nhds hxK)
    filter_upwards [hnear] with f hf
    exact not_ne_iff.mp (fun h => hf (heatNormalOneFrameLift_support g c C T h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Zero extension through a normal chart needs only continuity on the
source when the amplitude has compact support there. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem heatNormalScalarLift_continuous (C : OpenPartialHomeomorph FourSpace M)
    (ψ : FourSpace → ℝ) (hψ : ContinuousOn ψ C.source)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ C.source) :
    Continuous (heatNormalScalarLift C ψ) := by
  classical
  have hK : IsCompact (C '' tsupport ψ) := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ C.target
  · have hi := C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hx)
    have hp := hψ.continuousAt (C.open_source.mem_nhds (C.map_target hx))
    apply (hp.comp hi).congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hx] with y hy
    exact heatNormalScalarLift_on_target C ψ hy
  · have hxK : x ∉ C '' tsupport ψ := by
      rintro ⟨z, hz, hzx⟩
      exact hx (hzx ▸ C.map_source (hs hz))
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact Function.notMem_support.mp (fun h => hy (heatNormalScalarLift_support C ψ h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finiteness and boundedness of the actual Riemannian distance on the
connected compact manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem metricEDistance_continuous (g : SmoothMetric M) :
    Continuous (fun p : M × M => metricEDistance g p.1 p.2) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  exact continuous_edist

theorem metricEDistance_ne_top [PreconnectedSpace M] (g : SmoothMetric M) (x y : M) :
    metricEDistance g x y ≠ (⊤ : ℝ≥0∞) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  have hclopen : IsClopen (eball x (⊤ : ℝ≥0∞)) :=
    ⟨isClosed_eball_top, isOpen_eball⟩
  have heq : eball x (⊤ : ℝ≥0∞) = univ :=
    hclopen.eq_univ ⟨x, mem_eball_self (by simp)⟩
  have hy : y ∈ eball x (⊤ : ℝ≥0∞) := heq ▸ mem_univ y
  have hlt : edist y x < (⊤ : ℝ≥0∞) := hy
  change edist x y ≠ (⊤ : ℝ≥0∞)
  rw [edist_comm]
  exact hlt.ne

theorem metricEDistance_toReal_continuous [PreconnectedSpace M] (g : SmoothMetric M) :
    Continuous (fun p : M × M => (metricEDistance g p.1 p.2).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : ContinuousAt (fun q : M × M => metricEDistance g q.1 q.2) p :=
    (metricEDistance_continuous g).continuousAt
  exact ContinuousAt.comp (f := fun q : M × M => metricEDistance g q.1 q.2) (x := p)
    (ENNReal.continuousAt_toReal (metricEDistance_ne_top g p.1 p.2)) hp

theorem metricEDistance_uniform_bound [PreconnectedSpace M] [CompactSpace M]
    (g : SmoothMetric M) (x : M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : M, metricEDistance g x y ≤ ENNReal.ofReal D := by
  have hc : Continuous (fun y : M => (metricEDistance g x y).toReal) :=
    (metricEDistance_toReal_continuous g).comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, _, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hc.continuousOn
  refine ⟨(metricEDistance g x y).toReal, ENNReal.toReal_nonneg, fun z => ?_⟩
  rw [← ENNReal.ofReal_toReal (metricEDistance_ne_top g x z)]
  exact ENNReal.ofReal_le_ofReal (hmax (mem_univ z))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut time is the last time at which a radial geodesic
minimizes distance from its base. Its existence follows from local
minimization, compactness and the metric triangle inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def frameMinimizingTimes (g : SmoothMetric M) (e : FrameBundle g) : Set ℝ :=
  {t | 0 ≤ t ∧ metricEDistance g e.base (frameGeodesic g 0 e t) = ENNReal.ofReal t}

theorem frameMinimizingTimes_zero (g : SmoothMetric M) (e : FrameBundle g) :
    0 ∈ frameMinimizingTimes g e := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  refine ⟨le_rfl, ?_⟩
  simp only [frameGeodesic, parallelFrameFlowMap_zero, ENNReal.ofReal_zero]
  exact Manifold.riemannianEDist_self

theorem frameMinimizingTimes_closed (g : SmoothMetric M) (e : FrameBundle g) :
    IsClosed (frameMinimizingTimes g e) := by
  apply IsClosed.inter (isClosed_Ici : IsClosed (Ici (0 : ℝ)))
  exact isClosed_eq ((metricEDistance_continuous g).comp
    (continuous_const.prodMk (frameGeodesic_continuous g 0 e))) ENNReal.continuous_ofReal

theorem frameMinimizingTimes_downward (g : SmoothMetric M) (e : FrameBundle g)
    {s t : ℝ} (ht : t ∈ frameMinimizingTimes g e) (hs : 0 ≤ s) (hst : s ≤ t) :
    s ∈ frameMinimizingTimes g e := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hu : metricEDistance g e.base (frameGeodesic g 0 e s) ≤ ENNReal.ofReal s := by
    simpa only [abs_of_nonneg hs] using frameGeodesic_distance_from_start g 0 e s
  have hfin : metricEDistance g e.base (frameGeodesic g 0 e s) ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hseg : metricEDistance g (frameGeodesic g 0 e s) (frameGeodesic g 0 e t) ≤
      ENNReal.ofReal (t - s) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
      frameGeodesic_distance_le g 0 e s t
  have htri : ENNReal.ofReal t ≤
      metricEDistance g e.base (frameGeodesic g 0 e s) + ENNReal.ofReal (t - s) := by
    rw [← ht.2]
    exact (Manifold.riemannianEDist_triangle (I := I4) (x := e.base)
      (y := frameGeodesic g 0 e s) (z := frameGeodesic g 0 e t)).trans
        (add_le_add le_rfl hseg)
  refine ⟨hs, le_antisymm hu ?_⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) htri
  rw [ENNReal.toReal_ofReal ht.1, ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] at hreal
  linarith

theorem frameMinimizingTimes_has_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    ∃ t ∈ frameMinimizingTimes g e, 0 < t := by
  obtain ⟨r, hr, hmin⟩ := frameExponential_locally_minimizing g o hRic e he
  let t := r / 2
  have ht : 0 < t := half_pos hr
  have hc : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
  have hn : ‖t • (coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hc, mul_one]
  have hsmall : ‖t • (coordinateVector 0 : FourSpace)‖ < r := by rw [hn]; dsimp [t]; linarith
  have hm := hmin (t • coordinateVector 0) hsmall
  rw [frameExponential_first_ray g o e he t ht, hn] at hm
  exact ⟨t, ⟨ht.le, hm⟩, ht⟩

variable [PreconnectedSpace M]

theorem frameMinimizingTimes_bddAbove (g : SmoothMetric M) (e : FrameBundle g) :
    BddAbove (frameMinimizingTimes g e) := by
  obtain ⟨D, hD, hbound⟩ := metricEDistance_uniform_bound g e.base
  refine ⟨D, fun t ht => ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hD).mp (ht.2 ▸ hbound (frameGeodesic g 0 e t))

def actualCutTime (g : SmoothMetric M) (e : FrameBundle g) : ℝ :=
  sSup (frameMinimizingTimes g e)

theorem actualCutTime_mem (g : SmoothMetric M) (e : FrameBundle g) :
    actualCutTime g e ∈ frameMinimizingTimes g e :=
  (frameMinimizingTimes_closed g e).csSup_mem ⟨0, frameMinimizingTimes_zero g e⟩
    (frameMinimizingTimes_bddAbove g e)

theorem actualCutTime_pos (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    0 < actualCutTime g e := by
  obtain ⟨t, ht, hpos⟩ := frameMinimizingTimes_has_positive g o hRic e he
  exact hpos.trans_le (le_csSup (frameMinimizingTimes_bddAbove g e) ht)

theorem frameMinimizingTimes_eq_Icc (g : SmoothMetric M) (e : FrameBundle g) :
    frameMinimizingTimes g e = Icc 0 (actualCutTime g e) := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.1, le_csSup (frameMinimizingTimes_bddAbove g e) ht⟩
  · intro ht
    exact frameMinimizingTimes_downward g e (actualCutTime_mem g e) ht.1 ht.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual exponential, including zero vectors and
varying base frames. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_joint_continuous (g : SmoothMetric M) (o : FrameOrientation g) :
    Continuous (fun p : FrameBundle g × FourSpace => frameExponential g o p.1 p.2) := by
  let U : Set (FrameBundle g × FourSpace) := {p | p.2 ≠ 0}
  have hU : IsOpen U := isOpen_compl_singleton.preimage continuous_snd
  have hpol : Continuous (fun p : U => euclideanPolarHomeomorph
      (⟨p.val.2, p.property⟩ : ({0}ᶜ : Set FourSpace))) :=
    euclideanPolarHomeomorph.continuous.comp
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  have hturn : Continuous (fun p : U => unitTangentTurn p.val.1
      (euclideanPolarHomeomorph (⟨p.val.2,p.property⟩ : ({0}ᶜ : Set FourSpace))).1) :=
    continuous_unitTangentTurn.comp ((continuous_fst.comp continuous_subtype_val).prodMk hpol.fst)
  have htime : Continuous (fun p : U =>
      (euclideanPolarHomeomorph (⟨p.val.2,p.property⟩ : ({0}ᶜ : Set FourSpace))).2.val) :=
    continuous_subtype_val.comp hpol.snd
  have hnonzero : ContinuousOn
      (fun p : FrameBundle g × FourSpace => frameExponential g o p.1 p.2) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := (continuous_unitTangentBase g).comp
      ((unitTangentFlowMap_continuous g o).comp (htime.prodMk hturn))
    exact h.congr (fun p => (frameExponential_nonzero g o p.val.1 ⟨p.val.2,p.property⟩).symm)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨e,v⟩
  by_cases hv : v = 0
  · subst v
    let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
    apply (tendsto_iff_edist_tendsto_0).mpr
    change Tendsto (fun p : FrameBundle g × FourSpace =>
      edist (frameExponential g o p.1 p.2) (frameExponential g o e 0)) (𝓝 (e,0)) (𝓝 0)
    rw [frameExponential_zero]
    have hb : Tendsto (fun p : FrameBundle g × FourSpace =>
        metricEDistance g p.1.base e.base) (𝓝 (e,0)) (𝓝 0) := by
      have h : Continuous (fun p : FrameBundle g × FourSpace =>
          metricEDistance g p.1.base e.base) :=
        (metricEDistance_continuous g).comp
          (((continuous_frameBase g).comp continuous_fst).prodMk continuous_const)
      simpa only [metricEDistance, Manifold.riemannianEDist_self] using h.tendsto (e,(0 : FourSpace))
    have hn : Tendsto (fun p : FrameBundle g × FourSpace => ENNReal.ofReal ‖p.2‖)
        (𝓝 (e,0)) (𝓝 0) := by
      have h : Continuous (fun p : FrameBundle g × FourSpace => ENNReal.ofReal ‖p.2‖) :=
        ENNReal.continuous_ofReal.comp (continuous_norm.comp continuous_snd)
      simpa only [norm_zero, ENNReal.ofReal_zero] using h.tendsto (e,(0 : FourSpace))
    have hsum : Tendsto (fun p : FrameBundle g × FourSpace =>
        ENNReal.ofReal ‖p.2‖ + metricEDistance g p.1.base e.base) (𝓝 (e,0)) (𝓝 0) := by
      simpa only [zero_add] using hn.add hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le)
    intro p
    exact (Manifold.riemannianEDist_triangle (I := I4)
      (x := frameExponential g o p.1 p.2) (y := p.1.base) (z := e.base)).trans
      (add_le_add (by
        rw [Manifold.riemannianEDist_comm]
        exact frameExponential_distance g o p.1 p.2) le_rfl)
  · exact (hnonzero (e,v) hv).continuousAt (hU.mem_nhds hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative-slot correction in the covariant Hessian trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem heat_connection_trace_expand (H Q : Mat4) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (S : Fin 4 → ℝ) :
    -(∑ p, ∑ q, H p q * Q p q) +
      (∑ r, (∑ p, ∑ q, H p q * Γ r p q) * S r) =
    -(∑ p, ∑ q, H p q * (Q p q - ∑ r, Γ r p q * S r)) := by
  have he : (∑ r, (∑ p, ∑ q, H p q * Γ r p q) * S r) =
      ∑ p, ∑ q, H p q * (∑ r, Γ r p q * S r) := by
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  rw [he]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framed_second_covariant {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (E : Mat4) (x : FourSpace)
    (p q : Fin 4) (a : Fin n → Fin 4) :
    frameTensor E (fun v => covariantDerivative g c (covariantDerivative g c T) x
      (Fin.cons q (Fin.cons p v))) a =
      frameTensor E (tensorCovariantDirection (connectionMatrix g c)
        (tensorCovariantDirection (connectionMatrix g c) T p) q x) a -
      ∑ r, christoffel g c x r q p *
        frameTensor E (tensorCovariantDirection (connectionMatrix g c) T r x) a := by
  have he : (fun v => covariantDerivative g c (covariantDerivative g c T) x
      (Fin.cons q (Fin.cons p v))) =
      tensorCovariantDirection (connectionMatrix g c)
        (tensorCovariantDirection (connectionMatrix g c) T p) q x -
      (fun v => ∑ r, christoffel g c x r q p *
        tensorCovariantDirection (connectionMatrix g c) T r x v) := by
    funext v
    exact covariantDerivative_iterated_direction g c T x q p v
  rw [he, frameTensor_sub, frameTensor_sum]
  simp only [frameTensor_const_mul]

theorem heat_framed_twoFormSecondTrace (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 2) (E H : Mat4) (x : FourSpace)
    (hH : Hᵀ = H) (a : Fin 2 → Fin 4) :
    frameTensor E (twoFormSecondTrace H (covariantDerivative g c
      (covariantDerivative g c T) x)) a =
      ∑ p, ∑ q, H p q * (frameTensor E
        (tensorCovariantDirection (connectionMatrix g c)
          (tensorCovariantDirection (connectionMatrix g c) T p) q x) a -
        ∑ r, christoffel g c x r p q *
          frameTensor E (tensorCovariantDirection (connectionMatrix g c) T r x) a) := by
  have hsym (p q : Fin 4) : H q p = H p q := congrArg (fun A : Mat4 => A p q) hH
  unfold twoFormSecondTrace
  rw [frameTensor_sum]
  simp_rw [frameTensor_sum, frameTensor_const_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hsym, heat_framed_second_covariant]
  have hc (r : Fin 4) : christoffel g c x r q p = christoffel g c x r p q :=
    christoffel_comm g c x r q p
  simp only [hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! First-order product and germ rules used for the second covariant
derivative in normal coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_covariant_congr {n : ℕ} (C : Fin 4 → FourSpace → Mat4)
    (S T : FourSpace → CovariantCoordinates n) (x : FourSpace)
    (h : S =ᶠ[𝓝 x] T) (i : Fin 4) :
    tensorCovariantDirection C S i x = tensorCovariantDirection C T i x := by
  funext a
  have he : (fun y => S y a) =ᶠ[𝓝 x] (fun y => T y a) :=
    h.mono fun y hy => congrFun hy a
  have hd := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq
  change partialDeriv (fun y => S y a) i x = partialDeriv (fun y => T y a) i x at hd
  change partialDeriv (fun y => S y a) i x - tensorSlotAction (C i x) (S x) a = _
  rw [hd, h.self_of_nhds]
  rfl

theorem heat_covariant_weighted_sum {n : ℕ} (C : Fin 4 → FourSpace → Mat4)
    (f : Fin 4 → FourSpace → ℝ) (S : Fin 4 → FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hf : ∀ r, DifferentiableAt ℝ (f r) x)
    (hS : ∀ r a, DifferentiableAt ℝ (fun y => S r y a) x) (i : Fin 4) :
    tensorCovariantDirection C (fun y a => ∑ r, f r y * S r y a) i x =
      fun a => ∑ r, (partialDeriv (f r) i x * S r x a +
        f r x * tensorCovariantDirection C (S r) i x a) := by
  funext a
  have hd : partialDeriv (fun y => ∑ r, f r y * S r y a) i x =
      ∑ r, (partialDeriv (f r) i x * S r x a +
        f r x * partialDeriv (fun y => S r y a) i x) := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun r y => f r y * S r y a)
      (fun r _ => (hf r).mul (hS r a)), _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro r _
    simp only [fderiv_fun_mul (hf r) (hS r a), _root_.add_apply, _root_.smul_apply,
      smul_eq_mul]
    ring
  change partialDeriv (fun y => ∑ r, f r y * S r y a) i x -
    tensorSlotAction (C i x) (fun b => ∑ r, f r x * S r x b) a = _
  rw [hd, tensorSlotAction_sum]
  simp only [tensorSlotAction_const_mul, tensorCovariantDirection, Pi.sub_apply,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, tensorPartial]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer a slice of the joint inverse to the manifold on a prescribed
common ball. No new inverse or regularity assumption enters the geometry. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamily_manifold_chart {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (r : ℝ) (_hr : 0 < r) (hrD : r ≤ D.radius)
    (hsource : ∀ x ∈ ball (0 : FourSpace) r,
      frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hs : ∀ x ∈ ball (0 : FourSpace) r,
      x ∈ (heatFamilySliceChart P H hH (frameCoordinateState g c e)).source)
    (hi : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 4
      (heatFamilySliceChart P H hH (frameCoordinateState g c e)).symm
        (P (x, frameCoordinateState g c e)).1) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      C.target ⊆ (chartAt FourSpace c).source ∧ ContMDiffOn I4 I4 4 C.symm C.target := by
  let q := frameCoordinateState g c e
  let S₀ := heatFamilySliceChart P H hH q
  let S := S₀.restrOpen (ball 0 r) isOpen_ball
  have hS : S.source = ball 0 r := inter_eq_right.mpr (fun x hx => hs x hx)
  have hxD {x : FourSpace} (hx : x ∈ ball 0 r) : x ∈ ball 0 D.radius :=
    ball_subset_ball hrD hx
  have hchart {x : FourSpace} (hx : x ∈ ball 0 r) : S x ∈ (chartAt FourSpace c).target := by
    have hh := D.in_chart x (hxD hx)
    change (P (x, q)).1 ∈ (chartAt FourSpace c).target
    simpa only [hpoint] using hh
  let C := S.trans (chartAt FourSpace c).symm
  have hC : C.source = ball 0 r := by
    apply Set.ext
    intro x
    change (x ∈ S.source ∧ S x ∈ (chartAt FourSpace c).target) ↔ x ∈ ball 0 r
    rw [hS]
    exact ⟨And.left, fun hx => ⟨hx, hchart hx⟩⟩
  have heq : EqOn C (frameExponential g o e) C.source := by
    intro x hx
    have hb : x ∈ ball 0 r := hC ▸ hx
    have hd := D.exponential x (hxD hb)
    rw [hpoint] at hd
    change (chartAt FourSpace c).symm (P (x, q)).1 = _
    rw [hd]
    exact (chartAt FourSpace c).left_inv (hsource x hb)
  have htarget : C.target ⊆ (chartAt FourSpace c).source := by
    intro y hy
    let x := C.symm y
    have hx : x ∈ ball 0 r := hC ▸ C.map_target hy
    have h := (chartAt FourSpace c).map_target (hchart hx)
    change C x ∈ (chartAt FourSpace c).source at h
    rwa [C.right_inv hy] at h
  refine ⟨C, hC, heq, htarget, ?_⟩
  intro y hy
  let x := C.symm y
  have hx : x ∈ ball 0 r := hC ▸ C.map_target hy
  have hexp : frameExponential g o e x = y := (heq (C.map_target hy)).symm.trans (C.right_inv hy)
  have hd : (P (x, q)).1 = chartAt FourSpace c y := by
    have hh := D.exponential x (hxD hx)
    simpa only [hpoint, hexp] using hh
  have hInv : ContDiffAt ℝ 4 S₀.symm (chartAt FourSpace c y) := hd ▸ hi x hx
  have hch : ContMDiffAt I4 I4 4 (chartAt FourSpace c) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) (htarget hy)
  have hh := hInv.contMDiffAt.comp y hch
  change ContMDiffAt I4 I4 4 C.symm y at hh
  exact hh.contMDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Jacobian calculus needed for the finite-regularity normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatJacobian_entry_regular (n : ℕ) {F : FourSpace → FourSpace} {x : FourSpace}
    (hF : ContDiffAt ℝ (n + 1) F x) (r i : Fin 4) :
    ContDiffAt ℝ n (fun y => jacobianMatrix F y r i) x := by
  have hd : ContDiffAt ℝ n (fderiv ℝ F) x := hF.fderiv_right (by norm_cast)
  exact (EuclideanSpace.proj r : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt.comp x
    (hd.clm_apply (contDiffAt_const (c := coordinateVector i)))

theorem heatJacobian_partial {F : FourSpace → FourSpace} {x : FourSpace}
    (hF : ContDiffAt ℝ 2 F x) (r i j : Fin 4) :
    partialDeriv (fun y => jacobianMatrix F y r j) i x =
      fderiv ℝ (fderiv ℝ F) x (coordinateVector i) (coordinateVector j) r := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hF.fderiv_right (by norm_num)
  have he := hd.differentiableAt one_ne_zero |>.hasFDerivAt
  have ha := he.clm_apply (hasFDerivAt_const (coordinateVector j) x)
  have hp := (EuclideanSpace.proj r : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp x ha
  have hh := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hp.fderiv
  simpa [partialDeriv, jacobianMatrix, Function.comp_def] using! hh

theorem heatJacobian_partials_commute {F : FourSpace → FourSpace} {x : FourSpace}
    (hF : ContDiffAt ℝ 2 F x) (r i j : Fin 4) :
    partialDeriv (fun y => jacobianMatrix F y r j) i x =
      partialDeriv (fun y => jacobianMatrix F y r i) j x := by
  rw [heatJacobian_partial hF, heatJacobian_partial hF]
  exact congrArg (fun v : FourSpace => v r)
    ((hF.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector i) (coordinateVector j))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact finite-regularity normal-frame amplitude determines an
actual element of the global two-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalCoordinateTensor_continuousOn (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hP : ContDiffOn ℝ 2 D.point C.source)
    (hD : C.source ⊆ ball 0 D.radius) (a : FourSpace → TwoFormFour)
    (ha : ContDiff ℝ 2 a) : ContinuousOn (heatNormalCoordinateTensor D a) C.source := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro v
  exact (heatNormalCoordinateTensor_regular D a x (hD hx)
    (hP.contDiffAt (C.open_source.mem_nhds hx)) ha.contDiffAt v).continuousAt

def heatNormalAmplitudeTensor (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun f => WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f),
    (PiLp.continuous_toLp 2 _).comp (heatNormalFrameTensorLift_continuous g c C _ hCt
      (heatNormalCoordinateTensor_continuousOn D C hP hD a ha)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCoordinateTensor_support D a))
      ((heatNormalCoordinateTensor_support D a).trans hs))⟩

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalAmplitudeL2 (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : TwoFormL2 o :=
  twoFormFromContinuousTensor (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs)

theorem heatNormalAmplitudeL2_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : SmoothL2TwoForm o) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothTwoFormToL2 v) =
      (1 / 2 : ℝ) * ∫ f, inner ℝ (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f)
        (smoothTwoFormEuclideanValue (v : smoothTwoForms o) f) ∂canonicalFrameMeasure g o :=
  twoFormFromContinuousTensor_pairing _ v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual coordinate tensor reconstructed
from a time-dependent normal amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCoordinateTensor_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → TwoFormFour)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source)) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalCoordinateTensor D (A z.1) z.2)
      (Ioi 0 ×ˢ C.source) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hPx := hP.contDiffAt (C.open_source.mem_nhds hz.2)
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) z.2 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hPx.snd i) j
  have hEi (i j : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => (D.point w.2).2⁻¹ i j) z :=
    (heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) z.2 hE
      (heatNormalFrame_matrix_nondegenerate D (hD hz.2)) i j).continuousAt.comp continuousAt_snd
  have hAc := hA.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds hz)
  have hT : ContinuousAt (fun w : ℝ × FourSpace => twoFormTensor (A w.1 w.2)) z :=
    twoFormTensorLinear.toContinuousLinearMap.continuous.continuousAt.comp hAc
  apply continuousAt_pi.mpr
  intro v
  change ContinuousAt (fun w : ℝ × FourSpace =>
    ∑ b, (∏ k, (D.point w.2).2⁻¹ (b k) (v k)) * twoFormTensor (A w.1 w.2) b) z
  apply tendsto_finsetSum
  intro b _
  exact (tendsto_finsetProd _ (fun k _ => hEi (b k) (v k))).mul
    ((continuous_apply b).continuousAt.comp hT)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame connection acts on actual covariant derivatives of
the original geometric tensor, with the differential of the base map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_covariant_pullback {n : ℕ} (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hP : DifferentiableAt ℝ P x)
    (hT : ∀ a, DifferentiableAt ℝ (fun z => T z a) (P x).1)
    (hG : (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1) (i : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (T (P y).1)) i x =
    frameTensor (P x).2 (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      tensorCovariantDirection (connectionMatrix g c) T r (P x).1) := by
  have hE (a b : Fin 4) : DifferentiableAt ℝ (fun y => (P y).2 a b) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hP.snd a) b
  have hdet : IsUnit (P x).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hG
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hC : (P x).2 * heatNormalFrameConnection g c P i x =
      matrixPartial (fun y => (P y).2) i x +
        (∑ r : Fin 4, jacobianMatrix (fun y => (P y).1) x r i •
          connectionMatrix g c r (P x).1) * (P x).2 := by
    rw [heatFrame_matrixPartial P x hP i]
    simp_rw [heatFrame_baseJacobian P x hP]
    exact pulledConnection_equation _ _ _ hdet
  have h := heat_covariantDirection_pullback (fun y => (P y).1) (fun y => (P y).2)
    (heatNormalFrameConnection g c P) (connectionMatrix g c) T x hP.fst hE hT i hC
  simpa only [heatFrame_baseJacobian P x hP] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous family of normal tensors with one compact support
lifts to a jointly continuous family on the actual frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] {g : SmoothMetric M} {c : M}

theorem heatNormalFrameTensorLift_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : ℝ → FourSpace → CovariantCoordinates 2)
    (hT : ContinuousOn (fun z : ℝ × FourSpace => T z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hs : ∀ t > 0, tsupport (T t) ⊆ K) :
    ContinuousOn (fun z : ℝ × FrameBundle g => heatNormalFrameTensorLift g c C (T z.1) z.2)
      (Ioi 0 ×ˢ univ) := by
  have hCK : IsCompact (C '' K) := hK.image_of_continuousOn (C.continuousOn.mono hKC)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hbase : Continuous (fun w : ℝ × FrameBundle g => w.2.base) :=
    (continuous_frameBase g).comp continuous_snd
  by_cases he : z.2.base ∈ C.target
  · have hinv : ContinuousAt (fun w : ℝ × FrameBundle g => C.symm w.2.base) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2.base) (x := z)
        (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)) hbase.continuousAt
    have harg : ContinuousAt (fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base)) z :=
      continuousAt_fst.prodMk hinv
    have hTc : ContinuousAt (fun w : ℝ × FourSpace => T w.1 w.2) (z.1, C.symm z.2.base) :=
      hT.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds
        (show (z.1, C.symm z.2.base) ∈ Ioi (0 : ℝ) ×ˢ C.source from ⟨hz.1, C.map_target he⟩))
    have hval : ContinuousAt (fun w : ℝ × FrameBundle g => T w.1 (C.symm w.2.base)) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base))
        (x := z) hTc harg
    have hframe : ContinuousAt (fun w : ℝ × FrameBundle g =>
        frameTensor (frameChartMatrix g c w.2) (T w.1 (C.symm w.2.base))) z := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2) (x := z)
          (frameChartMatrix_continuousAt g c z.2 (hCt he) (b k) (a k)) continuousAt_snd)).mul
        ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (C.open_target.mem_nhds he)
    filter_upwards [hn] with w hw
    exact ite_eq_left hw
  · have hnot : z.2.base ∉ C '' K := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hKC hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 2))).congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (hCK.isClosed.isOpen_compl.mem_nhds hnot)
    have ht : ∀ᶠ w : ℝ × FrameBundle g in 𝓝 z, 0 < w.1 :=
      continuousAt_fst.eventually (Ioi_mem_nhds hz.1)
    filter_upwards [hn, ht] with w hw hwt
    apply not_ne_iff.mp
    intro hne
    obtain ⟨x, hx, hxe⟩ := heatNormalFrameTensorLift_support g c C (T w.1) hne
    exact hw ⟨x, hs w.1 hwt hx, hxe⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Convert a one-form amplitude in the constructed parallel frame to
an actual coordinate covector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalOneCoordinates {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → FourSpace) (x : FourSpace) : CovariantCoordinates 1 :=
  frameTensor (D.point x).2⁻¹ (fun v => a x (v 0))

theorem heatNormalOneCoordinates_regular {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → FourSpace) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x) (ha : ContDiffAt ℝ 2 a x)
    (v : Fin 1 → Fin 4) : ContDiffAt ℝ 2 (fun y => heatNormalOneCoordinates D a y v) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hEi (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2⁻¹ i j) x :=
    heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) x hE
      (heatNormalFrame_matrix_nondegenerate D hx) i j
  change ContDiffAt ℝ 2 (fun y => ∑ b : Fin 1 → Fin 4, (∏ k, (D.point y).2⁻¹ (b k) (v k)) *
    a y (b 0)) x
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod (fun k _ => hEi (b k) (v k))).mul
    ((EuclideanSpace.proj (b 0) : FourSpace →L[ℝ] ℝ).contDiff.comp_contDiffAt x ha)

theorem heatNormalOneCoordinates_support {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (a : FourSpace → FourSpace) :
    tsupport (heatNormalOneCoordinates D a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have ha : a x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  simp only [heatNormalOneCoordinates, ha, PiLp.zero_apply]
  funext v
  simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous family of normal tensors with one compact support
lifts to a jointly continuous family on the actual frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] {g : SmoothMetric M} {c : M}

theorem heatNormalOneFrameLift_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : ℝ → FourSpace → CovariantCoordinates 1)
    (hT : ContinuousOn (fun z : ℝ × FourSpace => T z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hs : ∀ t > 0, tsupport (T t) ⊆ K) :
    ContinuousOn (fun z : ℝ × FrameBundle g => heatNormalOneFrameLift g c C (T z.1) z.2)
      (Ioi 0 ×ˢ univ) := by
  have hCK : IsCompact (C '' K) := hK.image_of_continuousOn (C.continuousOn.mono hKC)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hbase : Continuous (fun w : ℝ × FrameBundle g => w.2.base) :=
    (continuous_frameBase g).comp continuous_snd
  by_cases he : z.2.base ∈ C.target
  · have hinv : ContinuousAt (fun w : ℝ × FrameBundle g => C.symm w.2.base) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2.base) (x := z)
        (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)) hbase.continuousAt
    have harg : ContinuousAt (fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base)) z :=
      continuousAt_fst.prodMk hinv
    have hTc : ContinuousAt (fun w : ℝ × FourSpace => T w.1 w.2) (z.1, C.symm z.2.base) :=
      hT.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds
        (show (z.1, C.symm z.2.base) ∈ Ioi (0 : ℝ) ×ˢ C.source from ⟨hz.1, C.map_target he⟩))
    have hval : ContinuousAt (fun w : ℝ × FrameBundle g => T w.1 (C.symm w.2.base)) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base))
        (x := z) hTc harg
    have hframe : ContinuousAt (fun w : ℝ × FrameBundle g =>
        frameTensor (frameChartMatrix g c w.2) (T w.1 (C.symm w.2.base))) z := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2) (x := z)
          (frameChartMatrix_continuousAt g c z.2 (hCt he) (b k) (a k)) continuousAt_snd)).mul
        ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (C.open_target.mem_nhds he)
    filter_upwards [hn] with w hw
    exact ite_eq_left hw
  · have hnot : z.2.base ∉ C '' K := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hKC hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 1))).congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (hCK.isClosed.isOpen_compl.mem_nhds hnot)
    have ht : ∀ᶠ w : ℝ × FrameBundle g in 𝓝 z, 0 < w.1 :=
      continuousAt_fst.eventually (Ioi_mem_nhds hz.1)
    filter_upwards [hn, ht] with w hw hwt
    apply not_ne_iff.mp
    intro hne
    obtain ⟨x, hx, hxe⟩ := heatNormalOneFrameLift_support g c C (T w.1) hne
    exact hw ⟨x, hs w.1 hwt hx, hxe⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-dimensional action of the actual normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatTwoFormSkewAction_swap (b a : TwoFormFour) :
    twoFormSkewAction b a = -twoFormSkewAction a b := by
  ext k
  fin_cases k <;> simp [twoFormSkewAction] <;> ring

def heatConnectionActionLinear (a : TwoFormFour) : Mat4 →ₗ[ℝ] TwoFormFour :=
  -(twoFormSkewActionLinear a).comp twoFormExtractLinear

theorem heatConnectionActionLinear_apply (a : TwoFormFour) (B : Mat4) :
    heatConnectionActionLinear a B = twoFormSkewAction (twoFormExtract B) a :=
  (heatTwoFormSkewAction_swap _ _).symm

def heatTwoFormConnectionMatrix (B : Mat4) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun k l => twoFormSkewAction (twoFormExtract B) (EuclideanSpace.basisFun (Fin 6) ℝ l) k

theorem heatTwoFormConnectionMatrix_action (B : Mat4) (a : TwoFormFour) :
    heatTwoFormConnectionMatrix B *ᵥ WithLp.ofLp a =
      WithLp.ofLp (twoFormSkewAction (twoFormExtract B) a) := by
  ext k
  fin_cases k <;>
    simp [heatTwoFormConnectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, twoFormSkewAction, EuclideanSpace.basisFun_apply] <;> ring

theorem heatTwoFormConnectionMatrix_skew (B : Mat4) :
    (heatTwoFormConnectionMatrix B)ᵀ = -heatTwoFormConnectionMatrix B := by
  ext k l
  have h := twoFormSkewAction_skewAdjoint (twoFormExtract B)
    (EuclideanSpace.basisFun (Fin 6) ℝ k) (EuclideanSpace.basisFun (Fin 6) ℝ l)
  simpa only [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_inner,
    heatTwoFormConnectionMatrix, Matrix.transpose_apply, Matrix.neg_apply] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatTwoFormConnection (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (i : Fin 4) (x : FourSpace) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  heatTwoFormConnectionMatrix (heatNormalFrameConnection g c P i x)

theorem heatTwoFormConnection_radial (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (h : (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0) :
    (∑ i : Fin 4, x i • heatTwoFormConnection g c P i x) = 0 := by
  ext k l
  have he := congrArg (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)) h
  simp only [map_sum, map_smul, map_zero, heatConnectionActionLinear_apply] at he
  have hk := congrArg (fun a : TwoFormFour => a k) he
  simpa only [heatTwoFormConnection, heatTwoFormConnectionMatrix, Matrix.sum_apply,
    Matrix.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.zero_apply, Matrix.zero_apply] using hk

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.twoForm_connection_radial {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ Metric.ball 0 D.radius) :
    (∑ i : Fin 4, x i • heatTwoFormConnection g c D.point i x) = 0 :=
  heatTwoFormConnection_radial g c D.point x (D.radial_connection x hx)

theorem HeatNormalFrameData.twoForm_connection_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ 11 (fun x => heatTwoFormConnection g c D.point i x k l) 0 := by
  have hB : ContDiffAt ℝ 11 (heatNormalFrameConnection g c D.point i) 0 :=
    contDiffAt_pi.mpr (fun j => contDiffAt_pi.mpr (D.connection_regular i j))
  let L := (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).toContinuousLinearMap
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hc := π.contDiff.contDiffAt.comp 0 (L.contDiff.contDiffAt.comp 0 hB)
  change ContDiffAt ℝ 11
    (fun x => heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)
      (heatNormalFrameConnection g c D.point i x) k) 0 at hc
  simpa only [heatConnectionActionLinear_apply, heatTwoFormConnection,
    heatTwoFormConnectionMatrix] using hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness gives a nearest point on a metric sphere. Every path to
an exterior endpoint crosses that sphere, so the nearest point splits
the actual Riemannian distance exactly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [CompactSpace M] in
theorem metric_path_crosses_sphere (g : SmoothMetric M) (p q : M)
    (γ : ℝ → M) (hγ : Continuous γ) (hstart : γ 0 = p) (hend : γ 1 = q)
    (r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ (metricEDistance g p q).toReal) :
    ∃ t ∈ Icc (0 : ℝ) 1, metricEDistance g p (γ t) = ENNReal.ofReal r := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let F := fun t => (metricEDistance g p (γ t)).toReal
  have hF : Continuous F := (metricEDistance_toReal_continuous g).comp
    (continuous_const.prodMk hγ)
  have h0 : F 0 = 0 := by
    change (metricEDistance g p (γ 0)).toReal = 0
    rw [hstart]
    simp [metricEDistance, Manifold.riemannianEDist_self]
  have h1 : F 1 = (metricEDistance g p q).toReal := by dsimp [F]; rw [hend]
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hF.continuousOn
    (show r ∈ Icc (F 0) (F 1) by rw [h0, h1]; exact ⟨hr, hrd⟩)
  refine ⟨t, ht, ?_⟩
  rw [← ENNReal.ofReal_toReal (metricEDistance_ne_top g p (γ t))]
  exact congrArg ENNReal.ofReal htr

theorem exists_metricDistance_split (g : SmoothMetric M) (p q : M)
    (r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ (metricEDistance g p q).toReal) :
    ∃ z : M, metricEDistance g p z = ENNReal.ofReal r ∧
      metricEDistance g p q = ENNReal.ofReal r + metricEDistance g z q := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let S := {z | metricEDistance g p z = ENNReal.ofReal r}
  have hS : IsCompact S := (isClosed_eq ((metricEDistance_continuous g).comp
    (continuous_const.prodMk continuous_id)) continuous_const).isCompact
  have hSne : S.Nonempty := by
    have hsmall : metricEDistance g p q < ENNReal.ofReal ((metricEDistance g p q).toReal + 1) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal (metricEDistance_ne_top g p q)]
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      linarith
    obtain ⟨γ, ha, hb, hγ, _, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hsmall zero_lt_one
    obtain ⟨t, _, ht⟩ := metric_path_crosses_sphere g p q γ hγ.continuous ha hb r hr hrd
    exact ⟨γ t, ht⟩
  have hc : Continuous (fun z : M => (metricEDistance g z q).toReal) :=
    (metricEDistance_toReal_continuous g).comp (continuous_id.prodMk continuous_const)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  have hmin' : ∀ w ∈ S, metricEDistance g z q ≤ metricEDistance g w q := by
    intro w hw
    exact (ENNReal.toReal_le_toReal (metricEDistance_ne_top g z q)
      (metricEDistance_ne_top g w q)).mp (hmin hw)
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · have htri : metricEDistance g p q ≤ metricEDistance g p z + metricEDistance g z q :=
      Manifold.riemannianEDist_triangle
    rwa [show metricEDistance g p z = ENNReal.ofReal r from hz] at htri
  · by_contra h
    have hlt : metricEDistance g p q < ENNReal.ofReal r + metricEDistance g z q :=
      lt_of_not_ge h
    obtain ⟨γ, ha, hb, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
    obtain ⟨t, ht, htr⟩ := metric_path_crosses_sphere g p q γ hγ.continuous ha hb r hr hrd
    have hleft : ENNReal.ofReal r ≤ Manifold.pathELength I4 γ 0 t := by
      have hh := Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn ha rfl ht.1
      change metricEDistance g p (γ t) ≤ Manifold.pathELength I4 γ 0 t at hh
      rwa [htr] at hh
    have hright : metricEDistance g z q ≤ Manifold.pathELength I4 γ t 1 :=
      (hmin' (γ t) htr).trans
        (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl hb ht.2)
    have hsum := add_le_add hleft hright
    rw [Manifold.pathELength_add ht.1 ht.2] at hsum
    exact (not_lt_of_ge hsum) hlen

end
end PositiveEinsteinFour.Geometry
end


section

/-! Measurability of the actual distance-minimizing radial domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_upperSemicontinuous (g : SmoothMetric M) :
    UpperSemicontinuous (actualCutTime g) := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro t
  by_cases ht : 0 ≤ t
  · have heq : actualCutTime g ⁻¹' Ici t =
        {e : FrameBundle g | metricEDistance g e.base (frameGeodesic g 0 e t) =
          ENNReal.ofReal t} := by
      ext e
      change t ≤ actualCutTime g e ↔ _
      constructor
      · intro h
        have hm : t ∈ frameMinimizingTimes g e := by
          rw [frameMinimizingTimes_eq_Icc]
          exact ⟨ht, h⟩
        exact hm.2
      · intro h
        have hm : t ∈ frameMinimizingTimes g e := ⟨ht, h⟩
        rw [frameMinimizingTimes_eq_Icc] at hm
        exact hm.2
    rw [heq]
    have hpoint : Continuous (fun e : FrameBundle g => frameGeodesic g 0 e t) :=
      (continuous_frameBase g).comp (parallelFrameFlowMap_continuous_slice g 0 t)
    exact isClosed_eq ((metricEDistance_continuous g).comp
      ((continuous_frameBase g).prodMk hpoint)) continuous_const
  · have heq : actualCutTime g ⁻¹' Ici t = univ := by
      apply eq_univ_of_forall
      intro e
      exact (lt_of_not_ge ht).le.trans (actualCutTime_mem g e).1
    rw [heq]
    exact isClosed_univ

theorem actualCutTime_measurable (g : SmoothMetric M) : Measurable (actualCutTime g) :=
  (actualCutTime_upperSemicontinuous g).measurable

def actualMinimizingRadialDomain (g : SmoothMetric M) : Set (ℝ × FrameBundle g) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ actualCutTime g p.2}

theorem actualMinimizingRadialDomain_measurable (g : SmoothMetric M) :
    MeasurableSet (actualMinimizingRadialDomain g) :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst ((actualCutTime_measurable g).comp measurable_snd))

theorem mem_actualMinimizingRadialDomain_iff (g : SmoothMetric M)
    (p : ℝ × FrameBundle g) : p ∈ actualMinimizingRadialDomain g ↔
      p.1 ∈ frameMinimizingTimes g p.2 := by
  rw [frameMinimizingTimes_eq_Icc]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine inverse exponential branch is continuous jointly in the
initial frame and the endpoint, near any nonconjugate radial pair. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_joint_exponential_log (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e) :
    ∃ U : Set (FrameBundle g × M), IsOpen U ∧
      (e,frameGeodesic g 0 e t) ∈ U ∧
      ∃ log : FrameBundle g × M → FourSpace, ContinuousOn log U ∧
        log (e,frameGeodesic g 0 e t) = t • coordinateVector 0 ∧
        ∀ p ∈ U, frameExponential g o p.1 (log p) = p.2 := by
  let v : FourSpace := t • coordinateVector 0
  let c := e.base
  let d := (parallelFrameFlowMap g 0 t e).base
  have hc : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hvexp : frameExponential g o e v = d := frameExponential_first_ray g o e he t ht
  have hvn : ‖v‖ = t := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit, mul_one]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvn]; exact ht.ne')
  let q := frameCoordinateState g c e
  let P : HeatRadialFrameSpace → CoordinateFrameSpace :=
    fun z => (exponentialFamilyCoordinates g o c d z, 0)
  have hP : ContDiffAt ℝ 1 P (v,q) :=
    (exponentialFamilyCoordinates_contDiffAt g o c d e hc v hv (hvexp ▸ hd)).prodMk contDiffAt_const
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL : IsUnit L := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let A : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hA : (A : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hder : HasFDerivAt (fun x => (P (x,q)).1) (A : FourSpace →L[ℝ] FourSpace) v := by
    rw [hA]
    have heq : (fun x => (P (x,q)).1) =ᶠ[𝓝 v]
        (fun x => chartAt FourSpace d (frameExponential g o e x)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
      exact exponentialFamilyCoordinates_frame g o c d e hc x hx
    exact (frameExponential_hasFDerivAt g o hRic d e he t ht hd).congr_of_eventuallyEq heq
  obtain ⟨H,hH,hvH,_⟩ := exponentialFamily_local_inverse P v q hP A hder
  let b : FrameBundle g × M := (e,d)
  let C : FrameBundle g × M → HeatRadialFrameSpace :=
    fun p => (chartAt FourSpace d p.2,frameCoordinateState g c p.1)
  have hC : C b = H (v,q) := by
    rw [hH]
    change (chartAt FourSpace d d,q) = (exponentialFamilyCoordinates g o c d (v,q),q)
    rw [exponentialFamilyCoordinates_frame g o c d e hc v hv,hvexp]
  have htarget : C b ∈ H.target := hC.symm ▸ H.map_source hvH
  let log : FrameBundle g × M → FourSpace := fun p => (H.symm (C p)).1
  have hlog : log b = v := by
    dsimp only [log]
    rw [hC,H.left_inv hvH]
  have hCcont : ContinuousAt C b := by
    have hfirst : ContinuousAt (fun p : FrameBundle g × M => chartAt FourSpace d p.2) b :=
      (chartAt FourSpace d).continuousAt hd |>.comp continuous_snd.continuousAt
    have hsecond : ContinuousAt (fun p : FrameBundle g × M => frameCoordinateState g c p.1) b := by
      simpa only [Function.comp_def] using!
        ((frameCoordinateState_continuousAt g c e hc).comp
          (continuous_fst.continuousAt : ContinuousAt (Prod.fst : FrameBundle g × M → FrameBundle g) b))
    exact hfirst.prodMk hsecond
  have hlcont : ContinuousAt log b :=
    continuous_fst.continuousAt.comp ((H.continuousAt_symm htarget).comp hCcont)
  have hbbase : b.1.base ∈ (chartAt FourSpace c).source := hc
  have hbpoint : b.2 ∈ (chartAt FourSpace d).source := hd
  have hlexp : frameExponential g o b.1 (log b) ∈ (chartAt FourSpace d).source := by
    rw [hlog]
    exact hvexp.symm ▸ hd
  have hlognz : log b ≠ 0 := by rw [hlog]; exact hv
  have hnear : {p : FrameBundle g × M |
      p.1.base ∈ (chartAt FourSpace c).source ∧ p.2 ∈ (chartAt FourSpace d).source ∧
      C p ∈ H.target ∧ log p ≠ 0 ∧
      frameExponential g o p.1 (log p) ∈ (chartAt FourSpace d).source} ∈ 𝓝 b := by
    apply Filter.inter_mem
      (((continuous_frameBase g).comp continuous_fst).continuousAt.preimage_mem_nhds
        ((chartAt FourSpace c).open_source.mem_nhds hbbase))
    apply Filter.inter_mem
      (continuous_snd.continuousAt.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hbpoint))
    apply Filter.inter_mem (hCcont.preimage_mem_nhds (H.open_target.mem_nhds htarget))
    apply Filter.inter_mem (hlcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hlognz))
    exact ((frameExponential_joint_continuous g o).continuousAt.comp
      (continuous_fst.continuousAt.prodMk hlcont)).preimage_mem_nhds
        ((chartAt FourSpace d).open_source.mem_nhds hlexp)
  obtain ⟨U,hUsub,hU,hbU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U,hU,hbU,log,?_,hlog,?_⟩
  · intro p hp
    obtain ⟨hpc,hpd,hpt,_,_⟩ := hUsub hp
    apply ContinuousAt.continuousWithinAt
    have hfirst : ContinuousAt (fun q : FrameBundle g × M => chartAt FourSpace d q.2) p :=
      (chartAt FourSpace d).continuousAt hpd |>.comp continuous_snd.continuousAt
    have hsecond : ContinuousAt (fun q : FrameBundle g × M => frameCoordinateState g c q.1) p := by
      simpa only [Function.comp_def] using!
        ((frameCoordinateState_continuousAt g c p.1 hpc).comp
          (continuous_fst.continuousAt : ContinuousAt (Prod.fst : FrameBundle g × M → FrameBundle g) p))
    exact continuous_fst.continuousAt.comp ((H.continuousAt_symm hpt).comp (hfirst.prodMk hsecond))
  · intro p hp
    obtain ⟨hpc,hpd,hpt,hnz,hpexp⟩ := hUsub hp
    have hr := H.right_inv hpt
    have hq : (H.symm (C p)).2 = (C p).2 := by
      have hh := congrArg Prod.snd hr
      rw [hH] at hh
      exact hh
    have hf := congrArg Prod.fst hr
    rw [hH] at hf
    change exponentialFamilyCoordinates g o c d (H.symm (C p)) = chartAt FourSpace d p.2 at hf
    have hpair : H.symm (C p) = (log p,frameCoordinateState g c p.1) :=
      Prod.ext rfl hq
    rw [hpair,exponentialFamilyCoordinates_frame g o c d p.1 hpc (log p) hnz] at hf
    exact (chartAt FourSpace d).injOn hpexp hpd hf

end
end PositiveEinsteinFour.Geometry
end


section

/-! The twice-differentiated moving-frame pullback. The derivative of the
base Jacobian is retained explicitly, for cancellation against the drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_covariant_second_pullback {n : ℕ}
    (F : FourSpace → FourSpace) (E : FourSpace → Mat4)
    (C D : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hE : ∀ a b, DifferentiableAt ℝ (fun y => E y a b) x)
    (hS : ∀ r a, DifferentiableAt ℝ
      (fun y => tensorCovariantDirection D T r y a) (F x))
    (hC : ∀ j, E x * C j x = matrixPartial E j x +
      (∑ s, jacobianMatrix F x s j • D s (F x)) * E x)
    (hfirst : ∀ᶠ y in 𝓝 x, ∀ i,
      tensorCovariantDirection C (fun z => frameTensor (E z) (T (F z))) i y =
        frameTensor (E y) (∑ r, jacobianMatrix F y r i • tensorCovariantDirection D T r (F y)))
    (i j : Fin 4) :
    tensorCovariantDirection C
      (tensorCovariantDirection C (fun y => frameTensor (E y) (T (F y))) i) j x =
      fun a => ∑ r, (partialDeriv (fun y => jacobianMatrix F y r i) j x *
        frameTensor (E x) (tensorCovariantDirection D T r (F x)) a +
        jacobianMatrix F x r i * frameTensor (E x)
          (∑ s, jacobianMatrix F x s j • tensorCovariantDirection D
            (tensorCovariantDirection D T r) s (F x)) a) := by
  let S := fun r y => frameTensor (E y) (tensorCovariantDirection D T r (F y))
  have hFd := hF.differentiableAt (by norm_num)
  have he : tensorCovariantDirection C (fun y => frameTensor (E y) (T (F y))) i =ᶠ[𝓝 x]
      (fun y a => ∑ r, jacobianMatrix F y r i * S r y a) := by
    filter_upwards [hfirst] with y hy
    rw [hy i]
    funext a
    exact heat_frameTensor_weighted_sum (E y) (fun r => jacobianMatrix F y r i) _ a
  rw [heat_covariant_congr C _ _ x he j]
  have hdiff (r : Fin 4) (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun y => S r y a) x :=
    frameTensor_differentiableAt E _ x hE (fun b => (hS r b).comp x hFd) a
  rw [heat_covariant_weighted_sum C _ S x
    (fun r => (heatJacobian_entry_regular 1 hF r i).differentiableAt one_ne_zero) hdiff j]
  funext a
  apply Finset.sum_congr rfl
  intro r _
  rw [heat_covariantDirection_pullback F E C D
    (tensorCovariantDirection D T r) x hFd hE (hS r) j (hC j)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Additivity of the actual normal amplitude realization, needed to
retain cancellation in the heat residual before estimating its norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCoordinateTensor_add (a b : FourSpace → TwoFormFour) :
    heatNormalCoordinateTensor D (a + b) =
      heatNormalCoordinateTensor D a + heatNormalCoordinateTensor D b := by
  funext x v
  change frameTensor (D.point x).2⁻¹ (twoFormTensor (a x + b x)) v = _
  rw [show twoFormTensor (a x + b x) = twoFormTensor (a x) + twoFormTensor (b x) from
    twoFormTensorLinear.map_add _ _, frameTensor_add]
  rfl

omit [T3Space M] [CompactSpace M] in
theorem heatNormalFrameTensorLift_add (C : OpenPartialHomeomorph FourSpace M)
    (T U : FourSpace → CovariantCoordinates 2) :
    heatNormalFrameTensorLift g c C (T + U) =
      heatNormalFrameTensorLift g c C T + heatNormalFrameTensorLift g c C U := by
  classical
  funext f v
  by_cases hf : f.base ∈ C.target
  · simp only [heatNormalFrameTensorLift, ite_eq_left hf, Pi.add_apply, frameTensor_add]
  · simp only [heatNormalFrameTensorLift, ite_eq_right hf, Pi.add_apply, Pi.zero_apply, add_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatNormalAmplitudeL2_add
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source) :
    heatNormalAmplitudeL2 D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalAmplitudeL2 D C hCt hP hD a ha hca hsa +
        heatNormalAmplitudeL2 D C hCt hP hD b hb hcb hsb := by
  have hT : heatNormalAmplitudeTensor D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalAmplitudeTensor D C hCt hP hD a ha hca hsa +
        heatNormalAmplitudeTensor D C hCt hP hD b hb hcb hsb := by
    ext f v
    change heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D (a + b)) f v = _
    rw [heatNormalCoordinateTensor_add, heatNormalFrameTensorLift_add]
    rfl
  change twoFormFromContinuousTensor _ = twoFormFromContinuousTensor _ + twoFormFromContinuousTensor _
  rw [hT, map_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Jointly continuous compact normal amplitudes give continuous curves
in the actual global two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalAmplitudeL2_continuous_family
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → TwoFormFour) (ha : ∀ t, ContDiff ℝ 2 (A t))
    (hc : ∀ t, HasCompactSupport (A t)) (hs : ∀ t, tsupport (A t) ⊆ C.source)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hsK : ∀ t > 0, tsupport (A t) ⊆ K) :
    ContinuousOn (fun t => heatNormalAmplitudeL2 D C hCt hP hD (A t) (ha t) (hc t) (hs t)) (Ioi 0) := by
  have hcoord := heatNormalCoordinateTensor_joint_continuous C hP hD A hA
  have hframe := heatNormalFrameTensorLift_joint_continuous (g := g) C hCt
    (fun t => heatNormalCoordinateTensor D (A t)) hcoord K hK hKC
    (fun t ht => (heatNormalCoordinateTensor_support D (A t)).trans (hsK t ht))
  have hTF : ContinuousOn (fun z : ℝ × FrameBundle g =>
      (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D (A z.1)) z.2)
        : TwoTensorEuclidean)) (Ioi 0 ×ˢ univ) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn hframe
  have hcurve : ContinuousOn (fun t => heatNormalAmplitudeTensor D C hCt hP hD
      (A t) (ha t) (hc t) (hs t)) (Ioi 0) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry _ hTF
  exact twoFormFromContinuousTensor.continuous.comp_continuousOn hcurve

end
end PositiveEinsteinFour.Geometry
end


section

/-! Nearby frames share a genuine normal chart radius, a jointly
regular parallel frame, and four derivatives of the inverse chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalCommonChart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ F : HeatRadialFrameFlow g e.base (frameCoordinateState g e.base e),
      ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (0, frameCoordinateState g e.base e) ∧
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, ∃ D : HeatNormalFrameData g o e.base e',
          ∃ C : OpenPartialHomeomorph FourSpace M,
            (D.point = fun x => heatRadialFrameFamily F t (x, frameCoordinateState g e.base e')) ∧
            C.source = ball 0 r ∧ EqOn C (frameExponential g o e') C.source ∧
            C.target ⊆ (chartAt FourSpace e.base).source ∧
            ContMDiffOn I4 I4 4 C.symm C.target ∧ r ≤ D.radius := by
  have he : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  obtain ⟨F, t, ht, htI, U₀, hU₀, he₀, R, hR, hD⟩ :=
    exists_heatNormalFrameCommonData g o e.base e he
  let p := frameCoordinateState g e.base e
  let P := heatRadialFrameFamily F t
  obtain ⟨_, D₀, hD₀R, hD₀P, hP⟩ := hD e he₀
  have hexp : (fun x => (P (x, p)).1) =ᶠ[𝓝 0]
      (fun x => chartAt FourSpace e.base (frameExponential g o e x)) := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D₀.radius_pos] with x hx
    simpa only [hD₀P] using D₀.exponential x hx
  obtain ⟨H, hH, hH0, hi⟩ := heatFamilyBaseAugment_actual_inverse g o e P hP hexp
  obtain ⟨S, hS, hslice⟩ := heatFamilySliceChart_uniform P p H hH hH0 hP hi
  obtain ⟨U₁, hU₁, he₁, T, hT, hsource⟩ := frameExponential_common_source g o e.base e he
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p S} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e he).preimage_mem_nhds (ball_mem_nhds _ hS)
  obtain ⟨U, hsub, hU, heU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU₀.mem_nhds he₀) (Filter.inter_mem (hU₁.mem_nhds he₁) hcoord))
  let r := min R (min S T)
  have hr : 0 < r := lt_min hR (lt_min hS hT)
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r ≤ S := (min_le_right _ _).trans (min_le_left _ _)
  have hrT : r ≤ T := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨F, t, ht, htI, hP, U, hU, heU, r, hr, ?_⟩
  intro e' he'
  obtain ⟨he'₀, he'₁, hq⟩ := hsub he'
  obtain ⟨_, D, hDR, hDP, _⟩ := hD e' he'₀
  have hrD : r ≤ D.radius := hDR ▸ hrR
  have hs (x : FourSpace) (hx : x ∈ ball 0 r) :=
    hslice (frameCoordinateState g e.base e') hq x (ball_subset_ball hrS hx)
  obtain ⟨C, hC, hCE, hCt, hCi⟩ := heatFamily_manifold_chart D P hDP H hH r hr hrD
    (fun x hx => hsource e' he'₁ x (ball_subset_ball hrT hx))
    (fun x hx => (hs x hx).1) (fun x hx => (hs x hx).2)
  exact ⟨D, C, hDP, hC, hCE, hCt, hCi, hrD⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual coordinate tensor reconstructed
from a time-dependent normal amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCoordinates_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → FourSpace)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source)) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneCoordinates D (A z.1) z.2)
      (Ioi 0 ×ˢ C.source) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hPx := hP.contDiffAt (C.open_source.mem_nhds hz.2)
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) z.2 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hPx.snd i) j
  have hEi (i j : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => (D.point w.2).2⁻¹ i j) z :=
    (heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) z.2 hE
      (heatNormalFrame_matrix_nondegenerate D (hD hz.2)) i j).continuousAt.comp continuousAt_snd
  have hAc := hA.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds hz)
  apply continuousAt_pi.mpr
  intro v
  change ContinuousAt (fun w : ℝ × FourSpace =>
    ∑ b : Fin 1 → Fin 4, (∏ k, (D.point w.2).2⁻¹ (b k) (v k)) * A w.1 w.2 (b 0)) z
  apply tendsto_finsetSum
  intro b _
  exact (tendsto_finsetProd _ (fun k _ => hEi (b k) (v k))).mul
    ((EuclideanSpace.proj (b 0) : FourSpace →L[ℝ] ℝ).continuous.continuousAt.comp hAc)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weitzenböck curvature potential in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatNormalFrameCurvature (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace) : CovariantCoordinates 4 :=
  frameTensor (P x).2 (curvatureCoordinates g c (P x).1)

def heatNormalPotential (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace) : TwoFormMatrix :=
  twoFormPotentialMatrix (heatNormalFrameCurvature g c P x)

theorem heatNormalFrameCurvature_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ n P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (v : Fin 4 → Fin 4) :
    ContDiffAt ℝ n (fun y => heatNormalFrameCurvature g c P y v) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hR (w : Fin 4 → Fin 4) :
      ContDiffAt ℝ n (fun y => curvatureCoordinates g c (P y).1 w) x := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => curvatureCoordinates g c z w) x
      ((curvatureCoordinates_contDiffAt g c (P x).1 hx
        (metricInChart_posDef g c (P x).1 hx).det_pos.ne' w).of_le (by simp)) hP.fst
  unfold heatNormalFrameCurvature frameTensor
  apply ContDiffAt.sum
  intro w _
  exact (contDiffAt_prod fun i _ => hE (w i) (v i)).mul (hR w)

theorem heatNormalPotential_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ n P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (k l : Fin 6) : ContDiffAt ℝ n (fun y => heatNormalPotential g c P y k l) x := by
  change ContDiffAt ℝ n (fun y =>
    6 * (1 : TwoFormMatrix) k l - 2 * -heatNormalFrameCurvature g c P y
      ![(AlgebraicCurvature.pair k).1, (AlgebraicCurvature.pair k).2,
        (AlgebraicCurvature.pair l).1, (AlgebraicCurvature.pair l).2]) x
  exact contDiffAt_const.sub (contDiffAt_const.mul
    (heatNormalFrameCurvature_contDiffAt n g c P x hP hx _).neg)

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.curvature_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (v : Fin 4 → Fin 4) :
    ContDiffAt ℝ 12 (fun y => heatNormalFrameCurvature g c D.point y v) 0 :=
  heatNormalFrameCurvature_contDiffAt 12 g c D.point 0 D.regular
    (D.in_chart 0 (Metric.mem_ball_self D.radius_pos)) v

theorem HeatNormalFrameData.potential_regular {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (k l : Fin 6) :
    ContDiffAt ℝ 12 (fun y => heatNormalPotential g c D.point y k l) 0 :=
  heatNormalPotential_contDiffAt 12 g c D.point 0 D.regular
    (D.in_chart 0 (Metric.mem_ball_self D.radius_pos)) k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth two-forms expressed in the normal frame. Regularity is
proved from their coordinate tensors, without differentiating a chosen
global reference frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_extract_twoFormTensor (a : TwoFormFour) :
    twoFormExtractLinear (twoTensorMatrixLinear (twoFormTensor a)) = a := by
  ext k
  fin_cases k <;> rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def heatNormalTwoFormValue (o : FrameOrientation g) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : M → TwoFormFour) (x : FourSpace) : TwoFormFour :=
  twoFormExtractLinear (twoTensorMatrixLinear
    (frameTensor (P x).2 (twoFormCoordinates o u c (P x).1)))

theorem heatNormalTwoFormValue_tensor (o : FrameOrientation g) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : M → TwoFormFour) (x : FourSpace) :
    twoFormTensor (heatNormalTwoFormValue o c P u x) =
      frameTensor (P x).2 (twoFormCoordinates o u c (P x).1) := by
  let p := (chartAt FourSpace c).symm (P x).1
  let A := (o.frame p).matrix⁻¹ * chartInverseMatrix c (P x).1 * (P x).2
  have hrep : frameTensor (P x).2 (twoFormCoordinates o u c (P x).1) =
      twoFormTensor (twoFormFrameAction A (u p)) := by
    unfold twoFormCoordinates twoFormTensorAt
    rw [← frameTensor_mul, ← frameTensor_mul]
    simpa only [A, p, Matrix.mul_assoc] using (twoFormTensor_frameAction A (u p)).symm
  unfold heatNormalTwoFormValue
  rw [hrep, heat_extract_twoFormTensor]

theorem heatNormalTwoFormValue_contDiffAt (n : ℕ) {o : FrameOrientation g}
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace) (hP : ContDiffAt ℝ n P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ n (heatNormalTwoFormValue o c P u) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hT (v : Fin 2 → Fin 4) :
      ContDiffAt ℝ n (fun y => twoFormCoordinates o u c (P y).1 v) x :=
    ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => twoFormCoordinates o u c z v) x
      ((hu.coordinates_contDiffAt c (P x).1 hx v).of_le (by simp)) hP.fst
  have hFT : ContDiffAt ℝ n
      (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) x := by
    apply contDiffAt_pi.mpr
    intro v
    unfold frameTensor
    apply ContDiffAt.sum
    intro w _
    exact (contDiffAt_prod fun i _ => hE (w i) (v i)).mul (hT w)
  let L := (twoFormExtractLinear.comp twoTensorMatrixLinear).toContinuousLinearMap
  exact L.contDiff.contDiffAt.comp x hFT

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature of the coordinate connection pulled back by the actual
finite-regularity normal-coordinate map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatWeightedConnection (F : FourSpace → FourSpace)
    (C : Fin 4 → FourSpace → Mat4) (i : Fin 4) (x : FourSpace) : Mat4 :=
  weightedConnection (jacobianMatrix F x) (fun a => C a (F x)) i

theorem heatWeightedConnection_partial
    (F : FourSpace → FourSpace) (C : Fin 4 → FourSpace → Mat4)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hC : ∀ a r s, DifferentiableAt ℝ (fun z => C a z r s) (F x))
    (i j : Fin 4) :
    matrixPartial (heatWeightedConnection F C j) i x =
      weightedConnectionDerivative (jacobianMatrix F x)
        (fun r => matrixPartial (jacobianMatrix F) r x)
        (fun a => C a (F x)) (fun b a => matrixPartial (C a) b (F x)) i j := by
  let J := jacobianMatrix F
  let A := fun a z => C a (F z)
  have hdF := hF.differentiableAt (by norm_num)
  have hJ (a : Fin 4) : DifferentiableAt ℝ (fun z => J z a j) x :=
    (heatJacobian_entry_regular 1 hF a j).differentiableAt one_ne_zero
  have hA (a r s : Fin 4) : DifferentiableAt ℝ (fun z => A a z r s) x :=
    (hC a r s).comp x hdF
  change matrixPartial (fun z => ∑ a, J z a j • A a z) i x = _
  rw [matrixPartial_sum_four (fun a z => J z a j • A a z) x
    (fun a r s => (hJ a).mul (hA a r s)) i]
  have hs (a : Fin 4) : matrixPartial (fun z => J z a j • A a z) i x =
      partialDeriv (fun z => J z a j) i x • A a x +
        J x a j • matrixPartial (A a) i x :=
    matrixPartial_smul _ _ x (hJ a) (hA a) i
  have hc (a : Fin 4) : matrixPartial (A a) i x =
      ∑ b, J x b i • matrixPartial (C a) b (F x) :=
    matrixPartial_comp hdF (hC a) i
  simp only [hs, hc]
  rfl

theorem heatWeightedConnection_curvature
    (F : FourSpace → FourSpace) (C : Fin 4 → FourSpace → Mat4)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hC : ∀ a r s, DifferentiableAt ℝ (fun z => C a z r s) (F x))
    (i j : Fin 4) :
    matrixPartial (heatWeightedConnection F C j) i x -
        matrixPartial (heatWeightedConnection F C i) j x +
      heatWeightedConnection F C i x * heatWeightedConnection F C j x -
        heatWeightedConnection F C j x * heatWeightedConnection F C i x =
      ∑ a, ∑ b, (jacobianMatrix F x a i * jacobianMatrix F x b j) •
        (matrixPartial (C b) a (F x) - matrixPartial (C a) b (F x) +
          C a (F x) * C b (F x) - C b (F x) * C a (F x)) := by
  rw [heatWeightedConnection_partial F C x hF hC,
    heatWeightedConnection_partial F C x hF hC]
  exact weightedConnection_curvature _ _ _ _
    (fun a b r => heatJacobian_partials_commute hF r a b) i j

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatWeightedConnection_actual_curvature (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    matrixPartial (heatWeightedConnection F (connectionMatrix g c) j) i x -
        matrixPartial (heatWeightedConnection F (connectionMatrix g c) i) j x +
      heatWeightedConnection F (connectionMatrix g c) i x *
        heatWeightedConnection F (connectionMatrix g c) j x -
      heatWeightedConnection F (connectionMatrix g c) j x *
        heatWeightedConnection F (connectionMatrix g c) i x =
      ∑ a, ∑ b, (jacobianMatrix F x a i * jacobianMatrix F x b j) •
        coordinateCurvatureMatrix g c a b (F x) := by
  apply heatWeightedConnection_curvature F (connectionMatrix g c) x hF
  intro a r s
  exact (christoffel_contDiffAt g c (F x) hx
    (metricInChart_posDef g c (F x) hx).det_pos.ne' r a s).differentiableAt (by simp)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-valued distance lemmas for the actual Riemannian path metric on
our connected compact manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

def metricDistance (g : SmoothMetric M) (p q : M) : ℝ := (metricEDistance g p q).toReal

omit [T3Space M] [PreconnectedSpace M] in
theorem metricDistance_nonneg (g : SmoothMetric M) (p q : M) :
    0 ≤ metricDistance g p q := ENNReal.toReal_nonneg

theorem ofReal_metricDistance (g : SmoothMetric M) (p q : M) :
    ENNReal.ofReal (metricDistance g p q) = metricEDistance g p q :=
  ENNReal.ofReal_toReal (metricEDistance_ne_top g p q)

theorem metricDistance_eq_iff (g : SmoothMetric M) (p q : M) {r : ℝ} (hr : 0 ≤ r) :
    metricDistance g p q = r ↔ metricEDistance g p q = ENNReal.ofReal r := by
  constructor
  · intro h
    rw [← ofReal_metricDistance g p q, h]
  · intro h
    change (metricEDistance g p q).toReal = r
    rw [h, ENNReal.toReal_ofReal hr]

theorem metricDistance_triangle (g : SmoothMetric M) (p q r : M) :
    metricDistance g p r ≤ metricDistance g p q + metricDistance g q r := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have h : metricEDistance g p r ≤ metricEDistance g p q + metricEDistance g q r :=
    Manifold.riemannianEDist_triangle
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨metricEDistance_ne_top g p q, metricEDistance_ne_top g q r⟩) h
  rwa [ENNReal.toReal_add (metricEDistance_ne_top g p q) (metricEDistance_ne_top g q r)] at ht

theorem metricDistance_continuous (g : SmoothMetric M) :
    Continuous (fun p : M × M => metricDistance g p.1 p.2) :=
  metricEDistance_toReal_continuous g

theorem metricDistance_eq_zero_iff (g : SmoothMetric M) (p q : M) :
    metricDistance g p q = 0 ↔ p = q := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  rw [metricDistance_eq_iff g p q le_rfl, ENNReal.ofReal_zero]
  change edist p q = 0 ↔ p = q
  exact edist_eq_zero

variable [CompactSpace M]

theorem exists_metricDistance_real_split (g : SmoothMetric M) (p q : M)
    (r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ metricDistance g p q) :
    ∃ z, metricDistance g p z = r ∧ metricDistance g p q = r + metricDistance g z q := by
  obtain ⟨z, hz, hsplit⟩ := exists_metricDistance_split g p q r hr hrd
  refine ⟨z, (metricDistance_eq_iff g p z hr).mpr hz, ?_⟩
  have h := congrArg ENNReal.toReal hsplit
  simpa only [metricDistance, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (metricEDistance_ne_top g z q), ENNReal.toReal_ofReal hr] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the two covariant derivative slots for actual one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def oneFormSecondTrace (G : Mat4) (T : CovariantCoordinates 3) : CovariantCoordinates 1 :=
  fun v => ∑ a, ∑ b, G a b * T (Fin.cons a (Fin.cons b v))

theorem oneFormSecondTrace_frame (E : Mat4) (T : CovariantCoordinates 3)
    (v : Fin 1 → Fin 4) :
    (∑ i, frameTensor E T (Fin.cons i (Fin.cons i v))) =
      frameTensor E (oneFormSecondTrace (E * Eᵀ) T) v := by
  simp only [frameTensor_cons]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ i, E a i * ∑ b, E b i * frameTensor E (fun w => T (Fin.cons a (Fin.cons b w))) v) =
        ∑ a, ∑ b, (∑ i, E a i * E b i) *
          frameTensor E (fun w => T (Fin.cons a (Fin.cons b w))) v := by
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
      change frameTensor E (fun w => ∑ a, ∑ b, (E * Eᵀ) a b *
        T (Fin.cons a (Fin.cons b w))) v = _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [frameTensor_const_mul]
      rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framed_oneFormSecondTrace (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 1) (E H : Mat4) (x : FourSpace)
    (hH : Hᵀ = H) (a : Fin 1 → Fin 4) :
    frameTensor E (oneFormSecondTrace H (covariantDerivative g c
      (covariantDerivative g c T) x)) a =
      ∑ p, ∑ q, H p q * (frameTensor E
        (tensorCovariantDirection (connectionMatrix g c)
          (tensorCovariantDirection (connectionMatrix g c) T p) q x) a -
        ∑ r, christoffel g c x r p q *
          frameTensor E (tensorCovariantDirection (connectionMatrix g c) T r x) a) := by
  have hsym (p q : Fin 4) : H q p = H p q := congrArg (fun A : Mat4 => A p q) hH
  unfold oneFormSecondTrace
  rw [frameTensor_sum]
  simp_rw [frameTensor_sum, frameTensor_const_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hsym, heat_framed_second_covariant]
  have hc (r : Fin 4) : christoffel g c x r q p = christoffel g c x r p q :=
    christoffel_comm g c x r q p
  simp only [hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual metric balls and spheres in a normal neighborhood are
precisely the images of Euclidean balls and spheres under the exponential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_image_closedBall (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (R : ℝ) (hR : 0 < R)
    (hball : closedBall 0 R ⊆ C.source) (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    frameExponential g o e '' closedBall 0 r =
      {y | metricEDistance g e.base y ≤ ENNReal.ofReal r} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ r := by simpa using hv
    exact (frameExponential_distance g o e v).trans (ENNReal.ofReal_le_ofReal hv')
  · intro hy
    have hyR : metricEDistance g e.base y < ENNReal.ofReal R :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR)
    obtain ⟨v, _, hvy, hvdist⟩ :=
      frameExponential_metric_ball_surj g o hRic e he C hC hI R hR hball y hyR
    have hv : ‖v‖ ≤ r := (ENNReal.ofReal_le_ofReal_iff hr).mp (hvdist ▸ hy)
    exact ⟨v, by simpa using hv, hvy⟩

theorem frameExponential_image_sphere (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (R : ℝ) (hR : 0 < R)
    (hball : closedBall 0 R ⊆ C.source) (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    frameExponential g o e '' sphere 0 r =
      {y | metricEDistance g e.base y = ENNReal.ofReal r} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : ‖v‖ = r := by simpa using hv
    have hvr : ‖v‖ < R := hv' ▸ hrR
    have hd := le_antisymm (frameExponential_distance g o e v)
      (frameExponential_normal_ball_distance_lower g o hRic e he C hC hI R hR hball v hvr)
    exact hd.trans (congrArg ENNReal.ofReal hv')
  · intro hy
    have hyR : metricEDistance g e.base y < ENNReal.ofReal R := by
      rw [hy]
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR
    obtain ⟨v, _, hvy, hvdist⟩ :=
      frameExponential_metric_ball_surj g o hRic e he C hC hI R hR hball y hyR
    have hv : ‖v‖ = r := (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) hr).mp
      (hvdist.symm.trans hy)
    exact ⟨v, by simpa using hv, hvy⟩

theorem exists_frameExponential_normal_ball_images (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ R > (0 : ℝ), ∀ r : ℝ, 0 ≤ r → r < R →
      frameExponential g o e '' closedBall 0 r =
        {y | metricEDistance g e.base y ≤ ENNReal.ofReal r} ∧
      frameExponential g o e '' sphere 0 r =
        {y | metricEDistance g e.base y = ENNReal.ofReal r} := by
  obtain ⟨T, C, hT, hs, hC, hI⟩ := frameExponential_normal_ball g o e
  have hball : closedBall 0 (T / 2) ⊆ C.source := by
    rw [hs]
    exact closedBall_subset_ball (by linarith)
  refine ⟨T / 2, half_pos hT, fun r hr hrT => ?_⟩
  exact ⟨frameExponential_image_closedBall g o hRic e he C hC hI _ (half_pos hT)
    hball r hr hrT, frameExponential_image_sphere g o hRic e he C hC hI _ (half_pos hT)
    hball r hr hrT⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint curvature and two-form connection coefficients of the actual
normal-frame family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyCurvature (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) :
    CovariantCoordinates 4 := frameTensor (P z).2 (curvatureCoordinates g c (P z).1)

def heatFamilyPotential (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) :
    TwoFormMatrix := twoFormPotentialMatrix (heatFamilyCurvature g c P z)

theorem heatFamilyCurvature_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ n P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (v : Fin 4 → Fin 4) :
    ContDiffAt ℝ n (fun y => heatFamilyCurvature g c P y v) z := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hR (w : Fin 4 → Fin 4) :
      ContDiffAt ℝ n (fun y => curvatureCoordinates g c (P y).1 w) z := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun x => curvatureCoordinates g c x w) z
      ((curvatureCoordinates_contDiffAt g c (P z).1 hz
        (metricInChart_posDef g c (P z).1 hz).det_pos.ne' w).of_le (by simp)) hP.fst
  unfold heatFamilyCurvature frameTensor
  apply ContDiffAt.sum
  intro w _
  exact (contDiffAt_prod fun i _ => hE (w i) (v i)).mul (hR w)

theorem heatFamilyPotential_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ n P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (k l : Fin 6) : ContDiffAt ℝ n (fun y => heatFamilyPotential g c P y k l) z := by
  change ContDiffAt ℝ n (fun y =>
    6 * (1 : TwoFormMatrix) k l - 2 * -heatFamilyCurvature g c P y
      ![(AlgebraicCurvature.pair k).1, (AlgebraicCurvature.pair k).2,
        (AlgebraicCurvature.pair l).1, (AlgebraicCurvature.pair l).2]) z
  exact contDiffAt_const.sub (contDiffAt_const.mul
    (heatFamilyCurvature_contDiffAt n g c P z hP hz _).neg)

theorem heatFamilyPotential_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (q : CoordinateFrameSpace)
    (x : FourSpace) :
    heatFamilyPotential g c P (x, q) = heatNormalPotential g c (fun v => P (v, q)) x := rfl

def heatFamilyTwoFormConnection (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (i : Fin 4)
    (z : HeatRadialFrameSpace) : TwoFormMatrix :=
  heatTwoFormConnectionMatrix (heatFamilyConnection g c P i z)

theorem heatFamilyTwoFormConnection_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target) (hdet : (P z).2.det ≠ 0)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => heatFamilyTwoFormConnection g c P i y k l) z := by
  have hB : ContDiffAt ℝ n (heatFamilyConnection g c P i) z :=
    contDiffAt_pi.mpr (fun j => contDiffAt_pi.mpr
      (heatFamilyConnection_contDiffAt n g c P z hP hz hdet i j))
  let L := (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).toContinuousLinearMap
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hc := π.contDiff.contDiffAt.comp z (L.contDiff.contDiffAt.comp z hB)
  change ContDiffAt ℝ n
    (fun y => heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)
      (heatFamilyConnection g c P i y) k) z at hc
  simpa only [heatConnectionActionLinear_apply, heatFamilyTwoFormConnection,
    heatTwoFormConnectionMatrix] using hc

theorem heatFamilyTwoFormConnection_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    heatFamilyTwoFormConnection g c P i z =
      heatTwoFormConnection g c (fun x => P (x, z.2)) i z.1 := by
  rw [heatFamilyTwoFormConnection, heatFamilyConnection_slice g c P z hP i]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual moving-frame connection law identifies
its curvature with the pullback of Levi-Civita curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_matrixPartial_comm_two (E : FourSpace → Mat4) (x : FourSpace)
    (hE : ∀ r s, ContDiffAt ℝ 2 (fun z => E z r s) x) (i j : Fin 4) :
    matrixPartial (matrixPartial E j) i x = matrixPartial (matrixPartial E i) j x := by
  ext r s
  have hd := ((hE r s).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (a b : Fin 4) :
      partialDeriv (partialDeriv (fun z => E z r s) b) a x =
        fderiv ℝ (fderiv ℝ (fun z => E z r s)) x (coordinateVector a) (coordinateVector b) := by
    unfold partialDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change partialDeriv (partialDeriv (fun z => E z r s) j) i x =
    partialDeriv (partialDeriv (fun z => E z r s) i) j x
  rw [he, he]
  exact ((hE r s).isSymmSndFDerivAt (by norm_num)).eq _ _

theorem heat_connection_law_derivative
    (E C U : FourSpace → Mat4) (x : FourSpace)
    (hE : ∀ r s, ContDiffAt ℝ 2 (fun z => E z r s) x)
    (hC : ∀ r s, DifferentiableAt ℝ (fun z => C z r s) x)
    (hU : ∀ r s, DifferentiableAt ℝ (fun z => U z r s) x)
    (j : Fin 4)
    (hLaw : (fun z => E z * C z) =ᶠ[𝓝 x]
      (fun z => matrixPartial E j z + U z * E z)) (i : Fin 4) :
    matrixPartial E i x * C x + E x * matrixPartial C i x =
      matrixPartial (matrixPartial E j) i x + matrixPartial U i x * E x +
        U x * matrixPartial E i x := by
  have hEd (r s : Fin 4) := (hE r s).differentiableAt (by norm_num)
  have hP (r s : Fin 4) :
      DifferentiableAt ℝ (fun z => matrixPartial E j z r s) x :=
    (((hE r s).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  have hprod (r s : Fin 4) : DifferentiableAt ℝ (fun z => (U z * E z) r s) x := by
    change DifferentiableAt ℝ (fun z => ∑ a, U z r a * E z a s) x
    exact DifferentiableAt.fun_sum (fun a _ => (hU r a).mul (hEd a s))
  have h := matrixPartial_congr hLaw i
  rw [matrixPartial_mul E C x hEd hC i,
    matrixPartial_add (matrixPartial E j) (fun z => U z * E z) x hP hprod i,
    matrixPartial_mul U E x hU hEd i] at h
  simpa only [add_assoc] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.connection_law (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ Metric.ball 0 D.radius) (i : Fin 4) :
    (D.point x).2 * heatNormalFrameConnection g c D.point i x =
      matrixPartial (fun z => (D.point z).2) i x +
        heatWeightedConnection (fun z => (D.point z).1) (connectionMatrix g c) i x *
          (D.point x).2 := by
  have hdet : IsUnit (D.point x).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  rw [heatFrame_matrixPartial D.point x (D.differentiable x hx) i]
  simp_rw [heatWeightedConnection, weightedConnection,
    heatFrame_baseJacobian D.point x (D.differentiable x hx)]
  exact pulledConnection_equation _ _ _ hdet

theorem HeatNormalFrameData.connection_curvature_intertwining
    (D : HeatNormalFrameData g o c e) (i j : Fin 4) :
    (D.point 0).2 *
      (matrixPartial (heatNormalFrameConnection g c D.point j) i 0 -
        matrixPartial (heatNormalFrameConnection g c D.point i) j 0 +
        heatNormalFrameConnection g c D.point i 0 * heatNormalFrameConnection g c D.point j 0 -
        heatNormalFrameConnection g c D.point j 0 * heatNormalFrameConnection g c D.point i 0) =
      (∑ a, ∑ b, (jacobianMatrix (fun z => (D.point z).1) 0 a i *
        jacobianMatrix (fun z => (D.point z).1) 0 b j) •
          coordinateCurvatureMatrix g c a b (D.point 0).1) * (D.point 0).2 := by
  let E := fun z => (D.point z).2
  let F := fun z => (D.point z).1
  let C := heatNormalFrameConnection g c D.point
  let U := heatWeightedConnection F (connectionMatrix g c)
  have hE (r s : Fin 4) : ContDiffAt ℝ 2 (fun z => E z r s) 0 :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp D.regular.snd r) s).of_le (by norm_num)
  have hF : ContDiffAt ℝ 2 F 0 := D.regular.fst.of_le (by norm_num)
  have hx : F 0 ∈ (chartAt FourSpace c).target :=
    D.in_chart 0 (Metric.mem_ball_self D.radius_pos)
  have hU (a r s : Fin 4) : DifferentiableAt ℝ (fun z => U a z r s) 0 := by
    change DifferentiableAt ℝ (fun z => ∑ b,
      jacobianMatrix F z b a * connectionMatrix g c b (F z) r s) 0
    apply DifferentiableAt.fun_sum
    intro b _
    apply ((heatJacobian_entry_regular 1 hF b a).differentiableAt one_ne_zero).mul
    exact ((christoffel_contDiffAt g c (F 0) hx
      (metricInChart_posDef g c (F 0) hx).det_pos.ne' r b s).differentiableAt
        (by simp)).comp 0 (hF.differentiableAt (by norm_num))
  have hC (a r s : Fin 4) : DifferentiableAt ℝ (fun z => C a z r s) 0 :=
    (D.connection_regular a r s).differentiableAt (by norm_num)
  have hLaw (a : Fin 4) : (fun z => E z * C a z) =ᶠ[𝓝 0]
      (fun z => matrixPartial E a z + U a z * E z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with z hz
    exact D.connection_law z hz a
  have hder (a b : Fin 4) := heat_connection_law_derivative E (C b) (U b) 0
    hE (hC b) (hU b) b (hLaw b) a
  have hcomm := heat_matrixPartial_comm_two E 0 hE i j
  have hc := curvature_intertwining_of_connection _ _ _ _ _ _ _ _ _ _ _ _
    (hLaw i).self_of_nhds (hLaw j).self_of_nhds (hder i j)
    (by simpa only [hcomm] using hder j i)
  rw [heatWeightedConnection_actual_curvature g c F 0 hF hx i j] at hc
  exact hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame curvature and potential are the intrinsic geometric
ones, evaluated on actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChartCurvature_eq (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    frameTensor (frameChartMatrix g c e) (curvatureCoordinates g c
      (chartAt FourSpace c e.base)) = twoFormMetricCurvatureTensor g e := by
  have hb := mem_chart_source FourSpace e.base
  have ht := curvatureCoordinates_transition g e.base c
    (chartAt FourSpace e.base e.base) ((chartAt FourSpace e.base).map_source hb)
    (by simpa only [(chartAt FourSpace e.base).left_inv hb] using he)
  have hz : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    change chartAt FourSpace c ((chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base e.base)) = _
    rw [(chartAt FourSpace e.base).left_inv hb]
  rw [hz] at ht
  rw [frameChartMatrix_eq, frameTensor_mul, ← ht]
  rfl

variable [T2Space M] [CompactSpace M]

def HeatNormalFrameData.frame {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) : FrameBundle g :=
  chartFrameStateToBundle g c ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩

theorem HeatNormalFrameData.frame_base_of_mem_source {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source) :
    (D.frame x hx).base = frameExponential g o e x := by
  change (chartAt FourSpace c).symm (D.point x).1 = _
  rw [D.exponential x hx]
  exact (chartAt FourSpace c).left_inv hs

theorem HeatNormalFrameData.curvature_as_actual {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    heatNormalFrameCurvature g c D.point x =
      twoFormMetricCurvatureTensor g (D.frame x hx) := by
  have hsource : (D.frame x hx).base ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target (D.in_chart x hx)
  have h := frameChartCurvature_eq g c (D.frame x hx) hsource
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  rw [hm] at h
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hb] at h
  exact h

theorem HeatNormalFrameData.potential_as_actual {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    heatNormalPotential g c D.point x =
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g (D.frame x hx)) := by
  unfold heatNormalPotential
  rw [D.curvature_as_actual x hx]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Second covariant differentiation in the constructed normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_covariant_second_pullback {n : ℕ} (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hT : ∀ z ∈ (chartAt FourSpace c).target, ∀ a,
      ContDiffAt ℝ ∞ (fun y => T y a) z)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i j : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x =
      fun a => ∑ r, (partialDeriv
        (fun y => jacobianMatrix (fun z => (P z).1) y r i) j x *
        frameTensor (P x).2 (tensorCovariantDirection (connectionMatrix g c) T r (P x).1) a +
        jacobianMatrix (fun y => (P y).1) x r i * frameTensor (P x).2
          (∑ s, jacobianMatrix (fun y => (P y).1) x s j •
            tensorCovariantDirection (connectionMatrix g c)
              (tensorCovariantDirection (connectionMatrix g c) T r) s (P x).1) a) := by
  have hPd := hP.differentiableAt (by norm_num)
  have hE (a b : Fin 4) : DifferentiableAt ℝ (fun y => (P y).2 a b) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hPd.snd a) b
  have hS (r : Fin 4) (a : Fin n → Fin 4) : DifferentiableAt ℝ
      (fun y => tensorCovariantDirection (connectionMatrix g c) T r y a) (P x).1 :=
    (covariantDerivative_contDiffAt g c (P x).1 hx
      (metricInChart_posDef g c (P x).1 hx).det_pos.ne' T (hT _ hx)
      (Fin.cons r a)).differentiableAt (by simp)
  have hdet : IsUnit (P x).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hG.self_of_nhds
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hC (k : Fin 4) : (P x).2 * heatNormalFrameConnection g c P k x =
      matrixPartial (fun y => (P y).2) k x +
      (∑ s, jacobianMatrix (fun y => (P y).1) x s k • connectionMatrix g c s (P x).1) *
        (P x).2 := by
    rw [heatFrame_matrixPartial P x hPd k]
    simp_rw [heatFrame_baseJacobian P x hPd]
    exact pulledConnection_equation _ _ _ hdet
  have hnear : ∀ᶠ y in 𝓝 x, ∀ k,
      tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun z => frameTensor (P z).2 (T (P z).1)) k y =
      frameTensor (P y).2 (∑ r, jacobianMatrix (fun z => (P z).1) y r k •
        tensorCovariantDirection (connectionMatrix g c) T r (P y).1) := by
    have hp : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 P y :=
      (hP.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)
    have ht : ∀ᶠ y in 𝓝 x, (P y).1 ∈ (chartAt FourSpace c).target :=
      hP.continuousAt.fst.preimage_mem_nhds ((chartAt FourSpace c).open_target.mem_nhds hx)
    filter_upwards [hp, ht, hG] with y hy hyt hyg
    intro k
    have hd := hy.differentiableAt one_ne_zero
    have h := heatNormal_covariant_pullback g c P T y hd
      (fun a => (hT _ hyt a).differentiableAt (by simp)) hyg k
    simpa only [heatFrame_baseJacobian P y hd] using h
  exact heat_covariant_second_pullback (fun y => (P y).1) (fun y => (P y).2)
    (heatNormalFrameConnection g c P) (connectionMatrix g c) T x hP.fst hE hS hC hnear i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame first-order expression is the pullback of the
actual Levi-Civita derivative of a smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def heatNormalTwoFormNabla (o : FrameOrientation g) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : M → TwoFormFour) (i : Fin 4)
    (x : FourSpace) : TwoFormFour :=
  fderiv ℝ (heatNormalTwoFormValue o c P u) x (coordinateVector i) +
    twoFormSkewAction (twoFormExtract (heatNormalFrameConnection g c P i x))
      (heatNormalTwoFormValue o c P u x)

theorem heatNormalTwoFormNabla_tensor {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ 1 P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i : Fin 4) :
    frameTensor (P x).2 (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      tensorCovariantDirection (connectionMatrix g c) (twoFormCoordinates o u c) r (P x).1) =
      twoFormTensor (heatNormalTwoFormNabla o c P u i x) := by
  have hPd := hP.differentiableAt one_ne_zero
  have ha : DifferentiableAt ℝ (heatNormalTwoFormValue o c P u) x :=
    (heatNormalTwoFormValue_contDiffAt 1 hu c P x hP hx).differentiableAt one_ne_zero
  have hT (v : Fin 2 → Fin 4) :
      DifferentiableAt ℝ (fun z => twoFormCoordinates o u c z v) (P x).1 :=
    (hu.coordinates_contDiffAt c (P x).1 hx v).differentiableAt (by simp)
  have h := heatNormal_covariant_pullback g c P (twoFormCoordinates o u c) x
    hPd hT hG.self_of_nhds i
  have hrep : (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) =
      (fun y => twoFormTensor (heatNormalTwoFormValue o c P u y)) := by
    funext y
    exact (heatNormalTwoFormValue_tensor o c P u y).symm
  rw [hrep] at h
  change tensorPartial (fun y => twoFormTensor (heatNormalTwoFormValue o c P u y)) i x -
      tensorSlotAction (heatNormalFrameConnection g c P i x)
        (twoFormTensor (heatNormalTwoFormValue o c P u x)) = _ at h
  rw [tensorPartial_twoForm ha] at h
  have hsk := heatNormalFrameConnection_skew g c P x hPd hx hG i
  rw [← twoFormMatrix_extract _ hsk, tensorSlotAction_twoForm, sub_neg_eq_add] at h
  exact ((twoFormTensorLinear.map_add _ _).trans h).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual kinetic energy bounds for C1 curve segments.  The elementary
square inequality suffices at a unit-speed minimizing reference curve. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def metricIntervalSpeed (g : SmoothMetric M) (γ : ℝ → M) (a b t : ℝ) : ℝ :=
  metricTangentNorm g (γ t) (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1)

def metricCurveEnergy (g : SmoothMetric M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (1 / 2 : ℝ) * (metricIntervalSpeed g γ a b t) ^ 2

theorem metricIntervalSpeed_continuousOn (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b)) :
    ContinuousOn (metricIntervalSpeed g γ a b) (Icc a b) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ => (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hv : ContinuousOn (fun t =>
      (⟨γ t, mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1⟩ : TangentBundle I4 M))
      (Icc a b) :=
    (hγ.continuousOn_tangentMapWithin le_rfl (uniqueDiffOn_Icc hab).uniqueMDiffOn).comp
      hinput.continuous.continuousOn (fun _ ht => ht)
  have hi := hv.inner_bundle hv
  have hs := Real.continuous_sqrt.comp_continuousOn hi
  change ContinuousOn (fun t => Real.sqrt (g.inner (γ t)
    (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1)
    (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1))) (Icc a b) at hs
  simpa only [metricIntervalSpeed, metricTangentNorm_eq_sqrt] using! hs

theorem metricIntervalSpeed_nonneg (g : SmoothMetric M) (γ : ℝ → M)
    (a b t : ℝ) : 0 ≤ metricIntervalSpeed g γ a b t := by
  rw [metricIntervalSpeed, metricTangentNorm_eq_sqrt]
  exact Real.sqrt_nonneg _

theorem metric_pathELength_eq_ofReal_integral (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b)) :
    (let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I4 γ a b) =
      ENNReal.ofReal (∫ t in a..b, metricIntervalSpeed g γ a b t) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  change (∫⁻ t in Icc a b, metricTangentENorm g (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1)) = _
  simp only [metricTangentENorm_eq_ofReal]
  change (∫⁻ t in Icc a b, ENNReal.ofReal (metricIntervalSpeed g γ a b t)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (metricIntervalSpeed_continuousOn g γ hab hγ).integrableOn_Icc
    (Filter.Eventually.of_forall (metricIntervalSpeed_nonneg g γ a b))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]

/-- Pointwise completion of the square, integrated on a compact interval. -/
theorem integral_speed_le_energy_add (s : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hs : ContinuousOn s (Icc a b)) :
    (∫ t in a..b, s t) ≤ (∫ t in a..b, (1 / 2 : ℝ) * (s t) ^ 2) + (b - a) / 2 := by
  have hsi : IntervalIntegrable s volume a b := hs.intervalIntegrable_of_Icc hab
  have hei : IntervalIntegrable (fun t => (1 / 2 : ℝ) * (s t) ^ 2) volume a b :=
    (continuousOn_const.mul (hs.pow 2)).intervalIntegrable_of_Icc hab
  have hbound := intervalIntegral.integral_mono_on hab hsi
    (hei.add intervalIntegrable_const) (fun t _ =>
      show s t ≤ (1 / 2 : ℝ) * (s t) ^ 2 + (1 / 2 : ℝ) by nlinarith [sq_nonneg (s t - 1)])
  rw [intervalIntegral.integral_add hei intervalIntegrable_const,
    intervalIntegral.integral_const] at hbound
  simpa only [smul_eq_mul, mul_one_div] using hbound

variable [T3Space M] [PreconnectedSpace M]

/-- A curve segment joining two points costs at least their distance minus
half its parameter duration, in the actual Riemannian kinetic energy. -/
theorem metricDistance_le_curveEnergy_add (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b)) :
    metricDistance g (γ a) (γ b) ≤ metricCurveEnergy g γ a b + (b - a) / 2 := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hl : metricEDistance g (γ a) (γ b) ≤
      ENNReal.ofReal (∫ t in a..b, metricIntervalSpeed g γ a b t) := by
    calc
      _ ≤ Manifold.pathELength I4 γ a b :=
        Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab.le
      _ = _ := metric_pathELength_eq_ofReal_integral g γ hab hγ
  have hnonneg : 0 ≤ ∫ t in a..b, metricIntervalSpeed g γ a b t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => metricIntervalSpeed_nonneg g γ a b t)
  rw [← ofReal_metricDistance g (γ a) (γ b), ENNReal.ofReal_le_ofReal_iff hnonneg] at hl
  exact hl.trans (integral_speed_le_energy_add _ hab.le
    (metricIntervalSpeed_continuousOn g γ hab hγ))


/-- The triangle inequality along a finite chain of actual points. -/
theorem metricDistance_le_sum_chain (g : SmoothMetric M) (p : ℕ → M) (n : ℕ) :
    metricDistance g (p 0) (p n) ≤
      ∑ i ∈ Finset.range n, metricDistance g (p i) (p (i + 1)) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact le_of_eq ((metricDistance_eq_zero_iff g (p 0) (p 0)).mpr rfl)
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (metricDistance_triangle g (p 0) (p n) (p (n + 1))).trans
        (_root_.add_le_add ih le_rfl)

/-- A finite piecewise C1 competitor with matching endpoints satisfies the
same energy bound.  There is no regularity requirement at its corners. -/
theorem finite_piece_metric_energy_lower (g : SmoothMetric M) (n : ℕ)
    (p : ℕ → M) (t : ℕ → ℝ) (γ : ℕ → ℝ → M)
    (ht : ∀ i < n, t i < t (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i) (Icc (t i) (t (i + 1))))
    (hleft : ∀ i < n, γ i (t i) = p i)
    (hright : ∀ i < n, γ i (t (i + 1)) = p (i + 1)) :
    metricDistance g (p 0) (p n) - (t n - t 0) / 2 ≤
      ∑ i ∈ Finset.range n, metricCurveEnergy g (γ i) (t i) (t (i + 1)) := by
  have hp : ∀ i ∈ Finset.range n,
      metricDistance g (p i) (p (i + 1)) ≤
        metricCurveEnergy g (γ i) (t i) (t (i + 1)) + (t (i + 1) - t i) / 2 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simpa only [hleft i hi', hright i hi'] using
      metricDistance_le_curveEnergy_add g (γ i) (ht i hi') (hγ i hi')
  have hs := (metricDistance_le_sum_chain g p n).trans (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub] at hs
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual path metric is bounded by a uniform speed bound on an interval. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem metricDistance_le_of_speed_bound (g : SmoothMetric M) {γ : ℝ → M}
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b))
    (hs : ∀ t ∈ Icc a b, metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C) :
    metricDistance g (γ a) (γ b) ≤ C * (b-a) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hb : metricEDistance g (γ a) (γ b) ≤ ENNReal.ofReal (C*(b-a)) := by
    apply (Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab).trans
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    change (∫⁻ t in Icc a b, metricTangentENorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1)) ≤ _
    calc
      _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal C := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [metricTangentENorm_eq_ofReal]
        exact ENNReal.ofReal_le_ofReal (hs t ht)
      _ = ENNReal.ofReal (C*(b-a)) := by
        rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
          ENNReal.ofReal_mul hC]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [metricDistance,ENNReal.toReal_ofReal (mul_nonneg hC (sub_nonneg.mpr hab))] using ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single convex linear chart carries both sharp metric comparison bounds. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

theorem exists_sharp_linear_chart_neighborhood (g : SmoothMetric M) (c : M)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : FourSpace ≃L[ℝ] FourSpace, ∃ V : Set FourSpace,
      IsOpen V ∧ Convex ℝ V ∧ A.symm (chartAt FourSpace c c) ∈ V ∧
      (∀ x ∈ V, A x ∈ (chartAt FourSpace c).target) ∧
      (∀ x ∈ V, ∀ y ∈ V,
        metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤
          Real.sqrt (1+δ)*dist x y) ∧
      (∀ x ∈ V, ∀ y ∈ V,
        dist x y ≤ (1 / Real.sqrt (1-δ))*
          metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y))) := by
  let Z := chartAt FourSpace c
  let z₀ : ChartTarget c := ⟨Z c,Z.map_source (mem_chart_source FourSpace c)⟩
  let A := frozenFrameLinearEquiv g c z₀
  let x₀ := A.symm (Z c)
  let T : FourSpace → M := fun x => Z.symm (A x)
  have hAc : A x₀ = Z c := A.apply_symm_apply _
  have hTc : T x₀ = c := by rw [show T x₀ = Z.symm (A x₀) from rfl,hAc,Z.left_inv (mem_chart_source FourSpace c)]
  obtain ⟨r,hr,htarget,hforward⟩ := exists_frozenFrame_symm_lipschitz g c z₀ δ hδ hδ1.le
  obtain ⟨s,hs,_,hreverse⟩ := exists_frozenFrame_chart_lipschitz_at g c z₀ δ hδ hδ1
  have hsc : s ∈ 𝓝 c := by
    change s ∈ 𝓝 (Z.symm (Z c)) at hs
    simpa only [Z.left_inv (mem_chart_source FourSpace c)] using hs
  have hT : ContinuousAt T x₀ :=
    (Z.symm.continuousAt (by rw [hAc]; exact z₀.property)).comp A.continuous.continuousAt
  have hn : (A ⁻¹' Metric.ball z₀.val r) ∩ T ⁻¹' s ∈ 𝓝 x₀ := by
    apply inter_mem
    · exact A.continuous.continuousAt (by rw [hAc]; exact Metric.ball_mem_nhds _ hr)
    · exact hT (by rwa [hTc])
  obtain ⟨ρ,hρ,hsmall⟩ := Metric.mem_nhds_iff.mp hn
  let V := Metric.ball x₀ ρ
  have hball (x : FourSpace) (hx : x ∈ V) : A x ∈ Metric.closedBall z₀.val r :=
    Metric.ball_subset_closedBall (hsmall hx).1
  have hVT (x : FourSpace) (hx : x ∈ V) : A x ∈ Z.target := htarget (hball x hx)
  refine ⟨A,V,Metric.isOpen_ball,convex_ball _ _,Metric.mem_ball_self hρ,hVT,?_,?_⟩
  · intro x hx y hy
    have hh := hforward (A x) (hball x hx) (A y) (hball y hy)
    change metricEDistance g (T x) (T y) ≤ ENNReal.ofReal (Real.sqrt (1+δ)) *
      edist (A.symm (A x)) (A.symm (A y)) at hh
    simp only [A.symm_apply_apply] at hh
    rw [← ofReal_metricDistance g,edist_dist,← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp hh
  · intro x hx y hy
    have hh := hreverse (T x) (hsmall hx).2 (T y) (hsmall hy).2
    have hTx : Z (T x) = A x := Z.right_inv (hVT x hx)
    have hTy : Z (T y) = A y := Z.right_inv (hVT y hy)
    change edist (A.symm (Z (T x))) (A.symm (Z (T y))) ≤ _ at hh
    rw [hTx,hTy,A.symm_apply_apply,A.symm_apply_apply,edist_dist,
      ← ofReal_metricDistance g,← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt (1-δ))] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity) (metricDistance_nonneg g _ _))).mp hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual Riemannian kinetic energy of a chart
curve with the coordinate energy used in the second-variation calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_curve_contMDiffOn (c : M) (x : ℝ → FourSpace) {a b : ℝ}
    (hx : ContDiffOn ℝ 1 x (Icc a b))
    (hz : MapsTo x (Icc a b) (chartAt FourSpace c).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (fun t => (chartAt FourSpace c).symm (x t)) (Icc a b) :=
  (contMDiffOn_chart_symm (I := I4) (x := c) (n := 1)).comp hx.contMDiffOn hz

theorem chart_curve_derivativeWithin (c : M) (x : ℝ → FourSpace)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hz : x t ∈ (chartAt FourSpace c).target) (v : JacobiCoordinateVector)
    (hx : HasDerivWithinAt x (WithLp.toLp 2 v) (Icc a b) t) :
    mfderivWithin 𝓘(ℝ, ℝ) I4 (fun s => (chartAt FourSpace c).symm (x s))
      (Icc a b) t 1 =
      mfderiv I4 I4 (chartAt FourSpace c).symm (x t) (WithLp.toLp 2 v) := by
  have hu : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffOn_Icc hab t ht
  have hxm : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I4 x (Icc a b) t :=
    hx.differentiableWithinAt.mdifferentiableWithinAt
  have hcomp := mfderiv_comp_mfderivWithin t
    ((mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hz)
    hxm hu.uniqueMDiffWithinAt
  have hd : mfderivWithin 𝓘(ℝ, ℝ) I4 x (Icc a b) t 1 = WithLp.toLp 2 v := by
    rw [mfderivWithin_eq_fderivWithin, hx.hasFDerivWithinAt.fderivWithin hu]
    exact one_smul ℝ _
  exact (congrArg (fun L => L 1) hcomp).trans
    (congrArg (mfderiv I4 I4 (chartAt FourSpace c).symm (x t)) hd)

theorem chart_curve_energy_density (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hz : x t ∈ (chartAt FourSpace c).target) (v : JacobiCoordinateVector)
    (hx : HasDerivWithinAt x (WithLp.toLp 2 v) (Icc a b) t) :
    (1 / 2 : ℝ) * (metricIntervalSpeed g
      (fun s => (chartAt FourSpace c).symm (x s)) a b t) ^ 2 =
      chartEnergyDensity g c (x t) v := by
  unfold metricIntervalSpeed
  rw [chart_curve_derivativeWithin c x hab ht hz v hx, metricTangentNorm_eq_sqrt]
  let u := mfderiv I4 I4 (chartAt FourSpace c).symm (x t) (WithLp.toLp 2 v)
  have hnonneg : 0 ≤ g.inner ((chartAt FourSpace c).symm (x t)) u u := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (g.pos _ u hu).le
  rw [Real.sq_sqrt hnonneg]
  exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
    (metricInChart_pairing g c (x t) v v).symm

theorem metricCurveEnergy_chart (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v : ℝ → JacobiCoordinateVector) {a b : ℝ} (hab : a < b)
    (hz : MapsTo x (Icc a b) (chartAt FourSpace c).target)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (WithLp.toLp 2 (v t)) (Icc a b) t) :
    metricCurveEnergy g (fun t => (chartAt FourSpace c).symm (x t)) a b =
      ∫ t in a..b, chartEnergyDensity g c (x t) (v t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab.le] at ht
  exact chart_curve_energy_density g c x hab ht (hz ht) (v t) (hx t ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential differential is arbitrarily close to an
isometry near zero, uniformly in the tangent direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_metric_differential_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (w : FourSpace) :
    metricTangentNorm g (frameExponential g o e 0)
      (mfderiv I4 I4 (frameExponential g o e) 0 w) = ‖w‖ := by
  have hd := frameExponential_chart_strictDerivative_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hzero : fderiv ℝ (fun v : FourSpace => chartAt FourSpace e.base
      (frameExponential g o e v)) 0 = e.frame.map.toContinuousLinearMap := by
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using hd.hasFDerivAt.fderiv
  have hc := frameExponential_center_fderiv g o e 0
  rw [frameExponential_zero] at hc
  have hm : mfderiv I4 I4 (frameExponential g o e) 0 w = e.frame.map w := by
    exact (congrArg (fun L : FourSpace →L[ℝ] FourSpace => L w) hc).symm.trans
      (congrArg (fun L : FourSpace →L[ℝ] FourSpace => L w) hzero)
  let u : FourSpace := mfderiv I4 I4 (frameExponential g o e) 0 w
  change metricTangentNorm g (frameExponential g o e 0) u = ‖w‖
  have hu : u = e.frame.map w := hm
  have hn : metricTangentNorm g e.base (show TangentSpace I4 e.base from e.frame.map w) =
      ‖w‖ := by
    have hh := metricTangentNorm_eq_sqrt g e.base
      (show TangentSpace I4 e.base from e.frame.map w)
    simpa only [e.frame.inner_map_self, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg w)] using! hh
  rw [hu, frameExponential_zero]
  exact hn

theorem frameExponential_metric_differential_continuous (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) :
    Continuous (fun p : FourSpace × FourSpace =>
      metricTangentNorm g (frameExponential g o e p.1)
        (mfderiv I4 I4 (frameExponential g o e) p.1 p.2)) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : Continuous (fun p : FourSpace × FourSpace =>
      (⟨p.1, p.2⟩ : TangentBundle I4 FourSpace)) :=
    (tangentBundleModelSpaceHomeomorph I4).symm.continuous
  have hv := ((frameExponential_contMDiff g o e).continuous_tangentMap le_rfl).comp hinput
  have hs := Real.continuous_sqrt.comp (hv.inner_bundle hv)
  change Continuous (fun p : FourSpace × FourSpace =>
    Real.sqrt (g.inner (frameExponential g o e p.1)
      (mfderiv I4 I4 (frameExponential g o e) p.1 p.2)
      (mfderiv I4 I4 (frameExponential g o e) p.1 p.2))) at hs
  simpa only [metricTangentNorm_eq_sqrt] using hs

theorem frameExponential_differential_norm_near (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 (0 : FourSpace), ∀ w : FourSpace,
      metricTangentNorm g (frameExponential g o e v)
        (mfderiv I4 I4 (frameExponential g o e) v w) ≤ (1 + ε) * ‖w‖ := by
  let B : FourSpace → FourSpace → ℝ := fun v w => metricTangentNorm g (frameExponential g o e v)
    (mfderiv I4 I4 (frameExponential g o e) v w)
  have hunit : ∀ᶠ v in 𝓝 (0 : FourSpace), ∀ w ∈ sphere (0 : FourSpace) 1,
      B v w < 1 + ε := by
    apply (isCompact_sphere (0 : FourSpace) 1).eventually_forall_of_forall_eventually
    intro w hw
    have hn : ‖w‖ = 1 := by simpa using hw
    have hc := (frameExponential_metric_differential_continuous g o e).continuousAt
      (x := ((0 : FourSpace), w))
    apply hc.eventually_lt continuousAt_const
    change B 0 w < 1 + ε
    dsimp [B]
    rw [frameExponential_metric_differential_zero, hn]
    linarith
  have hscale (v w : FourSpace) (r : ℝ) : B v (r • w) = |r| * B v w := by
    dsimp [B]
    have hm := (mfderiv I4 I4 (frameExponential g o e) v).map_smul r
      (show TangentSpace I4 v from w)
    have hh := congrArg (metricTangentNorm g (frameExponential g o e v)) hm
    apply hh.trans
    let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
    change ‖r • mfderiv I4 I4 (frameExponential g o e) v w‖ =
      |r| * ‖mfderiv I4 I4 (frameExponential g o e) v w‖
    rw [norm_smul, Real.norm_eq_abs]
  filter_upwards [hunit] with v hv
  intro w
  by_cases hw : w = 0
  · subst w
    have hz : B v 0 = 0 := by
      have h := hscale v (0 : FourSpace) 0
      simpa only [zero_smul, abs_zero, zero_mul] using! h
    change B v 0 ≤ _
    rw [hz, norm_zero, mul_zero]
  · let q : FourSpace := ‖w‖⁻¹ • w
    have hq : ‖q‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    have hwq : ‖w‖ • q = w := by
      dsimp [q]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
    change B v w ≤ (1 + ε) * ‖w‖
    calc
      B v w = ‖w‖ * B v q := by
        conv_lhs => rw [← hwq]
        rw [hscale, abs_of_nonneg (norm_nonneg w)]
      _ ≤ ‖w‖ * (1 + ε) := mul_le_mul_of_nonneg_left
        (hv q (by simpa using hq)).le (norm_nonneg w)
      _ = _ := mul_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual energy of a unit-speed distance-minimizing geodesic is a
local minimum among finite piecewise C1 variations with fixed endpoints. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricCurveEnergy_congr (g : SmoothMetric M) {γ η : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (h : EqOn γ η (Icc a b)) :
    metricCurveEnergy g γ a b = metricCurveEnergy g η a b := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have hv := congrArg (fun p : TangentBundle I4 M => metricTangentNorm g p.1 p.2)
    (tangentMapWithin_congr h (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) ht)
  change metricIntervalSpeed g γ a b t = metricIntervalSpeed g η a b t at hv
  dsimp only
  rw [hv]

variable [T3Space M] [CompactSpace M]

theorem frameGeodesic_intervalSpeed (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    metricIntervalSpeed g (frameGeodesic g k e) a b t = 1 := by
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t :=
    (uniqueDiffOn_Icc hab t ht).uniqueMDiffWithinAt
  have hd := (frameGeodesic_contMDiff g k e).mdifferentiable one_ne_zero t
  unfold metricIntervalSpeed
  rw [mfderivWithin_eq_mfderiv hu hd, frameGeodesic_mfderiv]
  have hn := metricTangentNorm_eq_sqrt g (parallelFrameFlowMap g k t e).base
    (show TangentSpace I4 (parallelFrameFlowMap g k t e).base from
      (parallelFrameFlowMap g k t e).frame.vector k)
  have h := congrArg Real.sqrt ((parallelFrameFlowMap g k t e).frame.inner_vector_self k)
  have heq := hn.trans (by simpa only [Real.sqrt_one] using! h)
  exact heq

theorem frameGeodesic_energy (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) {a b : ℝ} (hab : a < b) :
    metricCurveEnergy g (frameGeodesic g k e) a b = (b - a) / 2 := by
  have h : metricCurveEnergy g (frameGeodesic g k e) a b =
      ∫ _ in a..b, (1 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    dsimp only
    rw [frameGeodesic_intervalSpeed g k e hab ht, one_pow, mul_one]
  rw [h, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one_div]

variable [PreconnectedSpace M]

/-- The path distance and unit speed of the reference curve imply energy minimality. -/
theorem geodesic_piece_energy_isLocalMin (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (n : ℕ) (t : ℕ → ℝ)
    (γ : ℕ → ℝ → ℝ → M) (p : ℝ → ℕ → M)
    (ht : ∀ i < n, t i < t (i + 1))
    (hγ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n,
      ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i ε) (Icc (t i) (t (i + 1))))
    (hleft : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n, γ i ε (t i) = p ε i)
    (hright : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n, γ i ε (t (i + 1)) = p ε (i + 1))
    (hends : ∀ᶠ ε in 𝓝 (0 : ℝ),
      p ε 0 = frameGeodesic g k e (t 0) ∧ p ε n = frameGeodesic g k e (t n))
    (href : ∀ i < n, EqOn (γ i 0) (frameGeodesic g k e) (Icc (t i) (t (i + 1))))
    (hmin : metricDistance g (frameGeodesic g k e (t 0))
        (frameGeodesic g k e (t n)) = t n - t 0) :
    IsLocalMin (fun ε => ∑ i ∈ Finset.range n,
      metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) 0 := by
  have hzero : (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i 0) (t i) (t (i + 1))) =
      (t n - t 0) / 2 := by
    calc
      _ = ∑ i ∈ Finset.range n, (t (i + 1) - t i) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [metricCurveEnergy_congr g (ht i hi').le (href i hi'),
          frameGeodesic_energy g k e (ht i hi')]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub]
  show ∀ᶠ ε in 𝓝 (0 : ℝ), _
  filter_upwards [hγ, hleft, hright, hends] with ε hγε hle hre he
  have hb := finite_piece_metric_energy_lower g n (p ε) t (fun i => γ i ε) ht hγε hle hre
  rw [he.1, he.2, hmin] at hb
  rw [hzero]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the actual two-form covariant expression in the
normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heatTwoFormConnection_contDiffAt (n : ℕ) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ (n + 1) P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hdet : (P x).2.det ≠ 0) (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => heatTwoFormConnection g c P i y k l) x := by
  have hB : ContDiffAt ℝ n (heatNormalFrameConnection g c P i) x :=
    contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr
      (fun b => heatNormalFrameConnection_contDiffAt n g c P x hP hx hdet i a b))
  let L := (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).toContinuousLinearMap
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hc := π.contDiff.contDiffAt.comp x (L.contDiff.contDiffAt.comp x hB)
  change ContDiffAt ℝ n
    (fun y => heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)
      (heatNormalFrameConnection g c P i y) k) x at hc
  simpa only [heatConnectionActionLinear_apply, heatTwoFormConnection,
    heatTwoFormConnectionMatrix] using hc

theorem heatNormalTwoFormNabla_contDiffAt (n : ℕ) {o : FrameOrientation g}
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ (n + 1) P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hdet : (P x).2.det ≠ 0) (i : Fin 4) :
    ContDiffAt ℝ n (heatNormalTwoFormNabla o c P u i) x := by
  let a := heatNormalTwoFormValue o c P u
  have ha : ContDiffAt ℝ (n + 1) a x :=
    heatNormalTwoFormValue_contDiffAt (n + 1) hu c P x hP hx
  have ha0 : ContDiffAt ℝ n a x := ha.of_le (by exact_mod_cast Nat.le_succ n)
  have hal (l : Fin 6) : ContDiffAt ℝ n (fun y => a y l) x := by
    let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) l
    exact ContDiffAt.comp (f := a) (g := π) x π.contDiff.contDiffAt ha0
  have hproduct : ContDiffAt ℝ n
      (fun y => twoFormSkewAction (twoFormExtract (heatNormalFrameConnection g c P i y)) (a y)) x := by
    apply (contDiffAt_piLp 2).mpr
    intro k
    have hsum : ContDiffAt ℝ n (fun y => ∑ l : Fin 6, heatTwoFormConnection g c P i y k l * a y l) x :=
      ContDiffAt.sum (fun l _ => (heatTwoFormConnection_contDiffAt n c P x hP hx hdet i k l).mul
        (hal l))
    apply hsum.congr_of_eventuallyEq
    filter_upwards [] with y
    exact (congrFun (heatTwoFormConnectionMatrix_action (heatNormalFrameConnection g c P i y) (a y)) k).symm
  exact ((ha.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply
    (contDiffAt_const (c := coordinateVector i))).add hproduct

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame rough operator is the actual metric trace of the
covariant Hessian once the proved metric and drift transport laws apply. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_oneForm_rough_pullback (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates 1)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hT : ∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (A : Mat4) (b : Fin 4 → ℝ)
    (hA : jacobianMatrix (fun y => (P y).1) x * A *
      (jacobianMatrix (fun y => (P y).1) x)ᵀ = (metricInChart g c (P x).1)⁻¹)
    (hb : ∀ r, (∑ i, jacobianMatrix (fun y => (P y).1) x r i * b i) -
      (∑ i, ∑ j, A i j * partialDeriv
        (fun y => jacobianMatrix (fun z => (P z).1) y r j) i x) =
      ∑ p, ∑ q, (metricInChart g c (P x).1)⁻¹ p q * christoffel g c (P x).1 r p q)
    (v : Fin 1 → Fin 4) :
    -(∑ i, ∑ j, A i j * tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v) +
      (∑ i, b i * tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i x v) =
    -frameTensor (P x).2 (oneFormSecondTrace (metricInChart g c (P x).1)⁻¹
      (covariantDerivative g c (covariantDerivative g c T) (P x).1)) v := by
  let J := jacobianMatrix (fun y => (P y).1)
  let H := (metricInChart g c (P x).1)⁻¹
  let S := fun r => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c) T r (P x).1) v
  let Q : Mat4 := Matrix.of fun r s => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c)
      (tensorCovariantDirection (connectionMatrix g c) T r) s (P x).1) v
  have hPd := hP.differentiableAt (by norm_num)
  have hf (i : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (T (P y).1)) i x v = ∑ r, J x r i * S r := by
    have h := heatNormal_covariant_pullback g c P T x hPd
      (fun a => (hT _ hx a).differentiableAt (by simp)) hG.self_of_nhds i
    rw [h]
    simp_rw [← heatFrame_baseJacobian P x hPd]
    exact heat_frameTensor_weighted_sum _ _ _ v
  have hs (i j : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v =
      (∑ r, partialDeriv (fun y => J y r i) j x * S r) +
        ∑ r, ∑ s, J x r i * J x s j * Q r s := by
    rw [heatNormal_covariant_second_pullback g c P T x hP hT hx hG i j]
    simp only [heat_frameTensor_weighted_sum, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    change J x r i * (J x s j * Q r s) = _
    ring
  simp_rw [hf, hs]
  have h := heat_rough_trace_algebra (J x) A H Q
    (fun i => matrixPartial J i x) b S
    (fun r => ∑ p, ∑ q, H p q * christoffel g c (P x).1 r p q) hA
    (fun i j r => heatJacobian_partials_commute hP.fst r j i) hb
  simp only [matrixPartial] at h
  rw [h, heat_connection_trace_expand]
  have hH : Hᵀ = H := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    ext i j
    exact metricInChart_comm g c (P x).1 j i
  rw [heat_framed_oneFormSecondTrace g c T (P x).2 H (P x).1 hH v]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame rough operator is the actual metric trace of the
covariant Hessian once the proved metric and drift transport laws apply. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_rough_pullback (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates 2)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hT : ∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (A : Mat4) (b : Fin 4 → ℝ)
    (hA : jacobianMatrix (fun y => (P y).1) x * A *
      (jacobianMatrix (fun y => (P y).1) x)ᵀ = (metricInChart g c (P x).1)⁻¹)
    (hb : ∀ r, (∑ i, jacobianMatrix (fun y => (P y).1) x r i * b i) -
      (∑ i, ∑ j, A i j * partialDeriv
        (fun y => jacobianMatrix (fun z => (P z).1) y r j) i x) =
      ∑ p, ∑ q, (metricInChart g c (P x).1)⁻¹ p q * christoffel g c (P x).1 r p q)
    (v : Fin 2 → Fin 4) :
    -(∑ i, ∑ j, A i j * tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v) +
      (∑ i, b i * tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i x v) =
    -frameTensor (P x).2 (twoFormSecondTrace (metricInChart g c (P x).1)⁻¹
      (covariantDerivative g c (covariantDerivative g c T) (P x).1)) v := by
  let J := jacobianMatrix (fun y => (P y).1)
  let H := (metricInChart g c (P x).1)⁻¹
  let S := fun r => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c) T r (P x).1) v
  let Q : Mat4 := Matrix.of fun r s => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c)
      (tensorCovariantDirection (connectionMatrix g c) T r) s (P x).1) v
  have hPd := hP.differentiableAt (by norm_num)
  have hf (i : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (T (P y).1)) i x v = ∑ r, J x r i * S r := by
    have h := heatNormal_covariant_pullback g c P T x hPd
      (fun a => (hT _ hx a).differentiableAt (by simp)) hG.self_of_nhds i
    rw [h]
    simp_rw [← heatFrame_baseJacobian P x hPd]
    exact heat_frameTensor_weighted_sum _ _ _ v
  have hs (i j : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v =
      (∑ r, partialDeriv (fun y => J y r i) j x * S r) +
        ∑ r, ∑ s, J x r i * J x s j * Q r s := by
    rw [heatNormal_covariant_second_pullback g c P T x hP hT hx hG i j]
    simp only [heat_frameTensor_weighted_sum, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    change J x r i * (J x s j * Q r s) = _
    ring
  simp_rw [hf, hs]
  have h := heat_rough_trace_algebra (J x) A H Q
    (fun i => matrixPartial J i x) b S
    (fun r => ∑ p, ∑ q, H p q * christoffel g c (P x).1 r p q) hA
    (fun i j r => heatJacobian_partials_commute hP.fst r j i) hb
  simp only [matrixPartial] at h
  rw [h, heat_connection_trace_expand]
  have hH : Hᵀ = H := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    ext i j
    exact metricInChart_comm g c (P x).1 j i
  rw [heat_framed_twoFormSecondTrace g c T (P x).2 H (P x).1 hH v]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint limits for a continuous curve whose interior has bounded speed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

theorem metricDistance_le_of_interior_speed_bound (g : SmoothMetric M) {γ : ℝ → M}
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hγ : Continuous γ)
    (hd : ∀ t ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C) :
    metricDistance g (γ a) (γ b) ≤ C * (b-a) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    rw [(metricDistance_eq_zero_iff g _ _).mpr rfl]
    simp
  have hmid (c d : ℝ) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
      metricDistance g (γ c) (γ d) ≤ C*(d-c) := by
    apply metricDistance_le_of_speed_bound g hcd hC
    · intro t ht
      exact (hd t ⟨hac.trans_le ht.1,ht.2.trans_lt hdb⟩).contMDiffWithinAt
    · intro t ht
      exact hs t ⟨hac.trans_le ht.1,ht.2.trans_lt hdb⟩
  let c : ℝ → ℝ := fun t => a+t*(b-a)
  let d : ℝ → ℝ := fun t => b-t*(b-a)
  have hc : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have h : Continuous c := continuous_const.add (continuous_id.mul continuous_const)
    simpa [c] using (h.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hd' : Tendsto d (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    have h : Continuous d := continuous_const.sub (continuous_id.mul continuous_const)
    simpa [d] using (h.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim : Tendsto (fun t => metricDistance g (γ (c t)) (γ (d t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (metricDistance g (γ a) (γ b))) :=
    (metricDistance_continuous g).continuousAt.tendsto.comp
      ((hγ.continuousAt.tendsto.comp hc).prodMk_nhds (hγ.continuousAt.tendsto.comp hd'))
  apply le_of_tendsto hlim
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < (1/2 : ℝ) :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [self_mem_nhdsWithin,ht] with t ht0 ht1
  have htpos : 0 < t := ht0
  have hac : a < c t := by dsimp [c]; nlinarith
  have hcd : c t ≤ d t := by dsimp [c,d]; nlinarith
  have hdb : d t < b := by dsimp [d]; nlinarith
  exact (hmid (c t) (d t) hac hcd hdb).trans
    (mul_le_mul_of_nonneg_left (by dsimp [c,d]; nlinarith) hC)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The energy of a finite piecewise C1 path bounds the distance to every
point on that path, using only its actual speed integral. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem metricCurveEnergy_nonneg (g : SmoothMetric M) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ metricCurveEnergy g γ a b :=
  intervalIntegral.integral_nonneg hab (fun t _ => mul_nonneg (by norm_num) (sq_nonneg _))

theorem metricDistance_point_le_curveEnergy_add (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b))
    {r : ℝ} (hr : r ∈ Icc a b) :
    metricDistance g (γ a) (γ r) ≤ metricCurveEnergy g γ a b + (b - a) / 2 := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hl : metricEDistance g (γ a) (γ r) ≤
      ENNReal.ofReal (∫ t in a..b, metricIntervalSpeed g γ a b t) := by
    calc
      _ ≤ Manifold.pathELength I4 γ a r :=
        Manifold.riemannianEDist_le_pathELength
          (hγ.mono (Icc_subset_Icc le_rfl hr.2)) rfl rfl hr.1
      _ ≤ Manifold.pathELength I4 γ a b := Manifold.pathELength_mono le_rfl hr.2
      _ = _ := metric_pathELength_eq_ofReal_integral g γ hab hγ
  have hn : 0 ≤ ∫ t in a..b, metricIntervalSpeed g γ a b t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => metricIntervalSpeed_nonneg g γ a b t)
  rw [← ofReal_metricDistance g (γ a) (γ r),ENNReal.ofReal_le_ofReal_iff hn] at hl
  exact hl.trans (integral_speed_le_energy_add _ hab.le (metricIntervalSpeed_continuousOn g γ hab hγ))

theorem finite_piece_metric_energy_point_bound (g : SmoothMetric M) (n : ℕ)
    (p : ℕ → M) (t : ℕ → ℝ) (γ : ℕ → ℝ → M)
    (ht : ∀ i < n, t i < t (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i) (Icc (t i) (t (i + 1))))
    (hleft : ∀ i < n, γ i (t i) = p i)
    (hright : ∀ i < n, γ i (t (i + 1)) = p (i + 1))
    (i : ℕ) (hi : i < n) (r : ℝ) (hr : r ∈ Icc (t i) (t (i + 1))) :
    metricDistance g (p 0) (γ i r) ≤
      (∑ j ∈ Finset.range n, metricCurveEnergy g (γ j) (t j) (t (j + 1))) +
        (t n - t 0) / 2 := by
  have hprefix := finite_piece_metric_energy_lower g i p t γ
    (fun j hj => ht j (hj.trans hi)) (fun j hj => hγ j (hj.trans hi))
    (fun j hj => hleft j (hj.trans hi)) (fun j hj => hright j (hj.trans hi))
  have hlast := metricDistance_point_le_curveEnergy_add g (γ i) (ht i hi) (hγ i hi) hr
  rw [hleft i hi] at hlast
  have htri := metricDistance_triangle g (p 0) (p i) (γ i r)
  have hs : (∑ j ∈ Finset.range (i + 1), metricCurveEnergy g (γ j) (t j) (t (j + 1))) ≤
      ∑ j ∈ Finset.range n, metricCurveEnergy g (γ j) (t j) (t (j + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hi))
    intro j hj _
    exact metricCurveEnergy_nonneg g (γ j) (ht j (Finset.mem_range.mp hj)).le
  have htime (j k : ℕ) (hjk : j ≤ k) (hkn : k ≤ n) : t j ≤ t k := by
    induction k, hjk using Nat.le_induction with
    | base => rfl
    | succ k hjk ih => exact (ih (Nat.le_of_succ_le hkn)).trans (ht k (lt_of_lt_of_le (Nat.lt_succ_self k) hkn)).le
  have htn := htime (i+1) n (Nat.succ_le_of_lt hi) le_rfl
  rw [Finset.sum_range_succ] at hs
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint-corrected coordinate variations define genuine C1 manifold
curves, and their coordinate energy is the actual Riemannian energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

/-- Extend the two time fields only for the compactness argument.  The
resulting variation and its jets on the original segment are unchanged. -/
theorem endpointCorrectedPosition_inside_on (x y A B : ℝ → FourSpace)
    {a b : ℝ} (hab : a ≤ b) (hx : ContinuousOn x (Icc a b))
    (hy : ContinuousOn y (Icc a b)) (hA : Continuous A) (hB : Continuous B)
    (hA0 : A 0 = x a) (hB0 : B 0 = x b) (U : Set FourSpace) (hU : IsOpen U)
    (hxU : ∀ t ∈ Icc a b, x t ∈ U) :
    ∃ δ > 0, ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ U := by
  let X := IccExtend hab (fun t : Icc a b => x t)
  let Y := IccExtend hab (fun t : Icc a b => y t)
  have hX : Continuous X := hx.domRestrict.Icc_extend'
  have hY : Continuous Y := hy.domRestrict.Icc_extend'
  have hXe (t : ℝ) (ht : t ∈ Icc a b) : X t = x t := IccExtend_of_mem hab _ ht
  have hYe (t : ℝ) (ht : t ∈ Icc a b) : Y t = y t := IccExtend_of_mem hab _ ht
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  obtain ⟨δ, hδ, hinside⟩ := endpointCorrectedPosition_inside X Y A B a b hX hY hA hB
    (hA0.trans (hXe a ha).symm) (hB0.trans (hXe b hb).symm) U hU
    (fun t ht => (hXe t ht).symm ▸ hxU t ht)
  refine ⟨δ, hδ, fun ε hε t ht => ?_⟩
  have h := hinside ε hε t ht
  simpa only [endpointCorrectedPosition, endpointResidual, hXe t ht, hYe t ht,
    hXe a ha, hXe b hb, hYe a ha, hYe b hb] using h

theorem endpointCorrectedPosition_contDiffOn (x y v w A B : ℝ → FourSpace)
    {a b : ℝ} (hab : a < b) (ε : ℝ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (v t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (w t) t)
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b)) :
    ContDiffOn ℝ 1 (endpointCorrectedPosition x y A B a b ε) (Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :=
    endpointCorrectedPosition_time x y v w A B a b ε t (hx t ht) (hy t ht)
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
  have hc : ContinuousOn (endpointCorrectedVelocity x y v w A B a b ε) (Icc a b) :=
    ((hv.add (hw.const_smul ε)).sub continuousOn_const).add continuousOn_const
  apply hc.congr
  intro t ht
  exact (hd t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem endpointCorrected_curve_contMDiffOn (c : M) (x y v w A B : ℝ → FourSpace)
    {a b : ℝ} (hab : a < b) (ε : ℝ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (v t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (w t) t)
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hz : ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ (chartAt FourSpace c).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I4 1
      (fun t => (chartAt FourSpace c).symm (endpointCorrectedPosition x y A B a b ε t))
      (Icc a b) :=
  chart_curve_contMDiffOn c _ (endpointCorrectedPosition_contDiffOn x y v w A B hab ε
    hx hy hv hw) hz

theorem endpointCorrected_actual_energy (g : SmoothMetric M) (c : M)
    (x y v w A B : ℝ → FourSpace) {a b : ℝ} (hab : a < b) (ε : ℝ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (v t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (w t) t)
    (hz : ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ (chartAt FourSpace c).target) :
    metricCurveEnergy g (fun t => (chartAt FourSpace c).symm
      (endpointCorrectedPosition x y A B a b ε t)) a b =
      ∫ t in a..b, chartEnergyDensity g c (endpointCorrectedPosition x y A B a b ε t)
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A B a b ε t)) := by
  apply metricCurveEnergy_chart g c _ _ hab hz
  intro t ht
  simpa only [WithLp.toLp_ofLp] using
    (endpointCorrectedPosition_time x y v w A B a b ε t (hx t ht) (hy t ht)).hasDerivWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Sharp local distance bounds for the actual exponential. These bounds
will exclude corners in distance-minimizing concatenations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_distance_le_of_differential (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (s : Set FourSpace)
    (hs : Convex ℝ s) (K : ℝ≥0)
    (hK : ∀ z ∈ s, ∀ w : FourSpace, metricTangentNorm g (frameExponential g o e z)
      (mfderiv I4 I4 (frameExponential g o e) z w) ≤ K * ‖w‖)
    (u v : FourSpace) (hu : u ∈ s) (hv : v ∈ s) :
    metricEDistance g (frameExponential g o e u) (frameExponential g o e v) ≤
      K * edist u v := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let α : ℝ →ᴬ[ℝ] FourSpace := ContinuousAffineMap.lineMap u v
  let γ := fun t => frameExponential g o e (α t)
  have hα : ContDiff ℝ 1 α := α.contDiff
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ :=
    (frameExponential_contMDiff g o e).comp hα.contMDiff
  have hαs : MapsTo α (Icc 0 1) s := by
    rw [mapsTo_iff_image_subset, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hs.segment_subset hu hv
  have hstart : γ 0 = frameExponential g o e u := by
    simp [γ, α, ContinuousAffineMap.coe_lineMap_eq]
  have hend : γ 1 = frameExponential g o e v := by
    simp [γ, α, ContinuousAffineMap.coe_lineMap_eq]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      metricTangentENorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤
        K * ‖v - u‖ₑ := by
    have hd := frameExponential_curve_derivative g o e α hα t
    have hαd : deriv α t = v - u :=
      (AffineMap.hasDerivAt_lineMap (a := u) (b := v)).deriv
    have hbd := hK (α t) (hαs ht) (v - u)
    have hd' := hd.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) hαd)
    have heq := congrArg (metricTangentENorm g (γ t)) hd'
    rw [heq]
    have h := ENNReal.ofReal_le_ofReal hbd
    simpa only [metricTangentENorm_eq_ofReal, ENNReal.ofReal_mul K.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ofReal_norm] using! h
  calc
    _ ≤ Manifold.pathELength I4 γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hstart hend zero_le_one
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
        metricTangentENorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) :=
      Manifold.pathELength_eq_lintegral_mfderiv_Icc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (K : ℝ≥0∞) * ‖v - u‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hspeed
    _ = K * edist u v := by
      simp only [lintegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
        Measure.restrict_apply_univ, mul_one, edist_eq_enorm_sub, enorm_sub_rev]

theorem frameExponential_locally_almost_isometric (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > (0 : ℝ), ∀ u ∈ Metric.ball (0 : FourSpace) r,
      ∀ v ∈ Metric.ball (0 : FourSpace) r,
      metricEDistance g (frameExponential g o e u) (frameExponential g o e v) ≤
        ENNReal.ofReal (1 + ε) * edist u v := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (frameExponential_differential_norm_near g o e ε hε)
  let K : ℝ≥0 := ⟨1 + ε, by positivity⟩
  refine ⟨r, hr, fun u hu v hv => ?_⟩
  have h := frameExponential_distance_le_of_differential g o e _
    (convex_ball (0 : FourSpace) r) K (fun z hz w => hball hz w) u v hu hv
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (1 + ε) := ENNReal.coe_nnreal_eq K
  rw [hK] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finitely many exceptional parameters do not change a uniform path-speed bound. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

theorem metricDistance_le_of_speed_bound_off_finite (g : SmoothMetric M) (E : Finset ℝ)
    {γ : ℝ → M} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hγ : Continuous γ)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, t ∉ E → metricTangentNorm g (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C) :
    metricDistance g (γ a) (γ b) ≤ C * (b-a) := by
  classical
  induction E using Finset.induction_on generalizing a b with
  | empty =>
    exact metricDistance_le_of_interior_speed_bound g hab hC hγ
      (fun t ht => hd t ht (by simp)) (fun t ht => hs t ht (by simp))
  | @insert t E ht ih =>
    by_cases hti : t ∈ Ioo a b
    · have hleft : metricDistance g (γ a) (γ t) ≤ C*(t-a) := by
        apply ih hti.1.le
        · intro x hx hxE
          exact hd x ⟨hx.1,hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_lt hx.2,hxE⟩)
        · intro x hx hxE
          exact hs x ⟨hx.1,hx.2.trans hti.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_lt hx.2,hxE⟩)
      have hright : metricDistance g (γ t) (γ b) ≤ C*(b-t) := by
        apply ih hti.2.le
        · intro x hx hxE
          exact hd x ⟨hti.1.trans hx.1,hx.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_gt hx.1,hxE⟩)
        · intro x hx hxE
          exact hs x ⟨hti.1.trans hx.1,hx.2⟩
            (by simp only [Finset.mem_insert,not_or]; exact ⟨ne_of_gt hx.1,hxE⟩)
      calc
        _ ≤ metricDistance g (γ a) (γ t) + metricDistance g (γ t) (γ b) :=
          metricDistance_triangle g _ _ _
        _ ≤ C*(t-a)+C*(b-t) := add_le_add hleft hright
        _ = _ := by ring
    · apply ih hab
      · intro x hx hxE
        exact hd x hx (by
          simp only [Finset.mem_insert,not_or]
          exact ⟨fun h => hti (h ▸ hx),hxE⟩)
      · intro x hx hxE
        exact hs x hx (by
          simp only [Finset.mem_insert,not_or]
          exact ⟨fun h => hti (h ▸ hx),hxE⟩)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine corner between two radial geodesics can be shortened. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_corner_shortening (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (u v : FourSpace)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
    ∃ r > (0 : ℝ), ∀ t : ℝ, 0 < t → t < r →
      metricEDistance g (frameExponential g o e ((-t) • u))
        (frameExponential g o e (t • v)) < ENNReal.ofReal (2 * t) := by
  have hsum : ‖u + v‖ < 2 := by
    have hle : ‖u + v‖ ≤ 2 := by simpa only [hu, hv, one_add_one_eq_two] using norm_add_le u v
    apply lt_of_le_of_ne hle
    intro heq
    apply huv
    have hadd : ‖u + v‖ = ‖u‖ + ‖v‖ := by simpa only [hu, hv, one_add_one_eq_two] using heq
    simpa only [hu, hv, one_smul] using norm_add_eq_iff_real.mp hadd
  let ε := (2 - ‖u + v‖) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hfac : (1 + ε) * ‖u + v‖ < 2 := by
    have hp : 0 < (2 - ‖u + v‖) * (4 - ‖u + v‖) :=
      mul_pos (by linarith) (by linarith)
    dsimp [ε]
    nlinarith
  obtain ⟨r, hr, hbound⟩ := frameExponential_locally_almost_isometric g o e ε hε
  refine ⟨r, hr, fun t ht htr => ?_⟩
  have hleft : (-t) • u ∈ ball (0 : FourSpace) r := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos ht, hu, mul_one] using htr
  have hright : t • v ∈ ball (0 : FourSpace) r := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, hv, mul_one] using htr
  have hd : edist ((-t) • u) (t • v) = ENNReal.ofReal (t * ‖u + v‖) := by
    have heq : (-t) • u - t • v = (-t) • (u + v) := by
      rw [smul_add, neg_smul, neg_smul]
      abel
    rw [edist_eq_enorm_sub, ← ofReal_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos ht]
  have h := hbound ((-t) • u) hleft (t • v) hright
  rw [hd, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + ε)] at h
  apply h.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * t)).mpr
  nlinarith [mul_lt_mul_of_pos_right hfac ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint data and a common chart neighborhood for an actual normal
variation of one geodesic segment.  All endpoint jets come from the same
intrinsic affine curve, even when adjacent segments use different charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure NormalEndpointJetData (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (a : Fin 3 → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  position : ℝ → FourSpace
  first : ℝ → FourSpace
  second : ℝ → FourSpace
  position_continuous : Continuous position
  first_continuous : Continuous first
  second_continuous : Continuous second
  position_zero : position 0 = chartAt FourSpace c e.base
  first_zero : first 0 = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
  second_zero : second 0 = endpointChartSecond e.base c (chartAt FourSpace e.base e.base)
    (normalEndpointDirection g e a) 0
  derivative : ∀ ε ∈ Ioo (-radius) radius,
    HasDerivAt position (first ε) ε ∧ HasDerivAt first (second ε) ε
  inside : ∀ ε ∈ Icc (-radius) radius, position ε ∈ (chartAt FourSpace c).target
  realizes : ∀ ε ∈ Icc (-radius) radius,
    (chartAt FourSpace c).symm (position ε) = normalEndpointCurve g e a ε

def normalEndpointJetData (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    NormalEndpointJetData g e c a := Classical.choice (by
  obtain ⟨δ, hδ, A, A', A'', hA, hA', hA'', hzero, hfirst, hsecond, hder, hreal⟩ :=
    exists_normalEndpointJets g e c hc a
  exact ⟨⟨δ, hδ, A, A', A'', hA, hA', hA'', hzero, hfirst, hsecond, hder,
    fun ε hε => (hreal ε hε).1, fun ε hε => (hreal ε hε).2⟩⟩)

variable [T3Space M] [CompactSpace M]

def normalSegmentPosition (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε t : ℝ) : FourSpace :=
  endpointCorrectedPosition (fun s => chartAt FourSpace c (frameGeodesic g 0 e s))
    (fun s => WithLp.toLp 2 (normalChartField g c e N s)) A B a b ε t

def normalSegmentCurve (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε t : ℝ) : M :=
  (chartAt FourSpace c).symm (normalSegmentPosition g e c N A B a b ε t)

/-- A single positive parameter radius keeps the entire corrected segment
inside its chart and inside both endpoint-jet neighborhoods. -/
theorem normalSegment_common_radius (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ContinuousOn N (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    ∃ δ > 0, δ ≤ A.radius ∧ δ ≤ B.radius ∧ ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈
        (chartAt FourSpace c).target := by
  have hx : ContinuousOn (fun t => chartAt FourSpace c (frameGeodesic g 0 e t)) (Icc a b) :=
    ((frameGeodesic_chart_contDiffOn g 0 e c).mono hc).continuousOn
  have hy : ContinuousOn (fun t => WithLp.toLp 2 (normalChartField g c e N t)) (Icc a b) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (normalChartField_continuousOn g c e N (Icc a b) hc hN)
  obtain ⟨r, hr, hinside⟩ := endpointCorrectedPosition_inside_on
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (fun t => WithLp.toLp 2 (normalChartField g c e N t)) A.position B.position hab.le
    hx hy A.position_continuous B.position_continuous A.position_zero B.position_zero
    (chartAt FourSpace c).target (chartAt FourSpace c).open_target
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  refine ⟨min r (min A.radius B.radius), lt_min hr (lt_min A.radius_pos B.radius_pos),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro ε hε t ht
  apply hinside ε ?_ t ht
  constructor <;> linarith [hε.1, hε.2, min_le_left r (min A.radius B.radius)]

theorem normalSegmentCurve_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b t : ℝ}
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (ht : frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source) :
    normalSegmentCurve g e c N A.position B.position a b 0 t = frameGeodesic g 0 e t := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
  exact (chartAt FourSpace c).left_inv ht

theorem normalSegmentCurve_endpoints (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b ε : ℝ} (hab : a < b)
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : ε ∈ Icc (-A.radius) A.radius) (hB : ε ∈ Icc (-B.radius) B.radius) :
    normalSegmentCurve g e c N A.position B.position a b ε a =
      normalEndpointCurve g (parallelFrameFlowMap g 0 a e) (N a) ε ∧
    normalSegmentCurve g e c N A.position B.position a b ε b =
      normalEndpointCurve g (parallelFrameFlowMap g 0 b e) (N b) ε := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_left _ _ _ _ _ _ _ hab.ne,
    endpointCorrectedPosition_right _ _ _ _ _ _ _ hab.ne]
  exact ⟨A.realizes ε hA, B.realizes ε hB⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A distance-minimizing concatenation of radial geodesics has matching
incoming and outgoing tangent directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_ray_distance (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (q : Directions) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    metricEDistance g (frameExponential g o e (a • q.val))
      (frameExponential g o e (b • q.val)) ≤ ENNReal.ofReal |b - a| := by
  have h := unitGeodesic_distance_le g o (unitTangentTurn e q) a b
  rwa [← frameExponential_radial g o e q ⟨a, ha⟩,
    ← frameExponential_radial g o e q ⟨b, hb⟩] at h

theorem frameExponential_no_minimizing_corner (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (u v : FourSpace)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : metricEDistance g (frameExponential g o e ((-a) • u))
      (frameExponential g o e (b • v)) = ENNReal.ofReal (a + b)) : u = v := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_contra huv
  obtain ⟨r, hr, hshort⟩ := frameExponential_corner_shortening g o e u v hu hv huv
  let t := min r (min a b) / 2
  have hm : 0 < min r (min a b) := lt_min hr (lt_min ha hb)
  have ht : 0 < t := half_pos hm
  have htm : t < min r (min a b) := half_lt_self hm
  have htr : t < r := htm.trans_le (min_le_left _ _)
  have hta : t < a := htm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htb : t < b := htm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let qneg : Directions := ⟨-u, by simpa only [norm_neg] using hu⟩
  let qpos : Directions := ⟨v, hv⟩
  have hleft : metricEDistance g (frameExponential g o e ((-a) • u))
      (frameExponential g o e ((-t) • u)) ≤ ENNReal.ofReal (a - t) := by
    simpa only [qneg, smul_neg, neg_smul, abs_of_nonpos (sub_nonpos.mpr hta.le), neg_sub]
      using frameExponential_ray_distance g o e qneg a t ha ht
  have hright : metricEDistance g (frameExponential g o e (t • v))
      (frameExponential g o e (b • v)) ≤ ENNReal.ofReal (b - t) := by
    simpa only [qpos, abs_of_nonneg (sub_nonneg.mpr htb.le)]
      using frameExponential_ray_distance g o e qpos t b ht hb
  have hmid := hshort t ht htr
  let A := frameExponential g o e ((-a) • u)
  let B := frameExponential g o e (b • v)
  let L := frameExponential g o e ((-t) • u)
  let R := frameExponential g o e (t • v)
  have htri : metricEDistance g A B ≤ metricEDistance g A L +
      (metricEDistance g L R + metricEDistance g R B) :=
    (Manifold.riemannianEDist_triangle (I := I4) (x := A) (y := L) (z := B)).trans
      (add_le_add le_rfl (Manifold.riemannianEDist_triangle (I := I4) (x := L) (y := R) (z := B)))
  have hbound : ENNReal.ofReal (a + b) ≤ ENNReal.ofReal (a - t) +
      (metricEDistance g L R + ENNReal.ofReal (b - t)) := by
    rw [← hmin]
    exact htri.trans (add_le_add hleft (add_le_add le_rfl hright))
  have hs := ENNReal.add_lt_add_left (a := ENNReal.ofReal (a - t)) ENNReal.ofReal_ne_top
    (ENNReal.add_lt_add_right (a := ENNReal.ofReal (b - t)) ENNReal.ofReal_ne_top hmid)
  have heq : ENNReal.ofReal (a - t) + (ENNReal.ofReal (2 * t) + ENNReal.ofReal (b - t)) =
      ENNReal.ofReal (a + b) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * t) (by linarith : 0 ≤ b - t),
      ← ENNReal.ofReal_add (by linarith : 0 ≤ a - t) (by linarith : 0 ≤ 2 * t + (b - t))]
    congr 1
    ring
  rw [heq] at hs
  exact (not_lt_of_ge hbound) hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual normal variations with endpoint curves of zero covariant acceleration. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
theorem normalQuadraticSegment_common_radius (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ContinuousOn N (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    ∃ δ > 0, δ ≤ A.radius ∧ δ ≤ B.radius ∧ ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈
        (chartAt FourSpace c).target := by
  have hx : ContinuousOn (fun t => chartAt FourSpace c (frameGeodesic g 0 e t)) (Icc a b) :=
    ((frameGeodesic_chart_contDiffOn g 0 e c).mono hc).continuousOn
  have hy : ContinuousOn (fun t => WithLp.toLp 2 (normalChartField g c e N t)) (Icc a b) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (normalChartField_continuousOn g c e N (Icc a b) hc hN)
  obtain ⟨r, hr, hinside⟩ := endpointCorrectedPosition_inside_on
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (fun t => WithLp.toLp 2 (normalChartField g c e N t)) A.position B.position hab.le
    hx hy A.position_continuous B.position_continuous A.position_zero B.position_zero
    (chartAt FourSpace c).target (chartAt FourSpace c).open_target
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  refine ⟨min r (min A.radius B.radius), lt_min hr (lt_min A.radius_pos B.radius_pos),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro ε hε t ht
  apply hinside ε ?_ t ht
  constructor <;> linarith [hε.1, hε.2, min_le_left r (min A.radius B.radius)]

theorem normalQuadraticSegmentCurve_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b t : ℝ}
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (ht : frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source) :
    normalSegmentCurve g e c N A.position B.position a b 0 t = frameGeodesic g 0 e t := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
  exact (chartAt FourSpace c).left_inv ht

theorem normalQuadraticSegmentCurve_endpoints (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N : ℝ → Fin 3 → ℝ) {a b ε : ℝ} (hab : a < b)
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : ε ∈ Icc (-A.radius) A.radius) (hB : ε ∈ Icc (-B.radius) B.radius) :
    normalSegmentCurve g e c N A.position B.position a b ε a =
      normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 a e) (N a) ε ∧
    normalSegmentCurve g e c N A.position B.position a b ε b =
      normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 b e) (N b) ε := by
  unfold normalSegmentCurve normalSegmentPosition
  rw [endpointCorrectedPosition_left _ _ _ _ _ _ _ hab.ne,
    endpointCorrectedPosition_right _ _ _ _ _ _ _ hab.ne]
  exact ⟨A.realizes ε hA, B.realizes ε hB⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The corrected normal segment has the actual Riemannian kinetic energy.
Its initial raw jets are the prescribed normal field and its derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def normalSegmentVelocity (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε t : ℝ) : FourSpace :=
  endpointCorrectedVelocity (fun s => chartAt FourSpace c (frameGeodesic g 0 e s))
    (fun s => WithLp.toLp 2 (normalChartField g c e N s))
    (fun s => WithLp.toLp 2 (geodesicChartVelocity g c e s))
    (fun s => WithLp.toLp 2 (normalChartFieldRate g c e N P s)) A B a b ε t

def normalSegmentEnergy (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) (a b ε : ℝ) : ℝ :=
  ∫ t in a..b, chartEnergyDensity g c (normalSegmentPosition g e c N A B a b ε t)
    (WithLp.ofLp (normalSegmentVelocity g e c N P A B a b ε t))

theorem normalSegmentCurve_contMDiffOn (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) {a b ε : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A B a b ε t ∈ (chartAt FourSpace c).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (normalSegmentCurve g e c N A B a b ε) (Icc a b) := by
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  apply endpointCorrected_curve_contMDiffOn c _ _ _ _ A B hab ε
  · intro t ht
    exact geodesicChartPosition_hasDerivAt g c e t (hc t ht)
  · intro t ht
    exact normalChartField_toLp_hasDerivAt g c e N P t (hc t ht) (hN t ht)
  · exact (PiLp.continuous_toLp 2 _).comp_continuousOn
      (geodesicChartVelocity_continuousOn g c e (Icc a b) hc)
  · exact (PiLp.continuous_toLp 2 _).comp_continuousOn
      (normalChartFieldRate_continuousOn g c e N P (Icc a b) hc hNc hP)
  · exact hz

theorem normalSegmentEnergy_eq_actual (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) (A B : ℝ → FourSpace) {a b ε : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t)
    (hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A B a b ε t ∈ (chartAt FourSpace c).target) :
    normalSegmentEnergy g e c N P A B a b ε =
      metricCurveEnergy g (normalSegmentCurve g e c N A B a b ε) a b := by
  symm
  apply endpointCorrected_actual_energy g c _ _ _ _ A B hab ε
  · intro t ht
    exact geodesicChartPosition_hasDerivAt g c e t (hc t ht)
  · intro t ht
    exact normalChartField_toLp_hasDerivAt g c e N P t (hc t ht) (hN t ht)
  · exact hz

theorem normalSegmentEnergy_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t)
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    normalSegmentEnergy g e c N P A.position B.position a b 0 = (b - a) / 2 := by
  have href : EqOn (normalSegmentCurve g e c N A.position B.position a b 0)
      (frameGeodesic g 0 e) (Icc a b) :=
    fun t ht => normalSegmentCurve_zero g e c N A B (hc t ht)
  have hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b 0 t ∈
        (chartAt FourSpace c).target := by
    intro t ht
    unfold normalSegmentPosition
    rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
    exact (chartAt FourSpace c).map_source (hc t ht)
  rw [normalSegmentEnergy_eq_actual g e c N P A.position B.position hab hc hN hz,
    metricCurveEnergy_congr g hab.le href, frameGeodesic_energy g 0 e hab]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Time reversal of the actual complete geodesic, using the oriented
frame rotation by minus the identity in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def reverseDirection : Directions := ⟨-firstDirection.val, by simp [firstDirection.property]⟩

def reverseFrameRotation : OrientedOrthogonalFour := directionOrientedMatrix reverseDirection

theorem reverseFrameRotation_matrix : (orientedToOrthogonal reverseFrameRotation).val = -(1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reverseFrameRotation, orientedToOrthogonal, directionOrientedMatrix,
      directionFrameMatrix, reverseDirection, firstDirection, coordinateVector]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameAntipode (g : SmoothMetric M) (e : FrameBundle g) : FrameBundle g :=
  e.rotate (orientedToOrthogonal reverseFrameRotation)

theorem frameAntipode_chart (g : SmoothMetric M) (c : M) (e : FrameBundle g) :
    frameChartMatrix g c (frameAntipode g e) = -frameChartMatrix g c e := by
  rw [frameAntipode, frameChartMatrix_rotate, reverseFrameRotation_matrix, mul_neg, mul_one]

theorem parallelFrameCurveAt_antipode (g : SmoothMetric M) (γ : ℝ → FrameBundle g)
    (k : Fin 4) (t : ℝ) (h : ParallelFrameCurveAt g γ k (-t)) :
    ParallelFrameCurveAt g (fun s => frameAntipode g (γ (-s))) k t := by
  constructor
  · have hd := h.velocity.scomp t (hasDerivAt_neg t)
    change HasDerivAt (fun s => chartAt FourSpace (γ (-t)).base (γ (-s)).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g (γ (-t)).base
        (frameAntipode g (γ (-t))) r k)) t
    rw [frameAntipode_chart]
    simpa only [Matrix.neg_apply, neg_one_smul, PiLp.neg_apply, Function.comp_apply] using! hd
  · intro i j
    have hd := ((h.parallel i j).comp t (hasDerivAt_neg t)).neg
    change HasDerivAt (fun s => frameChartMatrix g (γ (-t)).base
      (frameAntipode g (γ (-s))) i j)
      (-((∑ r, frameChartMatrix g (γ (-t)).base (frameAntipode g (γ (-t))) r k •
        connectionMatrix g (γ (-t)).base r (chartAt FourSpace (γ (-t)).base (γ (-t)).base)) *
        frameChartMatrix g (γ (-t)).base (frameAntipode g (γ (-t)))) i j) t
    simp only [frameAntipode_chart, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib,
      neg_mul_neg]
    simpa only [Function.comp_apply, Pi.neg_apply, mul_neg_one, neg_neg] using! hd

variable [T3Space M] [CompactSpace M]

theorem parallelFrameFlowMap_antipode (g : SmoothMetric M) (k : Fin 4)
    (t : ℝ) (e : FrameBundle g) :
    frameAntipode g (parallelFrameFlowMap g k (-t) e) =
      parallelFrameFlowMap g k t (frameAntipode g e) := by
  let γ := fun s => frameAntipode g (parallelFrameFlowMap g k (-s) e)
  let η := fun s => parallelFrameFlowMap g k s (frameAntipode g e)
  have hc : Continuous γ := (continuous_frameRotate g).comp
    (((parallelFrameFlowMap_curve_continuous g k e).comp continuous_neg).prodMk continuous_const)
  have hd : Continuous η := parallelFrameFlowMap_curve_continuous g k _
  have hγ (s : ℝ) : ParallelFrameCurveAt g γ k s :=
    parallelFrameCurveAt_antipode g _ k s (parallelFrameFlowMap_primitive g k e (-s))
  have hη (s : ℝ) : ParallelFrameCurveAt g η k s := parallelFrameFlowMap_primitive g k _ s
  have hz : γ 0 = η 0 := by simp only [γ, η, neg_zero, parallelFrameFlowMap_zero]
  exact congrFun (intrinsic_parallelFrame_unique_global g γ η k hc hd hγ hη hz) t

theorem frameExponential_first_ray_neg (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    frameExponential g o e ((-t) • coordinateVector 0) = frameGeodesic g 0 e (-t) := by
  have hp : frameAntipode g e ∈ o.positive := frameRotate_oriented_positive o e he _
  have hL : orthogonalEuclideanIsometry (orientedToOrthogonal reverseFrameRotation).val
      (orientedToOrthogonal reverseFrameRotation).property (t • coordinateVector 0) =
        (-t) • coordinateVector 0 := by
    ext i
    change ((orientedToOrthogonal reverseFrameRotation).val *ᵥ
      WithLp.ofLp (t • coordinateVector 0)) i = _
    rw [reverseFrameRotation_matrix, Matrix.neg_mulVec, Matrix.one_mulVec]
    simp
  rw [← hL, ← frameExponential_rotate]
  change frameExponential g o (frameAntipode g e) (t • coordinateVector 0) = _
  rw [frameExponential_first_ray g o _ hp t ht]
  exact (congrArg FrameBundle.base (parallelFrameFlowMap_antipode g 0 t e)).symm

theorem frameExponential_first_ray_all (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    frameExponential g o e (t • coordinateVector 0) = frameGeodesic g 0 e t := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · exact frameExponential_first_ray g o e he t ht
  · subst t
    simp only [zero_smul, frameExponential_zero, frameGeodesic, parallelFrameFlowMap_zero]
  · simpa only [neg_neg] using frameExponential_first_ray_neg g o e he (-t) (neg_pos.mpr ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual corrected curve at the reference
geodesic, including both ends of each chart segment. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
theorem endpointCorrectedPosition_continuousAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x y A B : ℝ → E)
    (a b ε r : ℝ) (hx : ContinuousAt x r) (hy : ContinuousAt y r)
    (hA : ContinuousAt A ε) (hB : ContinuousAt B ε) :
    ContinuousAt (fun p : ℝ × ℝ => endpointCorrectedPosition x y A B a b p.1 p.2) (ε,r) := by
  have hxp := hx.comp (x := (ε,r)) (f := Prod.snd) continuous_snd.continuousAt
  have hyp := hy.comp (x := (ε,r)) (f := Prod.snd) continuous_snd.continuousAt
  have hAp := hA.comp (x := (ε,r)) (f := Prod.fst) continuous_fst.continuousAt
  have hBp := hB.comp (x := (ε,r)) (f := Prod.fst) continuous_fst.continuousAt
  unfold endpointCorrectedPosition endpointResidual endpointWeightLeft endpointWeightRight
  exact ((hxp.add (continuous_fst.continuousAt.smul hyp)).add
    (((continuousAt_const.sub continuous_snd.continuousAt).div_const (b-a)).smul
      ((hAp.sub continuousAt_const).sub (continuous_fst.continuousAt.smul continuousAt_const)))).add
    (((continuous_snd.continuousAt.sub continuousAt_const).div_const (b-a)).smul
      ((hBp.sub continuousAt_const).sub (continuous_fst.continuousAt.smul continuousAt_const)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalQuadraticSegmentCurve_continuousAt (g : SmoothMetric M)
    (e : FrameBundle g) (c : M) (a : Fin 3 → ℝ) (u v r : ℝ)
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 u e) c a)
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 v e) c a)
    (hr : frameGeodesic g 0 e r ∈ (chartAt FourSpace c).source) :
    ContinuousAt (fun p : ℝ × ℝ =>
      normalSegmentCurve g e c (fun _ => a) A.position B.position u v p.1 p.2) (0,r) := by
  let x := fun s => chartAt FourSpace c (frameGeodesic g 0 e s)
  let y := fun s => WithLp.toLp 2 (normalChartField g c e (fun _ => a) s)
  have hx : ContinuousAt x r := (geodesicChartPosition_hasDerivAt g c e r hr).continuousAt
  have hy : ContinuousAt y r :=
    ((PiLp.continuous_toLp 2 _).continuousAt.comp
      (normalChartField_hasDerivAt g c e (fun _ => a) (fun _ => 0) r hr
        (hasDerivAt_const r a)).continuousAt)
  have hp := endpointCorrectedPosition_continuousAt x y A.position B.position
    u v 0 r hx hy A.position_continuous.continuousAt B.position_continuous.continuousAt
  have hzero : endpointCorrectedPosition x y A.position B.position u v 0 r = x r :=
    endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero
  have hin : endpointCorrectedPosition x y A.position B.position u v 0 r ∈
      (chartAt FourSpace c).target := by
    rw [hzero]
    exact (chartAt FourSpace c).map_source hr
  exact ((chartAt FourSpace c).continuousAt_symm hin).comp
    (x := (0,r))
    (f := fun p : ℝ × ℝ => endpointCorrectedPosition x y A.position B.position u v p.1 p.2) hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual second parameter derivative of the corrected normal-segment energy.
The coordinate jets are supplied by the common intrinsic endpoint curves. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalSegmentEnergy_secondDeriv (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      (∫ t in a..b, chartEnergySecondDensity g c
        (chartAt FourSpace c (frameGeodesic g 0 e t))
        (normalChartField g c e N t) (geodesicChartVelocity g c e t)
        (normalChartFieldRate g c e N P t)
        (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) 0 := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have h := endpointCorrected_energy_secondDerivOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hδ hab.le
    hx hy hv hw A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn
    (fun ε hε => (A.derivative ε (ha ε hε)).1)
    (fun ε hε => (B.derivative ε (hb ε hε)).1)
    (fun ε hε => (A.derivative ε (ha ε hε)).2)
    (fun ε hε => (B.derivative ε (hb ε hε)).2) hz
  have hA0 : A.position 0 = x a := A.position_zero
  have hB0 : B.position 0 = x b := B.position_zero
  have hA1 : A.first 0 = y a := A.first_zero
  have hB1 : B.first 0 = y b := B.first_zero
  have hX (t : ℝ) := endpointCorrectedPosition_zero x y A.position B.position a b t hA0 hB0
  have hY (t : ℝ) := endpointCorrectedParameter_zero y A.first B.first a b t hA1 hB1
  have hV (t : ℝ) := endpointCorrectedVelocity_zero x y v w A.position B.position a b t hA0 hB0
  have hW (t : ℝ) := endpointCorrectedMixed_zero y w A.first B.first a b t hA1 hB1
  simpa only [hX, hY, hV, hW, x, y, v, w, WithLp.ofLp_toLp,
    normalSegmentEnergy, normalSegmentPosition, normalSegmentVelocity] using! h

theorem normalSegmentEnergy_first_differentiable (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (normalSegmentEnergy g e c N P A.position B.position a b) ε := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have hcont := endpointCorrected_energy_continuousOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hx hy hv hw
    A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn hz
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)] with ε hε
  apply HasDerivAt.differentiableAt
  apply intervalIntegral_hasDerivAt_rectangle
    (fun ε t => chartEnergyDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t)))
    (fun ε t => chartEnergyFirstDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b ε t))
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t))
      (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b ε t)))
    hab.le hε hcont.1 hcont.2.1
  intro s hs t ht
  apply chartEnergy_firstJet_hasDerivAt
  · exact hz s ⟨hs.1.le, hs.2.le⟩ t ht
  · simpa only [WithLp.toLp_ofLp] using endpointCorrectedPosition_parameter x y
      A.position B.position A.first B.first a b s t
      (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt s (endpointCorrectedVelocity_parameter x y v w
        A.position B.position A.first B.first a b s t
        (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous joint inverse branch agrees with the original radial
segment close to its nonconjugate endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem joint_exponential_log_radial_eventually (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualFirstConjugateTime g hRic e)
    (U : Set (FrameBundle g × M)) (hU : IsOpen U)
    (heU : (e,frameGeodesic g 0 e t) ∈ U)
    (log : FrameBundle g × M → FourSpace) (hlog : ContinuousOn log U)
    (hlog0 : log (e,frameGeodesic g 0 e t) = t • coordinateVector 0)
    (hreal : ∀ p ∈ U, frameExponential g o p.1 (log p) = p.2) :
    ∀ᶠ s in 𝓝 t, log (e,frameGeodesic g 0 e s) = s • coordinateVector 0 := by
  obtain ⟨V,_,heV,r,hr,hinj⟩ := frameExponential_common_injective_neighborhood g o hRic e he t ht htc
  let f : ℝ → FrameBundle g × M := fun s => (e,frameGeodesic g 0 e s)
  have hf : Continuous f := continuous_const.prodMk (frameGeodesic_continuous g 0 e)
  have hl : ContinuousAt (fun s => log (f s)) t :=
    (hlog.continuousAt (hU.mem_nhds heU)).comp (x := t) (f := f) hf.continuousAt
  have hline : Continuous (fun s : ℝ => s • (coordinateVector 0 : FourSpace)) :=
    continuous_id.smul continuous_const
  have hL : ∀ᶠ s in 𝓝 t, log (f s) ∈ ball (t • coordinateVector 0) r := by
    apply hl.preimage_mem_nhds
    rw [hlog0]
    exact ball_mem_nhds _ hr
  have hR : ∀ᶠ s in 𝓝 t, s • (coordinateVector 0 : FourSpace) ∈ ball (t • coordinateVector 0) r :=
    hline.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
  have hmem : ∀ᶠ s in 𝓝 t, f s ∈ U := hf.continuousAt.preimage_mem_nhds (hU.mem_nhds heU)
  filter_upwards [hL,hR,hmem] with s hs hs' hsU
  apply hinj e heV hs hs'
  rw [hreal _ hsU,frameExponential_first_ray_all g o e he s]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A minimizing radial segment that splits the distance to an exterior
point continues a positive distance along the same complete geodesic. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem frameExponential_shift_first (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (s t : ℝ) :
    frameExponential g o (parallelFrameFlowMap g 0 t e) (s • coordinateVector 0) =
      frameGeodesic g 0 e (s + t) := by
  rw [frameExponential_first_ray_all g o _ (parallelFrameFlowMap_positive g o e he t)]
  exact congrArg FrameBundle.base (parallelFrameFlowMap_add g 0 s t e).symm

theorem frameGeodesic_minimizing_split_extends (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : M) (a : ℝ) (ha : 0 < a)
    (had : a < metricDistance g e.base q)
    (hmin : metricDistance g e.base (frameGeodesic g 0 e a) = a)
    (hsplit : metricDistance g e.base q =
      a + metricDistance g (frameGeodesic g 0 e a) q) :
    ∃ b > (0 : ℝ), a + b < metricDistance g e.base q ∧
      metricDistance g e.base (frameGeodesic g 0 e (a + b)) = a + b ∧
      metricDistance g e.base q =
        (a + b) + metricDistance g (frameGeodesic g 0 e (a + b)) q := by
  let f := parallelFrameFlowMap g 0 a e
  have hf : f ∈ o.positive := parallelFrameFlowMap_positive g o e he a
  obtain ⟨R, hR, himage⟩ := exists_frameExponential_normal_ball_images g o hRic f hf
  let b := min R (metricDistance g e.base q - a) / 2
  have hb : 0 < b := half_pos (lt_min hR (sub_pos.mpr had))
  have hbm : b < min R (metricDistance g e.base q - a) :=
    half_lt_self (lt_min hR (sub_pos.mpr had))
  have hbR : b < R := hbm.trans_le (min_le_left _ _)
  have hbd : a + b < metricDistance g e.base q := by
    have := hbm.trans_le (min_le_right _ _)
    linarith
  have hbf : b ≤ metricDistance g f.base q := by
    change b ≤ metricDistance g (frameGeodesic g 0 e a) q
    linarith
  obtain ⟨z, hzf, hzq⟩ := exists_metricDistance_real_split g f.base q b hb.le hbf
  have hzimage : z ∈ frameExponential g o f '' sphere 0 b := by
    rw [(himage b hb.le hbR).2]
    exact (metricDistance_eq_iff g f.base z hb.le).mp hzf
  obtain ⟨v, hv, hvz⟩ := hzimage
  have hvn : ‖v‖ = b := by simpa only [mem_sphere, dist_zero_right] using hv
  let w := b⁻¹ • v
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb), hvn, inv_mul_cancel₀ hb.ne']
  have hbw : b • w = v := by simp [w, smul_smul, hb.ne']
  have hpz : metricDistance g e.base z = a + b := by
    have ht := metricDistance_triangle g e.base f.base z
    have hu := metricDistance_triangle g e.base z q
    change metricDistance g e.base (frameGeodesic g 0 e a) = a at hmin
    change metricDistance g e.base q = a + metricDistance g f.base q at hsplit
    change metricDistance g e.base z ≤ metricDistance g e.base (frameGeodesic g 0 e a) +
      metricDistance g f.base z at ht
    linarith
  have hback : frameExponential g o f ((-a) • coordinateVector 0) = e.base := by
    rw [frameExponential_shift_first g o e he (-a) a, neg_add_cancel]
    exact congrArg FrameBundle.base (parallelFrameFlowMap_zero g 0 e)
  have hcorner : coordinateVector 0 = w := by
    apply frameExponential_no_minimizing_corner g o f (coordinateVector 0) w
      firstDirection.property hw a b ha hb
    rw [hback, hbw, hvz]
    exact (metricDistance_eq_iff g e.base z (by positivity : 0 ≤ a + b)).mp hpz
  have hz : z = frameGeodesic g 0 e (a + b) := by
    rw [← hvz, ← hbw, ← hcorner, frameExponential_shift_first g o e he b a, add_comm]
  refine ⟨b, hb, hbd, ?_, ?_⟩
  · rwa [← hz]
  · rw [← hz]
    change metricDistance g e.base q = a + metricDistance g f.base q at hsplit
    linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual normal variations with endpoint curves of zero covariant acceleration. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
theorem normalQuadraticSegmentEnergy_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t)
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    normalSegmentEnergy g e c N P A.position B.position a b 0 = (b - a) / 2 := by
  have href : EqOn (normalSegmentCurve g e c N A.position B.position a b 0)
      (frameGeodesic g 0 e) (Icc a b) :=
    fun t ht => normalQuadraticSegmentCurve_zero g e c N A B (hc t ht)
  have hz : ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b 0 t ∈
        (chartAt FourSpace c).target := by
    intro t ht
    unfold normalSegmentPosition
    rw [endpointCorrectedPosition_zero _ _ _ _ _ _ _ A.position_zero B.position_zero]
    exact (chartAt FourSpace c).map_source (hc t ht)
  rw [normalSegmentEnergy_eq_actual g e c N P A.position B.position hab hc hN hz,
    metricCurveEnergy_congr g hab.le href, frameGeodesic_energy g 0 e hab]

theorem normalQuadraticSegmentEnergy_secondDeriv (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      (∫ t in a..b, chartEnergySecondDensity g c
        (chartAt FourSpace c (frameGeodesic g 0 e t))
        (normalChartField g c e N t) (geodesicChartVelocity g c e t)
        (normalChartFieldRate g c e N P t)
        (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) 0 := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have h := endpointCorrected_energy_secondDerivOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hδ hab.le
    hx hy hv hw A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn
    (fun ε hε => (A.derivative ε (ha ε hε)).1)
    (fun ε hε => (B.derivative ε (hb ε hε)).1)
    (fun ε hε => (A.derivative ε (ha ε hε)).2)
    (fun ε hε => (B.derivative ε (hb ε hε)).2) hz
  have hA0 : A.position 0 = x a := A.position_zero
  have hB0 : B.position 0 = x b := B.position_zero
  have hA1 : A.first 0 = y a := A.first_zero
  have hB1 : B.first 0 = y b := B.first_zero
  have hX (t : ℝ) := endpointCorrectedPosition_zero x y A.position B.position a b t hA0 hB0
  have hY (t : ℝ) := endpointCorrectedParameter_zero y A.first B.first a b t hA1 hB1
  have hV (t : ℝ) := endpointCorrectedVelocity_zero x y v w A.position B.position a b t hA0 hB0
  have hW (t : ℝ) := endpointCorrectedMixed_zero y w A.first B.first a b t hA1 hB1
  simpa only [hX, hY, hV, hW, x, y, v, w, WithLp.ofLp_toLp,
    normalSegmentEnergy, normalSegmentPosition, normalSegmentVelocity] using! h

theorem normalQuadraticSegmentEnergy_first_differentiable (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (normalSegmentEnergy g e c N P A.position B.position a b) ε := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have hcont := endpointCorrected_energy_continuousOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hx hy hv hw
    A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn hz
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)] with ε hε
  apply HasDerivAt.differentiableAt
  apply intervalIntegral_hasDerivAt_rectangle
    (fun ε t => chartEnergyDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t)))
    (fun ε t => chartEnergyFirstDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
      (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b ε t))
      (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t))
      (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b ε t)))
    hab.le hε hcont.1 hcont.2.1
  intro s hs t ht
  apply chartEnergy_firstJet_hasDerivAt
  · exact hz s ⟨hs.1.le, hs.2.le⟩ t ht
  · simpa only [WithLp.toLp_ofLp] using endpointCorrectedPosition_parameter x y
      A.position B.position A.first B.first a b s t
      (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt s (endpointCorrectedVelocity_parameter x y v w
        A.position B.position A.first B.first a b s t
        (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second derivative of the actual corrected-segment energy is its
normal Jacobi index plus intrinsic endpoint boundary terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalSegmentSecond_integral (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    (∫ t in a..b, chartEnergySecondDensity g c
      (chartAt FourSpace c (frameGeodesic g 0 e t))
      (normalChartField g c e N t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e N P t)
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
      (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) =
      (∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t)) +
      normalEndpointBoundary g (parallelFrameFlowMap g 0 b e) (N b) -
      normalEndpointBoundary g (parallelFrameFlowMap g 0 a e) (N a) := by
  let U : ℝ → JacobiCoordinateVector := fun t =>
    WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t)
  let Q : ℝ → JacobiCoordinateVector := fun _ =>
    WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0)
  have hU : Continuous U := (PiLp.continuous_ofLp 2 _).comp
    ((continuous_endpointCorrectedSecond A.second B.second a b
      A.second_continuous B.second_continuous).comp (continuous_const.prodMk continuous_id))
  have hQ : Continuous Q := continuous_const
  have hu (t : ℝ) : HasDerivAt U (Q t) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt t (endpointCorrectedSecond_time A.second B.second a b 0 t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hS := continuousOn_chartEnergySecondDensity g c
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (normalChartField g c e N) (geodesicChartVelocity g c e)
    (normalChartFieldRate g c e N P) U Q
    (geodesicChartPosition_continuousOn g c e _ hc)
    (normalChartField_continuousOn g c e N _ hc hNc)
    (geodesicChartVelocity_continuousOn g c e _ hc)
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
    hU.continuousOn hQ.continuousOn
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  have hi := normalChartField_second_integral g hRic c e N P U Q a b
    (by simpa only [uIcc_of_le hab.le, frameGeodesic] using hc)
    (by simpa only [uIcc_of_le hab.le] using hN)
    (by simpa only [uIcc_of_le hab.le] using hP)
    (fun t _ => hu t) (hS.intervalIntegrable_of_Icc hab.le)
  have hleft : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e a))
      (geodesicChartVelocity g c e a) (normalChartField g c e N a) (U a) =
      normalEndpointBoundary g (parallelFrameFlowMap g 0 a e) (N a) := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 a)) = _
    rw [endpointCorrectedSecond_left _ _ _ _ _ hab.ne, A.second_zero]
    exact normalEndpoint_boundary_chart g (parallelFrameFlowMap g 0 a e) c
      (hc a ⟨le_rfl, hab.le⟩) (N a)
  have hright : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e b))
      (geodesicChartVelocity g c e b) (normalChartField g c e N b) (U b) =
      normalEndpointBoundary g (parallelFrameFlowMap g 0 b e) (N b) := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 b)) = _
    rw [endpointCorrectedSecond_right _ _ _ _ _ hab.ne, B.second_zero]
    exact normalEndpoint_boundary_chart g (parallelFrameFlowMap g 0 b e) c
      (hc b ⟨hab.le, le_rfl⟩) (N b)
  simp only [frameGeodesic] at hleft hright
  rw [hleft, hright] at hi
  exact hi

theorem normalSegmentEnergy_index_secondDeriv (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      ((∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t)) +
        normalEndpointBoundary g (parallelFrameFlowMap g 0 b e) (N b) -
        normalEndpointBoundary g (parallelFrameFlowMap g 0 a e) (N a)) 0 := by
  have h := normalSegmentEnergy_secondDeriv g e c N P hab hδ hc hN hP A B hA hB hz
  rw [normalSegmentSecond_integral g hRic e c N P hab hc hN hP A B] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness and the local no-corner argument give a minimizing radial
geodesic to every point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def frameDistanceSplitTimes (g : SmoothMetric M) (e : FrameBundle g) (q : M) : Set ℝ :=
  {t | 0 ≤ t ∧ metricDistance g e.base (frameGeodesic g 0 e t) = t ∧
    metricDistance g e.base q = t + metricDistance g (frameGeodesic g 0 e t) q}

theorem frameDistanceSplitTimes_compact (g : SmoothMetric M) (e : FrameBundle g) (q : M) :
    IsCompact (frameDistanceSplitTimes g e q) := by
  have hfirst : Continuous (fun t => metricDistance g e.base (frameGeodesic g 0 e t)) :=
    (metricDistance_continuous g).comp (continuous_const.prodMk (frameGeodesic_continuous g 0 e))
  have hlast : Continuous (fun t => metricDistance g (frameGeodesic g 0 e t) q) :=
    (metricDistance_continuous g).comp ((frameGeodesic_continuous g 0 e).prodMk continuous_const)
  have hclosed : IsClosed (frameDistanceSplitTimes g e q) :=
    isClosed_Ici.inter ((isClosed_eq hfirst continuous_id).inter
      (isClosed_eq continuous_const (continuous_id.add hlast)))
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro t ht
  exact ⟨ht.1, by linarith [metricDistance_nonneg g (frameGeodesic g 0 e t) q, ht.2.2]⟩

theorem frameGeodesic_reaches_of_positive_split (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : M) (r : ℝ) (hr : 0 < r)
    (hrsplit : r ∈ frameDistanceSplitTimes g e q) :
    frameGeodesic g 0 e (metricDistance g e.base q) = q := by
  obtain ⟨a, ha, hmax⟩ := (frameDistanceSplitTimes_compact g e q).exists_isMaxOn
    ⟨r, hrsplit⟩ continuous_id.continuousOn
  have hapos : 0 < a := hr.trans_le (hmax hrsplit)
  have had : a ≤ metricDistance g e.base q := by
    linarith [metricDistance_nonneg g (frameGeodesic g 0 e a) q, ha.2.2]
  have heq : a = metricDistance g e.base q := by
    apply le_antisymm had
    by_contra hnot
    have hlt : a < metricDistance g e.base q := lt_of_not_ge hnot
    obtain ⟨b, hb, _, hbm, hbs⟩ := frameGeodesic_minimizing_split_extends g o hRic e he q a
      hapos hlt ha.2.1 ha.2.2
    have hbmem : a + b ∈ frameDistanceSplitTimes g e q := ⟨by linarith, hbm, hbs⟩
    have hle : a + b ≤ a := hmax hbmem
    linarith
  have hz : metricDistance g (frameGeodesic g 0 e a) q = 0 := by linarith [ha.2.2]
  rw [← heq]
  exact (metricDistance_eq_zero_iff g _ _).mp hz

theorem frameExponential_global_minimizing (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : M) :
    ∃ v : FourSpace, frameExponential g o e v = q ∧ ‖v‖ = metricDistance g e.base q := by
  by_cases hzero : metricDistance g e.base q = 0
  · refine ⟨0, ?_, by simpa only [norm_zero] using hzero.symm⟩
    rw [frameExponential_zero]
    exact (metricDistance_eq_zero_iff g _ _).mp hzero
  have hd : 0 < metricDistance g e.base q :=
    lt_of_le_of_ne (metricDistance_nonneg g e.base q) (Ne.symm hzero)
  obtain ⟨R, hR, himages⟩ := exists_frameExponential_normal_ball_images g o hRic e he
  let r := min R (metricDistance g e.base q) / 2
  have hr : 0 < r := half_pos (lt_min hR hd)
  have hrm : r < min R (metricDistance g e.base q) := half_lt_self (lt_min hR hd)
  have hrR : r < R := hrm.trans_le (min_le_left _ _)
  have hrd : r < metricDistance g e.base q := hrm.trans_le (min_le_right _ _)
  obtain ⟨z, hz, hsplit⟩ := exists_metricDistance_real_split g e.base q r hr.le hrd.le
  have hzmem : z ∈ frameExponential g o e '' sphere 0 r := by
    rw [(himages r hr.le hrR).2]
    exact (metricDistance_eq_iff g e.base z hr.le).mp hz
  obtain ⟨v, hv, hvz⟩ := hzmem
  have hvn : ‖v‖ = r := by simpa only [mem_sphere, dist_zero_right] using hv
  let w : FourSpace := r⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hvn, inv_mul_cancel₀ hr.ne']
  let Q := directionOrientedMatrix ⟨w, hwn⟩
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (coordinateVector 0) = w :=
    directionRotation_first ⟨w, hwn⟩
  have hexp (s : ℝ) : frameGeodesic g 0 f s = frameExponential g o e (s • w) := by
    rw [← frameExponential_first_ray_all g o f hf s, frameExponential_rotate]
    rw [map_smul, hdir]
  have hstart : frameGeodesic g 0 f r = z := by
    rw [hexp, show r • w = v by simp [w, smul_smul, hr.ne'], hvz]
  have hrmem : r ∈ frameDistanceSplitTimes g f q := by
    change 0 ≤ r ∧ metricDistance g e.base (frameGeodesic g 0 f r) = r ∧
      metricDistance g e.base q = r + metricDistance g (frameGeodesic g 0 f r) q
    rw [hstart]
    exact ⟨hr.le, hz, hsplit⟩
  have hend := frameGeodesic_reaches_of_positive_split g o hRic f hf q r hr hrmem
  refine ⟨metricDistance g e.base q • w, ?_, ?_⟩
  · rw [← hexp]
    exact hend
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (metricDistance_nonneg g e.base q), hwn, mul_one]

theorem frameExponential_surjective (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    Function.Surjective (frameExponential g o e) := fun q =>
  let ⟨v, hv, _⟩ := frameExponential_global_minimizing g o hRic e he q
  ⟨v, hv⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Nonnegativity of the normal index on a finite chart partition of an
actual minimizing geodesic.  The competitor curves and their endpoint jets
are constructed, rather than assumed as a second-variation input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
private theorem normalEndpointCurve_zero (g : SmoothMetric M) (e : FrameBundle g) (ε : ℝ) :
    normalEndpointCurve g e 0 ε = e.base := by
  have hz : (Fin.cons (0 : ℝ) (0 : Fin 3 → ℝ) : Fin 4 → ℝ) = 0 := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [normalEndpointCurve, normalEndpointDirection, hz, Matrix.mulVec_zero,
    WithLp.toLp_zero, endpointChartLine, smul_zero, add_zero]
  exact (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)

theorem finite_geodesic_normal_index_nonneg (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (n : ℕ) (t : ℕ → ℝ) (c : ℕ → M)
    (N P : ℕ → ℝ → Fin 3 → ℝ)
    (ht : ∀ i < n, t i < t (i + 1))
    (hc : ∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)),
      frameGeodesic g 0 e r ∈ (chartAt FourSpace (c i)).source)
    (hN : ∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)), HasDerivAt (N i) (P i r) r)
    (hP : ∀ i < n, ContinuousOn (P i) (Icc (t i) (t (i + 1))))
    (hmatch : ∀ i < n, N i (t (i + 1)) = N (i + 1) (t (i + 1)))
    (hstart : N 0 (t 0) = 0) (hend : N n (t n) = 0)
    (hmin : metricDistance g (frameGeodesic g 0 e (t 0))
      (frameGeodesic g 0 e (t n)) = t n - t 0) :
    0 ≤ ∑ i ∈ Finset.range n, ∫ r in t i..t (i + 1),
      normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e))
        (N i r) (P i r) := by
  classical
  let A := fun i : Fin n => normalEndpointJetData g (parallelFrameFlowMap g 0 (t i.val) e)
    (c i.val) (hc i.val i.isLt (t i.val) ⟨le_rfl, (ht i.val i.isLt).le⟩) (N i.val (t i.val))
  let B := fun i : Fin n => normalEndpointJetData g (parallelFrameFlowMap g 0 (t (i.val + 1)) e)
    (c i.val) (hc i.val i.isLt (t (i.val + 1)) ⟨(ht i.val i.isLt).le, le_rfl⟩)
      (N i.val (t (i.val + 1)))
  have hNc (i : Fin n) : ContinuousOn (N i.val) (Icc (t i.val) (t (i.val + 1))) :=
    fun r hr => (hN i.val i.isLt r hr).continuousAt.continuousWithinAt
  choose δ hδ hδA hδB hinside using fun i : Fin n => normalSegment_common_radius g e (c i.val)
    (N i.val) (ht i.val i.isLt) (hc i.val i.isLt) (hNc i) (A i) (B i)
  let E : ℕ → ℝ → ℝ := fun i ε => if hi : i < n then
    normalSegmentEnergy g e (c i) (N i) (P i) (A ⟨i, hi⟩).position (B ⟨i, hi⟩).position
      (t i) (t (i + 1)) ε else 0
  let γ : ℕ → ℝ → ℝ → M := fun i ε => if hi : i < n then
    normalSegmentCurve g e (c i) (N i) (A ⟨i, hi⟩).position (B ⟨i, hi⟩).position
      (t i) (t (i + 1)) ε else frameGeodesic g 0 e
  let p : ℝ → ℕ → M := fun ε i =>
    normalEndpointCurve g (parallelFrameFlowMap g 0 (t i) e) (N i (t i)) ε
  let I : ℕ → ℝ := fun i => ∫ r in t i..t (i + 1),
    normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (N i r) (P i r)
  let L : ℕ → ℝ := fun i => normalEndpointBoundary g (parallelFrameFlowMap g 0 (t i) e) (N i (t i))
  let R : ℕ → ℝ := fun i => normalEndpointBoundary g (parallelFrameFlowMap g 0 (t (i + 1)) e)
    (N i (t (i + 1)))
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, ε ∈ Icc (-δ i) (δ i) := by
    apply eventually_all.mpr
    intro i
    exact Icc_mem_nhds (neg_neg_of_pos (hδ i)) (hδ i)
  have hfd : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) ε := by
    have hf : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, DifferentiableAt ℝ (E i.val) ε := by
      apply eventually_all.mpr
      intro i
      simpa only [E, dite_eq_left i.isLt] using
        normalSegmentEnergy_first_differentiable g e (c i.val) (N i.val) (P i.val)
          (ht i.val i.isLt) (hδ i) (hc i.val i.isLt) (hN i.val i.isLt) (hP i.val i.isLt)
          (A i) (B i) (hδA i) (hδB i) (hinside i)
    filter_upwards [hf] with ε hε i hi
    exact hε ⟨i, hi⟩
  have hzero : (∑ i ∈ Finset.range n, E i 0) = (t n - t 0) / 2 := by
    calc
      _ = ∑ i ∈ Finset.range n, (t (i + 1) - t i) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [E, dite_eq_left hi'] using
          normalSegmentEnergy_zero g e (c i) (N i) (P i) (ht i hi') (hc i hi')
            (hN i hi') (A ⟨i, hi'⟩) (B ⟨i, hi'⟩)
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub]
  have hlocal : IsLocalMin (fun ε => ∑ i ∈ Finset.range n, E i ε) 0 := by
    filter_upwards [hnear] with ε hε
    have hregion (i : ℕ) (hi : i < n) :
        ε ∈ Icc (-(A ⟨i, hi⟩).radius) (A ⟨i, hi⟩).radius ∧
        ε ∈ Icc (-(B ⟨i, hi⟩).radius) (B ⟨i, hi⟩).radius := by
      have h := hε ⟨i, hi⟩
      have hA := hδA ⟨i, hi⟩
      have hB := hδB ⟨i, hi⟩
      constructor <;> constructor <;> linarith [h.1, h.2]
    have hγ (i : ℕ) (hi : i < n) :
        ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i ε) (Icc (t i) (t (i + 1))) := by
      simpa only [γ, dite_eq_left hi] using normalSegmentCurve_contMDiffOn g e (c i)
        (N i) (P i) (A ⟨i, hi⟩).position (B ⟨i, hi⟩).position (ht i hi) (hc i hi)
        (hN i hi) (hP i hi) (hinside ⟨i, hi⟩ ε (hε ⟨i, hi⟩))
    have hends (i : ℕ) (hi : i < n) :
        γ i ε (t i) = p ε i ∧ γ i ε (t (i + 1)) = p ε (i + 1) := by
      have h := normalSegmentCurve_endpoints g e (c i) (N i) (ht i hi)
        (A ⟨i, hi⟩) (B ⟨i, hi⟩) (hregion i hi).1 (hregion i hi).2
      simpa only [γ, dite_eq_left hi, p, hmatch i hi] using h
    have hp0 : p ε 0 = frameGeodesic g 0 e (t 0) := by
      simpa only [p, hstart, frameGeodesic] using normalEndpointCurve_zero g (parallelFrameFlowMap g 0 (t 0) e) ε
    have hpn : p ε n = frameGeodesic g 0 e (t n) := by
      simpa only [p, hend, frameGeodesic] using normalEndpointCurve_zero g (parallelFrameFlowMap g 0 (t n) e) ε
    have hb := finite_piece_metric_energy_lower g n (p ε) t (fun i => γ i ε) ht hγ
      (fun i hi => (hends i hi).1) (fun i hi => (hends i hi).2)
    have heq : (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) =
        ∑ i ∈ Finset.range n, E i ε := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simpa only [γ, E, dite_eq_left hi'] using
        (normalSegmentEnergy_eq_actual g e (c i) (N i) (P i) (A ⟨i, hi'⟩).position
          (B ⟨i, hi'⟩).position (ht i hi') (hc i hi') (hN i hi')
          (hinside ⟨i, hi'⟩ ε (hε ⟨i, hi'⟩))).symm
    rw [hp0, hpn, hmin, heq] at hb
    rw [hzero]
    linarith
  apply finite_piece_index_nonneg n E I L R hlocal hfd
  · intro i hi
    simpa only [E, dite_eq_left hi, I, L, R] using
      normalSegmentEnergy_index_secondDeriv g hRic e (c i) (N i) (P i) (ht i hi) (hδ ⟨i, hi⟩)
        (hc i hi) (hN i hi) (hP i hi) (A ⟨i, hi⟩) (B ⟨i, hi⟩)
        (hδA ⟨i, hi⟩) (hδB ⟨i, hi⟩) (hinside ⟨i, hi⟩)
  · intro i hi
    exact congrArg (normalEndpointBoundary g (parallelFrameFlowMap g 0 (t (i + 1)) e)) (hmatch i hi)
  · simpa only [L, hstart] using normalEndpointBoundary_zero g (parallelFrameFlowMap g 0 (t 0) e)
  · simpa only [L, hend] using normalEndpointBoundary_zero g (parallelFrameFlowMap g 0 (t n) e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first energy density of a normal variation vanishes in the
actual Levi-Civita connection, including nonconstant normal components. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartEnergyFirstDensity_covariant (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (y v w : JacobiCoordinateVector) :
    chartEnergyFirstDensity g c z y v w =
      jacobiMetricPair (metricInChart g c z) v
        (w + jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ y) := by
  have hG : (metricInChart g c z).IsSymm := by
    ext i j
    exact metricInChart_comm g c z j i
  rw [chartEnergyFirstDensity,jacobiMetricFirstDirectional_eq g c z hz,
    jacobiMetricRate_pair,jacobiMetricPair_symm hG _ v,
    actual_jacobiConnection_comm g c z y v,jacobiMetricPair_add_right]
  ring

theorem frame_normal_first_density_zero (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (a b : Fin 3 → ℝ) :
    chartEnergyFirstDensity g c (chartAt FourSpace c e.base)
      (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
      (fun i => frameChartMatrix g c e i 0)
      (frameChartMatrix g c e *ᵥ Fin.cons 0 b -
        jacobiConnection (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
          (fun i => frameChartMatrix g c e i 0) *ᵥ
            (frameChartMatrix g c e *ᵥ Fin.cons 0 a)) = 0 := by
  rw [chartEnergyFirstDensity_covariant g c _ ((chartAt FourSpace c).map_source he),sub_add_cancel]
  have hv : (fun i => frameChartMatrix g c e i 0) =
      frameChartMatrix g c e *ᵥ Pi.single 0 (1 : ℝ) := by
    ext i
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [hv,jacobiMetricPair_frame _ _ (frameChartMatrix_normalizes g c e he)]
  simp [dotProduct,Pi.single_apply]

variable [T3Space M] [CompactSpace M]

theorem normalChartField_first_density_zero (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (N P : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source) :
    chartEnergyFirstDensity g c (chartAt FourSpace c (frameGeodesic g 0 e t))
      (normalChartField g c e N t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e N P t) = 0 := by
  rw [normalChartFieldRate_eq]
  exact frame_normal_first_density_zero g c (parallelFrameFlowMap g 0 t e) hc (N t) (P t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The corrected normal variation has exactly the index as its second
energy derivative: both actual endpoint acceleration terms vanish. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalQuadraticSegmentSecond_integral (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    (∫ t in a..b, chartEnergySecondDensity g c
      (chartAt FourSpace c (frameGeodesic g 0 e t))
      (normalChartField g c e N t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e N P t)
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
      (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) =
      (∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t)) := by
  let U : ℝ → JacobiCoordinateVector := fun t =>
    WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t)
  let Q : ℝ → JacobiCoordinateVector := fun _ =>
    WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0)
  have hU : Continuous U := (PiLp.continuous_ofLp 2 _).comp
    ((continuous_endpointCorrectedSecond A.second B.second a b
      A.second_continuous B.second_continuous).comp (continuous_const.prodMk continuous_id))
  have hQ : Continuous Q := continuous_const
  have hu (t : ℝ) : HasDerivAt U (Q t) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt t (endpointCorrectedSecond_time A.second B.second a b 0 t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hS := continuousOn_chartEnergySecondDensity g c
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (normalChartField g c e N) (geodesicChartVelocity g c e)
    (normalChartFieldRate g c e N P) U Q
    (geodesicChartPosition_continuousOn g c e _ hc)
    (normalChartField_continuousOn g c e N _ hc hNc)
    (geodesicChartVelocity_continuousOn g c e _ hc)
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
    hU.continuousOn hQ.continuousOn
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  have hi := normalChartField_second_integral g hRic c e N P U Q a b
    (by simpa only [uIcc_of_le hab.le, frameGeodesic] using hc)
    (by simpa only [uIcc_of_le hab.le] using hN)
    (by simpa only [uIcc_of_le hab.le] using hP)
    (fun t _ => hu t) (hS.intervalIntegrable_of_Icc hab.le)
  have hleft : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e a))
      (geodesicChartVelocity g c e a) (normalChartField g c e N a) (U a) = 0 := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 a)) = _
    rw [endpointCorrectedSecond_left _ _ _ _ _ hab.ne, A.second_zero,WithLp.ofLp_toLp]
    exact normalQuadratic_boundary_chart_zero g (parallelFrameFlowMap g 0 a e) c
      (hc a ⟨le_rfl, hab.le⟩) (N a)
  have hright : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e b))
      (geodesicChartVelocity g c e b) (normalChartField g c e N b) (U b) = 0 := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 b)) = _
    rw [endpointCorrectedSecond_right _ _ _ _ _ hab.ne, B.second_zero,WithLp.ofLp_toLp]
    exact normalQuadratic_boundary_chart_zero g (parallelFrameFlowMap g 0 b e) c
      (hc b ⟨hab.le, le_rfl⟩) (N b)
  simp only [frameGeodesic] at hleft hright
  rw [hleft, hright,add_zero,sub_zero] at hi
  exact hi

theorem normalQuadraticSegmentEnergy_index_secondDeriv (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      ((∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t))) 0 := by
  have h := normalQuadraticSegmentEnergy_secondDeriv g e c N P hab hδ hc hN hP A B hA hB hz
  rw [normalQuadraticSegmentSecond_integral g hRic e c N P hab hc hN hP A B] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact set of minimizing tangent vectors and its polar
cut-time description. Its exponential image is the whole manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def actualMinimizingTangentDomain (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Set FourSpace :=
  {v | metricDistance g e.base (frameExponential g o e v) = ‖v‖}

theorem actualMinimizingTangentDomain_closed (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : IsClosed (actualMinimizingTangentDomain g o e) :=
  isClosed_eq ((metricDistance_continuous g).comp
    (continuous_const.prodMk (frameExponential_continuous g o e))) continuous_norm

theorem actualMinimizingTangentDomain_compact (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : IsCompact (actualMinimizingTangentDomain g o e) := by
  obtain ⟨D, hD, hbound⟩ := metricEDistance_uniform_bound g e.base
  apply (isCompact_closedBall (0 : FourSpace) D).of_isClosed_subset
    (actualMinimizingTangentDomain_closed g o e)
  intro v hv
  have heq := (metricDistance_eq_iff g e.base (frameExponential g o e v) (norm_nonneg v)).mp hv
  have hle : ‖v‖ ≤ D := (ENNReal.ofReal_le_ofReal_iff hD).mp (heq ▸ hbound _)
  simpa only [mem_closedBall, dist_zero_right] using hle

theorem actualMinimizingTangentDomain_image (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    frameExponential g o e '' actualMinimizingTangentDomain g o e = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨v, hv, hn⟩ := frameExponential_global_minimizing g o hRic e he q
  exact ⟨v, by change metricDistance g e.base (frameExponential g o e v) = ‖v‖; rw [hv, hn], hv⟩

omit [PreconnectedSpace M] in
theorem frameExponential_direction_ray (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (r : ℝ) :
    frameExponential g o e (r • q.val) =
      frameGeodesic g 0 (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) r := by
  have hdir := directionRotation_first q
  have hp := frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  rw [← frameExponential_first_ray_all g o _ hp r, frameExponential_rotate, map_smul, hdir]

theorem actualMinimizingTangentDomain_ray_iff (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (r : ℝ) (hr : 0 ≤ r) :
    r • q.val ∈ actualMinimizingTangentDomain g o e ↔
      r ≤ actualCutTime g (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) := by
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  have hnorm : ‖r • q.val‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, q.property, mul_one]
  change metricDistance g e.base (frameExponential g o e (r • q.val)) = ‖r • q.val‖ ↔ _
  rw [hnorm, metricDistance_eq_iff g e.base _ hr, frameExponential_direction_ray g o e he q r]
  have htime : (r ∈ frameMinimizingTimes g f) ↔ r ≤ actualCutTime g f := by
    rw [frameMinimizingTimes_eq_Icc]
    exact and_iff_right hr
  exact (and_iff_right hr).symm.trans htime

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual quadratic normal variation has zero first energy derivative. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalQuadraticSegmentEnergy_first_zero (g : SmoothMetric M) (e : FrameBundle g) (c : M)
    (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalQuadraticJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalQuadraticJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (normalSegmentEnergy g e c N P A.position B.position a b) 0 0 := by
  let x := fun t => chartAt FourSpace c (frameGeodesic g 0 e t)
  let y := fun t => WithLp.toLp 2 (normalChartField g c e N t)
  let v := fun t => WithLp.toLp 2 (geodesicChartVelocity g c e t)
  let w := fun t => WithLp.toLp 2 (normalChartFieldRate g c e N P t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hx : ContinuousOn x (Icc a b) := geodesicChartPosition_continuousOn g c e _ hc
  have hy : ContinuousOn y (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartField_continuousOn g c e N _ hc hNc)
  have hv : ContinuousOn v (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (geodesicChartVelocity_continuousOn g c e _ hc)
  have hw : ContinuousOn w (Icc a b) := (PiLp.continuous_toLp 2 _).comp_continuousOn
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
  have hcont := endpointCorrected_energy_continuousOnSegment g c x y v w
    A.position B.position A.first B.first A.second B.second hx hy hv hw
    A.position_continuous.continuousOn B.position_continuous.continuousOn
    A.first_continuous.continuousOn B.first_continuous.continuousOn
    A.second_continuous.continuousOn B.second_continuous.continuousOn hz
  have ha (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-A.radius) A.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hb (ε : ℝ) (hε : ε ∈ Ioo (-δ) δ) : ε ∈ Ioo (-B.radius) B.radius := by
    constructor <;> linarith [hε.1, hε.2]
  have hε : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith,hδ⟩
  have hd : HasDerivAt (normalSegmentEnergy g e c N P A.position B.position a b)
      (∫ t in a..b, chartEnergyFirstDensity g c
        (endpointCorrectedPosition x y A.position B.position a b 0 t)
        (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b 0 t))
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b 0 t))) 0 := by
    apply intervalIntegral_hasDerivAt_rectangle
      (fun ε t => chartEnergyDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t)))
      (fun ε t => chartEnergyFirstDensity g c (endpointCorrectedPosition x y A.position B.position a b ε t)
        (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b ε t))
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b ε t))
        (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b ε t)))
      hab.le hε hcont.1 hcont.2.1
    intro s hs t ht
    apply chartEnergy_firstJet_hasDerivAt
    · exact hz s ⟨hs.1.le, hs.2.le⟩ t ht
    · simpa only [WithLp.toLp_ofLp] using endpointCorrectedPosition_parameter x y
        A.position B.position A.first B.first a b s t
        (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1
    · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
        |>.comp_hasDerivAt s (endpointCorrectedVelocity_parameter x y v w
          A.position B.position A.first B.first a b s t
          (A.derivative s (ha s hs)).1 (B.derivative s (hb s hs)).1)
  have hA0 : A.position 0 = x a := A.position_zero
  have hB0 : B.position 0 = x b := B.position_zero
  have hA1 : A.first 0 = y a := A.first_zero
  have hB1 : B.first 0 = y b := B.first_zero
  have hX (t : ℝ) := endpointCorrectedPosition_zero x y A.position B.position a b t hA0 hB0
  have hY (t : ℝ) := endpointCorrectedParameter_zero y A.first B.first a b t hA1 hB1
  have hV (t : ℝ) := endpointCorrectedVelocity_zero x y v w A.position B.position a b t hA0 hB0
  have hW (t : ℝ) := endpointCorrectedMixed_zero y w A.first B.first a b t hA1 hB1
  have heq : (∫ t in a..b, chartEnergyFirstDensity g c
        (endpointCorrectedPosition x y A.position B.position a b 0 t)
        (WithLp.ofLp (endpointCorrectedParameter y A.first B.first a b 0 t))
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A.position B.position a b 0 t))
        (WithLp.ofLp (endpointCorrectedMixed y w A.first B.first a b 0 t))) = 0 := by
    calc
      _ = ∫ t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab.le] at ht
        simpa only [hX,hY,hV,hW,x,y,v,w,WithLp.ofLp_toLp] using
          normalChartField_first_density_zero g c e N P t (hc t ht)
      _ = 0 := intervalIntegral.integral_zero
  rwa [heq] at hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kernel of the actual smooth scalar Laplacian.  The proof uses
the actual parallel-flow Green formula, full support of base volume, and
constancy along the complete geodesics.  No elliptic kernel theorem is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

private theorem scalar_tensor_square (T : CovariantCoordinates 1) :
    frameTensorSquareNorm T = ∑ i : Fin 4, T ![i] ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_unique]
  have h (u : Fin 0 → Fin 4) : Fin.cons i u = ![i] := by
    funext j
    fin_cases j
    rfl
  rw [h, pow_two]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The squared norm of the scalar differential on the base. -/
def scalarDirichletDensity (g : SmoothMetric M) (a : M → ℝ) (c : M) : ℝ :=
  frameTensorSquareNorm (frameTensor (canonicalFrame g c).matrix
    (covariantDerivative g c (scalarCoordinates a c) (chartAt FourSpace c c)))

theorem scalarDirichletDensity_eq_frame (g : SmoothMetric M) (a : M → ℝ)
    (e : FrameBundle g) :
    scalarDirichletDensity g a e.base = ∑ i, scalarGradient g a e i ^ 2 := by
  unfold scalarDirichletDensity
  rw [frameTensor_norm_same_base (canonicalFrame g e.base) e.frame,
    scalar_tensor_square]
  rfl

theorem scalarDirichletDensity_nonneg (g : SmoothMetric M) (a : M → ℝ) (c : M) :
    0 ≤ scalarDirichletDensity g a c := by
  rw [scalarDirichletDensity_eq_frame g a (⟨c, canonicalFrame g c⟩ : FrameBundle g)]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

variable [T3Space M] [CompactSpace M]

theorem scalarDirichletDensity_continuous (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) : Continuous (scalarDirichletDensity g a) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  change Continuous (fun e : FrameBundle g => scalarDirichletDensity g a e.base)
  simp_rw [scalarDirichletDensity_eq_frame]
  exact continuous_finsetSum _ (fun i _ => (actual_scalarGradient_continuous g ha i).pow 2)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem scalarGradient_eq_zero_of_laplacian_eq_zero (g : SmoothMetric M)
    (o : FrameOrientation g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (d : MetricGreenData g (canonicalFrameMeasure g o))
    (s : ScalarCovariantData d a)
    (hLap : ∀ e : FrameBundle g, scalarLaplacian g a e = 0) :
    ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0 := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let := normalizedVolume_isOpenPosMeasure g
  have hE := scalarDirichletDensity_continuous g ha
  have hzero : (∫ e, scalarDirichletDensity g a e.base
      ∂canonicalFrameMeasure g o) = 0 := by
    have h := s.scalar_pairing_green s
    simp only [hLap, mul_zero, integral_zero, neg_zero] at h
    simpa only [scalarDirichletDensity_eq_frame, pow_two] using h
  have hbase : (∫ c, scalarDirichletDensity g a c ∂normalizedVolume g) = 0 := by
    rw [← (canonicalFrameMeasure_base g o).map_eq,
      integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable
        hE.aestronglyMeasurable]
    exact hzero
  have hInt : Integrable (scalarDirichletDensity g a) (normalizedVolume g) :=
    hE.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : scalarDirichletDensity g a =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg (scalarDirichletDensity_nonneg g a) hInt).mp hbase
  have hpoint : scalarDirichletDensity g a = 0 :=
    Measure.eq_of_ae_eq hae hE continuous_const
  intro e i
  have he : (∑ j, scalarGradient g a e j ^ 2) = 0 := by
    rw [← scalarDirichletDensity_eq_frame, hpoint]
    rfl
  have hle : scalarGradient g a e i ^ 2 ≤ ∑ j, scalarGradient g a e j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hs : scalarGradient g a e i ^ 2 = 0 := le_antisymm (he ▸ hle) (sq_nonneg _)
  exact sq_eq_zero_iff.mp hs

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalar_eq_along_parallelFlow_of_gradient_eq_zero (g : SmoothMetric M)
    {a : M → ℝ} (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hgrad : ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    a (parallelFrameFlowMap g i t e).base = a e.base := by
  have hd (r : ℝ) : HasDerivAt (fun s => a (parallelFrameFlowMap g i s e).base) 0 r := by
    simpa only [hgrad] using actual_scalarValue_parallel_derivative g ha
      (fun s => parallelFrameFlowMap g i s e) r i
      (parallelFrameFlowMap_curve_continuous g i e).continuousAt
      (parallelFrameFlowMap_primitive g i e r)
  have h := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [parallelFrameFlowMap_zero] using h

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalar_eq_on_exponential_of_gradient_eq_zero (g : SmoothMetric M)
    (o : FrameOrientation g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hgrad : ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) :
    a (frameExponential g o e v) = a e.base := by
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero]
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : FourSpace := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  let Q := directionOrientedMatrix ⟨w, hwn⟩
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (coordinateVector 0) = w :=
    directionRotation_first ⟨w, hwn⟩
  have hexp : frameExponential g o e v = (parallelFrameFlowMap g 0 ‖v‖ f).base := by
    rw [← frameExponential_first_ray g o f hf ‖v‖ hr,
      frameExponential_rotate, map_smul, hdir]
    congr 1
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hexp]
  exact scalar_eq_along_parallelFlow_of_gradient_eq_zero g ha hgrad f 0 ‖v‖

variable [PreconnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Vanishing actual scalar differential implies constancy on the connected
compact manifold. -/
theorem scalar_constants_of_gradient_eq_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hgrad : ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0) :
    ∃ c : ℝ, ∀ x, a x = c := by
  let x : M := Classical.arbitrary M
  let e : FrameBundle g := ⟨x, o.frame x⟩
  have he : e ∈ o.positive := o.frame_positive x
  refine ⟨a x, fun y => ?_⟩
  obtain ⟨v, hv⟩ := frameExponential_surjective g o hRic e he y
  rw [← hv]
  exact scalar_eq_on_exponential_of_gradient_eq_zero g o ha hgrad e he v

/-- A smooth harmonic scalar is constant for the actual normalized metric.
The Ricci normalization supplies the invariant flow data. -/
theorem scalarLaplacian_kernel_constants (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hLap : ∀ e : FrameBundle g, scalarLaplacian g a e = 0) :
    ∃ c : ℝ, ∀ x, a x = c := by
  let d := canonicalParallelMetricData g o hRic
  obtain ⟨s⟩ := d.scalarCalculus.toPetersenInput a ha
  have hgrad := scalarGradient_eq_zero_of_laplacian_eq_zero g o ha
    d.toMetricGreenData s hLap
  exact scalar_constants_of_gradient_eq_zero g o hRic ha hgrad

theorem scalarLaplacian_kernel_meanZero (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hLap : ∀ e : FrameBundle g, scalarLaplacian g a e = 0)
    (hmean : (∫ e, a e.base ∂canonicalFrameMeasure g o) = 0) :
    ∀ x, a x = 0 := by
  obtain ⟨c, hc⟩ := scalarLaplacian_kernel_constants g o hRic ha hLap
  have hc0 : c = 0 := by
    simpa [hc] using hmean
  intro x
  rw [hc, hc0]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual index inequality for a continuous normal field with a single
corner.  Each of its two C1 branches is subdivided into genuine chart pieces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem two_piece_geodesic_index_nonneg (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (NL NR PL PR : ℝ → Fin 3 → ℝ)
    (hNL : ∀ r, HasDerivAt NL (PL r) r) (hNR : ∀ r, HasDerivAt NR (PR r) r)
    (hPL : Continuous PL) (hPR : Continuous PR)
    (hjoin : NL c = NR c) (hstart : NL a = 0) (hend : NR b = 0)
    (hmin : metricDistance g (frameGeodesic g 0 e a) (frameGeodesic g 0 e b) = b - a) :
    0 ≤ (∫ r in a..c, normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NL r) (PL r)) +
      ∫ r in c..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NR r) (PR r) := by
  classical
  obtain ⟨n, hn, C, hC⟩ := exists_finite_curve_chart_partition (frameGeodesic g 0 e)
    (frameGeodesic_continuous g 0 e) a c hac
  obtain ⟨m, hm, D, hD⟩ := exists_finite_curve_chart_partition (frameGeodesic g 0 e)
    (frameGeodesic_continuous g 0 e) c b hcb
  let T := joinedPartitionTime a c b n m
  let charts := fun i => if i < n then C i else D (i - n)
  let N := fun i => if i < n then NL else NR
  let P := fun i => if i < n then PL else PR
  have hT0 : T 0 = a := joinedPartitionTime_zero a c b n m
  have hTn : T n = c := by
    change joinedPartitionTime a c b n m n = c
    rw [joinedPartitionTime_left _ _ _ _ _ _ le_rfl, affinePartitionTime_last _ _ _ hn]
  have hTend : T (n + m) = b := joinedPartitionTime_last a c b n m hn hm
  have hcharts := joinedPartition_chart_cover (frameGeodesic g 0 e) a c b n m hn C D hC hD
  have hindex : 0 ≤ ∑ i ∈ Finset.range (n + m), ∫ r in T i..T (i + 1),
      normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e))
        (N i r) (P i r) := by
    apply finite_geodesic_normal_index_nonneg g hRic e (n + m) T charts N P
    · intro i _
      exact joinedPartitionTime_step_lt a c b n m i hac hcb hn hm
    · exact hcharts
    · intro i _ r _
      dsimp only [N, P]
      split_ifs <;> first | exact hNL r | exact hNR r
    · intro i _
      dsimp only [P]
      split_ifs <;> first | exact hPL.continuousOn | exact hPR.continuousOn
    · intro i _
      by_cases hi : i < n
      · by_cases hnext : i + 1 < n
        · simp only [N, ite_eq_left hi, ite_eq_left hnext]
        · have hi' : i + 1 = n := by omega
          simp only [N, ite_eq_left hi, ite_eq_right hnext]
          rw [hi', hTn]
          exact hjoin
      · have hnext : ¬ i + 1 < n := by omega
        simp only [N, ite_eq_right hi, ite_eq_right hnext]
    · simpa only [N, ite_eq_left hn, hT0] using hstart
    · have hnot : ¬ n + m < n := by omega
      simpa only [N, ite_eq_right hnot, hTend] using hend
    · simpa only [hT0, hTend] using hmin
  let F := fun r => normalIndexDensity
    (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NL r) (PL r)
  let G := fun r => normalIndexDensity
    (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NR r) (PR r)
  have hR : Continuous (fun r => 1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) :=
    actualJacobiCurvature_continuous g hRic e
  have hF : Continuous F := continuous_normalIndexDensity hR
    (continuous_iff_continuousAt.mpr fun r => (hNL r).continuousAt) hPL
  have hG : Continuous G := continuous_normalIndexDensity hR
    (continuous_iff_continuousAt.mpr fun r => (hNR r).continuousAt) hPR
  have heq : (∑ i ∈ Finset.range (n + m), ∫ r in T i..T (i + 1),
      normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e))
        (N i r) (P i r)) =
      ∑ i ∈ Finset.range (n + m), ∫ r in T i..T (i + 1), if i < n then F r else G r := by
    apply Finset.sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [N, P, F, G]
    split_ifs <;> rfl
  rw [heq, joinedPartition_sum_integral a c b n m hn hm F G hF hG] at hindex
  exact hindex

end
end PositiveEinsteinFour.Geometry
end


section

/-! Before its cut time an actual radial geodesic is the unique minimizing
radial segment to its endpoint. This follows from the no-corner theorem. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem positive_frames_relative_rotation (g : SmoothMetric M) (o : FrameOrientation g)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base) :
    ∃ Q : OrientedOrthogonalFour, e.rotate (orientedToOrthogonal Q) = f := by
  cases e with
  | mk x E =>
    cases f with
    | mk y F =>
      change x = y at hbase
      subst y
      have hsign := (o.compatible x E F he).mp hf
      exact ⟨orientedFrameChange E F hsign, orientedFrameMap_change E F hsign⟩

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem frameGeodesic_minimizing_initial_unique (g : SmoothMetric M)
    (o : FrameOrientation g) (e f : FrameBundle g)
    (he : e ∈ o.positive) (hf : f ∈ o.positive) (hbase : e.base = f.base)
    (t : ℝ) (ht : 0 < t) (htc : t < actualCutTime g e)
    (hend : frameGeodesic g 0 e t = frameGeodesic g 0 f t) :
    unitTangentOfFrame e = unitTangentOfFrame f := by
  let E := parallelFrameFlowMap g 0 t e
  let F := parallelFrameFlowMap g 0 t f
  have hE : E ∈ o.positive := parallelFrameFlowMap_positive g o e he t
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf t
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o E F hE hF hend
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  let u : FourSpace := L (coordinateVector 0)
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖(coordinateVector 0 : FourSpace)‖ from L.norm_map _]
    exact firstDirection.property
  let s := (actualCutTime g e - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hts : t + s ≤ actualCutTime g e := by dsimp [s]; linarith
  have hleft : frameExponential g o E ((-t) • u) = f.base := by
    have hrot := frameExponential_rotate g o E Q ((-t) • coordinateVector 0)
    rw [hQ, map_smul] at hrot
    rw [← hrot, frameExponential_shift_first g o f hf (-t) t, neg_add_cancel]
    simp only [frameGeodesic, parallelFrameFlowMap_zero]
  have hright : frameExponential g o E (s • coordinateVector 0) =
      frameGeodesic g 0 e (t + s) := by
    rw [frameExponential_shift_first g o e he s t, add_comm]
  have hmin : metricEDistance g (frameExponential g o E ((-t) • u))
      (frameExponential g o E (s • coordinateVector 0)) = ENNReal.ofReal (t + s) := by
    rw [hleft, hright, ← hbase]
    exact (show t + s ∈ frameMinimizingTimes g e from by
      rw [frameMinimizingTimes_eq_Icc]; exact ⟨(add_pos ht hs).le,hts⟩).2
  have hueq : u = coordinateVector 0 := frameExponential_no_minimizing_corner g o E
    u (coordinateVector 0) hu firstDirection.property t s ht hs hmin
  have hstate : unitTangentOfFrame E = unitTangentOfFrame F := by
    rw [← hQ]
    apply unitTangent_ext (u := unitTangentOfFrame E)
      (v := unitTangentOfFrame (E.rotate (orientedToOrthogonal Q))) rfl
    change E.frame.vector 0 = (E.rotate (orientedToOrthogonal Q)).frame.vector 0
    rw [← E.frame.map_coordinateVector, ← (E.rotate (orientedToOrthogonal Q)).frame.map_coordinateVector,
      frameRotate_map]
    change E.frame.map (coordinateVector 0) = E.frame.map u
    rw [hueq]
  have hb := unitTangentOfFrame_flow_eq g o E F hE hF hstate (-t)
  dsimp [E,F] at hb
  rw [← parallelFrameFlowMap_add, ← parallelFrameFlowMap_add, neg_add_cancel,
    parallelFrameFlowMap_zero, parallelFrameFlowMap_zero] at hb
  exact hb

theorem frameExponential_minimizing_before_cut_unique (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualCutTime g e)
    (w : FourSpace) (hw : w ∈ actualMinimizingTangentDomain g o e)
    (hend : frameExponential g o e w = frameGeodesic g 0 e t) :
    w = t • coordinateVector 0 := by
  have hmin : t ∈ frameMinimizingTimes g e := by
    rw [frameMinimizingTimes_eq_Icc]; exact ⟨ht.le,htc.le⟩
  have hn : ‖w‖ = t := by
    rw [← hw, hend]
    exact (metricDistance_eq_iff g _ _ ht.le).mpr hmin.2
  let p : Directions := ⟨t⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),hn,inv_mul_cancel₀ ht.ne']⟩
  have hp : t • p.val = w := by
    change t • (t⁻¹ • w) = w
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix p))
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hpoint : frameGeodesic g 0 e t = frameGeodesic g 0 f t := by
    rw [← frameExponential_direction_ray g o e he p t,hp]
    exact hend.symm
  have hs := frameGeodesic_minimizing_initial_unique g o e f he hf rfl t ht htc hpoint
  have hv := congrArg (fun u : UnitTangentBundle g => u.vector) hs
  have hdir : p.val = coordinateVector 0 := by
    apply e.frame.map_injective
    change e.frame.vector 0 = (e.frame.turn p).vector 0 at hv
    rw [e.frame.turn_first] at hv
    rw [e.frame.map_coordinateVector]
    exact hv.symm
  rw [← hp,hdir]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing vectors over all positive frames form a compact
set. This gives uniform control of fibers near a unique minimizing vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def actualMinimizingFramePairs (g : SmoothMetric M) (o : FrameOrientation g) :
    Set (FrameBundle g × FourSpace) :=
  {p | p.1 ∈ o.positive ∧ p.2 ∈ actualMinimizingTangentDomain g o p.1}

theorem actualMinimizingFramePairs_compact (g : SmoothMetric M) (o : FrameOrientation g) :
    IsCompact (actualMinimizingFramePairs g o) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  obtain ⟨D,hD⟩ := (isCompact_range (metricDistance_continuous g)).bddAbove
  have hc : IsClosed (actualMinimizingFramePairs g o) :=
    (o.clopen.isClosed.preimage continuous_fst).inter
      (isClosed_eq ((metricDistance_continuous g).comp
        (((continuous_frameBase g).comp continuous_fst).prodMk
          (frameExponential_joint_continuous g o))) (continuous_norm.comp continuous_snd))
  apply (isCompact_univ.prod (isCompact_closedBall (0 : FourSpace) D)).of_isClosed_subset hc
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  rw [← hp.2]
  exact hD ⟨(p.1.base,frameExponential g o p.1 p.2),rfl⟩

theorem minimizing_vectors_common_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (t : ℝ) (U : Set FourSpace)
    (hU : IsOpen U)
    (hunique : ∀ w ∈ actualMinimizingTangentDomain g o e,
      frameExponential g o e w = frameGeodesic g 0 e t → w ∈ U) :
    ∃ V : Set (FrameBundle g), IsOpen V ∧ e ∈ V ∧
      ∀ f ∈ V, f ∈ o.positive → ∀ w ∈ actualMinimizingTangentDomain g o f,
        frameExponential g o f w = frameGeodesic g 0 f t → w ∈ U := by
  let K := actualMinimizingFramePairs g o ∩
    {p : FrameBundle g × FourSpace | frameExponential g o p.1 p.2 = frameGeodesic g 0 p.1 t} ∩
    {p : FrameBundle g × FourSpace | p.2 ∉ U}
  have hendpoint : Continuous (fun p : FrameBundle g × FourSpace => frameGeodesic g 0 p.1 t) :=
    ((continuous_frameBase g).comp (parallelFrameFlowMap_continuous_slice g 0 t)).comp continuous_fst
  have hK : IsCompact K :=
    ((actualMinimizingFramePairs_compact g o).inter_right
      (isClosed_eq (frameExponential_joint_continuous g o) hendpoint)).inter_right
        (hU.isClosed_compl.preimage continuous_snd)
  have hclosed : IsClosed (Prod.fst '' K) := (hK.image continuous_fst).isClosed
  refine ⟨(Prod.fst '' K)ᶜ,hclosed.isOpen_compl,?_,?_⟩
  · rintro ⟨⟨f,w⟩,⟨⟨hf,heq⟩,hwU⟩,hfe⟩
    change f = e at hfe
    subst f
    exact hwU (hunique w hf.2 heq)
  · intro f hf hpos w hw heq
    by_contra hwU
    exact hf ⟨(f,w),⟨⟨⟨hpos,hw⟩,heq⟩,hwU⟩,rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A minimizing geodesic cannot continue beyond its first conjugate point.
The negative Jacobi test field contradicts the index inequality obtained
from actual, endpoint-compatible variations of the minimizing segment. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_le_firstConjugateTime (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    actualCutTime g e ≤ actualFirstConjugateTime g hRic e := by
  by_contra hnot
  have hcb : actualFirstConjugateTime g hRic e < actualCutTime g e :=
    lt_of_not_ge hnot
  let d := actualJacobiSolution g hRic e
  let c := actualFirstConjugateTime g hRic e
  let b := actualCutTime g e
  have hc : 0 < c := actualFirstConjugateTime_pos g hRic e
  obtain ⟨w, _, hJ, hV⟩ := exists_actualFirstConjugate_vector g hRic e
  obtain ⟨ε, _, hneg⟩ := d.exists_negative_conjugate_index
    (actualJacobiCurvature_continuous g hRic e)
    (actualJacobiCurvature_symmetric g e) w hc hcb hJ hV
  have hmin : metricDistance g (frameGeodesic g 0 e 0)
      (frameGeodesic g 0 e b) = b - 0 := by
    have hb := actualCutTime_mem g e
    have hzero : frameGeodesic g 0 e 0 = e.base := by
      simp only [frameGeodesic, parallelFrameFlowMap_zero]
    rw [hzero, sub_zero]
    exact (metricDistance_eq_iff g e.base (frameGeodesic g 0 e b) hb.1).mpr hb.2
  have hind := two_piece_geodesic_index_nonneg g hRic e 0 c b hc hcb
    (conjugateLeftField d w c b ε) (conjugateRightField d w c b ε)
    (conjugateLeftRate d w c b ε) (conjugateRightRate d w c b ε)
    (conjugateLeftField_hasDerivAt d w c b ε)
    (conjugateRightField_hasDerivAt d w c b ε)
    (conjugateLeftRate_continuous d w c b ε)
    (conjugateRightRate_continuous d w c b ε)
    (conjugateBranches_agree d w c b ε hJ)
    (conjugateBranches_endpoints d w c b ε).1
    (conjugateBranches_endpoints d w c b ε).2 hmin
  change 0 ≤ conjugateIndexAction d w c b ε at hind
  exact (not_le_of_gt hneg) hind

theorem frameMinimizingTime_le_firstConjugateTime (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) {t : ℝ}
    (ht : t ∈ frameMinimizingTimes g e) :
    t ≤ actualFirstConjugateTime g hRic e := by
  have hcut : t ≤ actualCutTime g e := by
    rw [frameMinimizingTimes_eq_Icc g e] at ht
    exact ht.2
  exact hcut.trans (actualCutTime_le_firstConjugateTime g hRic e)

theorem actualCutTime_le_pi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : actualCutTime g e ≤ Real.pi :=
  (actualCutTime_le_firstConjugateTime g hRic e).trans
    (actualFirstConjugateTime_le_pi g hRic e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A nonconjugate cut point has two genuine minimizing radial vectors.
The compact set used below consists of actual distance-minimizing vectors. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

private theorem minimizing_vectors_near_unique (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (v : FourSpace)
    (U : Set FourSpace) (hU : IsOpen U) (hvU : v ∈ U)
    (hunique : ∀ w ∈ actualMinimizingTangentDomain g o e,
      frameExponential g o e w = frameExponential g o e v → w = v) :
    ∃ V : Set M, IsOpen V ∧ frameExponential g o e v ∈ V ∧
      ∀ w ∈ actualMinimizingTangentDomain g o e,
        frameExponential g o e w ∈ V → w ∈ U := by
  let K := actualMinimizingTangentDomain g o e ∩ Uᶜ
  have hK : IsCompact K := (actualMinimizingTangentDomain_compact g o e).inter_right
    hU.isClosed_compl
  have hclosed : IsClosed (frameExponential g o e '' K) :=
    (hK.image (frameExponential_continuous g o e)).isClosed
  refine ⟨(frameExponential g o e '' K)ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨w, hw, heq⟩
    exact hw.2 ((hunique w hw.1 heq) ▸ hvU)
  · intro w hw hV
    by_contra hnot
    exact hV ⟨w, ⟨hw, hnot⟩, rfl⟩

theorem actualCutTime_second_minimizing_vector (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hnoconj : actualCutTime g e < actualFirstConjugateTime g hRic e) :
    ∃ w : FourSpace, w ∈ actualMinimizingTangentDomain g o e ∧
      frameExponential g o e w = frameGeodesic g 0 e (actualCutTime g e) ∧
      w ≠ actualCutTime g e • coordinateVector 0 := by
  classical
  let c := actualCutTime g e
  let v : FourSpace := c • coordinateVector 0
  have hc : 0 < c := actualCutTime_pos g o hRic e he
  have hv : frameExponential g o e v = frameGeodesic g 0 e c :=
    frameExponential_first_ray g o e he c hc
  by_contra hnot
  have hunique : ∀ w ∈ actualMinimizingTangentDomain g o e,
      frameExponential g o e w = frameExponential g o e v → w = v := by
    intro w hw heq
    by_contra hne
    exact hnot ⟨w, hw, heq.trans hv, hne⟩
  obtain ⟨C, hvC, hC⟩ := frameExponential_preconjugate_localChart g o hRic e he c hc hnoconj
  obtain ⟨V, hV, hvV, hnear⟩ := minimizing_vectors_near_unique g o e v
    C.source C.open_source hvC hunique
  let line : ℝ → FourSpace := fun t => t • coordinateVector 0
  have hl : Continuous line := continuous_id.smul continuous_const
  have hgood : {t : ℝ | line t ∈ C.source ∧ frameExponential g o e (line t) ∈ V ∧ 0 < t}
      ∈ 𝓝 c := by
    exact Filter.inter_mem (C.open_source.preimage hl |>.mem_nhds hvC)
      (Filter.inter_mem (hV.preimage ((frameExponential_continuous g o e).comp hl)
        |>.mem_nhds hvV) (Ioi_mem_nhds hc))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let t := c + δ / 2
  have htc : c < t := by dsimp [t]; linarith
  have htg : line t ∈ C.source ∧ frameExponential g o e (line t) ∈ V ∧ 0 < t := by
    apply hball
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr htc)]
    dsimp [t]
    linarith
  obtain ⟨w, hw, hn⟩ := frameExponential_global_minimizing g o hRic e he
    (frameExponential g o e (line t))
  have hwK : w ∈ actualMinimizingTangentDomain g o e := by
    change metricDistance g e.base (frameExponential g o e w) = ‖w‖
    rw [hw, hn]
  have hwC : w ∈ C.source := hnear w hwK (hw ▸ htg.2.1)
  have heq : w = line t := C.injOn hwC htg.1
    ((hC hwC).trans (hw.trans (hC htg.1).symm))
  have hnline : ‖line t‖ = t := by
    dsimp [line]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htg.2.2]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit, mul_one]
  have hmin : t ∈ frameMinimizingTimes g e := by
    refine ⟨htg.2.2.le, ?_⟩
    have hd : metricDistance g e.base (frameGeodesic g 0 e t) = t := by
      rw [heq, hnline, frameExponential_first_ray g o e he t htg.2.2] at hn
      exact hn.symm
    exact (metricDistance_eq_iff g _ _ htg.2.2.le).mp hd
  rw [frameMinimizingTimes_eq_Icc] at hmin
  exact (not_lt_of_ge hmin.2) htc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric Jacobian formula in every initial direction. An oriented
rotation of the initial frame contributes determinant one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem orientedEuclidean_det (Q : OrientedOrthogonalFour) :
    LinearMap.det (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det (Matrix.toEuclideanLin Q.val) = 1
  rw [LinearMap.det_toLpLin 2]
  exact (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_chart_det_rotate (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (Q : OrientedOrthogonalFour) (d : M) (v : FourSpace)
    (hd : frameExponential g o e
      (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property v) ∈ (chartAt FourSpace d).source) :
    LinearMap.det (fderiv ℝ (fun w => chartAt FourSpace d
      (frameExponential g o (e.rotate (orientedToOrthogonal Q)) w)) v).toLinearMap =
    LinearMap.det (fderiv ℝ (fun w => chartAt FourSpace d (frameExponential g o e w))
      (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property v)).toLinearMap := by
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let F := fun w => chartAt FourSpace d (frameExponential g o e w)
  have hF : DifferentiableAt ℝ F (L v) :=
    (frameExponential_chart_contDiffAt g o d e (L v) hd).differentiableAt (by simp)
  have hL : HasFDerivAt (fun w => L w) (L : FourSpace →L[ℝ] FourSpace) v :=
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have h := hF.hasFDerivAt.comp v hL
  have heq : (fun w => F (L w)) = (fun w => chartAt FourSpace d
      (frameExponential g o (e.rotate (orientedToOrthogonal Q)) w)) := by
    funext w
    exact congrArg (chartAt FourSpace d) (frameExponential_rotate g o e Q w).symm
  change HasFDerivAt (fun w => F (L w)) ((fderiv ℝ F (L v)).comp
    (L : FourSpace →L[ℝ] FourSpace)) v at h
  rw [heq] at h
  rw [h.fderiv]
  change LinearMap.det ((fderiv ℝ F (L v)).toLinearMap.comp L.toLinearEquiv.toLinearMap) = _
  rw [LinearMap.det_comp]
  have hdet : LinearMap.det L.toLinearEquiv.toLinearMap = 1 := orientedEuclidean_det Q
  rw [hdet, mul_one]
  rfl

theorem frameExponential_metric_jacobian_direction (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : Directions) (d : M) (t : ℝ) (ht : 0 < t)
    (hd : frameExponential g o e (t • q.val) ∈ (chartAt FourSpace d).source) :
    chartVolumeDensity g d (chartAt FourSpace d (frameExponential g o e (t • q.val))) *
      |LinearMap.det (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e v)) (t • q.val)).toLinearMap| =
      |((actualJacobiSolution g hRic
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J t).det / t ^ 3| := by
  let Q := directionOrientedMatrix q
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (t • coordinateVector 0) = t • q.val := by
    rw [map_smul, directionRotation_first]
  have hpoint : frameExponential g o e (t • q.val) = (parallelFrameFlowMap g 0 t f).base :=
    frameExponential_direction_ray g o e he q t
  have hdf : (parallelFrameFlowMap g 0 t f).base ∈ (chartAt FourSpace d).source :=
    hpoint ▸ hd
  have hdet := frameExponential_chart_det_rotate g o e Q d (t • coordinateVector 0)
    (by rwa [hdir])
  rw [hdir] at hdet
  rw [← hdet, hpoint]
  exact frameExponential_metric_jacobian g o hRic d f hf t ht hdf

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform actual cut-time lower bound gives minimizing and injective normal balls. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_minimizing_of_cut_lower (R : ℝ)
    (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ R) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero]
    exact (metricDistance_eq_zero_iff g _ _).mpr rfl
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hm : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
    apply (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg _)).mpr
    exact hv.trans (hcut _ (frameRotate_oriented_positive o e he _))
  rwa [hrad] at hm

theorem direction_injective_of_cut_lower (R : ℝ)
    (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R)
    (hqp : frameExponential g o e (t • q.val) = frameExponential g o e (t • p.val)) : q = p := by
  let s := (R - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith [ht.2]
  have hsum : t + s < R := by dsimp [s]; linarith [ht.2]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := parallelFrameFlowMap g 0 (-s) f
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf (-s)
  have hbase : F.base = frameExponential g o e ((-s) • q.val) :=
    (frameExponential_direction_ray g o e he q (-s)).symm
  have hend : frameExponential g o F ((t + s) • coordinateVector 0) =
      frameExponential g o e (t • p.val) := by
    rw [frameExponential_shift_first g o f hf (t + s) (-s),
      show t + s + -s = t by ring]
    exact (frameExponential_direction_ray g o e he q t).symm.trans hqp
  have hnorm : ‖(t + s) • (coordinateVector 0 : FourSpace)‖ = t + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos ht.1 hs)]
    simp [coordinateVector]
  have hmin := frameExponential_minimizing_of_cut_lower R hcut F hF
    ((t + s) • coordinateVector 0) (by rw [hnorm]; exact hsum.le)
  rw [hbase, hend, hnorm] at hmin
  have hd := (metricDistance_eq_iff g _ _ (add_pos ht.1 hs).le).mp hmin
  rw [add_comm t s] at hd
  exact Subtype.ext (frameExponential_no_minimizing_corner g o e q.val p.val
    q.property p.property s t hs ht.1 hd)

theorem frameExponential_injOn_ball_of_cut_lower (R : ℝ)
    (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (Metric.ball 0 R) := by
  intro v hv w hw heq
  have hvπ : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hwπ : ‖w‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hn : ‖v‖ = ‖w‖ := by
    rw [← frameExponential_minimizing_of_cut_lower R hcut e he v hvπ.le,
      ← frameExponential_minimizing_of_cut_lower R hcut e he w hwπ.le, heq]
  by_cases hz : v = 0
  · subst v
    have hwzero : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn.symm)
    exact hwzero.symm
  have hwz : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa only [h, norm_zero] using hn))
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let p : Directions := ⟨‖w‖⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwz)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hp : ‖v‖ • p.val = w := by
    change ‖v‖ • (‖w‖⁻¹ • w) = w
    rw [hn, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hwz), one_smul]
  have hqp : q = p := direction_injective_of_cut_lower R hcut e he q p
    ‖v‖ ⟨norm_pos_iff.mpr hz, hvπ⟩ (by rwa [hq, hp])
  rw [← hq, hqp, hp]


end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness of the frame bundle gives a positive common normal radius. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_uniform_exponential_injective_radius (g : SmoothMetric M)
    (o : FrameOrientation g) :
    ∃ R > (0 : ℝ), ∀ e : FrameBundle g, InjOn (frameExponential g o e) (ball 0 R) := by
  classical
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hlocal (e : FrameBundle g) :
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧ ∃ r > (0 : ℝ),
        ∀ e' ∈ U, InjOn (frameExponential g o e') (ball 0 r) := by
    obtain ⟨F, t, _, _, _, U, hU, heU, r, hr, hdata⟩ := exists_heatNormalCommonChart g o e
    refine ⟨U, hU, heU, r, hr, ?_⟩
    intro e' he'
    obtain ⟨D, C, _, hCs, hCE, _⟩ := hdata e' he'
    intro v hv w hw heq
    have hvC : v ∈ C.source := hCs ▸ hv
    have hwC : w ∈ C.source := hCs ▸ hw
    exact C.injOn hvC hwC ((hCE hvC).trans (heq.trans (hCE hwC).symm))
  choose U hU heU r hr hinj using hlocal
  obtain ⟨t, ht⟩ := finite_cover_nhds (fun e => (hU e).mem_nhds (heU e))
  have hex : ∃ R > (0 : ℝ), ∀ e ∈ t, R ≤ r e := by
    clear ht
    induction t using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert e s hes ih =>
      obtain ⟨R,hR,hRs⟩ := ih
      refine ⟨min R (r e), lt_min hR (hr e), ?_⟩
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hfs
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hRs f hfs)
  obtain ⟨R, hR, hRt⟩ := hex
  refine ⟨R, hR, ?_⟩
  intro e
  have he : e ∈ ⋃ f ∈ t, U f := by rw [ht]; trivial
  obtain ⟨f,hft,hef⟩ := mem_iUnion₂.mp he
  exact (hinj f e hef).mono (ball_subset_ball (hRt f hft))

variable [PreconnectedSpace M]

theorem frameExponential_minimizing_of_injOn (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (R : ℝ)
    (hinj : InjOn (frameExponential g o e) (ball 0 R))
    (v : FourSpace) (hv : ‖v‖ < R) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  obtain ⟨w,hw,hn⟩ := frameExponential_global_minimizing g o hRic e he
    (frameExponential g o e v)
  have hle : metricDistance g e.base (frameExponential g o e v) ≤ ‖v‖ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (frameExponential_distance g o e v)
    simpa only [metricDistance, ENNReal.toReal_ofReal (norm_nonneg _)] using hh
  have hwR : w ∈ ball (0 : FourSpace) R := by
    rw [mem_ball, dist_zero_right, hn]
    exact hle.trans_lt hv
  have heq : w = v := hinj hwR (by simpa only [mem_ball, dist_zero_right] using hv) hw
  rw [heq] at hn
  exact hn.symm

theorem exists_uniform_positive_cut_time (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ e ∈ o.positive, r ≤ actualCutTime g e := by
  obtain ⟨R,hR,hinj⟩ := exists_uniform_exponential_injective_radius g o
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro e he
  have hn : ‖(R / 2) • (coordinateVector 0 : FourSpace)‖ = R / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hR)]
    have hh : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hh, mul_one]
  have hm := frameExponential_minimizing_of_injOn g o hRic e he R (hinj e)
    ((R / 2) • coordinateVector 0) (by rw [hn]; linarith)
  rw [frameExponential_first_ray g o e he _ (half_pos hR), hn] at hm
  have hmem : R / 2 ∈ frameMinimizingTimes g e :=
    ⟨(half_pos hR).le, (metricDistance_eq_iff g _ _ (half_pos hR).le).mp hm⟩
  rw [frameMinimizingTimes_eq_Icc] at hmem
  exact hmem.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine finite chart variation of a geodesic in a parallel normal
direction strictly lowers its energy when sectional curvature is positive.
The endpoint curves have zero covariant acceleration, and are shared by
all adjacent pieces. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_finite_parallel_normal_shortening (g : SmoothMetric M)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (n : ℕ) (hn : 0 < n) (t : ℕ → ℝ) (c : ℕ → M)
    (a : Fin 3 → ℝ) (ha : a ≠ 0)
    (ht : ∀ i < n, t i < t (i + 1))
    (hc : ∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)),
      frameGeodesic g 0 e r ∈ (chartAt FourSpace (c i)).source) :
    ∃ γ : ℕ → ℝ → ℝ → M,
      (∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)), γ i 0 r = frameGeodesic g 0 e r) ∧
      (∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)),
        ContinuousAt (fun p : ℝ × ℝ => γ i p.1 p.2) (0,r)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i ε) (Icc (t i) (t (i + 1)))) ∧
        (∀ i < n, γ i ε (t i) = normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 (t i) e) a ε ∧
          γ i ε (t (i + 1)) = normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 (t (i + 1)) e) a ε) ∧
        (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) <
          (t n - t 0) / 2 := by
  classical
  let A := fun i : Fin n => Classical.choice (exists_normalQuadraticJetData g
    (parallelFrameFlowMap g 0 (t i.val) e) (c i.val)
      (hc i.val i.isLt (t i.val) ⟨le_rfl,(ht i.val i.isLt).le⟩) a)
  let B := fun i : Fin n => Classical.choice (exists_normalQuadraticJetData g
    (parallelFrameFlowMap g 0 (t (i.val + 1)) e) (c i.val)
      (hc i.val i.isLt (t (i.val + 1)) ⟨(ht i.val i.isLt).le,le_rfl⟩) a)
  let N : ℝ → Fin 3 → ℝ := fun _ => a
  let P : ℝ → Fin 3 → ℝ := fun _ => 0
  have hN (i : Fin n) (r : ℝ) (_ : r ∈ Icc (t i.val) (t (i.val + 1))) :
      HasDerivAt N (P r) r := hasDerivAt_const r a
  choose δ hδ hδA hδB hinside using fun i : Fin n =>
    normalQuadraticSegment_common_radius g e (c i.val) N (ht i.val i.isLt)
      (hc i.val i.isLt) continuousOn_const (A i) (B i)
  let E : ℕ → ℝ → ℝ := fun i ε => if hi : i < n then
    normalSegmentEnergy g e (c i) N P (A ⟨i,hi⟩).position (B ⟨i,hi⟩).position
      (t i) (t (i + 1)) ε else 0
  let γ : ℕ → ℝ → ℝ → M := fun i ε => if hi : i < n then
    normalSegmentCurve g e (c i) N (A ⟨i,hi⟩).position (B ⟨i,hi⟩).position
      (t i) (t (i + 1)) ε else frameGeodesic g 0 e
  let I : ℕ → ℝ := fun i => ∫ r in t i..t (i + 1),
    normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) a 0
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, ε ∈ Icc (-δ i) (δ i) := by
    apply eventually_all.mpr
    intro i
    exact Icc_mem_nhds (neg_neg_of_pos (hδ i)) (hδ i)
  have hfd : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) ε := by
    have hh : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, DifferentiableAt ℝ (E i.val) ε := by
      apply eventually_all.mpr
      intro i
      simpa only [E,dite_eq_left i.isLt] using
        normalQuadraticSegmentEnergy_first_differentiable g e (c i.val) N P
          (ht i.val i.isLt) (hδ i) (hc i.val i.isLt) (hN i) continuousOn_const
          (A i) (B i) (hδA i) (hδB i) (hinside i)
    filter_upwards [hh] with ε hε i hi
    exact hε ⟨i,hi⟩
  have hzero : (∑ i ∈ Finset.range n, E i 0) = (t n - t 0) / 2 := by
    calc
      _ = ∑ i ∈ Finset.range n, (t (i + 1) - t i) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [E,dite_eq_left hi'] using
          normalQuadraticSegmentEnergy_zero g e (c i) N P (ht i hi') (hc i hi')
            (hN ⟨i,hi'⟩) (A ⟨i,hi'⟩) (B ⟨i,hi'⟩)
      _ = _ := by rw [← Finset.sum_div,Finset.sum_range_sub]
  have hfirst (i : ℕ) (hi : i < n) : HasDerivAt (E i) 0 0 := by
    simpa only [E,dite_eq_left hi] using
      normalQuadraticSegmentEnergy_first_zero g e (c i) N P (ht i hi) (hδ ⟨i,hi⟩)
        (hc i hi) (hN ⟨i,hi⟩) continuousOn_const (A ⟨i,hi⟩) (B ⟨i,hi⟩)
        (hδA ⟨i,hi⟩) (hδB ⟨i,hi⟩) (hinside ⟨i,hi⟩)
  have hsecond (i : ℕ) (hi : i < n) : HasDerivAt (deriv (E i)) (I i) 0 := by
    simpa only [E,dite_eq_left hi,I,N,P] using
      normalQuadraticSegmentEnergy_index_secondDeriv g hRic e (c i) N P
        (ht i hi) (hδ ⟨i,hi⟩) (hc i hi) (hN ⟨i,hi⟩) continuousOn_const
        (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hδA ⟨i,hi⟩) (hδB ⟨i,hi⟩) (hinside ⟨i,hi⟩)
  have hnegative : (∑ i ∈ Finset.range n, I i) < 0 := by
    have hI (i : ℕ) (hi : i ∈ Finset.range n) : I i < 0 :=
      parallel_normal_index_negative hRic hpositive e a ha (ht i (Finset.mem_range.mp hi))
    have h := Finset.sum_lt_sum (fun i hi => (hI i hi).le)
      ⟨0,Finset.mem_range.mpr hn,hI 0 (Finset.mem_range.mpr hn)⟩
    simpa only [Finset.sum_const_zero] using h
  have hsum0 : deriv (fun ε => ∑ i ∈ Finset.range n, E i ε) 0 = 0 := by
    have h := (HasDerivAt.fun_sum (fun i hi => hfirst i (Finset.mem_range.mp hi))).deriv
    simpa only [Finset.sum_const_zero] using h
  have hsumdiff : ∀ᶠ ε in 𝓝 (0 : ℝ), DifferentiableAt ℝ
      (fun ε => ∑ i ∈ Finset.range n, E i ε) ε := by
    filter_upwards [hfd] with ε hε
    exact DifferentiableAt.fun_sum (fun i hi => hε i (Finset.mem_range.mp hi))
  have hshort := scalar_second_variation_decreases _ _ hsumdiff hsum0
    (finite_piece_secondDeriv n E I hfd hsecond) hnegative
  rw [hzero] at hshort
  refine ⟨γ,?_,?_,?_⟩
  · intro i hi r hr
    simpa only [γ,dite_eq_left hi] using
      normalQuadraticSegmentCurve_zero g e (c i) N (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hc i hi r hr)
  · intro i hi r hr
    simpa only [γ,dite_eq_left hi,N] using
      normalQuadraticSegmentCurve_continuousAt g e (c i) a (t i) (t (i + 1)) r
        (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hc i hi r hr)
  · filter_upwards [hshort,hnear.filter_mono nhdsWithin_le_nhds] with ε hε hεnear
    have hregion (i : Fin n) : ε ∈ Icc (-(A i).radius) (A i).radius ∧
        ε ∈ Icc (-(B i).radius) (B i).radius := by
      have hh := hεnear i
      have hA := hδA i
      have hB := hδB i
      constructor <;> constructor <;> linarith [hh.1,hh.2]
    refine ⟨?_,?_,?_⟩
    · intro i hi
      simpa only [γ,dite_eq_left hi] using
        normalSegmentCurve_contMDiffOn g e (c i) N P (A ⟨i,hi⟩).position
          (B ⟨i,hi⟩).position (ht i hi) (hc i hi) (hN ⟨i,hi⟩) continuousOn_const
          (hinside ⟨i,hi⟩ ε (hεnear ⟨i,hi⟩))
    · intro i hi
      simpa only [γ,dite_eq_left hi,N] using
        normalQuadraticSegmentCurve_endpoints g e (c i) N (ht i hi)
          (A ⟨i,hi⟩) (B ⟨i,hi⟩) (hregion ⟨i,hi⟩).1 (hregion ⟨i,hi⟩).2
    · have heq : (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) =
          ∑ i ∈ Finset.range n, E i ε := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [γ,E,dite_eq_left hi'] using
          (normalSegmentEnergy_eq_actual g e (c i) N P (A ⟨i,hi'⟩).position
            (B ⟨i,hi'⟩).position (ht i hi') (hc i hi') (hN ⟨i,hi'⟩)
            (hinside ⟨i,hi'⟩ ε (hεnear ⟨i,hi'⟩))).symm
      rw [heq]
      exact hε

end
end PositiveEinsteinFour.Geometry
end


section

/-! Translation along the actual parallel flow is controlled by the scalar
Dirichlet energy.  The bound survives closure of smooth first jets, so a weak
scalar with zero gradient is invariant under each parallel flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

section Generic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The `L²` isometry obtained by translating an actual scalar field along
one parallel flow. -/
def scalarFlowTranslation (d : ParallelMetricData g μ) (i : Fin 4) (t : ℝ) :
    ScalarL2 g μ →L[ℝ] ScalarL2 g μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ ((d.flow i).map t)
    ((d.flow i).preserves t)).toContinuousLinearMap

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalarFlowTranslation_norm (d : ParallelMetricData g μ) (i : Fin 4)
    (t : ℝ) (f : ScalarL2 g μ) : ‖scalarFlowTranslation d i t f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f ((d.flow i).preserves t)

def scalarTranslatedField (d : ParallelMetricData g μ) (i : Fin 4)
    (t : ℝ) (f : C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => f ((d.flow i).map t e), f.continuous.comp ((d.flow i).continuous_slice t)⟩

theorem scalarFlowTranslation_toLp (d : ParallelMetricData g μ)
    (i : Fin 4) (t : ℝ) (f : C(FrameBundle g, ℝ)) :
    scalarFlowTranslation d i t (ContinuousMap.toLp 2 μ ℝ f) =
      ContinuousMap.toLp 2 μ ℝ (scalarTranslatedField d i t f) := by
  apply Lp.ext
  have hcomp := ((d.flow i).preserves t).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 μ ℝ f) ((d.flow i).preserves t), hcomp,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (scalarTranslatedField d i t f)]
    with e h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

theorem smoothScalar_flow_translation_bound (d : ParallelMetricData g μ)
    (i : Fin 4) (hzero : ∀ e, (d.flow i).map 0 e = e)
    (a : SmoothScalar (M := M)) (t : ℝ) :
    ‖scalarFlowTranslation d i t (smoothScalarValueL2 g μ a) -
      smoothScalarValueL2 g μ a‖ ≤ |t| * ‖smoothScalarGradientL2 d i a‖ := by
  let F : ℝ → C(FrameBundle g, ℝ) := fun r =>
    scalarTranslatedField d i r (smoothScalarValue g a)
  let G : ℝ → C(FrameBundle g, ℝ) := fun r =>
    scalarTranslatedField d i r (smoothScalarGradient d i a)
  have hG : Continuous (fun p : ℝ × FrameBundle g => G p.1 p.2) :=
    (actual_scalarGradient_continuous g a.property i).comp (d.flow i).continuous
  have hd (r : ℝ) : HasDerivAt F (G r) r := by
    apply Averages.continuousField_hasDerivAt_of_joint hG
    intro s e
    exact actual_scalarValue_parallel_derivative g a.property
      (fun u => (d.flow i).map u e) s i (d.curve_continuous i e).continuousAt
      (d.parallelCurve i s e)
  let L : C(FrameBundle g, ℝ) →L[ℝ] ScalarL2 g μ := ContinuousMap.toLp 2 μ ℝ
  have hdL (r : ℝ) : HasDerivAt (fun s => L (F s)) (L (G r)) r :=
    L.hasFDerivAt.comp_hasDerivAt r (hd r)
  have hn (r : ℝ) : ‖L (G r)‖ = ‖smoothScalarGradientL2 d i a‖ := by
    rw [show L (G r) = scalarFlowTranslation d i r (smoothScalarGradientL2 d i a) from
      (scalarFlowTranslation_toLp d i r (smoothScalarGradient d i a)).symm]
    exact scalarFlowTranslation_norm d i r _
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun r _ => (hdL r).hasDerivWithinAt)
    (fun r _ => (hn r).le) convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  have hF0 : F 0 = smoothScalarValue g a := by
    ext e
    change a.val ((d.flow i).map 0 e).base = a.val e.base
    rw [hzero]
  have hFt : L (F t) = scalarFlowTranslation d i t (smoothScalarValueL2 g μ a) :=
    (scalarFlowTranslation_toLp d i t (smoothScalarValue g a)).symm
  rw [hF0, hFt] at h
  simpa only [L, smoothScalarValueL2, LinearMap.comp_apply, sub_zero,
    Real.norm_eq_abs, mul_comm] using! h

/-- The smooth translation estimate extends to the actual first-jet closure. -/
theorem scalarH1_flow_translation_bound (d : ParallelMetricData g μ)
    (i : Fin 4) (hzero : ∀ e, (d.flow i).map 0 e = e)
    (u : scalarH1 d) (t : ℝ) :
    ‖scalarFlowTranslation d i t (scalarH1Value d u) - scalarH1Value d u‖ ≤
      |t| * ‖scalarH1Gradient d i u‖ := by
  let p₀ : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none
  let pᵢ : ScalarJetL2 g μ →L[ℝ] ScalarL2 g μ :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)
  let S : Set (ScalarJetL2 g μ) := {v |
    ‖scalarFlowTranslation d i t (p₀ v) - p₀ v‖ ≤ |t| * ‖pᵢ v‖}
  have hS : IsClosed S := isClosed_le
    (((scalarFlowTranslation d i t).continuous.comp p₀.continuous).sub p₀.continuous).norm
    (continuous_const.mul pᵢ.continuous.norm)
  have hsubset : (LinearMap.range (smoothScalarFirstJet d) : Set (ScalarJetL2 g μ)) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact smoothScalar_flow_translation_bound d i hzero a t
  have hu : u.val ∈ closure
      (LinearMap.range (smoothScalarFirstJet d) : Set (ScalarJetL2 g μ)) := u.property
  exact (closure_minimal hsubset hS) hu

theorem scalarH1_flow_invariant_of_gradient_zero (d : ParallelMetricData g μ)
    (i : Fin 4) (hzero : ∀ e, (d.flow i).map 0 e = e)
    (u : scalarH1 d) (hgrad : scalarH1Gradient d i u = 0) (t : ℝ) :
    scalarFlowTranslation d i t (scalarH1Value d u) = scalarH1Value d u := by
  have h := scalarH1_flow_translation_bound d i hzero u t
  rw [hgrad, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end Generic

section Actual

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarPoissonWeakCompactFrames (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem actual_scalarH1_flow_translation_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (u : scalarH1 (canonicalParallelMetricData g o hRic)) (i : Fin 4) (t : ℝ) :
    ‖scalarFlowTranslation (canonicalParallelMetricData g o hRic) i t
        (scalarH1Value (canonicalParallelMetricData g o hRic) u) -
      scalarH1Value (canonicalParallelMetricData g o hRic) u‖ ≤
      |t| * ‖scalarH1Gradient (canonicalParallelMetricData g o hRic) i u‖ := by
  apply scalarH1_flow_translation_bound
  intro e
  exact parallelFrameFlowMap_zero g i e

theorem actual_scalarH1_flow_invariant_of_gradient_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (u : scalarH1 (canonicalParallelMetricData g o hRic)) (i : Fin 4)
    (hgrad : scalarH1Gradient (canonicalParallelMetricData g o hRic) i u = 0) (t : ℝ) :
    scalarFlowTranslation (canonicalParallelMetricData g o hRic) i t
        (scalarH1Value (canonicalParallelMetricData g o hRic) u) =
      scalarH1Value (canonicalParallelMetricData g o hRic) u := by
  apply scalarH1_flow_invariant_of_gradient_zero _ i _ u hgrad t
  intro e
  exact parallelFrameFlowMap_zero g i e

end Actual

end
end PositiveEinsteinFour.Geometry
end


section

/-! A vanishing positively weighted scalar energy has zero actual
differential. Full support is used only on the base manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem scalarGradient_zero_of_weighted_energy (g : SmoothMetric M)
    (o : FrameOrientation g) {a k : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (hk : Continuous k)
    (hpos : ∀ x, 0 < k x)
    (hzero : (∫ e, k e.base * (∑ i, scalarGradient g a e i ^ 2)
      ∂canonicalFrameMeasure g o) = 0) :
    ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0 := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let := normalizedVolume_isOpenPosMeasure g
  have hE : Continuous (fun x => k x * scalarDirichletDensity g a x) :=
    hk.mul (scalarDirichletDensity_continuous g ha)
  have hbase : (∫ c, k c * scalarDirichletDensity g a c ∂normalizedVolume g) = 0 := by
    rw [← (canonicalFrameMeasure_base g o).map_eq,
      integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable
        hE.aestronglyMeasurable]
    simpa only [scalarDirichletDensity_eq_frame] using hzero
  have hnonneg (x : M) : 0 ≤ k x * scalarDirichletDensity g a x :=
    mul_nonneg (hpos x).le (scalarDirichletDensity_nonneg g a x)
  have hInt : Integrable (fun x => k x * scalarDirichletDensity g a x)
      (normalizedVolume g) :=
    hE.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : (fun x => k x * scalarDirichletDensity g a x) =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hInt).mp hbase
  have hpoint : (fun x => k x * scalarDirichletDensity g a x) = 0 :=
    Measure.eq_of_ae_eq hae hE continuous_const
  intro e i
  have hv := congrFun hpoint e.base
  have hz : scalarDirichletDensity g a e.base = 0 :=
    (mul_eq_zero.mp hv).resolve_left (ne_of_gt (hpos e.base))
  have hs : (∑ j, scalarGradient g a e j ^ 2) = 0 := by
    rwa [scalarDirichletDensity_eq_frame g a e] at hz
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => sq_nonneg (scalarGradient g a e j))
    (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp (le_antisymm (hs ▸ hle) (sq_nonneg _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The zeroth de Rham space is exactly the constant smooth functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev ZeroFormDeRhamCohomology (g : SmoothMetric M) :=
  (smoothScalarDifferentialLinear g).ker

local instance : AddCommGroup (ZeroFormDeRhamCohomology g) := Submodule.addCommGroup _

def scalarConstantLinear : ℝ →ₗ[ℝ] SmoothScalar (M := M) where
  toFun := smoothScalarConst
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def scalarConstantToDeRham : ℝ →ₗ[ℝ] ZeroFormDeRhamCohomology g :=
  (scalarConstantLinear (M := M)).codRestrict (ZeroFormDeRhamCohomology g)
    (fun c => smoothScalarDifferential_const c)

variable [T3Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem scalarConstantToDeRham_injective :
    Function.Injective (scalarConstantToDeRham (g := g)) := by
  intro a b hab
  exact congrArg (fun f : ZeroFormDeRhamCohomology g => f.val.val (Classical.arbitrary M)) hab

include o

theorem scalarConstantToDeRham_surjective (hRic : RicciThree g) :
    Function.Surjective (scalarConstantToDeRham (g := g)) := by
  intro f
  have hdf : smoothScalarDifferential g f.val = 0 := f.property
  have hg (e : FrameBundle g) (i : Fin 4) : scalarGradient g f.val.val e i = 0 := by
    rw [← smoothScalarDifferential_framed, hdf]
    simp only [Submodule.coe_zero, covariantFieldFramed_eq, frameTensor, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero]
  obtain ⟨c, hc⟩ := scalar_constants_of_gradient_eq_zero g o hRic f.val.property hg
  refine ⟨c, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact funext (fun x => (hc x).symm)

def scalarConstantDeRhamEquiv (hRic : RicciThree g) :
    ℝ ≃ₗ[ℝ] ZeroFormDeRhamCohomology g :=
  LinearEquiv.ofBijective scalarConstantToDeRham
    ⟨scalarConstantToDeRham_injective, scalarConstantToDeRham_surjective (o := o) hRic⟩

theorem zeroFormDeRhamCohomology_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (ZeroFormDeRhamCohomology g) :=
  FiniteDimensional.of_surjective (scalarConstantToDeRham (g := g))
    (scalarConstantToDeRham_surjective (o := o) hRic)

theorem zeroFormDeRhamCohomology_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (ZeroFormDeRhamCohomology g) = 1 := by
  rw [← (scalarConstantDeRhamEquiv (o := o) hRic).finrank_eq]
  exact Module.finrank_self ℝ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform cut bounds compare initial vectors even when their frames
are different. A scalar derivative test supplies strict short variations. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem scalar_decreases_right {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have hs := hf.hasDerivWithinAt.limsup_slope_le' (s := Ioi (0 : ℝ)) (by simp) ha
  filter_upwards [hs,self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field,sub_zero] at ht
  have h := (div_lt_iff₀ htpos).mp ht
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem uniform_cut_initial_vector_unique (g : SmoothMetric M) (o : FrameOrientation g)
    (c : ℝ) (hcut : ∀ e ∈ o.positive, c ≤ actualCutTime g e)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base) (v w : FourSpace) (hv : ‖v‖ < c) (hw : ‖w‖ < c)
    (hend : frameExponential g o e v = frameExponential g o f w) :
    e.frame.map v = f.frame.map w := by
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o e f he hf hbase
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  have hnorm : ‖L w‖ < c := by rw [L.norm_map]; exact hw
  have hexp : frameExponential g o e v = frameExponential g o e (L w) := by
    rw [← frameExponential_rotate g o e Q w,hQ]
    exact hend
  have heq : v = L w := frameExponential_injOn_ball_of_cut_lower c hcut e he
    (by simpa only [mem_ball,dist_zero_right] using hv)
    (by simpa only [mem_ball,dist_zero_right] using hnorm) hexp
  rw [heq,← hQ,frameRotate_map]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual cut times are lower semicontinuous on the oriented frame bundle,
and attain a positive global minimum. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_common_lower_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualCutTime g e) :
    ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∀ f ∈ U, f ∈ o.positive → t ≤ actualCutTime g f := by
  obtain ⟨U,hU,heU,r,hr,hinj⟩ := frameExponential_common_injective_neighborhood g o hRic e he
    t ht (htc.trans_le (actualCutTime_le_firstConjugateTime g hRic e))
  obtain ⟨V,hV,heV,hnear⟩ := minimizing_vectors_common_neighborhood g o e t
    (ball (t • coordinateVector 0) r) isOpen_ball (by
      intro w hw hend
      rw [frameExponential_minimizing_before_cut_unique g o e he t ht htc w hw hend]
      exact mem_ball_self hr)
  refine ⟨U ∩ V,hU.inter hV,⟨heU,heV⟩,?_⟩
  intro f hf hpos
  obtain ⟨w,hw,hn⟩ := frameExponential_global_minimizing g o hRic f hpos
    (frameGeodesic g 0 f t)
  have hwK : w ∈ actualMinimizingTangentDomain g o f := by
    change metricDistance g f.base (frameExponential g o f w) = ‖w‖
    rw [hw,hn]
  have hwball := hnear f hf.2 hpos w hwK hw
  have heq : w = t • coordinateVector 0 := hinj f hf.1 hwball (mem_ball_self hr)
    (hw.trans (frameExponential_first_ray g o f hpos t ht).symm)
  have hnorm : ‖(t • coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit,mul_one]
  rw [heq,hnorm] at hn
  have hm : t ∈ frameMinimizingTimes g f :=
    ⟨ht.le,(metricDistance_eq_iff g _ _ ht.le).mp hn.symm⟩
  rw [frameMinimizingTimes_eq_Icc] at hm
  exact hm.2

theorem actualCutTime_lowerSemicontinuousOn_positive (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    LowerSemicontinuousOn (actualCutTime g) o.positive := by
  apply lowerSemicontinuousOn_iff.mpr
  intro e he
  apply lowerSemicontinuousWithinAt_iff.mpr
  intro a ha
  obtain ⟨t,ht,htc⟩ := exists_between (max_lt (actualCutTime_pos g o hRic e he) ha)
  obtain ⟨U,hU,heU,hbound⟩ := actualCutTime_common_lower_bound g o hRic e he t
    ((le_max_left 0 a).trans_lt ht) htc
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds heU),self_mem_nhdsWithin]
    with f hf hpos
  exact ((le_max_right 0 a).trans_lt ht).trans_le (hbound f hf hpos)

theorem exists_minimal_actualCutTime [Nonempty M] (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    ∃ e ∈ o.positive, 0 < actualCutTime g e ∧
      ∀ f ∈ o.positive, actualCutTime g e ≤ actualCutTime g f := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hne : o.positive.Nonempty :=
    ⟨⟨Classical.arbitrary M,o.frame (Classical.arbitrary M)⟩,o.frame_positive _⟩
  obtain ⟨e,he,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne o.clopen.isClosed.isCompact
    (actualCutTime_lowerSemicontinuousOn_positive g o hRic)
  exact ⟨e,he,actualCutTime_pos g o hRic e he,hmin⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous intrinsic Jacobian density for the actual exponential.
Its expression in any output chart is the metric density times the
absolute coordinate determinant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def frameExponentialGram (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : Mat4 := fun i j =>
  g.inner (frameExponential g o e v)
    (mfderiv I4 I4 (frameExponential g o e) v (coordinateVector i))
    (mfderiv I4 I4 (frameExponential g o e) v (coordinateVector j))

def frameExponentialJacobian (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : ℝ := Real.sqrt (frameExponentialGram g o e v).det

theorem frameExponentialGram_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponentialGram g o e) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hv (i : Fin 4) : Continuous (fun v : FourSpace =>
      tangentMap I4 I4 (frameExponential g o e) (⟨v, coordinateVector i⟩ : TangentBundle I4 FourSpace)) := by
    apply ((frameExponential_contMDiff g o e).continuous_tangentMap le_rfl).comp
    exact (tangentBundleModelSpaceHomeomorph I4).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hv i).inner_bundle (hv j)

theorem frameExponentialJacobian_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponentialJacobian g o e) :=
  Real.continuous_sqrt.comp ((frameExponentialGram_continuous g o e).matrix_det)

theorem frameExponentialJacobian_nonneg (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : 0 ≤ frameExponentialJacobian g o e v :=
  Real.sqrt_nonneg _

theorem frameExponential_chart_backward (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (d : M) (v w : FourSpace)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    chartBackwardOperator d (chartAt FourSpace d (frameExponential g o e v))
      (fderiv ℝ (fun z => chartAt FourSpace d (frameExponential g o e z)) v w) =
        mfderiv I4 I4 (frameExponential g o e) v w := by
  have h := mfderiv_comp v
    ((mdifferentiable_chart (I := I4) d).mdifferentiableAt hd)
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero v)
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun z => chartAt FourSpace d (frameExponential g o e z)) v =
    (chartForwardOperator d (frameExponential g o e v)).comp
      (mfderiv I4 I4 (frameExponential g o e) v) at h
  rw [h]
  have hb := congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
    L (mfderiv I4 I4 (frameExponential g o e) v w))
      (chartBackward_forward d (frameExponential g o e v) hd)
  exact hb

private theorem euclideanMatrix_column (D : FourSpace →ₗ[ℝ] FourSpace) (j : Fin 4) :
    WithLp.toLp 2 (fun i => (Matrix.toEuclideanLin.symm D) i j) = D (coordinateVector j) := by
  have h := congrArg (fun L : FourSpace →ₗ[ℝ] FourSpace => L (coordinateVector j))
    (Matrix.toEuclideanLin.apply_symm_apply D)
  change WithLp.toLp 2 ((Matrix.toEuclideanLin.symm D) *ᵥ
    (Pi.single j 1 : Fin 4 → ℝ)) = D (coordinateVector j) at h
  rw [Matrix.mulVec_single_one] at h
  exact h

theorem frameExponentialJacobian_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (d : M) (v : FourSpace)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    frameExponentialJacobian g o e v =
      chartVolumeDensity g d (chartAt FourSpace d (frameExponential g o e v)) *
        |LinearMap.det (fderiv ℝ (fun z => chartAt FourSpace d
          (frameExponential g o e z)) v).toLinearMap| := by
  let D := fderiv ℝ (fun z => chartAt FourSpace d (frameExponential g o e z)) v
  let A : Mat4 := Matrix.toEuclideanLin.symm D.toLinearMap
  let G := metricInChart g d (chartAt FourSpace d (frameExponential g o e v))
  have hGram : frameExponentialGram g o e v = Aᵀ * (G * A) := by
    ext i j
    change _ = (fun k => A k i) ⬝ᵥ (G *ᵥ (fun k => A k j))
    have hp := metricInChart_pairing g d (chartAt FourSpace d (frameExponential g o e v))
      (fun k => A k i) (fun k => A k j)
    have hi := euclideanMatrix_column D.toLinearMap i
    have hj := euclideanMatrix_column D.toLinearMap j
    change WithLp.toLp 2 (fun k => A k i) = D (coordinateVector i) at hi
    change WithLp.toLp 2 (fun k => A k j) = D (coordinateVector j) at hj
    rw [hi, hj] at hp
    change (fun k => A k i) ⬝ᵥ (G *ᵥ (fun k => A k j)) =
      g.inner ((chartAt FourSpace d).symm (chartAt FourSpace d (frameExponential g o e v)))
        (chartBackwardOperator d (chartAt FourSpace d (frameExponential g o e v)) (D (coordinateVector i)))
        (chartBackwardOperator d (chartAt FourSpace d (frameExponential g o e v)) (D (coordinateVector j))) at hp
    rw [frameExponential_chart_backward g o e d v (coordinateVector i) hd,
      frameExponential_chart_backward g o e d v (coordinateVector j) hd,
      (chartAt FourSpace d).left_inv hd] at hp
    exact hp.symm
  have hdet : LinearMap.det D.toLinearMap = A.det := by
    rw [← Matrix.toEuclideanLin.apply_symm_apply D.toLinearMap, LinearMap.det_toLpLin 2]
  rw [show frameExponentialJacobian g o e v = Real.sqrt (frameExponentialGram g o e v).det from rfl,
    hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have halg : A.det * (G.det * A.det) = A.det ^ 2 * G.det := by ring
  rw [halg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  change |A.det| * Real.sqrt G.det = Real.sqrt G.det * |LinearMap.det D.toLinearMap|
  rw [hdet, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous local inverse branch cannot cross the uniform cut-radius
sphere while its actual endpoint stays strictly inside the distance ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exponential_log_norm_lt_along_curve (g : SmoothMetric M) (o : FrameOrientation g)
    (R : ℝ) (hcut : ∀ e ∈ o.positive, R ≤ actualCutTime g e)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (log : ℝ → FourSpace) (γ : ℝ → M) {a b : ℝ}
    (hlog : ContinuousOn log (Icc a b)) (hstart : ‖log a‖ < R)
    (hreal : ∀ s ∈ Icc a b, frameExponential g o e (log s) = γ s)
    (hdist : ∀ s ∈ Icc a b, metricDistance g e.base (γ s) < R) :
    ∀ s ∈ Icc a b, ‖log s‖ < R := by
  intro s hs
  by_contra hnot
  have hn : R ≤ ‖log s‖ := le_of_not_gt hnot
  have hc : ContinuousOn (fun t => ‖log t‖) (Icc a s) :=
    hlog.norm.mono (Icc_subset_Icc le_rfl hs.2)
  obtain ⟨r,hr,hrR⟩ := intermediate_value_Icc hs.1 hc ⟨hstart.le,hn⟩
  change ‖log r‖ = R at hrR
  have hrb : r ∈ Icc a b := ⟨hr.1,hr.2.trans hs.2⟩
  have hm := frameExponential_minimizing_of_cut_lower R hcut e he (log r) hrR.le
  rw [hreal r hrb,hrR] at hm
  exact (ne_of_lt (hdist r hrb)) hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous base curve has a local positive orthonormal frame lift
through any prescribed positive frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_moving_positive_frame (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (γ : ℝ → M)
    (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = e.base) :
    ∃ α : ℝ → FrameBundle g, ContinuousAt α 0 ∧ α 0 = e ∧
      (∀ s, (α s).base = γ s) ∧ ∀ᶠ s in 𝓝 (0 : ℝ), α s ∈ o.positive := by
  obtain ⟨S,hS,hpositive⟩ := exists_positive_localGramSection g o e.base
  let F := localGramSection g e.base S hS e.base
  have hF : F ∈ o.positive := hpositive.self_of_nhds
  obtain ⟨Q,hQ⟩ := positive_frames_relative_rotation g o F e hF he
    (localGramSection_base g e.base S hS e.base)
  let α : ℝ → FrameBundle g := fun s =>
    (localGramSection g e.base S hS (γ s)).rotate (orientedToOrthogonal Q)
  have hsection : ContinuousAt (fun s => localGramSection g e.base S hS (γ s)) 0 := by
    have hh : ContinuousAt (localGramSection g e.base S hS) (γ 0) := by
      rw [hγ0]; exact continuousAt_localGramSection g e.base S hS
    exact hh.comp hγ
  refine ⟨α,?_,?_,?_,?_⟩
  · exact (continuous_frameRotate g).continuousAt.comp
      (f := fun s => (localGramSection g e.base S hS (γ s),orientedToOrthogonal Q))
      (hsection.prodMk continuousAt_const)
  · change (localGramSection g e.base S hS (γ 0)).rotate (orientedToOrthogonal Q) = e
    rw [hγ0]
    exact hQ
  · intro s
    exact localGramSection_base g e.base S hS (γ s)
  · have hp : ∀ᶠ s in 𝓝 (0 : ℝ), localGramSection g e.base S hS (γ s) ∈ o.positive := by
      have hh : ∀ᶠ x in 𝓝 (γ 0), localGramSection g e.base S hS x ∈ o.positive := by
        rw [hγ0]; exact hpositive
      exact hγ hh
    filter_upwards [hp] with s hs
    exact frameRotate_oriented_positive o _ hs Q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pushforward of the actual exponential Jacobian on minimizing
vectors dominates Riemannian volume. The proof is local in output charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [MeasurableSpace M] [BorelSpace M]

def chartCoordinateExtension (c : M) : M → FourSpace := by
  classical
  exact (chartAt FourSpace c).source.piecewise (chartAt FourSpace c) (fun _ => 0)

theorem chartCoordinateExtension_measurable (c : M) : Measurable (chartCoordinateExtension c) := by
  classical
  exact (chartAt FourSpace c).continuousOn.measurable_piecewise continuousOn_const
    (chartAt FourSpace c).open_source.measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartCoordinateExtension_eq (c x : M) (hx : x ∈ (chartAt FourSpace c).source) :
    chartCoordinateExtension c x = chartAt FourSpace c x := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

variable [IsManifold I4 ∞ M]

def chartWeight (g : SmoothMetric M) (c : M) : FourSpace → ℝ≥0∞ := by
  classical
  exact (chartAt FourSpace c).target.piecewise
    (fun z => ENNReal.ofReal (chartVolumeDensity g c z)) (fun _ => 0)

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartWeight_eq (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    chartWeight g c z = ENNReal.ofReal (chartVolumeDensity g c z) := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartWeight_measurable (g : SmoothMetric M) (c : M) : Measurable (chartWeight g c) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  exact (ENNReal.continuous_ofReal.continuousAt.comp
    (chartVolumeDensity_contDiffAt g c z hz).continuousAt).continuousWithinAt

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def exponentialAreaMeasure (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Measure M :=
  riemannianChartFactor • Measure.map (frameExponential g o e)
    ((volume.restrict (actualMinimizingTangentDomain g o e)).withDensity
      (fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)))

omit [PreconnectedSpace M] in
theorem exponentialAreaMeasure_apply (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (A : Set M) (hA : MeasurableSet A) :
    exponentialAreaMeasure g o e A = riemannianChartFactor *
      ∫⁻ v in (frameExponential g o e) ⁻¹' A ∩ actualMinimizingTangentDomain g o e,
        ENNReal.ofReal (frameExponentialJacobian g o e v) := by
  rw [exponentialAreaMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (frameExponential_continuous g o e).measurable hA,
    withDensity_apply _ ((frameExponential_continuous g o e).measurable hA),
    Measure.restrict_restrict ((frameExponential_continuous g o e).measurable hA)]

theorem volumeMeasure_le_exponentialAreaMeasure_on_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (c : M) (A : Set M) (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt FourSpace c).source) :
    volumeMeasure g A ≤ exponentialAreaMeasure g o e A := by
  let s := (frameExponential g o e) ⁻¹' A ∩ actualMinimizingTangentDomain g o e
  let F := fun v => chartCoordinateExtension c (frameExponential g o e v)
  let D := fun v => fderiv ℝ (fun w => chartAt FourSpace c (frameExponential g o e w)) v
  have hs : MeasurableSet s := ((frameExponential_continuous g o e).measurable hA).inter
    (actualMinimizingTangentDomain_closed g o e).measurableSet
  have hF : Measurable F := (chartCoordinateExtension_measurable c).comp
    (frameExponential_continuous g o e).measurable
  have hD : ∀ v ∈ s, HasFDerivWithinAt F (D v) s v := by
    intro v hv
    have hx : frameExponential g o e v ∈ (chartAt FourSpace c).source := hAc hv.1
    have hd := (frameExponential_chart_contDiffAt g o c e v hx).differentiableAt (by simp)
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hx)
    have heq : F =ᶠ[𝓝 v] (fun w => chartAt FourSpace c (frameExponential g o e w)) := by
      filter_upwards [hnear] with w hw
      exact chartCoordinateExtension_eq c _ hw
    exact (hd.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have himage : F '' s = (chartAt FourSpace c) '' A := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨frameExponential g o e v, hv.1, (chartCoordinateExtension_eq c _ (hAc hv.1)).symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hximage : x ∈ frameExponential g o e '' actualMinimizingTangentDomain g o e := by
        rw [actualMinimizingTangentDomain_image g o hRic e he]
        trivial
      obtain ⟨v, hv, hvx⟩ := hximage
      refine ⟨v, ⟨by change frameExponential g o e v ∈ A; rwa [hvx], hv⟩, ?_⟩
      dsimp [F]
      rw [hvx, chartCoordinateExtension_eq c x (hAc hx)]
  have hb := weighted_area_inequality hs hF hD (chartWeight g c) (chartWeight_measurable g c)
  rw [himage] at hb
  have hleft : (∫⁻ z in (chartAt FourSpace c) '' A, chartWeight g c z) =
      ∫⁻ z in (chartAt FourSpace c) '' A, ENNReal.ofReal (chartVolumeDensity g c z) := by
    apply setLIntegral_congr_fun (chart_image_measurable c A hA hAc)
    rintro z ⟨x, hx, rfl⟩
    exact chartWeight_eq g c _ ((chartAt FourSpace c).map_source (hAc hx))
  have hright : (∫⁻ v in s, ENNReal.ofReal |(D v).det| * chartWeight g c (F v)) =
      ∫⁻ v in s, ENNReal.ofReal (frameExponentialJacobian g o e v) := by
    apply setLIntegral_congr_fun hs
    intro v hv
    have hx : frameExponential g o e v ∈ (chartAt FourSpace c).source := hAc hv.1
    dsimp [F, D]
    rw [chartCoordinateExtension_eq c _ hx,
      chartWeight_eq g c _ ((chartAt FourSpace c).map_source hx),
      ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
      ← frameExponentialJacobian_chart g o e c v hx]
  rw [hleft, hright] at hb
  rw [volumeMeasure_chart_image g c A hA hAc, exponentialAreaMeasure_apply g o e A hA]
  exact mul_le_mul_right hb riemannianChartFactor

variable [SecondCountableTopology M]

theorem volumeMeasure_le_exponentialAreaMeasure (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) : volumeMeasure g ≤ exponentialAreaMeasure g o e := by
  have h := measure_restrict_le_of_local (volumeMeasure g) (exponentialAreaMeasure g o e)
    univ isOpen_univ (fun x _ => ?_)
  · simpa only [Measure.restrict_univ] using h
  refine ⟨(chartAt FourSpace x).source, (chartAt FourSpace x).open_source,
    mem_chart_source FourSpace x, subset_univ _, ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact volumeMeasure_le_exponentialAreaMeasure_on_chart g o hRic e he x
    (A ∩ (chartAt FourSpace x).source) (hA.inter (chartAt FourSpace x).open_source.measurableSet)
    inter_subset_right

theorem volumeMeasure_le_integral_exponentialJacobian (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      ∫⁻ v in actualMinimizingTangentDomain g o e,
        ENNReal.ofReal (frameExponentialJacobian g o e v) := by
  have h := volumeMeasure_le_exponentialAreaMeasure g o hRic e he univ
  rwa [exponentialAreaMeasure_apply g o e univ MeasurableSet.univ,
    preimage_univ, univ_inter] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two nonconjugate branches at a globally shortest cut point have
opposite terminal velocities. Both branches are actual exponential inverses. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem minimal_cut_terminal_opposite (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (hcut : ∀ e ∈ o.positive, t ≤ actualCutTime g e)
    (e f : FrameBundle g) (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (hbase : e.base = f.base)
    (hne : e.frame.vector 0 ≠ f.frame.vector 0)
    (hend : frameGeodesic g 0 e t = frameGeodesic g 0 f t)
    (hte : t < actualFirstConjugateTime g hRic e)
    (htf : t < actualFirstConjugateTime g hRic f) :
    (parallelFrameFlowMap g 0 t e).frame.vector 0 =
      -(parallelFrameFlowMap g 0 t f).frame.vector 0 := by
  let E := parallelFrameFlowMap g 0 t e
  let F := parallelFrameFlowMap g 0 t f
  let d := E.base
  have hFd : F.base = d := hend.symm
  let u := E.frame.vector 0
  let v := F.frame.vector 0
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner d
  by_contra hopposite
  have hsum : u + v ≠ 0 := by
    intro h
    apply hopposite
    exact eq_neg_of_add_eq_zero_left h
  have huu : B u u = 1 := E.frame.inner_vector_self 0
  have hvv : B v v = 1 := by
    change g.inner d (F.frame.vector 0) (F.frame.vector 0) = 1
    rw [← hFd]
    exact F.frame.inner_vector_self 0
  have hsym : B v u = B u v := g.symm d v u
  have hpositive : 0 < B (u + v) (u + v) := g.pos d (u + v) hsum
  simp only [map_add,add_apply] at hpositive
  rw [huu,hvv,hsym] at hpositive
  let a : FourSpace := -(u + v)
  have hnegU : g.inner d u a < 0 := by
    dsimp [a]
    change B u (-(u + v)) < 0
    simp only [map_neg,map_add]
    rw [huu]
    linarith
  have hnegV : g.inner d v a < 0 := by
    dsimp [a]
    change B v (-(u + v)) < 0
    simp only [map_neg,map_add]
    rw [hvv,hsym]
    linarith
  obtain ⟨C,hC,hc,hCd⟩ := exists_exponential_log_center g o hRic e he d t ht hte rfl
  obtain ⟨D,hD,hd,hDd⟩ := exists_exponential_log_center g o hRic f hf d t ht htf hFd
  let z := chartAt FourSpace d d
  let x : ℝ → FourSpace := fun ε => C.symm (z + ε • a)
  let y : ℝ → FourSpace := fun ε => D.symm (z + ε • a)
  have hCv : C (t • coordinateVector 0) = z := by
    rw [hC]
    change chartAt FourSpace d (frameExponential g o e (t • coordinateVector 0)) = z
    rw [frameExponential_first_ray g o e he t ht]
  have hDv : D (t • coordinateVector 0) = z := by
    rw [hD]
    change chartAt FourSpace d (frameExponential g o f (t • coordinateVector 0)) = z
    rw [frameExponential_first_ray g o f hf t ht,hFd]
  have hzC : z ∈ C.target := hCv ▸ C.map_source hc
  have hzD : z ∈ D.target := hDv ▸ D.map_source hd
  have hx0 : x 0 = t • coordinateVector 0 := by
    dsimp [x]; rw [zero_smul,add_zero,← hCv]; exact C.left_inv hc
  have hy0 : y 0 = t • coordinateVector 0 := by
    dsimp [y]; rw [zero_smul,add_zero,← hDv]; exact D.left_inv hd
  have hnorm : ‖(t • coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hi : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hi,mul_one]
  have hdx : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x ε‖ ^ 2 < t ^ 2 := by
    have hh := scalar_decreases_right (hCd a) (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht) hnegU)
    change ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x ε‖ ^ 2 < ‖x 0‖ ^ 2 at hh
    simpa only [hx0,hnorm] using hh
  have hdy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε‖ ^ 2 < t ^ 2 := by
    have hh := scalar_decreases_right (hDd a) (mul_neg_of_pos_of_neg (mul_pos (by norm_num) ht) hnegV)
    change ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε‖ ^ 2 < ‖y 0‖ ^ 2 at hh
    simpa only [hy0,hnorm] using hh
  have hline : Continuous (fun ε : ℝ => z + ε • a) := continuous_const.add (continuous_id.smul continuous_const)
  have hxcont : ContinuousAt x 0 := by
    have hcc : ContinuousAt (C.symm : FourSpace → FourSpace) (z + (0 : ℝ) • a) := by
      simpa only [zero_smul,add_zero] using C.continuousAt_symm hzC
    have hh := hcc.comp (x := 0) hline.continuousAt
    simpa only [Function.comp_def,x] using! hh
  have hycont : ContinuousAt y 0 := by
    have hdc : ContinuousAt (D.symm : FourSpace → FourSpace) (z + (0 : ℝ) • a) := by
      simpa only [zero_smul,add_zero] using D.continuousAt_symm hzD
    have hh := hdc.comp (x := 0) hline.continuousAt
    simpa only [Function.comp_def,y] using! hh
  have hpointx : frameExponential g o e (x 0) = d := by
    rw [hx0,frameExponential_first_ray g o e he t ht]
  have hpointy : frameExponential g o f (y 0) = d := by
    rw [hy0,frameExponential_first_ray g o f hf t ht]; exact hFd
  have hnearx : ∀ᶠ ε in 𝓝 (0 : ℝ), frameExponential g o e (x ε) ∈ (chartAt FourSpace d).source :=
    ((frameExponential_continuous g o e).continuousAt.comp hxcont).preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds (hpointx ▸ mem_chart_source FourSpace d))
  have hneary : ∀ᶠ ε in 𝓝 (0 : ℝ), frameExponential g o f (y ε) ∈ (chartAt FourSpace d).source :=
    ((frameExponential_continuous g o f).continuousAt.comp hycont).preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds (hpointy ▸ mem_chart_source FourSpace d))
  have htargets : ∀ᶠ ε in 𝓝 (0 : ℝ), z + ε • a ∈ C.target ∩ D.target := by
    have h0 : z + (0 : ℝ) • a ∈ C.target ∩ D.target := by simpa using And.intro hzC hzD
    exact hline.continuousAt.preimage_mem_nhds ((C.open_target.inter D.open_target).mem_nhds h0)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), e.frame.map (x ε) = f.frame.map (y ε) := by
    filter_upwards [hdx,hdy,hnearx.filter_mono nhdsWithin_le_nhds,
      hneary.filter_mono nhdsWithin_le_nhds,htargets.filter_mono nhdsWithin_le_nhds]
      with ε hx hy hxs hys htg
    have hxlt : ‖x ε‖ < t := by nlinarith [norm_nonneg (x ε)]
    have hylt : ‖y ε‖ < t := by nlinarith [norm_nonneg (y ε)]
    apply uniform_cut_initial_vector_unique g o t hcut e f he hf hbase (x ε) (y ε) hxlt hylt
    apply (chartAt FourSpace d).injOn hxs hys
    calc
      _ = C (x ε) := (congrFun hC (x ε)).symm
      _ = z + ε • a := C.right_inv htg.1
      _ = D (y ε) := (D.right_inv htg.2).symm
      _ = _ := congrFun hD (y ε)
  have hl : Tendsto (fun ε => e.frame.map (x ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (e.frame.map (t • coordinateVector 0))) := by
    rw [← hx0]
    exact ((e.frame.map.toContinuousLinearMap.continuous.continuousAt).comp hxcont).tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun ε => f.frame.map (y ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (f.frame.map (t • coordinateVector 0))) := by
    rw [← hy0]
    exact ((f.frame.map.toContinuousLinearMap.continuous.continuousAt).comp hycont).tendsto.mono_left nhdsWithin_le_nhds
  have hsame := tendsto_nhds_unique (hl.congr' heq) hr
  have hvectors := congrArg (fun w : FourSpace => t⁻¹ • w) hsame
  apply hne
  simpa only [map_smul,smul_smul,inv_mul_cancel₀ ht.ne',one_smul,
    e.frame.map_coordinateVector,f.frame.map_coordinateVector] using hvectors

end
end PositiveEinsteinFour.Geometry
end


section

/-! Two short inverse branches cannot approach different initial vectors
at a common cut radius. The comparison is made in a fixed actual chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Matrix
open scoped Manifold ContDiff _root_.Topology BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [T3Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem moving_frame_chart_vector_continuousAt (g : SmoothMetric M) (c : M)
    (α : ℝ → FrameBundle g) (u : ℝ → FourSpace)
    (hα : ContinuousAt α 0) (hu : ContinuousAt u 0)
    (hc : (α 0).base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (fun s => WithLp.toLp 2
      (frameChartMatrix g c (α s) *ᵥ WithLp.ofLp (u s))) 0 := by
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  change Tendsto (fun s => ∑ j, frameChartMatrix g c (α s) i j * (u s) j)
    (𝓝 0) (𝓝 (∑ j, frameChartMatrix g c (α 0) i j * (u 0) j))
  apply tendsto_finsetSum
  intro j _
  exact ((frameChartMatrix_continuousAt g c (α 0) hc i j).comp hα).mul
    ((continuous_apply j).continuousAt.comp ((PiLp.continuous_ofLp 2 _).continuousAt.comp hu))

theorem short_inverse_branches_limit (g : SmoothMetric M) (o : FrameOrientation g)
    (c : ℝ) (hcut : ∀ e ∈ o.positive, c ≤ actualCutTime g e)
    (e f : FrameBundle g) (hbase : e.base = f.base)
    (α β : ℝ → FrameBundle g) (u v : ℝ → FourSpace)
    (hα : ContinuousAt α 0) (hβ : ContinuousAt β 0)
    (hu : ContinuousAt u 0) (hv : ContinuousAt v 0)
    (hα0 : α 0 = e) (hβ0 : β 0 = f)
    (hshort : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      α s ∈ o.positive ∧ β s ∈ o.positive ∧ (α s).base = (β s).base ∧
      ‖u s‖ < c ∧ ‖v s‖ < c ∧
      frameExponential g o (α s) (u s) = frameExponential g o (β s) (v s)) :
    e.frame.map (u 0) = f.frame.map (v 0) := by
  have hec : (α 0).base ∈ (chartAt FourSpace e.base).source := by
    rw [hα0]; exact mem_chart_source FourSpace e.base
  have hfc : (β 0).base ∈ (chartAt FourSpace e.base).source := by
    rw [hβ0,← hbase]; exact mem_chart_source FourSpace e.base
  let A := fun s => WithLp.toLp 2 (frameChartMatrix g e.base (α s) *ᵥ WithLp.ofLp (u s))
  let B := fun s => WithLp.toLp 2 (frameChartMatrix g e.base (β s) *ᵥ WithLp.ofLp (v s))
  have hA := moving_frame_chart_vector_continuousAt g e.base α u hα hu hec
  have hB := moving_frame_chart_vector_continuousAt g e.base β v hβ hv hfc
  have hnearA : ∀ᶠ s in 𝓝 (0 : ℝ), (α s).base ∈ (chartAt FourSpace e.base).source :=
    (continuous_frameBase g).continuousAt.comp hα |>.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_source.mem_nhds hec)
  have hnearB : ∀ᶠ s in 𝓝 (0 : ℝ), (β s).base ∈ (chartAt FourSpace e.base).source :=
    (continuous_frameBase g).continuousAt.comp hβ |>.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_source.mem_nhds hfc)
  have heq : A =ᶠ[𝓝[>] (0 : ℝ)] B := by
    filter_upwards [hshort,hnearA.filter_mono nhdsWithin_le_nhds,
      hnearB.filter_mono nhdsWithin_le_nhds] with s hs hsa hsb
    have hvec := uniform_cut_initial_vector_unique g o c hcut (α s) (β s)
      hs.1 hs.2.1 hs.2.2.1 (u s) (v s) hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2
    dsimp [A,B]
    rw [frameChart_map g e.base _ hsa,frameChart_map g e.base _ hsb]
    have hOp : (chartForwardOperator e.base (α s).base : FourSpace →L[ℝ] FourSpace) =
        chartForwardOperator e.base (β s).base := congrArg
          (fun x => (chartForwardOperator e.base x : FourSpace →L[ℝ] FourSpace)) hs.2.2.1
    rw [hOp,hvec]
  have hzero : A 0 = B 0 := tendsto_nhds_unique
    (hA.tendsto.mono_left nhdsWithin_le_nhds)
    ((hB.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  dsimp [A,B] at hzero
  rw [frameChart_map g e.base _ hec,frameChart_map g e.base _ hfc,hα0,hβ0] at hzero
  have hOp : (chartForwardOperator e.base f.base : FourSpace →L[ℝ] FourSpace) =
      ContinuousLinearMap.id ℝ FourSpace := by
    rw [← hbase,chartForwardOperator_center]
  rw [hOp,chartForwardOperator_center] at hzero
  exact hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! A short actual curve near a nonconjugate radial segment ends in the
corresponding short inverse branch. The proof uses compactness only on
a final subinterval and the actual cut-radius barrier. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem short_variation_log_norm_lt (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (htc : t < actualFirstConjugateTime g hRic e)
    (hcut : ∀ f ∈ o.positive, t ≤ actualCutTime g f)
    (U : Set (FrameBundle g × M)) (hU : IsOpen U)
    (heU : (e,frameGeodesic g 0 e t) ∈ U)
    (log : FrameBundle g × M → FourSpace) (hlog : ContinuousOn log U)
    (hlog0 : log (e,frameGeodesic g 0 e t) = t • coordinateVector 0)
    (hreal : ∀ p ∈ U, frameExponential g o p.1 (log p) = p.2)
    (a : ℝ) (ha : 0 ≤ a) (hat : a < t)
    (α : ℝ → FrameBundle g) (hα : ContinuousAt α 0) (hα0 : α 0 = e)
    (hαpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), α ε ∈ o.positive)
    (γ : ℝ → ℝ → M)
    (href : ∀ r ∈ Icc a t, γ 0 r = frameGeodesic g 0 e r)
    (hjoint : ∀ r ∈ Icc a t, ContinuousAt (fun p : ℝ × ℝ => γ p.1 p.2) (0,r))
    (hcont : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (γ ε) (Icc a t))
    (hshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc a t,
      metricDistance g (α ε).base (γ ε r) < t) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖log (α ε,γ ε t)‖ < t := by
  have hrad := joint_exponential_log_radial_eventually g o hRic e he t ht htc U hU heU
    log hlog hlog0 hreal
  have hcurve : Continuous (fun r => (e,frameGeodesic g 0 e r)) :=
    continuous_const.prodMk (frameGeodesic_contMDiff g 0 e).continuous
  have hmem : ∀ᶠ r in 𝓝 t, (e,frameGeodesic g 0 e r) ∈ U :=
    hcurve.continuousAt.preimage_mem_nhds (hU.mem_nhds heU)
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp (hmem.and hrad)
  let d := min (δ/2) ((t-a)/2)
  let b := t-d
  have hd : 0 < d := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hat))
  have hb : a < b := by dsimp [b]; have := min_le_right (δ/2) ((t-a)/2); dsimp [d] at *; linarith
  have hbt : b < t := by dsimp [b]; linarith
  have hgood (r : ℝ) (hr : r ∈ Icc b t) :
      (e,frameGeodesic g 0 e r) ∈ U ∧ log (e,frameGeodesic g 0 e r) = r • coordinateVector 0 := by
    apply hδball
    rw [mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hr.2)]
    have hsmall := min_le_left (δ/2) ((t-a)/2)
    have hrleft : t-d ≤ r := hr.1
    dsimp [d] at *
    linarith [hrleft]
  have hba : Icc b t ⊆ Icc a t := Icc_subset_Icc hb.le le_rfl
  let H : ℝ × ℝ → FrameBundle g × M := fun p => (α p.1,γ p.1 p.2)
  have hH (r : ℝ) (hr : r ∈ Icc b t) : ContinuousAt H (0,r) :=
    (hα.comp (x := (0,r)) (f := Prod.fst) continuous_fst.continuousAt).prodMk (hjoint r (hba hr))
  have hH0 (r : ℝ) (hr : r ∈ Icc b t) : H (0,r) = (e,frameGeodesic g 0 e r) := by
    change (α 0,γ 0 r) = _
    rw [hα0,href r (hba hr)]
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ r ∈ Icc b t, H (ε,r) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    exact (hH r hr).preimage_mem_nhds (hU.mem_nhds ((hH0 r hr).symm ▸ (hgood r hr).1))
  have hbmem : b ∈ Icc b t := ⟨le_rfl,hbt.le⟩
  have hbH : H (0,b) ∈ U := (hH0 b hbmem).symm ▸ (hgood b hbmem).1
  have hstart0 : ‖log (H (0,b))‖ < t := by
    rw [hH0 b hbmem,(hgood b hbmem).2,norm_smul,Real.norm_eq_abs,abs_of_pos (ha.trans_lt hb)]
    have hunit : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
    rw [hunit,mul_one]
    exact hbt
  have hstart : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖log (H (ε,b))‖ < t := by
    have hc := ((hlog.continuousAt (hU.mem_nhds hbH)).comp (hH b hbmem)).norm
    have hε : ContinuousAt (fun ε : ℝ => ‖log (H (ε,b))‖) 0 :=
      hc.comp (x := 0) (f := fun ε : ℝ => (ε,b)) (continuous_id.prodMk continuous_const).continuousAt
    exact hε.preimage_mem_nhds (isOpen_Iio.mem_nhds hstart0)
  filter_upwards [hαpos,hcont,hshort,hnear.filter_mono nhdsWithin_le_nhds,
    hstart.filter_mono nhdsWithin_le_nhds] with ε hpos hγε hdist hUε hstartε
  have hcomp : ContinuousOn (fun r => log (H (ε,r))) (Icc b t) := by
    have hp : ContinuousOn (fun r => (α ε,γ ε r)) (Icc b t) :=
      (continuousOn_const (c := α ε)).prodMk (hγε.mono hba)
    exact hlog.comp hp (fun r hr => hUε r hr)
  exact exponential_log_norm_lt_along_curve g o t hcut (α ε) hpos
    (fun r => log (H (ε,r))) (γ ε) hcomp hstartε
    (fun r hr => hreal _ (hUε r hr)) (fun r hr => hdist r (hba hr)) t ⟨hbt.le,le_rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The reverse area inequality on an injective exponential ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [MeasurableSpace M] [BorelSpace M] [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def exponentialBallAreaMeasure (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) : Measure M :=
  riemannianChartFactor • Measure.map (frameExponential g o e)
    ((volume.restrict (ball 0 r)).withDensity
      (fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)))

theorem exponentialBallAreaMeasure_apply (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (A : Set M) (hA : MeasurableSet A) :
    exponentialBallAreaMeasure g o e r A = riemannianChartFactor *
      ∫⁻ v in (frameExponential g o e) ⁻¹' A ∩ ball 0 r,
        ENNReal.ofReal (frameExponentialJacobian g o e v) := by
  rw [exponentialBallAreaMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (frameExponential_continuous g o e).measurable hA,
    withDensity_apply _ ((frameExponential_continuous g o e).measurable hA),
    Measure.restrict_restrict ((frameExponential_continuous g o e).measurable hA)]

theorem exponentialBallAreaMeasure_le_on_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (hinj : InjOn (frameExponential g o e) (ball 0 r))
    (c : M) (A : Set M) (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt FourSpace c).source) :
    exponentialBallAreaMeasure g o e r A ≤ volumeMeasure g A := by
  let s := (frameExponential g o e) ⁻¹' A ∩ ball 0 r
  let F := fun v => chartCoordinateExtension c (frameExponential g o e v)
  let D := fun v => fderiv ℝ (fun w => chartAt FourSpace c (frameExponential g o e w)) v
  have hs : MeasurableSet s := ((frameExponential_continuous g o e).measurable hA).inter
    isOpen_ball.measurableSet
  have hD : ∀ v ∈ s, HasFDerivWithinAt F (D v) s v := by
    intro v hv
    have hx := hAc hv.1
    have hd := (frameExponential_chart_contDiffAt g o c e v hx).differentiableAt (by simp)
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hx)
    have heq : F =ᶠ[𝓝 v] (fun w => chartAt FourSpace c (frameExponential g o e w)) := by
      filter_upwards [hnear] with w hw
      exact chartCoordinateExtension_eq c _ hw
    exact (hd.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have hF : InjOn F s := by
    intro v hv w hw heq
    apply hinj hv.2 hw.2
    apply (chartAt FourSpace c).injOn (hAc hv.1) (hAc hw.1)
    simpa only [F, chartCoordinateExtension_eq c _ (hAc hv.1),
      chartCoordinateExtension_eq c _ (hAc hw.1)] using heq
  have himage : F '' s ⊆ (chartAt FourSpace c) '' A := by
    rintro z ⟨v,hv,rfl⟩
    exact ⟨_,hv.1,(chartCoordinateExtension_eq c _ (hAc hv.1)).symm⟩
  have hb := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hD hF (chartWeight g c)
  have hle := lintegral_mono_set (μ := volume) (f := chartWeight g c) himage
  rw [hb] at hle
  have hleft : (∫⁻ z in (chartAt FourSpace c) '' A, chartWeight g c z) =
      ∫⁻ z in (chartAt FourSpace c) '' A, ENNReal.ofReal (chartVolumeDensity g c z) := by
    apply setLIntegral_congr_fun (chart_image_measurable c A hA hAc)
    rintro z ⟨x,hx,rfl⟩
    exact chartWeight_eq g c _ ((chartAt FourSpace c).map_source (hAc hx))
  have hright : (∫⁻ v in s, ENNReal.ofReal |(D v).det| * chartWeight g c (F v)) =
      ∫⁻ v in s, ENNReal.ofReal (frameExponentialJacobian g o e v) := by
    apply setLIntegral_congr_fun hs
    intro v hv
    have hx := hAc hv.1
    dsimp [F,D]
    rw [chartCoordinateExtension_eq c _ hx,
      chartWeight_eq g c _ ((chartAt FourSpace c).map_source hx),
      ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
      ← frameExponentialJacobian_chart g o e c v hx]
  rw [hleft, hright] at hle
  rw [exponentialBallAreaMeasure_apply g o e r A hA, volumeMeasure_chart_image g c A hA hAc]
  exact mul_le_mul_right hle riemannianChartFactor

variable [SecondCountableTopology M]

theorem exponentialBallAreaMeasure_le (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (hinj : InjOn (frameExponential g o e) (ball 0 r)) :
    exponentialBallAreaMeasure g o e r ≤ volumeMeasure g := by
  have h := measure_restrict_le_of_local (exponentialBallAreaMeasure g o e r)
    (volumeMeasure g) univ isOpen_univ (fun x _ => ?_)
  · simpa only [Measure.restrict_univ] using h
  refine ⟨(chartAt FourSpace x).source, (chartAt FourSpace x).open_source,
    mem_chart_source FourSpace x, subset_univ _, ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact exponentialBallAreaMeasure_le_on_chart g o e r hinj x
    (A ∩ (chartAt FourSpace x).source) (hA.inter (chartAt FourSpace x).open_source.measurableSet)
    inter_subset_right

theorem exponential_ball_integral_le_volume (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) (hinj : InjOn (frameExponential g o e) (ball 0 r)) :
    riemannianChartFactor * (∫⁻ v in ball 0 r,
      ENNReal.ofReal (frameExponentialJacobian g o e v)) ≤ volumeMeasure g univ := by
  have h := exponentialBallAreaMeasure_le g o e r hinj univ
  rwa [exponentialBallAreaMeasure_apply g o e r univ MeasurableSet.univ,
    preimage_univ, univ_inter] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Polar coordinates for the actual minimizing-domain Jacobian integral.
The radial cutoff is the proved cut time, not a supplied geometric domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponentialJacobian_direction (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (r : ℝ) (hr : 0 < r) :
    frameExponentialJacobian g o e (r • q.val) =
      |((actualJacobiSolution g hRic
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r).det / r ^ 3| := by
  let c := frameExponential g o e (r • q.val)
  rw [frameExponentialJacobian_chart g o e c (r • q.val) (mem_chart_source FourSpace c)]
  exact frameExponential_metric_jacobian_direction g o hRic e he q c r hr
    (mem_chart_source FourSpace c)

variable [PreconnectedSpace M]

theorem minimizing_exponential_integral_polar (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    (∫⁻ v in actualMinimizingTangentDomain g o e,
      ENNReal.ofReal (frameExponentialJacobian g o e v)) =
    ∫⁻ p : Directions × Ioi (0 : ℝ),
      (if p.2.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1))) then
        ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))).J p.2.val).det /
            p.2.val ^ 3| else 0)
      ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) := by
  classical
  let S := actualMinimizingTangentDomain g o e
  let J := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)
  have hS : MeasurableSet S := (actualMinimizingTangentDomain_closed g o e).measurableSet
  have hJ : Measurable J := (ENNReal.continuous_ofReal.comp
    (frameExponentialJacobian_continuous g o e)).measurable
  have h := euclideanPolarReconstruction_measurePreserving.lintegral_comp (hJ.indicator hS)
  calc
    _ = ∫⁻ v, S.indicator J v := (lintegral_indicator hS J).symm
    _ = ∫⁻ p : Directions × Ioi (0 : ℝ), S.indicator J (euclideanPolarReconstruction p)
        ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) := h.symm
    _ = _ := by
      apply lintegral_congr
      intro p
      have hiff := actualMinimizingTangentDomain_ray_iff g o e he p.1 p.2.val p.2.property.le
      by_cases hc : p.2.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))
      · have hm : euclideanPolarReconstruction p ∈ S := hiff.mpr hc
        rw [ite_eq_left hc, Set.indicator_of_mem hm]
        exact congrArg ENNReal.ofReal (frameExponentialJacobian_direction g o hRic e he
          p.1 p.2.val p.2.property)
      · have hm : euclideanPolarReconstruction p ∉ S := fun hh => hc (hiff.mp hh)
        rw [ite_eq_right hc, Set.indicator_of_notMem hm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual parallel normal shortening produces a short inverse-exponential
branch with the prescribed moving endpoints. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators
noncomputable section

theorem affinePartitionTime_strictMono {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    StrictMono (affinePartitionTime 0 b n) := by
  intro i j hij
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hijr : (i : ℝ) < j := by exact_mod_cast hij
  simp only [affinePartitionTime,sub_zero,zero_add]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hijr hb) hnr

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_parallel_short_branch (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e)
    (hcut : ∀ f ∈ o.positive, t ≤ actualCutTime g f)
    (a : Fin 3 → ℝ) (ha : a ≠ 0) :
    ∃ (α : ℝ → FrameBundle g) (u : ℝ → FourSpace),
      ContinuousAt α 0 ∧ ContinuousAt u 0 ∧ α 0 = e ∧ u 0 = t • coordinateVector 0 ∧
      (∀ ε, (α ε).base = normalQuadraticEndpointCurve g e a ε) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), α ε ∈ o.positive ∧ ‖u ε‖ < t ∧
        frameExponential g o (α ε) (u ε) =
          normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 t e) a ε := by
  obtain ⟨n,hn,C,hC⟩ := exists_finite_curve_chart_partition (frameGeodesic g 0 e)
    (frameGeodesic_contMDiff g 0 e).continuous 0 t ht
  let T := affinePartitionTime 0 t n
  have hT0 : T 0 = 0 := affinePartitionTime_zero 0 t n
  have hTn : T n = t := affinePartitionTime_last 0 t n hn
  have hTmono : StrictMono T := affinePartitionTime_strictMono ht hn
  have hT (i : ℕ) (_ : i < n) : T i < T (i+1) := hTmono (Nat.lt_succ_self i)
  obtain ⟨γ,href,hjoint,hshort⟩ := exists_finite_parallel_normal_shortening
    g hRic hpositive e n hn T C a ha hT hC
  obtain ⟨α,hα,hα0,hbase,hαpos⟩ := exists_moving_positive_frame g o e he
    (normalQuadraticEndpointCurve g e a)
    (normalQuadraticEndpointCurve_continuousAt g e a)
    (normalQuadraticEndpointCurve_zero g e a)
  obtain ⟨U,hU,heU,log,hlog,hlog0,hreal⟩ :=
    exists_joint_exponential_log g o hRic e he t ht htc
  let k := n-1
  have hk : k < n := Nat.sub_lt hn (by omega)
  have hkn : k+1=n := by dsimp [k]; omega
  have hTk : 0 ≤ T k := by rw [← hT0]; exact hTmono.monotone (Nat.zero_le k)
  have hTkt : T k < t := by rw [← hTn]; exact hTmono hk
  have hlastref (r : ℝ) (hr : r ∈ Icc (T k) t) : γ k 0 r = frameGeodesic g 0 e r := by
    apply href k hk
    simpa only [hkn,hTn] using hr
  have hlastjoint (r : ℝ) (hr : r ∈ Icc (T k) t) :
      ContinuousAt (fun p : ℝ × ℝ => γ k p.1 p.2) (0,r) := by
    apply hjoint k hk
    simpa only [hkn,hTn] using hr
  have hlast : ContinuousAt (fun ε : ℝ => γ k ε t) 0 :=
    (hlastjoint t ⟨hTkt.le,le_rfl⟩).comp (f := fun ε : ℝ => (ε,t))
      (continuous_id.prodMk continuous_const).continuousAt
  let H : ℝ → FrameBundle g × M := fun ε => (α ε,γ k ε t)
  have hH : ContinuousAt H 0 := hα.prodMk hlast
  have hH0 : H 0 = (e,frameGeodesic g 0 e t) := by
    dsimp [H]; rw [hα0,hlastref t ⟨hTkt.le,le_rfl⟩]
  have hHU : H 0 ∈ U := hH0.symm ▸ heU
  let u : ℝ → FourSpace := fun ε => log (H ε)
  have hu : ContinuousAt u 0 := (hlog.continuousAt (hU.mem_nhds hHU)).comp hH
  have hu0 : u 0 = t • coordinateVector 0 := by dsimp [u]; rw [hH0,hlog0]
  have hcont : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (γ k ε) (Icc (T k) t) := by
    filter_upwards [hshort] with ε hε
    simpa only [hkn,hTn] using (hε.1 k hk).continuousOn
  have hdist : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ r ∈ Icc (T k) t,
      metricDistance g (α ε).base (γ k ε r) < t := by
    filter_upwards [hshort] with ε hε r hr
    let p := fun i => normalQuadraticEndpointCurve g (parallelFrameFlowMap g 0 (T i) e) a ε
    have hleft (i : ℕ) (hi : i < n) : γ i ε (T i) = p i := (hε.2.1 i hi).1
    have hright (i : ℕ) (hi : i < n) : γ i ε (T (i+1)) = p (i+1) := (hε.2.1 i hi).2
    have hbound := finite_piece_metric_energy_point_bound g n p T (fun i => γ i ε)
      hT hε.1 hleft hright k hk r (by simpa only [hkn,hTn] using hr)
    have hp0 : p 0 = (α ε).base := by
      dsimp [p]; rw [hT0,parallelFrameFlowMap_zero]; exact (hbase ε).symm
    rw [hp0,hT0,hTn,sub_zero] at hbound
    have henergy := hε.2.2
    rw [hT0,hTn,sub_zero] at henergy
    linarith
  have hnorm := short_variation_log_norm_lt g o hRic e he t ht htc hcut U hU heU
    log hlog hlog0 hreal (T k) hTk hTkt α hα hα0
    (hαpos.filter_mono nhdsWithin_le_nhds) (γ k) hlastref hlastjoint hcont hdist
  refine ⟨α,u,hα,hu,hα0,hu0,hbase,?_⟩
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), H ε ∈ U := hH.preimage_mem_nhds (hU.mem_nhds hHU)
  filter_upwards [hnorm,hshort,hαpos.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds] with ε hnε hε hpε hUε
  refine ⟨hpε,hnε,?_⟩
  change frameExponential g o (H ε).1 (log (H ε)) = _
  rw [hreal _ hUε]
  change γ k ε t = _
  have hh := (hε.2.1 k hk).2
  simpa only [hkn,hTn] using hh

end
end PositiveEinsteinFour.Geometry
end

end OAI
