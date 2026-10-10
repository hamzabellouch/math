import Mathlib
import OAI.Geometry.CubicTorus.Estimates.ConeSlopeReciprocalArea

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def minimalGraphDensity (g ψ : Plane → ℝ) (y : Plane) : ℝ :=
  fderiv ℝ ψ y (gradient g y)/Real.sqrt (1+‖gradient g y‖^2)

lemma graphAreaVector_norm_sqrt {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ = Real.sqrt (1+‖gradient g y‖^2) := by
  rw [plane_gradient_norm,← graphAreaVector_norm_sq hn g y,Real.sqrt_sq (norm_nonneg _)]

lemma minimalGraphDensity_tsupport (g ψ : Plane → ℝ) :
    tsupport (minimalGraphDensity g ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  by_contra hh
  exact hy (by simp [minimalGraphDensity,fderiv_of_notMem_tsupport ℝ hh])

lemma minimalGraphDensity_integrable {g ψ : Plane → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsψ : HasCompactSupport ψ)
    (hg : ∀ y ∈ tsupport ψ, ContinuousAt (fderiv ℝ g) y) :
    Integrable (minimalGraphDensity g ψ) := by
  have hc : Continuous (minimalGraphDensity g ψ) := by
    apply continuous_of_tsupport
    intro y hy
    have hd := hg y (minimalGraphDensity_tsupport g ψ hy)
    have hgrad : ContinuousAt (gradient g) y :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp hd
    exact ((hψ.continuous_fderiv (by simp)).continuousAt.clm_apply hgrad).div
      ((hgrad.norm.pow 2).const_add 1).sqrt
      (Real.sqrt_pos.2 (by positivity : 0<1+‖gradient g y‖^2)).ne'
  exact hc.integrable_of_hasCompactSupport
    (hsψ.of_isClosed_subset isClosed_closure (minimalGraphDensity_tsupport g ψ))

lemma continuous_mul_on_tsupport {f ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hf : ∀ s ∈ tsupport ψ, ContinuousAt f s) : Continuous (fun s ↦ f s*ψ s) := by
  apply continuous_of_tsupport
  intro s hs
  exact (hf s (tsupport_mul_subset_right hs)).mul hψ.continuousAt

lemma integrable_mul_on_tsupport {f ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hsψ : HasCompactSupport ψ) (hf : ∀ s ∈ tsupport ψ, ContinuousAt f s) :
    Integrable (fun s ↦ f s*ψ s) :=
  (continuous_mul_on_tsupport hψ hf).integrable_of_hasCompactSupport hsψ.mul_left

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarWedgeChart_continuous : Continuous planarWedgeChart :=
  planeProductCoordinates.symm.continuous.comp (continuous_fst.prodMk (continuous_fst.mul continuous_snd))

lemma slopeScalarTest_support_coordinates {χ ψ : ℝ → ℝ}
    (hχ0 : 0 ∉ tsupport χ) {y : Plane} (hy : y ∈ tsupport (slopeScalarTest χ ψ)) :
    (planeProductCoordinates y).1 ∈ tsupport χ ∧
      (planeProductCoordinates y).2/(planeProductCoordinates y).1 ∈ tsupport ψ := by
  have hr : (planeProductCoordinates y).1 ∈ tsupport χ := by
    by_contra hh
    have heχ := notMem_tsupport_iff_eventuallyEq.mp hh
    have he : slopeScalarTest χ ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [(planeProductCoordinates.continuous.fst.tendsto y).eventually heχ] with z hz
      simp only [slopeScalarTest,hz,Pi.zero_apply,zero_mul]
    exact notMem_tsupport_iff_eventuallyEq.mpr he hy
  refine ⟨hr,?_⟩
  have hr0 : (planeProductCoordinates y).1≠0 := fun hh ↦ hχ0 (hh ▸ hr)
  by_contra hh
  have heψ := notMem_tsupport_iff_eventuallyEq.mp hh
  have hc : ContinuousAt (fun z : Plane ↦ (planeProductCoordinates z).2/(planeProductCoordinates z).1) y :=
    planeProductCoordinates.continuous.snd.continuousAt.div planeProductCoordinates.continuous.fst.continuousAt hr0
  have he : slopeScalarTest χ ψ =ᶠ[𝓝 y] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hc.eventually heψ] with z hz
    simp only [slopeScalarTest,hz,Pi.zero_apply,mul_zero]
  exact notMem_tsupport_iff_eventuallyEq.mpr he hy

lemma planarWedgeChart_coordinates_inverse {y : Plane} (hy : (planeProductCoordinates y).1≠0) :
    planarWedgeChart ((planeProductCoordinates y).1,
      (planeProductCoordinates y).2/(planeProductCoordinates y).1)=y := by
  simp only [planarWedgeChart,mul_div_cancel₀ _ hy]
  exact ContinuousLinearEquiv.symm_apply_apply planeProductCoordinates y

lemma slopeScalarTest_compactSupport {χ ψ : ℝ → ℝ} (hχ0 : 0 ∉ tsupport χ)
    (hχ : HasCompactSupport χ) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (slopeScalarTest χ ψ) := by
  apply ((hχ.prod hψ).image planarWedgeChart_continuous).of_isClosed_subset isClosed_closure
  intro y hy
  obtain ⟨hr,hs⟩ := slopeScalarTest_support_coordinates hχ0 hy
  exact ⟨((planeProductCoordinates y).1,(planeProductCoordinates y).2/(planeProductCoordinates y).1),
    ⟨hr,hs⟩,planarWedgeChart_coordinates_inverse (fun hh ↦ hχ0 (hh ▸ hr))⟩

lemma slopeScalarTest_derivative_zero {χ ψ : ℝ → ℝ} {y : Plane}
    (hy : (planeProductCoordinates y).1 ∉ tsupport χ ∨
      (planeProductCoordinates y).2/(planeProductCoordinates y).1 ∉ tsupport ψ)
    (hχ0 : 0 ∉ tsupport χ) : fderiv ℝ (slopeScalarTest χ ψ) y=0 := by
  apply fderiv_of_notMem_tsupport
  intro hh
  obtain ⟨hr,hs⟩ := slopeScalarTest_support_coordinates hχ0 hh
  exact hy.elim (fun h ↦ h hr) (fun h ↦ h hs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_norm_sq_coordinates (v : Plane) :
    ‖v‖^2=(planeProductCoordinates v).1^2+(planeProductCoordinates v).2^2 := by
  rw [← real_inner_self_eq_norm_sq,plane_inner_coordinates]
  ring

lemma exists_smooth_radial_test {a b : ℝ} (hab : a<b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo a b ∧ (∫ r : ℝ, χ r)=1 := by
  let φ : ContDiffBump ((a+b)/2) :=
    ⟨(b-a)/8,(b-a)/4,by linarith,by linarith⟩
  refine ⟨φ.normed volume,φ.contDiff_normed,φ.hasCompactSupport_normed,?_,φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]
  intro r hr
  simp only [Metric.mem_closedBall,Real.dist_eq,abs_le] at hr
  change -( (b-a)/4) ≤ r-(a+b)/2 ∧ r-(a+b)/2 ≤ (b-a)/4 at hr
  constructor <;> linarith

lemma minimalGraphDensity_slope {g : Plane → ℝ} {χ ψ f q : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) {r s : ℝ} (hr : r≠0)
    (hg : planeProductCoordinates (gradient g (planarWedgeChart (r,s)))=(f s-s*q s,q s)) :
    minimalGraphDensity g (slopeScalarTest χ ψ) (planarWedgeChart (r,s)) =
      deriv χ r*((f s-s*q s)*coneSlopeReciprocalArea f q s*ψ s)+
        (χ r/r)*(coneSlopeFlux f q s*deriv ψ s) := by
  rw [minimalGraphDensity,slopeScalarTest_derivative hχ hψ hχ0 hr,
    plane_norm_sq_coordinates,hg]
  dsimp only [Prod.fst,Prod.snd,coneSlopeReciprocalArea,coneSlopeFlux]
  ring_nf

theorem stationary_euler_graph_affine {g : Plane → ℝ} {a b c d : ℝ}
    (ha : 0<a) (hab : a<b)
    (hg : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, DifferentiableAt ℝ g (planarWedgeChart (r,s)))
    (hC : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d, ContinuousAt (fderiv ℝ g) (planarWedgeChart (r,s)))
    (he : ∀ r ∈ Ioo a b, ∀ s ∈ Ioo c d,
      fderiv ℝ g (planarWedgeChart (r,s)) (planarWedgeChart (r,s))=g (planarWedgeChart (r,s)))
    (hw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ →
      tsupport Ψ ⊆ planarWedgeChart '' (Ioo a b ×ˢ Ioo c d) →
      (∫ y : Plane, minimalGraphDensity g Ψ y)=0)
    {r₀ r x s : ℝ} (hr₀ : r₀ ∈ Ioo a b) (hr : r ∈ Ioo a b)
    (hx : x ∈ Ioo c d) (hs : s ∈ Ioo c d) :
    g (planarWedgeChart (r,s)) =
      r*(g (planarWedgeChart (r₀,x))/r₀+
        fderiv ℝ g (planarWedgeChart (r₀,x)) slopeVerticalVector*(s-x)) := by
  let f : ℝ → ℝ := fun t ↦ g (planarWedgeChart (r₀,t))/r₀
  let q : ℝ → ℝ := fun t ↦ fderiv ℝ g (planarWedgeChart (r₀,t)) slopeVerticalVector
  have hrd : r₀≠0 := (ha.trans hr₀.1).ne'
  have hfd (t : ℝ) (ht : t ∈ Ioo c d) : HasDerivAt f (q t) t :=
    graph_angular_slice_hasDerivAt hrd (hg r₀ hr₀ t ht)
  have hqc (t : ℝ) (ht : t ∈ Ioo c d) : ContinuousAt q t := by
    have hc : ContinuousAt (fun t : ℝ ↦ fderiv ℝ g (planarWedgeChart (r₀,t))) t :=
      (hC r₀ hr₀ t ht).comp (f := fun t : ℝ ↦ planarWedgeChart (r₀,t))
        (planarWedgeChart_hasDerivAt_angular r₀ t).continuousAt
    exact hc.clm_apply continuousAt_const
  have hfc : ContinuousOn f (Ioo c d) := fun t ht ↦ (hfd t ht).continuousAt.continuousWithinAt
  have hqC : ContinuousOn q (Ioo c d) := fun t ht ↦ (hqc t ht).continuousWithinAt
  have hcc := coneSlopeReciprocalArea_continuousOn hfc hqC
  have hu := hfc.sub (continuousOn_id.mul hqC)
  have hflux : ContinuousOn (coneSlopeFlux f q) (Ioo c d) :=
    (hqC.sub (continuousOn_id.mul hu)).mul hcc
  have hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo c d →
      (∫ t : ℝ, coneSlopeFlux f q t*deriv ψ t)=
        (∫ t : ℝ, (f t-t*q t)*coneSlopeReciprocalArea f q t*ψ t) := by
    intro ψ hψ hsψ
    obtain ⟨χ,hχ,hχc,hχs,hχi⟩ := exists_smooth_radial_test hab
    have hχpos : tsupport χ ⊆ Ioi (0 : ℝ) := fun t ht ↦ ha.trans (hχs ht).1
    have hχ0 : (0 : ℝ) ∉ tsupport χ := fun hh ↦ (lt_irrefl (0 : ℝ)) (hχpos hh)
    have hψc : HasCompactSupport ψ :=
      isCompact_Icc.of_isClosed_subset isClosed_closure (hsψ.trans Ioo_subset_Icc_self)
    let Ψ := slopeScalarTest χ ψ
    have hΨ := slopeScalarTest_contDiff hχ hψ hχ0
    have hΨc := slopeScalarTest_compactSupport hχ0 hχc hψc
    have hΨs : tsupport Ψ ⊆ planarWedgeChart '' (Ioo a b ×ˢ Ioo c d) := by
      intro y hy
      obtain ⟨hr,ht⟩ := slopeScalarTest_support_coordinates hχ0 hy
      exact ⟨((planeProductCoordinates y).1,(planeProductCoordinates y).2/(planeProductCoordinates y).1),
        ⟨hχs hr,hsψ ht⟩,planarWedgeChart_coordinates_inverse (fun hh ↦ hχ0 (hh ▸ hr))⟩
    have hGi : Integrable (minimalGraphDensity g Ψ) := by
      apply minimalGraphDensity_integrable hΨ hΨc
      intro y hy
      obtain ⟨⟨r,t⟩,⟨hr,ht⟩,rfl⟩ := hΨs hy
      exact hC r hr t ht
    have hAi : Integrable (fun t ↦ (f t-t*q t)*coneSlopeReciprocalArea f q t*ψ t) := by
      apply integrable_mul_on_tsupport hψ.continuous hψc
      intro t ht
      exact (hu.mul hcc).continuousAt (isOpen_Ioo.mem_nhds (hsψ ht))
    have hBi : Integrable (fun t ↦ coneSlopeFlux f q t*deriv ψ t) := by
      apply integrable_mul_on_tsupport (hψ.continuous_deriv (by simp)) hψc.deriv
      intro t ht
      exact hflux.continuousAt (isOpen_Ioo.mem_nhds (hsψ (tsupport_deriv_subset ht)))
    have hzero (r : ℝ) (hr : r≤0) (y : ℝ) :
        minimalGraphDensity g Ψ (planeProductCoordinates.symm (r,y))=0 := by
      have hz : r ∉ tsupport χ := fun hh ↦ not_lt_of_ge hr (hχpos hh)
      have hd := slopeScalarTest_derivative_zero (χ := χ) (ψ := ψ)
        (y := planeProductCoordinates.symm (r,y)) (Or.inl (by simpa using hz)) hχ0
      simp only [minimalGraphDensity,Ψ,hd,zero_apply,zero_div]
    have hid (r : ℝ) (hr : 0<r) (t : ℝ) :
        minimalGraphDensity g Ψ (planarWedgeChart (r,t)) =
          deriv χ r*((f t-t*q t)*coneSlopeReciprocalArea f q t*ψ t)+
            (χ r/r)*(coneSlopeFlux f q t*deriv ψ t) := by
      by_cases hrχ : r ∈ tsupport χ
      · by_cases htψ : t ∈ tsupport ψ
        · exact minimalGraphDensity_slope hχ hψ hχ0 hr.ne'
            (euler_graph_gradient ha hg he (hχs hrχ) hr₀ (hsψ htψ))
        · have hd := slopeScalarTest_derivative_zero (χ := χ) (ψ := ψ)
            (y := planarWedgeChart (r,t)) (Or.inr (by simpa [planarWedgeChart,hr.ne'] using htψ)) hχ0
          simp only [minimalGraphDensity,Ψ,hd,zero_apply,zero_div,
            image_eq_zero_of_notMem_tsupport htψ,deriv_of_notMem_tsupport htψ,mul_zero,add_zero]
      · have hd := slopeScalarTest_derivative_zero (χ := χ) (ψ := ψ)
          (y := planarWedgeChart (r,t)) (Or.inl (by simpa [planarWedgeChart] using hrχ)) hχ0
        simp only [minimalGraphDensity,Ψ,hd,zero_apply,zero_div,
          image_eq_zero_of_notMem_tsupport hrχ,deriv_of_notMem_tsupport hrχ,zero_mul,zero_div,add_zero]
    have hi := integral_slope_separated hGi hχ hχc hχpos hAi hBi hzero hid
    rw [hw Ψ hΨ hΨs,hχi,one_mul] at hi
    linarith
  have haf := (weak_cone_slope_affine hfd hqC hweak hx hs).2
  have hh := euler_graph_homogeneous ha hg he hr hr₀ hs
  change g (planarWedgeChart (r,s))/r=f s at hh
  rw [haf] at hh
  apply (div_eq_iff (ha.trans hr.1).ne').mp at hh
  simpa only [f,q,mul_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphReparam (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ) (g : Plane → ℝ) : Plane → ℝ :=
  fun y ↦ g (R y-v)+c

lemma graphReparam_fderiv (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ) (g : Plane → ℝ) (y : Plane) :
    fderiv ℝ (graphReparam R v c g) y =
      (fderiv ℝ g (R y-v)).comp R.toContinuousLinearEquiv.toContinuousLinearMap := by
  change fderiv ℝ (fun z ↦ g (R z-v)+c) y = _
  rw [fderiv_add_const]
  have he := R.toContinuousLinearEquiv.comp_right_fderiv (f := fun z ↦ g (z-v)) (x := y)
  simp only [Function.comp_def,sub_eq_add_neg,fderiv_comp_add_right] at he ⊢
  exact he

lemma graphReparam_gradient (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ) (g : Plane → ℝ) (y : Plane) :
    gradient (graphReparam R v c g) y=R.symm (gradient g (R y-v)) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,graphReparam_fderiv,ContinuousLinearMap.comp_apply]
  rw [← R.inner_map_map, R.apply_symm_apply,inner_gradient_left]
  rfl

lemma minimalGraphDensity_reparam (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    (g ψ : Plane → ℝ) (y : Plane) :
    minimalGraphDensity (graphReparam R v c g) (graphReparam R v 0 ψ) y =
      minimalGraphDensity g ψ (R y-v) := by
  rw [minimalGraphDensity,graphReparam_fderiv,graphReparam_gradient,
    ContinuousLinearMap.comp_apply]
  change fderiv ℝ ψ (R y-v) (R (R.symm (gradient g (R y-v)))) / _ = _
  rw [R.apply_symm_apply,R.symm.norm_map]
  rfl

lemma integral_minimalGraphDensity_reparam (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    (g ψ : Plane → ℝ) :
    (∫ y : Plane, minimalGraphDensity (graphReparam R v c g) (graphReparam R v 0 ψ) y) =
      ∫ y : Plane, minimalGraphDensity g ψ y := by
  simp_rw [minimalGraphDensity_reparam]
  calc
    _ = ∫ y : Plane, minimalGraphDensity g ψ (y-v) :=
      R.measurePreserving.integral_comp R.toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := integral_sub_right_eq_self _ _

lemma graphReparam_contDiffAt (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    {g : Plane → ℝ} {y : Plane} (hg : ContDiffAt ℝ 1 g (R y-v)) :
    ContDiffAt ℝ 1 (graphReparam R v c g) y := by
  exact (hg.comp y (R.toContinuousLinearEquiv.contDiff.contDiffAt.sub contDiffAt_const)).add contDiffAt_const

lemma graphReparam_contDiff (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (c : ℝ)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (graphReparam R v c g) :=
  (hg.comp (R.toContinuousLinearEquiv.contDiff.sub contDiff_const)).add contDiff_const

lemma graphReparam_zero_tsupport (R : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane) (g : Plane → ℝ) :
    tsupport (graphReparam R v 0 g) = (fun y ↦ R y-v) ⁻¹' tsupport g := by
  have he : graphReparam R v 0 g = g ∘ (R.toHomeomorph.trans (Homeomorph.subRight v)) := by
    ext y
    simp [graphReparam]
  rw [he,tsupport_comp_eq_preimage]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positive_wedge_rectangle {U : Set Plane} (hU : IsOpen U) {z : Plane}
    (hz : z ∈ U) (hzp : 0<(planeProductCoordinates z).1) :
    ∃ a b c d : ℝ, 0<a ∧
      (planeProductCoordinates z).1 ∈ Ioo a b ∧
      (planeProductCoordinates z).2/(planeProductCoordinates z).1 ∈ Ioo c d ∧
      planarWedgeChart '' (Ioo a b ×ˢ Ioo c d) ⊆ U := by
  let r := (planeProductCoordinates z).1
  let s := (planeProductCoordinates z).2/r
  have hW : planarWedgeChart (r,s)=z := planarWedgeChart_coordinates_inverse hzp.ne'
  have hu : planarWedgeChart ⁻¹' U ∈ 𝓝 (r,s) := by
    apply (hU.preimage planarWedgeChart_continuous).mem_nhds
    simpa only [mem_preimage,hW] using hz
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hu
  obtain ⟨a,b,hrab,hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨c,d,hscd,hcd⟩ := mem_nhds_iff_exists_Ioo_subset.mp hB
  refine ⟨max a (r/2),b,c,d,lt_max_of_lt_right (by dsimp [r]; linarith),
    ⟨max_lt hrab.1 (by dsimp [r]; linarith),hrab.2⟩,hscd,?_⟩
  rintro _ ⟨⟨u,t⟩,⟨hu,ht⟩,rfl⟩
  exact hAB ⟨hab ⟨(le_max_left _ _).trans_lt hu.1,hu.2⟩,hcd ht⟩

theorem local_euler_graph_linear {U : Set Plane} (hU : IsOpen U) {g : Plane → ℝ}
    (hg : ∀ y ∈ U, ContDiffAt ℝ 1 g y)
    (he : ∀ y ∈ U, fderiv ℝ g y y=g y)
    (hw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ U →
      (∫ y : Plane, minimalGraphDensity g Ψ y)=0)
    {z : Plane} (hz : z ∈ U) (hzp : 0<(planeProductCoordinates z).1) :
    ∀ᶠ y in 𝓝 z, g y=fderiv ℝ g z y := by
  obtain ⟨a,b,c,d,ha,hr,hs,hW⟩ := positive_wedge_rectangle hU hz hzp
  let r := (planeProductCoordinates z).1
  let s := (planeProductCoordinates z).2/r
  have hWz : planarWedgeChart (r,s)=z := planarWedgeChart_coordinates_inverse hzp.ne'
  have hmem (u : ℝ) (hu : u ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo c d) :
      planarWedgeChart (u,t) ∈ U := hW ⟨(u,t),⟨hu,ht⟩,rfl⟩
  have hgd (u : ℝ) (hu : u ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo c d) :=
    (hg _ (hmem u hu t ht)).differentiableAt (by norm_num)
  have hgc (u : ℝ) (hu : u ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo c d) :=
    (hg _ (hmem u hu t ht)).continuousAt_fderiv (by norm_num)
  have helin : g z/r=fderiv ℝ g z slopeHorizontalVector+s*fderiv ℝ g z slopeVerticalVector := by
    have hlin := congrArg (fderiv ℝ g z) (planarWedgeChart_expand r s)
    rw [hWz,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,he z hz] at hlin
    apply (div_eq_iff hzp.ne').mpr
    linarith
  have hc : ContinuousAt (fun y : Plane ↦ ((planeProductCoordinates y).1,
      (planeProductCoordinates y).2/(planeProductCoordinates y).1)) z :=
    planeProductCoordinates.continuous.fst.continuousAt.prodMk
      (planeProductCoordinates.continuous.snd.continuousAt.div
        planeProductCoordinates.continuous.fst.continuousAt hzp.ne')
  have hneigh := hc.eventually ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hr,hs⟩)
  filter_upwards [hneigh] with y hy
  let u := (planeProductCoordinates y).1
  let t := (planeProductCoordinates y).2/u
  have huy : planarWedgeChart (u,t)=y := planarWedgeChart_coordinates_inverse (ha.trans hy.1.1).ne'
  have hh := stationary_euler_graph_affine ha (hr.1.trans hr.2) hgd hgc
    (fun u hu t ht ↦ he _ (hmem u hu t ht))
    (fun Ψ hΨ hsΨ ↦ hw Ψ hΨ (hsΨ.trans hW)) hr hy.1 hs hy.2
  rw [hWz,huy,helin] at hh
  rw [hh]
  have hlin := congrArg (fderiv ℝ g z) (planarWedgeChart_expand u t)
  rw [huy,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hlin
  rw [hlin]
  ring

theorem local_euler_graph_linear_of_ne_zero {U : Set Plane} (hU : IsOpen U) {g : Plane → ℝ}
    (hg : ∀ y ∈ U, ContDiffAt ℝ 1 g y)
    (he : ∀ y ∈ U, fderiv ℝ g y y=g y)
    (hw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ U →
      (∫ y : Plane, minimalGraphDensity g Ψ y)=0)
    {z : Plane} (hz : z ∈ U) (hz0 : z≠0) :
    ∀ᶠ y in 𝓝 z, g y=fderiv ℝ g z y := by
  let n : Plane := ‖z‖⁻¹ • z
  have hzn : 0<‖z‖ := norm_pos_iff.mpr hz0
  have hn : ‖n‖=1 := by
    dsimp only [n]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hzn.le),inv_mul_cancel₀ hzn.ne']
  let R := planarNormalRotation n
  let H := graphReparam R 0 0 g
  have hH (y : Plane) : H y=g (R y) := by simp [H,graphReparam]
  have hHp : ∀ y ∈ R ⁻¹' U, ContDiffAt ℝ 1 H y := by
    intro y hy
    apply graphReparam_contDiffAt
    simpa only [sub_zero] using hg (R y) hy
  have hHe : ∀ y ∈ R ⁻¹' U, fderiv ℝ H y y=H y := by
    intro y hy
    rw [graphReparam_fderiv]
    change fderiv ℝ g (R y-0) (R y)=H y
    simpa only [sub_zero,hH] using he (R y) hy
  have hHw : ∀ Ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ R ⁻¹' U →
      (∫ y : Plane, minimalGraphDensity H Ψ y)=0 := by
    intro Ψ hΨ hsΨ
    let ψ := graphReparam R.symm 0 0 Ψ
    have hψ := graphReparam_contDiff R.symm 0 0 hΨ
    have hsψ : tsupport ψ ⊆ U := by
      rw [graphReparam_zero_tsupport]
      intro y hy
      have hh := hsΨ hy
      simpa only [mem_preimage,sub_zero,R.apply_symm_apply] using hh
    have hrev : graphReparam R 0 0 ψ=Ψ := by
      ext y
      simp only [graphReparam,sub_zero,add_zero,R.symm_apply_apply,ψ]
    rw [← hrev,integral_minimalGraphDensity_reparam]
    exact hw ψ hψ hsψ
  have hzR : R.symm z ∈ R ⁻¹' U := by simpa using hz
  have hpR : 0<(planeProductCoordinates (R.symm z)).1 := by
    change 0<(planarWedgeCoordinates ((planarNormalRotation n).symm z)).1
    rw [planarNormalRotation_radial hn]
    dsimp only [n]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    positivity
  have hlocal := local_euler_graph_linear (hU.preimage R.continuous) hHp hHe hHw hzR hpR
  have hi := R.symm.continuous.continuousAt.eventually hlocal
  filter_upwards [hi] with y hy
  rw [hH,R.apply_symm_apply,graphReparam_fderiv] at hy
  change g y=fderiv ℝ g (R (R.symm z)-0) (R (R.symm y)) at hy
  simpa only [R.apply_symm_apply,sub_zero] using hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_inner_coordinates {n : Cover} (hn : ‖n‖=1) (y : Plane) (x : Cover) :
    ⟪normalPlaneEmbedding n y,x⟫ = ⟪y,normalPlaneCoordinates n x⟫ := by
  conv_lhs => rhs; rw [← normalPlaneCoordinates_reconstruct hn x]
  have hz : ⟪normalPlaneEmbedding n y,n⟫=0 :=
    (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn y)
  rw [inner_add_right,inner_smul_right,hz,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map y (normalPlaneCoordinates n x)

lemma normalGraph_coordinates_eq_iff {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (x : Cover) :
    normalGraph n g (normalPlaneCoordinates n x)=x ↔ g (normalPlaneCoordinates n x)=⟪n,x⟫ := by
  constructor
  · intro hh
    simpa only [normalGraph_inner hn] using congrArg (fun v : Cover ↦ ⟪n,v⟫) hh
  · intro hh
    rw [normalGraph,hh,normalPlaneCoordinates_reconstruct hn x]

def rebasedGraph (a n : Cover) (g : Plane → ℝ) : Plane → ℝ :=
  graphReparam (LinearIsometryEquiv.refl ℝ Plane) (normalPlaneCoordinates n a) ⟪n,a⟫ g

lemma rebasedGraph_apply (a n : Cover) (g : Plane → ℝ) (y : Plane) :
    rebasedGraph a n g y=g (y-normalPlaneCoordinates n a)+⟪n,a⟫ := rfl

lemma rebasedGraph_fderiv (a n : Cover) (g : Plane → ℝ) (y : Plane) :
    fderiv ℝ (rebasedGraph a n g) y=fderiv ℝ g (y-normalPlaneCoordinates n a) := by
  rw [rebasedGraph,graphReparam_fderiv]
  ext z
  rfl

lemma normalGraph_rebased (a : Cover) {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (y : Plane) :
    normalGraph n (rebasedGraph a n g) y=a+normalGraph n g (y-normalPlaneCoordinates n a) := by
  have ha := normalPlaneCoordinates_reconstruct hn a
  simp only [normalGraph,rebasedGraph_apply,add_smul]
  change normalPlaneLinearIsometry n y+(g (y-normalPlaneCoordinates n a) • n+⟪n,a⟫ • n)=
    a+(normalPlaneLinearIsometry n (y-normalPlaneCoordinates n a)+g (y-normalPlaneCoordinates n a) • n)
  rw [map_sub]
  change normalPlaneLinearIsometry n (normalPlaneCoordinates n a)+⟪n,a⟫ • n=a at ha
  rw [show normalPlaneLinearIsometry n (normalPlaneCoordinates n a)=a-⟪n,a⟫ • n from
    eq_sub_iff_add_eq.mpr ha]
  abel

lemma rebasedGraph_graph_eq (a : Cover) {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (x : Cover) :
    normalGraph n (rebasedGraph a n g) (normalPlaneCoordinates n x)=x ↔
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
  rw [normalGraph_rebased a hn,map_sub,eq_sub_iff_add_eq]
  constructor <;> intro hh <;> simpa only [add_comm] using hh

lemma rebasedGraph_continuous (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    Continuous (rebasedGraph a n g) :=
  (hg.comp (continuous_id.sub continuous_const)).add continuous_const

lemma rebasedGraph_weak_equation (a : Cover) {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ)
    {p : Cover} {ρ : ℝ} (hρ : 0<ρ)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0)
    {Ψ : Plane → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hs : ∀ y ∈ tsupport Ψ, normalGraph n (rebasedGraph a n g) y ∈ Metric.ball p (ρ/2)) :
    (∫ y : Plane, minimalGraphDensity (rebasedGraph a n g) Ψ y)=0 := by
  let v := normalPlaneCoordinates n a
  let R := LinearIsometryEquiv.refl ℝ Plane
  let ψ := graphReparam R (-v) 0 Ψ
  have hψ := graphReparam_contDiff R (-v) 0 hΨ
  have hsψ (y : Plane) (hy : y ∈ tsupport ψ) : a+normalGraph n g y ∈ Metric.ball p (ρ/2) := by
    rw [graphReparam_zero_tsupport] at hy
    change y-(-v) ∈ tsupport Ψ at hy
    have hh := hs (y+v) (by simpa only [sub_neg_eq_add] using hy)
    rw [normalGraph_rebased a hn] at hh
    simpa only [v,add_sub_cancel_right] using hh
  have hi := stationary_graph_weak_equation a hn g hρ hstat hψ hsψ
  simp_rw [graphAreaVector_norm_sqrt hn] at hi
  have hh : graphReparam R v 0 ψ=Ψ := by
    ext y
    simp [graphReparam,ψ,R]
  rw [← hh]
  change (∫ y : Plane, minimalGraphDensity (graphReparam R v ⟪n,a⟫ g) (graphReparam R v 0 ψ) y)=0
  rw [integral_minimalGraphDensity_reparam]
  exact hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem conical_stationary_patch_plane {A : Set Cover}
    (hcone : ∀ t : ℝ, 1≤t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {a n p : Cover} {g : Plane → ℝ} {R ρ : ℝ}
    (hn : ‖n‖=1) (hg : LipschitzWith (1/4) g) (hρ : 0<ρ)
    (hC : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y)
    (hRp : p ∈ Metric.ball a R)
    (hp : p ∈ coverEssentialBoundary A) (hpn : ‖p‖<1) (hp0 : p≠0)
    (hgraph : ∀ x ∈ Metric.closedBall p (2*ρ), x ∈ coverEssentialBoundary A ↔
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a)
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall p ρ →
      (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖)=0) :
    ∃ N : Cover, ‖N‖=1 ∧ ∀ᶠ x in 𝓝 p, x ∈ coverEssentialBoundary A ↔ ⟪N,x⟫=0 := by
  let H := rebasedGraph a n g
  let v := normalPlaneCoordinates n a
  let G := normalGraph n H
  have hHc : Continuous H := rebasedGraph_continuous a n hg.continuous
  have hGc : Continuous G :=
    (normalPlaneLinearIsometry n).continuous.add (hHc.smul continuous_const)
  let U : Set Plane := (fun y ↦ y-v) ⁻¹' Metric.ball (0 : Plane) R ∩
    G ⁻¹' (Metric.ball p (ρ/2) ∩ Metric.ball (0 : Cover) 1)
  have hU : IsOpen U :=
    (Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)).inter
      ((Metric.isOpen_ball.inter Metric.isOpen_ball).preimage hGc)
  have hHC (y : Plane) (hy : y ∈ U) : ContDiffAt ℝ 1 H y := by
    apply graphReparam_contDiffAt
    exact hC _ (Metric.ball_subset_closedBall hy.1)
  have hbigger (x : Cover) (hx : x ∈ Metric.ball p (ρ/2)) : x ∈ Metric.ball p (2*ρ) :=
    Metric.ball_subset_ball (by linarith) hx
  have hxp (y : Plane) : normalPlaneCoordinates n (G y)=y := normalPlaneCoordinates_graph hn H y
  have hEuler (y : Plane) (hy : y ∈ U) : fderiv ℝ H y y=H y := by
    have hxb := hy.2.1
    have hxgraph : normalGraph n g (normalPlaneCoordinates n (G y-a))=G y-a := by
      apply (rebasedGraph_graph_eq a hn g (G y)).mp
      rw [hxp]
    have hxB := (hgraph (G y) (Metric.ball_subset_closedBall (hbigger _ hxb))).mpr hxgraph
    have hproj : normalPlaneCoordinates n (G y-a)=y-v := by rw [map_sub,hxp]
    have hgd : DifferentiableAt ℝ g (normalPlaneCoordinates n (G y-a)) := by
      rw [hproj]
      exact (hC _ (Metric.ball_subset_closedBall hy.1)).differentiableAt (by norm_num)
    have hloc : ∀ᶠ x in 𝓝 (G y), x ∈ coverEssentialBoundary A →
        normalGraph n g (normalPlaneCoordinates n (x-a))=x-a := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (hbigger _ hxb)] with x hx
      exact (hgraph x (Metric.ball_subset_closedBall hx)).mp
    have hr := cone_graph_radial_derivative hcone hn hxB
      (by simpa only [Metric.mem_ball,dist_zero_right] using hy.2.2) hgd hloc
    rw [hproj,hxp] at hr
    rw [rebasedGraph_fderiv]
    exact hr.trans (normalGraph_inner hn H y)
  have hweak (Ψ : Plane → ℝ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hs : tsupport Ψ ⊆ U) :
      (∫ y : Plane, minimalGraphDensity H Ψ y)=0 :=
    rebasedGraph_weak_equation a hn g hρ hstat hΨ (fun y hy ↦ (hs hy).2.1)
  have hpclosed : p ∈ Metric.closedBall p (2*ρ) := Metric.mem_closedBall_self (by linarith)
  have hpG : G (normalPlaneCoordinates n p)=p :=
    (rebasedGraph_graph_eq a hn g p).mpr ((hgraph p hpclosed).mp hp)
  have hpU : normalPlaneCoordinates n p ∈ U := by
    refine ⟨?_,?_⟩
    · simp only [mem_preimage,v,← map_sub,Metric.mem_ball,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n (p-a)).trans_lt (by simpa only [Metric.mem_ball,dist_eq_norm] using hRp)
    · change G (normalPlaneCoordinates n p) ∈ Metric.ball p (ρ/2) ∩ Metric.ball (0 : Cover) 1
      rw [hpG]
      exact ⟨Metric.mem_ball_self (by positivity),by simpa using hpn⟩
  have hpz : normalPlaneCoordinates n p≠0 := by
    apply cone_graph_radial_projection_ne_zero hn hp0 (L := fderiv ℝ H (normalPlaneCoordinates n p))
    have he := hEuler _ hpU
    have hpheight := congrArg (fun x : Cover ↦ ⟪n,x⟫) hpG
    rw [normalGraph_inner hn] at hpheight
    exact he.trans hpheight
  have hline := local_euler_graph_linear_of_ne_zero hU hHC hEuler hweak hpU hpz
  let M := n-normalPlaneEmbedding n (gradient H (normalPlaneCoordinates n p))
  have hM : 0<‖M‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1)
    (graphSlopeVector_norm_ge hn (gradient H (normalPlaneCoordinates n p)))
  let N := ‖M‖⁻¹ • M
  have hN : ‖N‖=1 := by
    dsimp only [N]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hM.le),inv_mul_cancel₀ hM.ne']
  refine ⟨N,hN,?_⟩
  have hprojline := (normalPlaneCoordinates n).continuous.continuousAt.eventually hline
  filter_upwards [hprojline,Metric.ball_mem_nhds p (by positivity : 0<2*ρ)] with x hx hxball
  rw [hgraph x (Metric.ball_subset_closedBall hxball),← rebasedGraph_graph_eq a hn g,
    normalGraph_coordinates_eq_iff hn]
  change H (normalPlaneCoordinates n x)=⟪n,x⟫ ↔ ⟪N,x⟫=0
  rw [hx]
  have hinner : ⟪N,x⟫=‖M‖⁻¹*(⟪n,x⟫-fderiv ℝ H (normalPlaneCoordinates n p) (normalPlaneCoordinates n x)) := by
    rw [show N=‖M‖⁻¹ • M from rfl,real_inner_smul_left]
    congr 1
    rw [show M=n-normalPlaneEmbedding n (gradient H (normalPlaneCoordinates n p)) from rfl,
      inner_sub_left,normalPlaneEmbedding_inner_coordinates hn,inner_gradient_left]
  rw [hinner,mul_eq_zero,inv_eq_zero,or_iff_right hM.ne',sub_eq_zero]
  exact eq_comm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverEssentialBoundary_isClosed (A : Set Cover) : IsClosed (coverEssentialBoundary A) := by
  rw [coverEssentialBoundary_eq_support]
  exact Measure.isClosed_support.inter Measure.isClosed_support

lemma inner_kernel_mono_of_local {n m x : Cover} (hx : ⟪n,x⟫=0)
    (hlocal : ∀ᶠ y in 𝓝 x, ⟪n,y⟫=0 → ⟪m,y⟫=0) :
    ∀ v : Cover, ⟪n,v⟫=0 → ⟪m,v⟫=0 := by
  intro v hv
  have ht : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      (show Continuous (fun t : ℝ ↦ x+t • v) from
        continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)
  have he : (fun t : ℝ ↦ ⟪m,x+t • v⟫) =ᶠ[𝓝 0] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [ht.eventually hlocal] with t h
    exact h (by simp only [inner_add_right,inner_smul_right,hx,hv,mul_zero,add_zero])
  have hd : HasDerivAt (fun t : ℝ ↦ ⟪m,x+t • v⟫) ⟪m,v⟫ 0 := by
    simpa only [inner_add_right,inner_smul_right,id_eq,one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const ⟪m,v⟫).const_add ⟪m,x⟫)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq he)

lemma inner_kernel_eq_of_local {n m x : Cover} (hx : ⟪n,x⟫=0)
    (hlocal : ∀ᶠ y in 𝓝 x, ⟪n,y⟫=0 ↔ ⟪m,y⟫=0) :
    ∀ v : Cover, ⟪n,v⟫=0 ↔ ⟪m,v⟫=0 := by
  have hmx := (hlocal.self_of_nhds).mp hx
  exact fun v ↦ ⟨inner_kernel_mono_of_local hx (hlocal.mono fun _ h ↦ h.mp) v,
    inner_kernel_mono_of_local hmx (hlocal.mono fun _ h ↦ h.mpr) v⟩

lemma normal_plane_disk_preconnected {n : Cover} (hn : ‖n‖=1) :
    IsPreconnected {x : Cover | ⟪n,x⟫=0 ∧ ‖x‖<1 ∧ x≠0} := by
  have he : normalPlaneEmbedding n '' (Metric.ball (0 : Plane) 1 \ {0}) =
      {x : Cover | ⟪n,x⟫=0 ∧ ‖x‖<1 ∧ x≠0} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨normalPlaneEmbedding_inner hn z,?_,?_⟩
      · rw [normalPlaneEmbedding_norm]
        simpa only [Metric.mem_ball,dist_zero_right] using hz.1
      · intro hh
        have hhz := congrArg (normalPlaneCoordinates n) hh
        exact hz.2 (by simpa only [normalPlaneCoordinates_embedding,map_zero,mem_singleton_iff] using hhz)
    · rintro ⟨hx,hb,h0⟩
      have hh : normalPlaneEmbedding n (normalPlaneCoordinates n x)=x := by
        simpa only [hx,zero_smul,add_zero] using normalPlaneCoordinates_reconstruct hn x
      refine ⟨normalPlaneCoordinates n x,⟨?_,?_⟩,hh⟩
      · simp only [Metric.mem_ball,dist_zero_right]
        exact (normalPlaneCoordinates_norm_le n x).trans_lt hb
      · intro hz
        have hz' : normalPlaneCoordinates n x=0 := hz
        rw [hz'] at hh
        have he0 : normalPlaneEmbedding n (0 : Plane)=0 := (normalPlaneLinearIsometry n).map_zero
        exact h0 (hh.symm.trans he0)
  rw [← he]
  exact (planar_punctured_ball_preconnected (by norm_num : (0 : ℝ)<1)).image _
    (normalPlaneLinearIsometry n).continuous.continuousOn

theorem local_plane_disk_continuation {B : Set Cover} (hB : IsClosed B)
    (hloc : ∀ p ∈ B, ‖p‖<1 → p≠0 →
      ∃ n : Cover, ‖n‖=1 ∧ ∀ᶠ x in 𝓝 p, x∈B ↔ ⟪n,x⟫=0)
    {n p : Cover} (hn : ‖n‖=1) (hp : p∈B) (hpn : ‖p‖<1) (hp0 : p≠0)
    (hnloc : ∀ᶠ x in 𝓝 p, x∈B ↔ ⟪n,x⟫=0) :
    ∀ q : Cover, ⟪n,q⟫=0 → ‖q‖<1 → q≠0 →
      ∀ᶠ x in 𝓝 q, x∈B ↔ ⟪n,x⟫=0 := by
  let D : Set Cover := {x | ⟪n,x⟫=0 ∧ ‖x‖<1 ∧ x≠0}
  let K : Set Cover := {q | ∀ᶠ x in 𝓝 q, x∈B ↔ ⟪n,x⟫=0}
  have hKo : IsOpen K := isOpen_setOfPred_eventually_nhds
  have hKc : IsClosed ((Subtype.val : D → Cover) ⁻¹' K) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    by_cases hqB : (q : Cover)∈B
    · obtain ⟨m,hm,hmloc⟩ := hloc q hqB q.prop.2.1 q.prop.2.2
      let U : Set Cover := {y | ∀ᶠ x in 𝓝 y, x∈B ↔ ⟪m,x⟫=0}
      have hUo : IsOpen U := isOpen_setOfPred_eventually_nhds
      have hqU : (q : Cover)∈U := hmloc
      apply Filter.mem_of_superset ((hUo.preimage continuous_subtype_val).mem_nhds hqU)
      intro z hz hzK
      have he : ∀ x : Cover, ⟪n,x⟫=0 ↔ ⟪m,x⟫=0 :=
        inner_kernel_eq_of_local z.prop.1 (hzK.and hz |>.mono fun _ h ↦ h.1.symm.trans h.2)
      apply hq
      change ∀ᶠ x in 𝓝 (q : Cover), x∈B ↔ ⟪n,x⟫=0
      exact hmloc.mono fun x h ↦ h.trans (he x).symm
    · apply Filter.mem_of_superset ((hB.isOpen_compl.preimage continuous_subtype_val).mem_nhds hqB)
      intro z hz hzK
      exact hz ((hzK.self_of_nhds).mpr z.prop.1)
  have : PreconnectedSpace D :=
    isPreconnected_iff_preconnectedSpace.mp (normal_plane_disk_preconnected hn)
  have hpD : p∈D := ⟨(hnloc.self_of_nhds).mp hp,hpn,hp0⟩
  have he := (show IsClopen ((Subtype.val : D → Cover) ⁻¹' K) from
    ⟨hKc,hKo.preimage continuous_subtype_val⟩).eq_univ ⟨⟨p,hpD⟩,hnloc⟩
  intro q hqn hqb hq0
  have hh : (⟨q,hqn,hqb,hq0⟩ : D)∈(Subtype.val : D → Cover) ⁻¹' K := by rw [he]; trivial
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma two_cover_planes_meet {n m : Cover} (hn : ‖n‖=1) :
    ∃ q : Cover, ⟪n,q⟫=0 ∧ ⟪m,q⟫=0 ∧ ‖q‖<1 ∧ q≠0 := by
  let v := normalPlaneCoordinates n m
  have hw : ∃ w : Plane, w≠0 ∧ ⟪w,v⟫=0 := by
    by_cases hv : v=0
    · refine ⟨EuclideanSpace.single 0 1,?_,by simp [hv]⟩
      intro h
      have hh := congrArg (fun z : Plane ↦ z 0) h
      norm_num at hh
    · exact exists_planar_perpendicular hv
  obtain ⟨w,hw,hwi⟩ := hw
  let x := normalPlaneEmbedding n w
  have hx : 0<‖x‖ := by rw [normalPlaneEmbedding_norm]; exact norm_pos_iff.mpr hw
  have hnxi : ⟪n,x⟫=0 := normalPlaneEmbedding_inner hn w
  have hmxi : ⟪m,x⟫=0 := by
    rw [real_inner_comm]
    exact (normalPlaneEmbedding_inner_coordinates hn w m).trans hwi
  let q := ((1/2 : ℝ)*‖x‖⁻¹) • x
  have hqn : ‖q‖=(1/2 : ℝ) := by
    rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(1/2 : ℝ)*‖x‖⁻¹),
      mul_assoc,inv_mul_cancel₀ hx.ne',mul_one]
  refine ⟨q,?_,?_,by rw [hqn]; norm_num,?_⟩
  · simp only [q,inner_smul_right,hnxi,mul_zero]
  · simp only [q,inner_smul_right,hmxi,mul_zero]
  · intro hh
    rw [hh,norm_zero] at hqn
    norm_num at hqn

theorem closed_locally_planar_single_plane {B : Set Cover} (hB : IsClosed B)
    (hloc : ∀ p ∈ B, ‖p‖<1 → p≠0 →
      ∃ n : Cover, ‖n‖=1 ∧ ∀ᶠ x in 𝓝 p, x∈B ↔ ⟪n,x⟫=0)
    {p : Cover} (hp : p∈B) (hpn : ‖p‖<1) (hp0 : p≠0) :
    ∃ n : Cover, ‖n‖=1 ∧ ∀ x : Cover, ‖x‖<1 → x∈B → ⟪n,x⟫=0 := by
  obtain ⟨n,hn,hnloc⟩ := hloc p hp hpn hp0
  have hnext := local_plane_disk_continuation hB hloc hn hp hpn hp0 hnloc
  refine ⟨n,hn,?_⟩
  intro q hqb hqB
  by_cases hq0 : q=0
  · simp [hq0]
  obtain ⟨m,hm,hmloc⟩ := hloc q hqB hqb hq0
  have hmext := local_plane_disk_continuation hB hloc hm hqB hqb hq0 hmloc
  obtain ⟨z,hzn,hzm,hzb,hz0⟩ := two_cover_planes_meet (m := m) hn
  have hnz := hnext z hzn hzb hz0
  have hmz := hmext z hzm hzb hz0
  have he := inner_kernel_eq_of_local hzn (hnz.and hmz |>.mono fun _ h ↦ h.1.symm.trans h.2)
  exact (he q).mpr ((hmloc.self_of_nhds).mp hqB)

lemma cover_punctured_ball_preconnected {r : ℝ} (hr : 0<r) :
    IsPreconnected (Metric.ball (0 : Cover) r \ {0}) := by
  let f := OpenPartialHomeomorph.univBall (0 : Cover) r
  have hrank : 1 < Module.rank ℝ Cover := by
    rw [← Module.finrank_eq_rank]
    norm_num [Cover]
  have hc := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : Cover)).isPreconnected
  have hi : f '' ({0}ᶜ : Set Cover) = Metric.ball (0 : Cover) r \ {0} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target (0 : Cover) hr]
        exact f.map_source (by simp [f])
      · intro he
        have he0 : f x=0 := he
        have hh := congrArg f.symm he0
        rw [f.left_inv (by simp [f]),OpenPartialHomeomorph.univBall_symm_apply_center] at hh
        exact hx hh
    · rintro ⟨hy,hy0⟩
      have hyt : y∈f.target := by rwa [OpenPartialHomeomorph.univBall_target _ hr]
      refine ⟨f.symm y,?_,f.right_inv hyt⟩
      intro hz
      have hz' : f.symm y=0 := hz
      have hh := congrArg f hz'
      rw [f.right_inv hyt,OpenPartialHomeomorph.univBall_apply_zero] at hh
      exact hy0 hh
  rw [← hi]
  exact hc.image f (OpenPartialHomeomorph.continuous_univBall (0 : Cover) r).continuousOn

lemma cover_boundary_nonzero {A : Set Cover} (hA : MeasurableSet A)
    {r : ℝ} (hr : 0<r)
    (hpos : 0<volume (Metric.ball (0 : Cover) r ∩ A))
    (hneg : 0<volume (Metric.ball (0 : Cover) r ∩ Aᶜ)) :
    ∃ p : Cover, ‖p‖<r ∧ p≠0 ∧ p∈coverEssentialBoundary A := by
  by_contra he
  have hd : Disjoint (Metric.ball (0 : Cover) r \ {0}) (coverEssentialBoundary A) := by
    rw [Set.disjoint_left]
    intro x hx hb
    exact he ⟨x,by simpa only [Metric.mem_ball,dist_zero_right] using hx.1,hx.2,hb⟩
  have hnull (B : Set Cover) (h : volume ((Metric.ball (0 : Cover) r \ {0}) ∩ B)=0) :
      volume (Metric.ball (0 : Cover) r ∩ B)=0 := by
    apply measure_mono_null (t := ((Metric.ball (0 : Cover) r \ {0}) ∩ B) ∪ {0}) ?_
      (measure_union_null h (measure_singleton 0))
    intro x hx
    by_cases hx0 : x=0
    · exact Or.inr hx0
    · exact Or.inl ⟨⟨hx.1,hx0⟩,hx.2⟩
  rcases connected_cover_phase hA (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0))
    (cover_punctured_ball_preconnected hr) hd with hh|hh
  · exact (ne_of_gt hpos) (hnull A hh)
  · exact (ne_of_gt hneg) (hnull Aᶜ hh)

end CubicTorus
end
end
end

end OAI
