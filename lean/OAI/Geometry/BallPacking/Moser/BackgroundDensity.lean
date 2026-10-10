import Mathlib
import OAI.Geometry.BallPacking.Moser.CircleCorrection

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology NNReal
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Topology
open Set Metric
open scoped ContDiff Classical
open Set Function MeasureTheory
open scoped ContDiff Topology Classical NNReal
open Set Function MeasureTheory
theorem exists_relative_planar_moser_correction {ι : Type*} [Fintype ι]
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : (∫ p, f p) = 0) (hpos : ∀ x, 0 < 1+f x)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i, (∫ p in roundDisk (R i), f p) = 0) :
    ∃ Φ : Plane ≃ₜ Plane, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      HasCompactSupport (fun x => Φ x - x) ∧
      (∀ x v w, (1+f (Φ x)) * planarArea (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = planarArea v w) ∧
      (∀ i, Φ '' roundDisk (R i) = roundDisk (R i)) := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,htan⟩ :=
    exists_relative_planar_primitive hf hfc hf0 R hR hRi hz
  have hXs := moserField_smooth hf hU hV hpos
  have hXc := moserField_hasCompactSupport (f := f) hUc hVc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  let X : C(ℝ × Plane,Plane) := ⟨moserField f U V,hXs.continuous⟩
  let K := tsupport U ∪ tsupport V
  have hK : IsCompact K := hUc.union hVc
  have hfix (t : ℝ) (x : Plane) (hx : x ∉ K) : X (t,x) = 0 := by
    have hu : U x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hv : V x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    change moserField f U V (t,x) = 0
    simp [moserField,hu,hv]
  obtain ⟨Φ,hΦ,hΦi,_,hΦc,hΦarea,_,hΦdisk⟩ := exists_density_transport_relative X hL hXs hXc
    (moserDensity f) (moserDensity_smooth hf) planarArea
    (moserField_transport hf hU hV hpos hcurl) K hK hfix R hR
    (fun i => moserField_tangent (htan i)) 0 1
  refine ⟨Φ,hΦ,hΦi,hΦc,?_,hΦdisk⟩
  intro x v w
  simpa only [zero_add,moserDensity,Real.smoothTransition.one,Real.smoothTransition.zero,
    one_mul,zero_mul,add_zero] using hΦarea x v w

theorem homeomorph_image_closedRoundDisk (Φ : Plane ≃ₜ Plane) (R : ℝ)
    (hcircle : ∀ p, radiusSq (Φ p) = R^2 ↔ radiusSq p = R^2) :
    Φ '' closedRoundDisk R = closedRoundDisk R := by
  apply Set.Subset.antisymm
  · exact (homeomorph_mapsTo_closedRoundDisk Φ R (fun p => (hcircle p).mpr)).image_subset
  · intro p hp
    have hi : ∀ q, radiusSq (Φ.symm q) = R^2 → radiusSq q = R^2 := by
      intro q hq
      simpa only [Homeomorph.apply_symm_apply] using (hcircle (Φ.symm q)).mpr hq
    exact ⟨Φ.symm p,homeomorph_mapsTo_closedRoundDisk Φ.symm R
      (fun q hq => (hcircle (Φ.symm q)).mp (by simpa only [Homeomorph.apply_symm_apply] using hq)) hp,
      Φ.apply_symm_apply p⟩

def backgroundDensity (g f : Plane → ℝ) (p : ℝ × Plane) : ℝ :=
  g p.2 + Real.smoothTransition p.1 * f p.2

theorem backgroundDensity_positive {g f : Plane → ℝ}
    (hg : ∀ x, 0 < g x) (hf : ∀ x, 0 < g x+f x) (p : ℝ × Plane) :
    0 < backgroundDensity g f p := by
  have hb := Real.smoothTransition.nonneg p.1
  have hc := Real.smoothTransition.le_one p.1
  unfold backgroundDensity
  by_cases hx : 0 ≤ f p.2
  · exact add_pos_of_pos_of_nonneg (hg p.2) (mul_nonneg hb hx)
  · have hx' : f p.2 < 0 := lt_of_not_ge hx
    have hmul := mul_le_mul_of_nonpos_right hc hx'.le
    nlinarith [hf p.2]

theorem backgroundDensity_smooth {g f : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (backgroundDensity g f) :=
  (hg.comp contDiff_snd).add ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (hf.comp contDiff_snd))

def backgroundField (g f U V : Plane → ℝ) (p : ℝ × Plane) : Plane :=
  (-(deriv Real.smoothTransition p.1) * V p.2 / backgroundDensity g f p,
    (deriv Real.smoothTransition p.1) * U p.2 / backgroundDensity g f p)

theorem backgroundField_smooth {g f U V : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hgpos : ∀ x, 0 < g x) (hpos : ∀ x, 0 < g x+f x) :
    ContDiff ℝ ∞ (backgroundField g f U V) := by
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  exact (((hβ.comp contDiff_fst).neg.mul (hV.comp contDiff_snd)).div
    (backgroundDensity_smooth hg hf) (fun p => (backgroundDensity_positive hgpos hpos p).ne')).prodMk
    (((hβ.comp contDiff_fst).mul (hU.comp contDiff_snd)).div
      (backgroundDensity_smooth hg hf) (fun p => (backgroundDensity_positive hgpos hpos p).ne'))

theorem backgroundField_compact {g f U V : Plane → ℝ}
    (hU : HasCompactSupport U) (hV : HasCompactSupport V) : HasCompactSupport (backgroundField g f U V) := by
  apply HasCompactSupport.intro (smoothTransition_deriv_compact.prod (hU.union hV))
  intro p hp
  have hn : p.1 ∉ tsupport (deriv Real.smoothTransition) ∨ p.2 ∉ tsupport U ∪ tsupport V := by
    simpa only [mem_prod, not_and_or] using hp
  rcases hn with ht | hx
  · simp [backgroundField, image_eq_zero_of_notMem_tsupport ht]
  · have hUx : U p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hVx : V p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    simp [backgroundField,hUx,hVx]

theorem backgroundField_transport {g f U V : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (hgpos : ∀ x, 0 < g x) (hpos : ∀ x, 0 < g x+f x)
    (hcurl : ∀ p, deriv (fun x => V (x,p.2)) p.1 - deriv (fun t => U (p.1,t)) p.2 = f p)
    (p : ℝ × Plane) (v w : Plane) :
    fderiv ℝ (backgroundDensity g f) p (1,backgroundField g f U V p) * planarArea v w +
      backgroundDensity g f p * (planarArea (fderiv ℝ (backgroundField g f U V) p (0,v)) w +
        planarArea v (fderiv ℝ (backgroundField g f U V) p (0,w))) = 0 := by
  let X := backgroundField g f U V
  let ρ := backgroundDensity g f
  let b := deriv Real.smoothTransition p.1
  let d := fderiv ℝ ρ p
  let A := (fderiv ℝ X p).comp (ContinuousLinearMap.inr ℝ ℝ Plane)
  have hXd : Differentiable ℝ X := (backgroundField_smooth hg hf hU hV hgpos hpos).differentiable (by simp)
  have hρd : Differentiable ℝ ρ := (backgroundDensity_smooth hg hf).differentiable (by simp)
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hflux1 : d (0,(1,0)) * (X p).1 + ρ p * (A (1,0)).1 =
      -b * fderiv ℝ V p.2 (1,0) := by
    have hd := (hasDerivAt_horizontal_first hρd p).mul (hasDerivAt_horizontal_first hXd p).fst
    have he : (fun x => ρ (p.1,(x,p.2.2)) * (X (p.1,(x,p.2.2))).1) =
        fun x => -b * V (x,p.2.2) := by
      funext x
      dsimp [X,ρ,backgroundField,b]
      field_simp [(backgroundDensity_positive hgpos hpos (p.1,(x,p.2.2))).ne']
    change HasDerivAt (fun x => ρ (p.1,(x,p.2.2)) * (X (p.1,(x,p.2.2))).1) _ p.2.1 at hd
    rw [he] at hd
    have hd' := ((hVd p.2).hasFDerivAt.comp_hasDerivAt p.2.1
      ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2))).const_mul (-b)
    exact hd.unique hd'
  have hflux2 : d (0,(0,1)) * (X p).2 + ρ p * (A (0,1)).2 =
      b * fderiv ℝ U p.2 (0,1) := by
    have hd := (hasDerivAt_horizontal_second hρd p).mul (hasDerivAt_horizontal_second hXd p).snd
    have he : (fun y => ρ (p.1,(p.2.1,y)) * (X (p.1,(p.2.1,y))).2) =
        fun y => b * U (p.2.1,y) := by
      funext y
      dsimp [X,ρ,backgroundField,b]
      field_simp [(backgroundDensity_positive hgpos hpos (p.1,(p.2.1,y))).ne']
    change HasDerivAt (fun y => ρ (p.1,(p.2.1,y)) * (X (p.1,(p.2.1,y))).2) _ p.2.2 at hd
    rw [he] at hd
    have hd' := ((hUd p.2).hasFDerivAt.comp_hasDerivAt p.2.2
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2))).const_mul b
    exact hd.unique hd'
  have ht : d (1,(0,0)) = b * f p.2 := by
    have hd := (hρd p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    have hβ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    have hb := (hβ.differentiable (by simp) p.1).hasDerivAt
    have hd' := (hb.mul_const (f p.2)).const_add (g p.2)
    exact hd.unique hd'
  have hc : fderiv ℝ V p.2 (1,0) - fderiv ℝ U p.2 (0,1) = f p.2 := by
    simpa only [plane_deriv_first hVd,plane_deriv_second hUd] using hcurl p.2
  have hlin : d (1,X p) = d (1,(0,0)) + (X p).1 * d (0,(1,0)) + (X p).2 * d (0,(0,1)) := by
    have he : ((1:ℝ),X p) = ((1:ℝ),(0:Plane)) +
        (X p).1 • ((0:ℝ),((1:ℝ),(0:ℝ))) + (X p).2 • ((0:ℝ),((0:ℝ),(1:ℝ))) := by
      ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hdiv : d (1,X p) + ρ p * ((A (1,0)).1+(A (0,1)).2) = 0 := by
    rw [hlin]
    linear_combination hflux1 + hflux2 + ht - b * hc
  change d (1,X p) * planarArea v w + ρ p * (planarArea (A v) w + planarArea v (A w)) = 0
  rw [planarArea_trace_identity]
  linear_combination (planarArea v w) * hdiv

theorem backgroundField_tangent {g f U V : Plane → ℝ} {R : ℝ}
    (ht : ∀ p, radiusSq p = R^2 → -p.2*U p+p.1*V p = 0) :
    ∀ t p, radiusSq p = R^2 → radialDrift (backgroundField g f U V) (t,p) = 0 := by
  intro t p hp
  have he := ht p hp
  unfold radialDrift backgroundField
  dsimp only
  calc
    2*(p.1*(-deriv Real.smoothTransition t*V p/backgroundDensity g f (t,p)) +
      p.2*(deriv Real.smoothTransition t*U p/backgroundDensity g f (t,p))) =
      (-2*deriv Real.smoothTransition t/backgroundDensity g f (t,p)) * (-p.2*U p+p.1*V p) := by ring
    _ = 0 := by rw [he,mul_zero]

theorem exists_relative_background_moser {ι : Type*} [Fintype ι]
    {g f : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : (∫ p, f p) = 0)
    (hgpos : ∀ x, 0 < g x) (hpos : ∀ x, 0 < g x+f x)
    (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i, (∫ p in roundDisk (R i), f p) = 0) :
    ∃ Φ : Plane ≃ₜ Plane, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      HasCompactSupport (fun x => Φ x - x) ∧
      (∀ x v w, (g (Φ x)+f (Φ x)) * planarArea (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) =
        g x * planarArea v w) ∧
      (∀ i, Φ '' closedRoundDisk (R i) = closedRoundDisk (R i)) := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,htan⟩ :=
    exists_relative_planar_primitive hf hfc hf0 R hR hRi hz
  have hXs := backgroundField_smooth hg hf hU hV hgpos hpos
  have hXc := backgroundField_compact (g := g) (f := f) hUc hVc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  let X : C(ℝ × Plane,Plane) := ⟨backgroundField g f U V,hXs.continuous⟩
  let K := tsupport U ∪ tsupport V
  have hK : IsCompact K := hUc.union hVc
  have hfix (t : ℝ) (x : Plane) (hx : x ∉ K) : X (t,x) = 0 := by
    have hu : U x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
    have hv : V x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inr h))
    change backgroundField g f U V (t,x) = 0
    simp [backgroundField,hu,hv]
  obtain ⟨Φ,hΦ,hΦi,_,hΦc,hΦarea,hΦcircle,_⟩ := exists_density_transport_relative X hL hXs hXc
    (backgroundDensity g f) (backgroundDensity_smooth hg hf) planarArea
    (backgroundField_transport hg hf hU hV hgpos hpos hcurl) K hK hfix R hR
    (fun i => backgroundField_tangent (htan i)) 0 1
  refine ⟨Φ,hΦ,hΦi,hΦc,?_,?_⟩
  · intro x v w
    simpa only [zero_add,backgroundDensity,Real.smoothTransition.one,Real.smoothTransition.zero,
      one_mul,zero_mul,add_zero] using hΦarea x v w
  · intro i
    exact homeomorph_image_closedRoundDisk Φ (R i) (hΦcircle i)


end

section
open scoped ContDiff Topology NNReal
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def parameterSegmentLinear : (P × ℝ) →L[ℝ] C(Time,P × ℝ) :=
  LinearMap.mkContinuous {
    toFun := fun p => ⟨fun s => (p.1,(s:ℝ)*p.2),
      continuous_const.prodMk (continuous_subtype_val.mul continuous_const)⟩
    map_add' := by intros; ext s <;> simp [mul_add]
    map_smul' := by intros; ext s <;> simp [mul_left_comm] }
    1 (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro s
      change ‖(p.1,(s:ℝ)*p.2)‖ ≤ ‖p‖
      simp only [Prod.norm_def,norm_mul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
      apply max_le
      · exact le_max_left _ _
      · exact (mul_le_of_le_one_left (abs_nonneg p.2) s.property.2).trans (le_max_right _ _))

def parameterSegmentPath (a : ℝ) (p : P × ℝ) : C(Time,P × ℝ) :=
  constantPath (0,a) + parameterSegmentLinear (p-(0,a))

@[simp] theorem parameterSegmentPath_apply (a : ℝ) (p : P × ℝ) (s : Time) :
    parameterSegmentPath a p s = (p.1,a+(s:ℝ)*(p.2-a)) := by
  change (0+(p.1-0),a+(s:ℝ)*(p.2-a)) = _
  simp

theorem parameterSegmentPath_smooth (a : ℝ) : ContDiff ℝ ∞ (parameterSegmentPath (P := P) a) :=
  contDiff_const.add ((parameterSegmentLinear (P := P)).contDiff.comp (contDiff_id.sub contDiff_const))

theorem parameter_segment_integral_eq (f : P × ℝ → ℝ) (hf : Continuous f)
    (a : ℝ) (p : P × ℝ) :
    (∫ x in a..p.2, f (p.1,x)) =
      (p.2-a) * pathAverage ((⟨f,hf⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)) := by
  let u := (⟨f,hf⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)
  have he : (∫ s in (0:ℝ)..1, extendPath u s) =
      ∫ s in (0:ℝ)..1, f (p.1,a+s*(p.2-a)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    rw [show extendPath u s = u ⟨s,hs⟩ from extendPath_coe u ⟨s,hs⟩]
    change f (parameterSegmentPath a p ⟨s,hs⟩) = _
    rw [parameterSegmentPath_apply]
  change _ = (p.2-a) * (∫ s in (0:ℝ)..1, extendPath u s)
  rw [he]
  have hi := intervalIntegral.smul_integral_comp_add_mul (fun x => f (p.1,x))
    (a := (0:ℝ)) (b := 1) (p.2-a) a
  simpa only [smul_eq_mul,mul_zero,mul_one,add_zero,add_sub_cancel,mul_comm] using hi.symm

variable [FiniteDimensional ℝ P]

theorem contDiff_parameter_segment_integral {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : P × ℝ => ∫ x in a..p.2, f (p.1,x)) := by
  have he : (fun p : P × ℝ => ∫ x in a..p.2, f (p.1,x)) =
      fun p => (p.2-a)*pathAverage
        ((⟨f,hf.continuous⟩ : C(P × ℝ,ℝ)).comp (parameterSegmentPath a p)) := by
    funext p
    exact parameter_segment_integral_eq f hf.continuous a p
  rw [he]
  exact (contDiff_snd.sub contDiff_const).mul
    (pathAverage.contDiff.comp ((postcomp_contDiff (K := Time) (E := P × ℝ) (F := ℝ) hf).comp (parameterSegmentPath_smooth (P := P) a)))

theorem planarPrimitive_parameter_smooth {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (A : ℝ) :
    ContDiff ℝ ∞ (fun p : P × Plane => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2) ∧
    ContDiff ℝ ∞ (fun p : P × Plane => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2) := by
  have hff : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => f (p.1.1,(p.2,p.1.2))) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
  have hg : ContDiff ℝ ∞ (fun p : P × ℝ => planarMarginal A (fun x => f (p.1,x)) p.2) :=
    (contDiff_parameter_segment_integral hff (-A)).comp (contDiff_id.prodMk contDiff_const)
  have hG : ContDiff ℝ ∞ (fun p : P × Plane =>
      ∫ t in -A..p.2.2, planarMarginal A (fun x => f (p.1,x)) t) :=
    (contDiff_parameter_segment_integral hg (-A)).comp
      (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  refine ⟨((hρ.comp (contDiff_fst.comp contDiff_snd)).neg.mul hG),?_⟩
  have hF : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ =>
      f (p.1.1,(p.2,p.1.2)) - ρ p.2*planarMarginal A (fun x => f (p.1.1,x)) p.1.2) :=
    hff.sub ((hρ.comp contDiff_snd).mul (hg.comp contDiff_fst))
  exact (contDiff_parameter_segment_integral hF (-A)).comp
    ((contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).prodMk (contDiff_fst.comp contDiff_snd))

omit [FiniteDimensional ℝ P] in
theorem planarPrimitive_zero_outside {A : ℝ} (hA : 0 ≤ A) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hfs : ∀ x t, A ≤ |x| ∨ A ≤ |t| → f (x,t) = 0)
    (hρs : ∀ x, A ≤ |x| → ρ x = 0)
    (hρ1 : (∫ x in -A..A, ρ x) = 1)
    (hg : Continuous (planarMarginal A f))
    (hf0 : (∫ t in -A..A, planarMarginal A f t) = 0) :
    ∀ p, A ≤ |p.1| ∨ A ≤ |p.2| →
      planarPrimitiveX A f ρ p = 0 ∧ planarPrimitiveY A f ρ p = 0 := by
  have hgt (t : ℝ) (ht : A ≤ |t|) : planarMarginal A f t = 0 := by
    unfold planarMarginal
    have he : (fun x => f (x,t)) = fun _ => (0:ℝ) := by
      funext x
      exact hfs x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hF (t : ℝ) : (∫ x in -A..A, f (x,t) - ρ x * planarMarginal A f t) = 0 := by
    have hc : Continuous (fun x => f (x,t)) := hf.comp (continuous_id.prodMk continuous_const)
    have hd : Continuous (fun x => ρ x * planarMarginal A f t) := hρ.mul continuous_const
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable (-A) A)
      (hd.intervalIntegrable (-A) A)]
    rw [intervalIntegral.integral_mul_const, hρ1, one_mul]
    exact sub_self _
  have hzero (p : ℝ × ℝ) (hp : A ≤ |p.1| ∨ A ≤ |p.2|) :
      planarPrimitiveX A f ρ p = 0 ∧ planarPrimitiveY A f ρ p = 0 := by
    rcases hp with hp | hp
    · constructor
      · simp [planarPrimitiveX, hρs _ hp]
      · apply interval_primitive_zero_outside hA
          ((hf.comp (continuous_id.prodMk continuous_const)).sub (hρ.mul continuous_const))
          (fun x hx => by
            change f (x,p.2) - ρ x * planarMarginal A f p.2 = 0
            rw [hfs x p.2 (Or.inl hx),hρs x hx]; ring) (hF p.2) hp
    · constructor
      · unfold planarPrimitiveX
        rw [interval_primitive_zero_outside hA hg hgt hf0 hp, mul_zero]
      · unfold planarPrimitiveY
        have he : (fun x => f (x,p.2) - ρ x * planarMarginal A f p.2) = fun _ => (0:ℝ) := by
          funext x
          rw [hfs x p.2 (Or.inr hp), hgt p.2 hp]
          ring
        rw [he,intervalIntegral.integral_zero]
  exact hzero

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in

theorem compactSupport_fiber {Q F : Type*} [TopologicalSpace Q] [T2Space Q]
    [Zero F] {f : P × Q → F} (hc : HasCompactSupport f) (y : P) :
    HasCompactSupport (fun x => f (y,x)) := by
  apply HasCompactSupport.intro (hc.image continuous_snd)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(y,x),h,rfl⟩)

theorem exists_parametric_compact_primitive {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : ∀ y, (∫ x, f (y,x)) = 0) :
    ∃ U V : P × Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y p, deriv (fun x => V (y,(x,p.2))) p.1 -
        deriv (fun t => U (y,(p.1,t))) p.2 = f (y,p)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, U (y,x) = 0 ∧ V (y,x) = 0 := by
  obtain ⟨A,hA,hbound⟩ := hfc.isBounded.subset_ball_lt 1 (0 : P × Plane)
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hzero (y : P) (x t : ℝ) (ht : A ≤ ‖y‖ ∨ A ≤ |x| ∨ A ≤ |t|) : f (y,(x,t)) = 0 := by
    by_contra hn
    have hb := hbound (subset_tsupport f (show (y,(x,t)) ∈ support f from hn))
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] at hb
    rcases ht with ht | ht | ht
    · exact (not_lt_of_ge ht) hb.1
    · exact (not_lt_of_ge ht) hb.2.1
    · exact (not_lt_of_ge ht) hb.2.2
  let b : ContDiffBump (0 : ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρs (x : ℝ) (hx : A ≤ |x|) : ρ x = 0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hb' : |x| < A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hb'
  have hρ1 : (∫ x in -A..A, ρ x) = 1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact b.integral_normed
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hg (y : P) : ContDiff ℝ ∞ (planarMarginal A (fun x => f (y,x))) :=
    planarMarginal_smooth (hfy y) A
  have hgt (y : P) (t : ℝ) (ht : A ≤ |t|) : planarMarginal A (fun x => f (y,x)) t = 0 := by
    unfold planarMarginal
    have he : (fun x => f (y,(x,t))) = fun _ => (0:ℝ) := funext fun x => hzero y x t (Or.inr (Or.inr ht))
    rw [he,intervalIntegral.integral_zero]
  have hgm (y : P) (t : ℝ) : planarMarginal A (fun x => f (y,x)) t = ∫ x, f (y,(x,t)) :=
    integral_eq_full_of_box_support (fun x hx => hzero y x t (Or.inr (Or.inl hx)))
  have hgm0 (y : P) : (∫ t in -A..A, planarMarginal A (fun x => f (y,x)) t) = 0 := by
    rw [integral_eq_full_of_box_support (hgt y)]
    simp_rw [hgm]
    rw [← integral_prod_symm (fun x => f (y,x))]
    · exact hf0 y
    · exact (hfy y).continuous.integrable_of_hasCompactSupport (compactSupport_fiber hfc y)
  let U : P × Plane → ℝ := fun p => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2
  let V : P × Plane → ℝ := fun p => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2
  have huv (p : P × Plane) (hp : p ∉ Metric.closedBall 0 A) : U p = 0 ∧ V p = 0 := by
    have hp' : A < max ‖p.1‖ (max |p.2.1| |p.2.2|) := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hp
    rcases lt_max_iff.mp hp' with hp' | hp'
    · have he : (fun x => f (p.1,x)) = fun _ => (0:ℝ) := by
        funext x
        exact hzero p.1 x.1 x.2 (Or.inl hp'.le)
      change planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2 = 0 ∧
        planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2 = 0
      rw [he]
      simp [planarPrimitiveX,planarPrimitiveY,planarMarginal]
    · apply planarPrimitive_zero_outside hA0.le (hfy p.1).continuous hρ.continuous
        (fun x t ht => hzero p.1 x t (Or.inr ht)) hρs hρ1 (hg p.1).continuous (hgm0 p.1) p.2
      exact (lt_max_iff.mp hp').imp le_of_lt le_of_lt
  refine ⟨U,V,(planarPrimitive_parameter_smooth hf hρ A).1,
    (planarPrimitive_parameter_smooth hf hρ A).2,
    HasCompactSupport.intro (isCompact_closedBall 0 A) (fun p hp => (huv p hp).1),
    HasCompactSupport.intro (isCompact_closedBall 0 A) (fun p hp => (huv p hp).2),?_,?_⟩
  · intro y p
    exact planarPrimitive_curl (hfy y).continuous hρ.continuous (hg y).continuous p
  · intro y hy x
    have he : (fun x => f (y,x)) = fun _ => (0:ℝ) := funext hy
    change planarPrimitiveX A (fun x => f (y,x)) ρ x = 0 ∧
      planarPrimitiveY A (fun x => f (y,x)) ρ x = 0
    rw [he]
    simp [planarPrimitiveX,planarPrimitiveY,planarMarginal]


end

section
open scoped ContDiff
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem fixed_spatial_planar_primitive {A : ℝ} (hA : 0<A)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ y x t, A ≤ |x| ∨ A ≤ |t| → f (y,(x,t))=0)
    (hmass : ∀ y, (∫ x, f (y,x))=0) :
    ∃ U V : P × Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      (∀ y x t, A ≤ |x| ∨ A ≤ |t| → U (y,(x,t))=0 ∧ V (y,(x,t))=0) ∧
      (∀ y p, deriv (fun x => V (y,(x,p.2))) p.1 -
        deriv (fun t => U (y,(p.1,t))) p.2 = f (y,p)) ∧
      ∀ y, (∀ x, f (y,x)=0) → ∀ x, U (y,x)=0 ∧ V (y,x)=0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨A/2,A,by positivity,by linarith⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρs (x : ℝ) (hx : A ≤ |x|) : ρ x=0 := by
    by_contra hn
    have hb : x ∈ support (b.normed volume) := hn
    rw [b.support_normed_eq] at hb
    have hh : |x|<A := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hb
    exact (not_lt_of_ge hx) hh
  have hρ1 : (∫ x in -A..A, ρ x)=1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact b.integral_normed
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hfc (y : P) : HasCompactSupport (fun x => f (y,x)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) A)
    intro p hp
    have hh : A < max |p.1| |p.2| := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hp
    exact hzero y p.1 p.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  have hg (y : P) : ContDiff ℝ ∞ (planarMarginal A (fun x => f (y,x))) :=
    planarMarginal_smooth (hfy y) A
  have hgt (y : P) (t : ℝ) (ht : A ≤ |t|) : planarMarginal A (fun x => f (y,x)) t=0 := by
    unfold planarMarginal
    have he : (fun x => f (y,(x,t))) = fun _ => (0:ℝ) := funext fun x => hzero y x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hgm (y : P) (t : ℝ) : planarMarginal A (fun x => f (y,x)) t = ∫ x, f (y,(x,t)) :=
    integral_eq_full_of_box_support (fun x hx => hzero y x t (Or.inl hx))
  have hgm0 (y : P) : (∫ t in -A..A, planarMarginal A (fun x => f (y,x)) t)=0 := by
    rw [integral_eq_full_of_box_support (hgt y)]
    simp_rw [hgm]
    rw [←integral_prod_symm (fun x => f (y,x))]
    · exact hmass y
    · exact (hfy y).continuous.integrable_of_hasCompactSupport (hfc y)
  let U : P × Plane → ℝ := fun p => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2
  let V : P × Plane → ℝ := fun p => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2
  refine ⟨U,V,(planarPrimitive_parameter_smooth hf hρ A).1,
    (planarPrimitive_parameter_smooth hf hρ A).2,?_,?_,?_⟩
  · intro y x t ht
    exact planarPrimitive_zero_outside hA.le (hfy y).continuous hρ.continuous
      (hzero y) hρs hρ1 (hg y).continuous (hgm0 y) (x,t) ht
  · intro y p
    exact planarPrimitive_curl (hfy y).continuous hρ.continuous (hg y).continuous p
  · intro y hy x
    have he : (fun x => f (y,x)) = fun _ => (0:ℝ) := funext hy
    change planarPrimitiveX A (fun x => f (y,x)) ρ x=0 ∧
      planarPrimitiveY A (fun x => f (y,x)) ρ x=0
    rw [he]
    simp [planarPrimitiveX,planarPrimitiveY,planarMarginal]


end

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def euclideanExteriorOneForm (α : E → E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ α x - (fderiv ℝ α x).flip

theorem fderiv_clm_eval {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → E →L[ℝ] F} {x : E} (hg : DifferentiableAt ℝ g x) (u v : E) :
    fderiv ℝ (fun y => g y v) x u = fderiv ℝ g x u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv]
  simp

theorem fderiv_bilinear_eval {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hg : DifferentiableAt ℝ g x) (u v w : E) :
    fderiv ℝ (fun y => g y v w) x u = fderiv ℝ g x u v w := by
  rw [fderiv_clm_eval (hg.clm_apply (differentiableAt_const v)),fderiv_clm_eval hg]

theorem euclideanExteriorOneForm_smooth {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (euclideanExteriorOneForm α) := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ α x) := hα.fderiv_right (by simp)
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ)
  have hf : ContDiff ℝ ∞ (fun x => (fderiv ℝ α x).flip) := hflip.comp hd
  exact hd.sub hf

theorem euclideanExteriorOneForm_fderiv {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (x u v w : E) :
    fderiv ℝ (euclideanExteriorOneForm α) x u v w =
      fderiv ℝ (fderiv ℝ α) x u v w - fderiv ℝ (fderiv ℝ α) x u w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ α) x :=
    (hα.fderiv_right (m := ∞) (by simp)).contDiffAt.differentiableAt (by simp)
  rw [←fderiv_bilinear_eval ((euclideanExteriorOneForm_smooth hα).contDiffAt.differentiableAt (by simp))]
  change fderiv ℝ ((fun y => fderiv ℝ α y v w) - (fun y => fderiv ℝ α y w v)) x u = _
  rw [fderiv_sub (hd.clm_apply (differentiableAt_const v) |>.clm_apply (differentiableAt_const w))
    (hd.clm_apply (differentiableAt_const w) |>.clm_apply (differentiableAt_const v))]
  simp only [sub_apply,fderiv_bilinear_eval hd]

theorem euclideanExteriorOneForm_closed {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (x u v w : E) :
    fderiv ℝ (euclideanExteriorOneForm α) x u v w -
      fderiv ℝ (euclideanExteriorOneForm α) x v u w +
      fderiv ℝ (euclideanExteriorOneForm α) x w u v = 0 := by
  have hs := (hα.contDiffAt (x := x)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [euclideanExteriorOneForm_fderiv hα]
  rw [hs.eq u v,hs.eq u w,hs.eq v w]
  ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
