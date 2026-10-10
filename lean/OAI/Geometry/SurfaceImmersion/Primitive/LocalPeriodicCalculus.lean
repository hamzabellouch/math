import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicPrimitive
import OAI.Geometry.SurfaceImmersion.Primitive.SlowPeriodicDerivative

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma smooth_slice [NormedSpace ℝ E] {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) {p : P} (hp : p ∈ S) :
    ContDiff ℝ ∞ (fun t => F (p, t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp t
    (contDiff_const.prodMk contDiff_id).contDiffAt

def bundleOn (F : P × ℝ → E) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1) : P → C(Period, E) := by
  classical
  exact fun p => if hp : p ∈ S then
    bundle (fun t => F (p, t)) (hper p hp) (smooth_slice hS hF hp).continuous else 0

lemma bundleOn_apply (F : P × ℝ → E) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1)
    {p : P} (hp : p ∈ S) (t : ℝ) : bundleOn F S hS hF hper p (t : Period) = F (p, t) := by
  simp only [bundleOn, dite_eq_left hp, bundle_apply]

lemma bundleOn_smooth (F : P × ℝ → E) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => bundleOn F S hS hF hper z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := by
  apply hF.congr
  intro z hz
  exact bundleOn_apply F S hS hF hper hz.1 z.2

lemma angle_smooth {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (angleDerivative F) (S ×ˢ Set.univ) :=
  (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

lemma slow_smooth {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) (v : P) :
    ContDiffOn ℝ ∞ (slowDerivative F v) (S ×ˢ Set.univ) :=
  (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

lemma angle_hasDerivAt {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s => F (p, s)) (angleDerivative F (p, t)) t := by
  have hi : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ P ℝ) t := by
    simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inr ℝ P ℝ).hasFDerivAt (x := t)).add_const (p, 0)
  have hd := ((hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).differentiableAt
    (by simp)).hasFDerivAt.comp t hi
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    angleDerivative] using hd.hasDerivAt

lemma fderiv_slice {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ)) {p : P} (hp : p ∈ S) (v : P) (t : ℝ) :
    fderiv ℝ (fun q => F (q, t)) p v = slowDerivative F v (p, t) := by
  have hi : HasFDerivAt (fun q : P => (q, t)) (ContinuousLinearMap.inl ℝ P ℝ) p := by
    simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add] using
      ((ContinuousLinearMap.inl ℝ P ℝ).hasFDerivAt (x := p)).add_const (0, t)
  have hd := ((hF.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).differentiableAt
    (by simp)).hasFDerivAt.comp p hi
  change fderiv ℝ (F ∘ fun q => (q, t)) p v = _
  rw [hd.fderiv]
  rfl

lemma periodic_angle {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1) {p : P} (hp : p ∈ S) :
    Function.Periodic (fun t => angleDerivative F (p, t)) 1 := by
  have he : (fun t => angleDerivative F (p, t)) = deriv (fun t => F (p, t)) :=
    funext (fun t => (angle_hasDerivAt hS hF hp t).deriv.symm)
  rw [he]
  exact PeriodicCalculus.periodic_deriv (hper p hp)

lemma periodic_slow (F : P → C(Period, E)) {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) :
    Function.Periodic (fun t => slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t)) 1 := by
  intro t
  have he : (fun q => F q ((t + 1 : ℝ) : Period)) = fun q => F q (t : Period) :=
    funext (fun q => periodic_lift F q t)
  have hd := congrArg (fun f : P → E => fderiv ℝ f p v) he
  simpa only [fderiv_slice hS hF hp] using hd

def angleOn (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    P → C(Period, E) :=
  bundleOn (angleDerivative (fun z : P × ℝ => F z.1 (z.2 : Period))) S hS
    (angle_smooth hS hF) (fun _ hp => periodic_angle hS hF (fun p _ => periodic_lift F p) hp)

lemma angleOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (angleOn F S hS hF p (t : Period)) t := by
  rw [angleOn, bundleOn_apply _ _ _ _ _ hp]
  exact angle_hasDerivAt hS hF hp t

lemma angleOn_smooth (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => angleOn F S hS hF z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := bundleOn_smooth _ _ _ _ _

lemma angleOn_zero_at (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (hz : F p = 0) : angleOn F S hS hF p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  have hd := angleOn_hasDerivAt F S hS hF hp t
  rw [hz] at hd
  exact hd.unique (hasDerivAt_const t (0 : E))

def slowOn (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) : P → C(Period, E) :=
  bundleOn (slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v) S hS
    (slow_smooth hS hF v) (fun _ hp => periodic_slow F hS hF v hp)

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t

lemma slowOn_smooth (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ)) (v : P) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => slowOn F S hS hF v z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := bundleOn_smooth _ _ _ _ _


lemma slowOn_zero_on (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {O : Set P} (hO : IsOpen O) (hz : ∀ p ∈ O, F p = 0) (v : P)
    {p : P} (hp : p ∈ S) (hpO : p ∈ O) : slowOn F S hS hF v p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  rw [slowOn_apply F S hS hF v hp, ← fderiv_slice hS hF hp]
  have he : (fun q => F q (t : Period)) =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hO.mem_nhds hpO] with q hq
    rw [hz q hq]
    rfl
  rw [he.fderiv_eq, fderiv_const_apply, zero_apply]
  rfl

variable [FiniteDimensional ℝ P] [CompleteSpace E]

def primitiveOn (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) : P → C(Period, E) :=
  bundleOn (fun z : P × ℝ => PeriodicPrimitive.primitive (fun t => F z.1 (t : Period)) z.2)
    S hS (PeriodicPrimitive.contDiffOn_primitive_joint hS hF)
    (fun p hp => PeriodicPrimitive.primitive_periodic
      ((F p).continuous.comp (AddCircle.continuous_mk' 1)) (periodic_lift F p)
      ((PeriodicPrimitive.integral_lift_eq_haar (F p)).trans (hm p hp)))

lemma primitiveOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    primitiveOn F S hS hF hm p (t : Period) =
      PeriodicPrimitive.primitive (fun s => F p (s : Period)) t :=
  bundleOn_apply _ _ _ _ _ hp t

lemma primitiveOn_smooth (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => primitiveOn F S hS hF hm z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := bundleOn_smooth _ _ _ _ _

lemma primitiveOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveOn F S hS hF hm p (s : Period)) (F p (t : Period)) t := by
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_hasDerivAt ((F p).continuous.comp (AddCircle.continuous_mk' 1)) t

lemma primitiveOn_mean_zero (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) :
    average (primitiveOn F S hS hF hm p) = 0 := by
  rw [CovarianceCorrector.average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_mean_zero
    ((F p).continuous.comp (AddCircle.continuous_mk' 1))

lemma primitiveOn_zero_at (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (hz : F p = 0) :
    primitiveOn F S hS hF hm p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  rw [primitiveOn_apply F S hS hF hm hp, hz]
  exact PeriodicPrimitive.primitive_zero t

omit [CompleteSpace E] in
lemma slowOn_mean_zero (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) (v : P) {p : P} (hp : p ∈ S) :
    average (slowOn F S hS hF v p) = 0 := by
  let f : P × ℝ → E := fun z => F z.1 (z.2 : Period)
  have hzero : (fun q => ∫ t in 0..1, f (q, t)) =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact (PeriodicPrimitive.integral_lift_eq_haar (F q)).trans (hm q hq)
  have hd := (SmoothParameterIntegral.hasFDerivAt_integral_on hS hF 0 1 hp).fderiv
  change fderiv ℝ (fun q => ∫ t in 0..1, f (q, t)) p = _ at hd
  rw [hzero.fderiv_eq, fderiv_const_apply] at hd
  have he := congrArg (fun L : P →L[ℝ] E => L v) hd.symm
  have hi := ContinuousLinearMap.intervalIntegral_apply (μ := volume)
    (φ := fun t => SmoothParameterIntegral.partialDerivative f (p, t))
    ((smooth_slice hS (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)) hp).continuous
      |>.clm_comp continuous_const |>.intervalIntegrable 0 1) v
  rw [CovarianceCorrector.average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [slowOn_apply F S hS hF v hp]
  exact hi.symm.trans he

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
