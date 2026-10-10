import Mathlib
import OAI.Probability.SLE.RectangleMeans

namespace OAI

/-! Nested Means for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
universe u
lemma slice_oscillation_le_integral {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hl : LocallyLipschitzOn (Ioo a b) f)
    (hg : IntegrableOn g (Icc a b)) (hgn : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv f t‖ ≤ g t) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f x-f y‖ ≤ ∫ t in Icc a b, g t := by
  have hint (x y : ℝ) (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :
      ‖f y-f x‖ ≤ ∫ t in Icc a b, g t := by
    have hs : Icc x y ⊆ Ioo a b := by
      intro t ht
      exact ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc (hl.mono hs)
    have hAC : AbsolutelyContinuousOnInterval f x y :=
      (by simpa [uIcc_of_le hxy] using hK : LipschitzOnWith K f (uIcc x y)).absolutelyContinuousOnInterval
    rw [← hAC.integral_deriv_eq_sub, intervalIntegral.integral_of_le hxy]
    have hdint : IntegrableOn (deriv f) (Ioc x y) :=
      hAC.intervalIntegrable_deriv.1
    have hgin : IntegrableOn g (Ioc x y) := hg.mono_set (by
      intro t ht; exact ⟨hx.1.le.trans ht.1.le,ht.2.trans hy.2.le⟩)
    calc
      ‖∫ t in Ioc x y, deriv f t‖ ≤ ∫ t in Ioc x y, ‖deriv f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc x y, g t := integral_mono_ae hdint.norm hgin (by
        filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Ioc] with t ht htS
        exact ht (hs ⟨htS.1.le,htS.2⟩))
      _ ≤ ∫ t in Icc a b, g t := setIntegral_mono_set hg
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hgn t ht)
        (Eventually.of_forall fun t ht => ⟨hx.1.le.trans ht.1.le,ht.2.trans hy.2.le⟩)
  have hi (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo a b) :
      ‖f x-f y‖ ≤ ∫ t in Icc a b, g t := by
    rcases le_total x y with h | h
    · simpa only [norm_sub_rev] using hint x y hx hy h
    · exact hint y x hy hx h
  have hc : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hyall (x : ℝ) (hx : x ∈ Ioo a b) :
      ∀ y ∈ Icc a b, ‖f x-f y‖ ≤ ∫ t in Icc a b, g t := by
    intro y hy
    apply le_on_closure (fun y hy => hi x hx y hy) _ continuousOn_const (hc.symm ▸ hy)
    rw [hc]
    exact (continuousOn_const.sub hf).norm
  intro x hx y hy
  apply le_on_closure (fun x hx => hyall x hx y hy) _ continuousOn_const (hc.symm ▸ hx)
  rw [hc]
  exact (hf.sub continuousOn_const).norm

lemma locallyLipschitz_ae_differentiable {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hl : LocallyLipschitzOn D u) :
    ∀ᵐ z ∂volume, z ∈ D → DifferentiableAt ℝ u z := by
  classical
  have hloc (z : D) : ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ z.1 ∈ U ∧
      LipschitzOnWith K u U := by
    obtain ⟨K,t,ht,htl⟩ := hl z.2
    rw [nhdsWithin_eq_nhds.mpr (hD.mem_nhds z.2)] at ht
    obtain ⟨U,hUt,hUo,hzU⟩ := _root_.mem_nhds_iff.mp ht
    exact ⟨K,U,hUo,hzU,htl.mono hUt⟩
  choose K U hUo hxU hULip using hloc
  have hcov : D ⊆ ⋃ x : D, U x := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hxU ⟨z,hz⟩⟩
  obtain ⟨t,ht,htcov⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover U hUo hcov
  have ha (x : D) : ∀ᵐ z ∂volume, z ∈ U x → DifferentiableAt ℝ u z := by
    filter_upwards [(hULip x).ae_differentiableWithinAt_of_mem (μ := volume)] with z hz hzU
    exact (hz hzU).differentiableAt ((hUo x).mem_nhds hzU)
  filter_upwards [(ae_ball_iff ht).mpr (fun x _ => ha x)] with z hz hzD
  obtain ⟨x,htx,hzx⟩ := mem_iUnion₂.mp (htcov hzD)
  exact hz x htx hzx

def complexCoordinates (p : ℝ × ℝ) : ℂ := p.1 + p.2*Complex.I

lemma complexCoordinates_eq (p : ℝ × ℝ) :
    complexCoordinates p = Complex.measurableEquivRealProd.symm p := by
  apply Complex.ext <;> simp [complexCoordinates]

lemma complexCoordinates_preserving : MeasurePreserving complexCoordinates volume volume := by
  simpa only [funext complexCoordinates_eq] using
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd

lemma complexCoordinates_continuous : Continuous complexCoordinates := by
  unfold complexCoordinates
  fun_prop

lemma vertical_isometry (x : ℝ) : Isometry (fun y : ℝ => complexCoordinates (x,y)) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm,complexCoordinates]
  have he : ((x:ℂ)+(y:ℂ)*Complex.I)-((x:ℂ)+(z:ℂ)*Complex.I) =
      ((y-z:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real]

lemma horizontal_isometry (y : ℝ) : Isometry (fun x : ℝ => complexCoordinates (x,y)) := by
  apply Isometry.of_dist_eq
  intro x z
  simp [dist_eq_norm,complexCoordinates, ← Complex.ofReal_sub]

lemma locallyLipschitz_comp_of_isometry {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hu : LocallyLipschitzOn D u) {f : ℝ → ℂ} (hf : Isometry f) {s : Set ℝ}
    (hs : MapsTo f s D) : LocallyLipschitzOn s (u ∘ f) := by
  intro x hx
  obtain ⟨K,t,ht,hKt⟩ := hu (hs hx)
  rw [nhdsWithin_eq_nhds.mpr (hD.mem_nhds (hs hx))] at ht
  refine ⟨K*1,f ⁻¹' t,mem_nhdsWithin_of_mem_nhds (hf.continuous.continuousAt.preimage_mem_nhds ht),?_⟩
  exact hKt.comp hf.lipschitzWith.lipschitzOnWith (fun _ h => h)

lemma vertical_deriv_norm_le {u : ℂ → ℝ} {x y : ℝ}
    (hu : DifferentiableAt ℝ u (complexCoordinates (x,y))) :
    ‖deriv (fun t : ℝ => u (complexCoordinates (x,t))) y‖ ≤
      ‖gradient u (complexCoordinates (x,y))‖ := by
  have hi : HasDerivAt (fun t : ℝ => complexCoordinates (x,t)) Complex.I y := by
    simpa [complexCoordinates] using
      ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x:ℂ)
  have hh := hu.hasFDerivAt.comp_hasDerivAt y hi
  change ‖deriv (u ∘ (fun t : ℝ => complexCoordinates (x,t))) y‖ ≤ _
  rw [hh.deriv, ← inner_gradient_left]
  simpa using norm_inner_le_norm (𝕜 := ℝ) (gradient u (complexCoordinates (x,y))) Complex.I

lemma horizontal_deriv_norm_le {u : ℂ → ℝ} {x y : ℝ}
    (hu : DifferentiableAt ℝ u (complexCoordinates (x,y))) :
    ‖deriv (fun t : ℝ => u (complexCoordinates (t,y))) x‖ ≤
      ‖gradient u (complexCoordinates (x,y))‖ := by
  have hi : HasDerivAt (fun t : ℝ => complexCoordinates (t,y)) 1 x := by
    simpa [complexCoordinates] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y:ℂ)*Complex.I)
  have hh := hu.hasFDerivAt.comp_hasDerivAt x hi
  change ‖deriv (u ∘ (fun t : ℝ => complexCoordinates (t,y))) x‖ ≤ _
  rw [hh.deriv, ← inner_gradient_left]
  simpa using norm_inner_le_norm (𝕜 := ℝ) (gradient u (complexCoordinates (x,y))) 1

def cartesianRectangle (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

lemma cartesianRectangle_preimage (a b c d : ℝ) :
    cartesianRectangle a b c d = Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d) := by
  ext z
  simp only [cartesianRectangle, mem_ofPred_eq,mem_preimage,mem_prod,mem_Icc,Complex.measurableEquivRealProd_apply]
  tauto

lemma cartesianRectangle_measurable (a b c d : ℝ) : MeasurableSet (cartesianRectangle a b c d) := by
  rw [cartesianRectangle_preimage]
  exact (measurableSet_Icc.prod measurableSet_Icc).preimage
    Complex.measurableEquivRealProd.measurable

lemma complexCoordinates_rect_preserving (a b c d : ℝ) :
    MeasurePreserving complexCoordinates
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))
      (volume.restrict (cartesianRectangle a b c d)) := by
  have h := complexCoordinates_preserving.restrict_preimage (cartesianRectangle_measurable a b c d)
  have he : complexCoordinates ⁻¹' cartesianRectangle a b c d = Icc a b ×ˢ Icc c d := by
    ext p
    simp only [mem_preimage,cartesianRectangle,mem_ofPred_eq,complexCoordinates,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,sub_self,add_zero,mul_one,zero_add,mem_prod,mem_Icc]
    tauto
  rwa [he,Measure.volume_eq_prod, ← Measure.prod_restrict] at h

lemma cartesianRectangle_compact (a b c d : ℝ) : IsCompact (cartesianRectangle a b c d) := by
  have he : cartesianRectangle a b c d = complexCoordinates '' (Icc a b ×ˢ Icc c d) := by
    ext z; constructor
    · intro hz
      refine ⟨(z.re,z.im),?_,?_⟩
      · exact ⟨⟨hz.1,hz.2.1⟩,hz.2.2⟩
      · apply Complex.ext <;> simp [complexCoordinates]
    · rintro ⟨p,hp,rfl⟩
      rcases hp with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
      simpa [cartesianRectangle,complexCoordinates] using And.intro ha (And.intro hb (And.intro hc hd))
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image complexCoordinates_continuous

lemma cartesianRectangle_integral {a b c d : ℝ} {u : ℂ → ℝ}
    (hu : IntegrableOn u (cartesianRectangle a b c d)) :
    (∫ z in cartesianRectangle a b c d, u z) =
      ∫ x in Icc a b, ∫ y in Icc c d, u (complexCoordinates (x,y)) := by
  have hp := complexCoordinates_rect_preserving a b c d
  have hemb : MeasurableEmbedding complexCoordinates := by
    simpa only [funext complexCoordinates_eq] using Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [← hp.integral_comp hemb]
  exact integral_prod _ ((hp.integrable_comp hu.aestronglyMeasurable).mpr hu)

def fullOpenStrip : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
def fullClosedStrip : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi}

lemma fullOpenStrip_isOpen : IsOpen fullOpenStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

lemma cartesianRectangle_ae_strip (a b : ℝ) :
    cartesianRectangle a b 0 Real.pi ≤ᵐ[volume] fullOpenStrip := by
  have hf (c : ℝ) : volume {z : ℂ | z.im = c} = 0 := by
    have hh := Complex.volume_preserving_equiv_real_prod.measure_preimage
      (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet
    simpa [Set.preimage,Measure.volume_eq_prod,Measure.prod_prod] using hh
  have h0 : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
    simpa only [ae_iff,not_not] using hf 0
  have hp : ∀ᵐ z : ℂ ∂volume, z.im ≠ Real.pi := by
    simpa only [ae_iff,not_not] using hf Real.pi
  filter_upwards [h0,hp] with z hz0 hzp hzQ
  exact ⟨lt_of_le_of_ne hzQ.2.2.1 hz0.symm,lt_of_le_of_ne hzQ.2.2.2 hzp⟩

lemma cartesianRectangle_volume (a b c d : ℝ) :
    volume (cartesianRectangle a b c d) = ENNReal.ofReal (b-a)*ENNReal.ofReal (d-c) := by
  rw [cartesianRectangle_preimage,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]

lemma unitSlab_norm_integral_le {u : ℂ → ℝ} {a : ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict (cartesianRectangle a (a+1) 0 Real.pi))) :
    (∫ z in cartesianRectangle a (a+1) 0 Real.pi, ‖gradient u z‖) ≤
      Real.sqrt (Real.pi * ∫ z in cartesianRectangle a (a+1) 0 Real.pi, ‖gradient u z‖^2) := by
  let Q := cartesianRectangle a (a+1) 0 Real.pi
  have hv : volume Q = ENNReal.ofReal Real.pi := by
    simp [Q,cartesianRectangle_volume]
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by simp [hv]⟩
  have hconst : MemLp (fun _ : ℂ => (1:ℝ)) 2 (volume.restrict Q) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := volume.restrict Q) (f := fun z => ‖gradient u z‖) (g := fun _ => (1:ℝ))
    (Eventually.of_forall fun z => norm_nonneg _) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hg.norm) (by simpa using hconst)
  simp only [mul_one,Real.rpow_two,← Real.sqrt_eq_rpow,one_pow,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,hv,ENNReal.toReal_ofReal Real.pi_pos.le] at hh
  simpa only [Real.sqrt_mul Real.pi_pos.le,mul_comm] using hh

lemma vertical_derivative_bound_ae {u : ℂ → ℝ} (hu : LocallyLipschitzOn fullOpenStrip u) :
    ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume, y ∈ Ioo 0 Real.pi →
      ‖deriv (fun t : ℝ => u (complexCoordinates (x,t))) y‖ ≤
        ‖gradient u (complexCoordinates (x,y))‖ := by
  have hd := locallyLipschitz_ae_differentiable fullOpenStrip_isOpen hu
  have hp := complexCoordinates_preserving.quasiMeasurePreserving.tendsto_ae.eventually hd
  rw [Measure.volume_eq_prod] at hp
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with x hx
  filter_upwards [hx] with y hy hyI
  apply vertical_deriv_norm_le
  apply hy
  simpa [fullOpenStrip,complexCoordinates] using hyI

lemma negativeSlab_mean_le {u : ℂ → ℝ}
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hz : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0)
    {a : ℝ} (ha : a+1 ≤ 0) :
    Real.pi⁻¹*(∫ z in cartesianRectangle a (a+1) 0 Real.pi, u z) ≤
      Real.sqrt (Real.pi * ∫ z in cartesianRectangle a (a+1) 0 Real.pi, ‖gradient u z‖^2) := by
  let Q := cartesianRectangle a (a+1) 0 Real.pi
  have hQ : Q ⊆ fullClosedStrip := fun _ h => h.2.2
  have hgQ : MemLp (gradient u) 2 (volume.restrict Q) :=
    hg.mono_measure (Measure.restrict_mono_ae (cartesianRectangle_ae_strip a (a+1)))
  have hv : volume Q < ⊤ := (cartesianRectangle_compact a (a+1) 0 Real.pi).measure_lt_top
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by simpa using hv⟩
  have hgI : IntegrableOn (fun z => ‖gradient u z‖) Q := (hgQ.integrable (by norm_num)).norm
  have huI : IntegrableOn u Q := (hu.mono hQ).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have hp := complexCoordinates_rect_preserving a (a+1) 0 Real.pi
  have hgp := (hp.integrable_comp hgI.aestronglyMeasurable).mpr hgI
  have hup := (hp.integrable_comp huI.aestronglyMeasurable).mpr huI
  have hder := vertical_derivative_bound_ae hl
  have hslice : ∀ᵐ x ∂volume.restrict (Icc a (a+1)),
      (∫ y in Icc 0 Real.pi, u (complexCoordinates (x,y))) ≤
        Real.pi * ∫ y in Icc 0 Real.pi, ‖gradient u (complexCoordinates (x,y))‖ := by
    filter_upwards [ae_restrict_of_ae hder,hgp.prod_right_ae,ae_restrict_mem measurableSet_Icc] with x hdx hgx hx
    have hcont : ContinuousOn (fun y => u (complexCoordinates (x,y))) (Icc 0 Real.pi) :=
      hu.comp (vertical_isometry x).continuous.continuousOn (by
        intro y hy; simpa [fullClosedStrip,complexCoordinates] using hy)
    have hlip : LocallyLipschitzOn (Ioo 0 Real.pi) (fun y => u (complexCoordinates (x,y))) :=
      locallyLipschitz_comp_of_isometry fullOpenStrip_isOpen hl (vertical_isometry x) (by
        intro y hy; simpa [fullOpenStrip,complexCoordinates] using hy)
    obtain ⟨y0,hy0,huy0⟩ := hz x (hx.2.trans ha)
    have hosc := slice_oscillation_le_integral Real.pi_pos hcont hlip hgx
      (fun _ _ => norm_nonneg _) hdx
    have hpoint (y : ℝ) (hy : y ∈ Icc 0 Real.pi) :
        u (complexCoordinates (x,y)) ≤ ∫ t in Icc 0 Real.pi, ‖gradient u (complexCoordinates (x,t))‖ := by
      have hh := hosc y hy y0 hy0
      rw [huy0,sub_zero,Real.norm_eq_abs] at hh
      exact (le_abs_self _).trans hh
    have hci : IntegrableOn (fun _ : ℝ => ∫ t in Icc 0 Real.pi, ‖gradient u (complexCoordinates (x,t))‖) (Icc 0 Real.pi) := continuousOn_const.integrableOn_Icc
    have hh := setIntegral_mono_on hcont.integrableOn_Icc hci measurableSet_Icc hpoint
    simpa [integral_const,Real.volume_Icc,Real.pi_pos.le] using hh
  have htotal := integral_mono_ae hup.integral_prod_left
    (hgp.integral_prod_left.const_mul Real.pi) hslice
  rw [integral_const_mul] at htotal
  have huEq := cartesianRectangle_integral huI
  have hgEq := cartesianRectangle_integral hgI
  change (∫ z in Q,u z) = _ at huEq
  change (∫ z in Q,‖gradient u z‖) = _ at hgEq
  simp only [Function.comp_def] at htotal
  rw [← huEq,← hgEq] at htotal
  calc
    Real.pi⁻¹*(∫ z in Q,u z) ≤ ∫ z in Q,‖gradient u z‖ := by
      have hh := mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr Real.pi_pos.le)
      simpa [← mul_assoc,Real.pi_pos.ne'] using hh
    _ ≤ _ := unitSlab_norm_integral_le hgQ

lemma interval_unit_mean_comparison {f g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc (-1) (a+1)))
    (hl : LocallyLipschitzOn (Ioo (-1) (a+1)) f)
    (hg : IntegrableOn g (Icc (-1) (a+1))) (hgn : ∀ t ∈ Icc (-1) (a+1), 0 ≤ g t)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo (-1) (a+1) → ‖deriv f t‖ ≤ g t) :
    (∫ t in Icc a (a+1), f t) ≤ (∫ t in Icc (-1) 0, f t) + ∫ t in Icc (-1) (a+1), g t := by
  have hA : Icc a (a+1) ⊆ Icc (-1) (a+1) := by
    intro t ht; exact ⟨by linarith [ht.1],ht.2⟩
  have hB : Icc (-1:ℝ) 0 ⊆ Icc (-1) (a+1) := by
    intro t ht; exact ⟨ht.1,by linarith [ht.2]⟩
  have hffA := (hf.mono hA).integrableOn_Icc (μ := volume)
  have hffB := (hf.mono hB).integrableOn_Icc (μ := volume)
  have hosc := slice_oscillation_le_integral (by linarith : (-1:ℝ)<a+1) hf hl hg hgn hd
  let B := ∫ t in Icc (-1) (a+1),g t
  have hpt (x : ℝ) (hx : x ∈ Icc a (a+1)) (y : ℝ) (hy : y ∈ Icc (-1:ℝ) 0) : f x ≤ f y+B := by
    have hh := hosc x (hA hx) y (hB hy)
    have hh' := (le_abs_self (f x-f y)).trans (by simpa [Real.norm_eq_abs] using hh)
    dsimp [B]
    linarith
  have hxpt (x : ℝ) (hx : x ∈ Icc a (a+1)) : f x ≤ (∫ t in Icc (-1) 0,f t)+B := by
    have hc : IntegrableOn (fun _ : ℝ => f x) (Icc (-1) 0) := continuousOn_const.integrableOn_Icc
    have hh := setIntegral_mono_on hc (hffB.add (continuousOn_const.integrableOn_Icc))
      measurableSet_Icc (hpt x hx)
    simpa [integral_add hffB continuousOn_const.integrableOn_Icc,integral_const,Real.volume_Icc] using hh
  have hc : IntegrableOn (fun _ : ℝ => (∫ t in Icc (-1) 0,f t)+B) (Icc a (a+1)) :=
    continuousOn_const.integrableOn_Icc
  have hh := setIntegral_mono_on hffA hc measurableSet_Icc hxpt
  simpa [integral_const,Real.volume_Icc] using hh

lemma cartesianRectangle_integral_symm {a b c d : ℝ} {u : ℂ → ℝ}
    (hu : IntegrableOn u (cartesianRectangle a b c d)) :
    (∫ z in cartesianRectangle a b c d, u z) =
      ∫ y in Icc c d, ∫ x in Icc a b, u (complexCoordinates (x,y)) := by
  have hp := complexCoordinates_rect_preserving a b c d
  have hemb : MeasurableEmbedding complexCoordinates := by
    simpa only [funext complexCoordinates_eq] using Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [← hp.integral_comp hemb]
  exact integral_prod_symm _ ((hp.integrable_comp hu.aestronglyMeasurable).mpr hu)

lemma horizontal_derivative_bound_ae {u : ℂ → ℝ} (hu : LocallyLipschitzOn fullOpenStrip u) :
    ∀ᵐ y : ℝ ∂volume, y ∈ Ioo 0 Real.pi → ∀ᵐ x : ℝ ∂volume,
      ‖deriv (fun t : ℝ => u (complexCoordinates (t,y))) x‖ ≤
        ‖gradient u (complexCoordinates (x,y))‖ := by
  have hd := locallyLipschitz_ae_differentiable fullOpenStrip_isOpen hu
  have hp := complexCoordinates_preserving.quasiMeasurePreserving.tendsto_ae.eventually hd
  rw [Measure.volume_eq_prod] at hp
  have hs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).quasiMeasurePreserving.tendsto_ae.eventually hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy hyI
  filter_upwards [hy] with x hx
  apply horizontal_deriv_norm_le
  apply hx
  simpa [fullOpenStrip,complexCoordinates] using hyI

lemma slab_integral_comparison {u : ℂ → ℝ}
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip)) {a : ℝ} (ha : 0 ≤ a) :
    (∫ z in cartesianRectangle a (a+1) 0 Real.pi,u z) ≤
      (∫ z in cartesianRectangle (-1) 0 0 Real.pi,u z) +
      ∫ z in cartesianRectangle (-1) (a+1) 0 Real.pi, ‖gradient u z‖ := by
  let R := cartesianRectangle (-1) (a+1) 0 Real.pi
  have hR : R ⊆ fullClosedStrip := fun _ h => h.2.2
  have huI : IntegrableOn u R := (hu.mono hR).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have huA : IntegrableOn u (cartesianRectangle a (a+1) 0 Real.pi) :=
    (hu.mono (fun _ h => h.2.2)).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have huB : IntegrableOn u (cartesianRectangle (-1) 0 0 Real.pi) :=
    (hu.mono (fun _ h => h.2.2)).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have hgR : MemLp (gradient u) 2 (volume.restrict R) :=
    hg.mono_measure (Measure.restrict_mono_ae (cartesianRectangle_ae_strip (-1) (a+1)))
  let : IsFiniteMeasure (volume.restrict R) :=
    ⟨by simpa using (cartesianRectangle_compact (-1) (a+1) 0 Real.pi).measure_lt_top⟩
  have hgI : IntegrableOn (fun z => ‖gradient u z‖) R := (hgR.integrable (by norm_num)).norm
  have hpR := complexCoordinates_rect_preserving (-1) (a+1) 0 Real.pi
  have hpA := complexCoordinates_rect_preserving a (a+1) 0 Real.pi
  have hpB := complexCoordinates_rect_preserving (-1) 0 0 Real.pi
  have hgp := (hpR.integrable_comp hgI.aestronglyMeasurable).mpr hgI
  have hupA := (hpA.integrable_comp huA.aestronglyMeasurable).mpr huA
  have hupB := (hpB.integrable_comp huB.aestronglyMeasurable).mpr huB
  have hder := horizontal_derivative_bound_ae hl
  have hY : ∀ᵐ y : ℝ ∂volume.restrict (Icc 0 Real.pi), y ∈ Ioo 0 Real.pi := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0:ℝ)),
      ae_restrict_of_ae (volume.ae_ne Real.pi)] with y hy hy0 hyp
    exact ⟨lt_of_le_of_ne hy.1 hy0.symm,lt_of_le_of_ne hy.2 hyp⟩
  have hslice : ∀ᵐ y ∂volume.restrict (Icc 0 Real.pi),
      (∫ x in Icc a (a+1), u (complexCoordinates (x,y))) ≤
        (∫ x in Icc (-1) 0, u (complexCoordinates (x,y)))+
          ∫ x in Icc (-1) (a+1), ‖gradient u (complexCoordinates (x,y))‖ := by
    filter_upwards [ae_restrict_of_ae hder,hgp.prod_left_ae,hY] with y hdy hgy hy
    have hcont : ContinuousOn (fun x => u (complexCoordinates (x,y))) (Icc (-1) (a+1)) :=
      hu.comp (horizontal_isometry y).continuous.continuousOn (by
        intro x _; simpa [fullClosedStrip,complexCoordinates] using And.intro hy.1.le hy.2.le)
    have hlip : LocallyLipschitzOn (Ioo (-1) (a+1)) (fun x => u (complexCoordinates (x,y))) :=
      locallyLipschitz_comp_of_isometry fullOpenStrip_isOpen hl (horizontal_isometry y) (by
        intro x _; simpa [fullOpenStrip,complexCoordinates] using hy)
    exact interval_unit_mean_comparison ha hcont hlip hgy (fun _ _ => norm_nonneg _)
      ((hdy hy).mono fun _ h _ => h)
  have hh := integral_mono_ae hupA.integral_prod_right
    (hupB.integral_prod_right.add hgp.integral_prod_right) hslice
  simp only [Pi.add_apply] at hh
  rw [integral_add hupB.integral_prod_right hgp.integral_prod_right] at hh
  simp only [Function.comp_def] at hh
  rwa [← cartesianRectangle_integral_symm huA,← cartesianRectangle_integral_symm huB,
    ← cartesianRectangle_integral_symm hgI] at hh

lemma rectangle_energy_le_total {u : ℂ → ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip)) (a b : ℝ) :
    (∫ z in cartesianRectangle a b 0 Real.pi, ‖gradient u z‖^2) ≤
      ∫ z in fullOpenStrip, ‖gradient u z‖^2 := by
  exact integral_mono_measure
    (Measure.restrict_mono_ae (cartesianRectangle_ae_strip a b))
    (Eventually.of_forall fun _ => sq_nonneg _) hg.norm.integrable_sq

lemma rectangle_norm_integral_le {u : ℂ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : MemLp (gradient u) 2 (volume.restrict (cartesianRectangle a b 0 Real.pi))) :
    (∫ z in cartesianRectangle a b 0 Real.pi, ‖gradient u z‖) ≤
      Real.sqrt ((b-a)*Real.pi * ∫ z in cartesianRectangle a b 0 Real.pi, ‖gradient u z‖^2) := by
  let Q := cartesianRectangle a b 0 Real.pi
  have harea : 0 ≤ (b-a)*Real.pi := mul_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le
  have hv : volume Q = ENNReal.ofReal ((b-a)*Real.pi) := by
    simp [Q,cartesianRectangle_volume,ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by simp [hv]⟩
  have hconst : MemLp (fun _ : ℂ => (1:ℝ)) 2 (volume.restrict Q) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := volume.restrict Q) (f := fun z => ‖gradient u z‖) (g := fun _ => (1:ℝ))
    (Eventually.of_forall fun z => norm_nonneg _) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hg.norm) (by simpa using hconst)
  simp only [mul_one,Real.rpow_two,← Real.sqrt_eq_rpow,one_pow,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,hv,ENNReal.toReal_ofReal harea] at hh
  rw [Real.sqrt_mul harea]
  simpa only [Q,mul_comm] using hh

lemma negativeSlab_mean_small {u : ℂ → ℝ} {H a : ℝ} (hH : 1024 ≤ H)
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H)
    (hz : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0)
    (ha : a+1 ≤ 0) :
    Real.pi⁻¹*(∫ z in cartesianRectangle a (a+1) 0 Real.pi, u z) ≤ H/4 := by
  apply (negativeSlab_mean_le hu hl hg hz ha).trans
  have hEq := (rectangle_energy_le_total hg a (a+1)).trans hE
  apply (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hEq Real.pi_pos.le)).trans
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · have hp := Real.pi_lt_four
    have hps : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos]
    have hHn : 0 ≤ H := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hps hHn, mul_nonneg hHn (show 0 ≤ H-512 by linarith)]

lemma positiveSlab_mean_small {u : ℂ → ℝ} {H a : ℝ} (hH : 1024 ≤ H)
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H)
    (hz : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0)
    (ha : 0 ≤ a) (haH : a ≤ H/128) :
    Real.pi⁻¹*(∫ z in cartesianRectangle a (a+1) 0 Real.pi, u z) ≤ H/2 := by
  have hh := mul_le_mul_of_nonneg_left (slab_integral_comparison hu hl hg ha)
    (inv_nonneg.mpr Real.pi_pos.le)
  have hm := negativeSlab_mean_small hH hu hl hg hE hz (a := -1) (by norm_num)
  have hgR := hg.mono_measure (Measure.restrict_mono_ae (cartesianRectangle_ae_strip (-1) (a+1)))
  have hn := rectangle_norm_integral_le (by linarith : (-1:ℝ) ≤ a+1) hgR
  have hER := (rectangle_energy_le_total hg (-1) (a+1)).trans hE
  have hn' : (∫ z in cartesianRectangle (-1) (a+1) 0 Real.pi, ‖gradient u z‖) ≤ Real.pi*H/4 := by
    apply hn.trans
    apply (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hER
      (mul_nonneg (by linarith) Real.pi_pos.le))).trans
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hHn : 0 ≤ H := by linarith
      have hbase : 2*(a+2)*H ≤ H^2/16 := by
        nlinarith [mul_nonneg hHn (show 0 ≤ H-128 by linarith),
          mul_le_mul_of_nonneg_right haH hHn]
      nlinarith [mul_le_mul_of_nonneg_right hbase (sq_nonneg Real.pi)]
  have hn'' := mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr Real.pi_pos.le)
  have he : Real.pi⁻¹*(Real.pi*H/4) = H/4 := by field_simp
  rw [he] at hn''
  simp only [mul_add] at hh
  norm_num at hm
  linarith

def SourceSlabSmallMeanTarget : Prop :=
  ∃ b H0 : ℝ, 0 < b ∧ 0 < H0 ∧ ∀ H : ℝ, H0 ≤ H → ∀ (u : ℂ → ℝ),
    ContinuousOn u {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} →
    LocallyLipschitzOn {z : ℂ | 0 < z.im ∧ z.im < Real.pi} u →
    MemLp (gradient u) 2 (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) →
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient u z‖^2) ≤ 2*Real.pi*H →
    (∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (x + y*Complex.I) = 0) →
    ∀ j : ℤ, (j:ℝ) ≤ b*H →
      (Real.pi)⁻¹ * ∫ z in {z : ℂ | (j:ℝ) ≤ z.re ∧ z.re ≤ (j:ℝ)+1 ∧
          0 ≤ z.im ∧ z.im ≤ Real.pi}, u z ≤ H/2

theorem sourceSlabSmallMean : SourceSlabSmallMeanTarget := by
  refine ⟨1/128,1024,by norm_num,by norm_num,?_⟩
  intro H hH u hu hl hg hE hz j hj
  have hz' : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0 := hz
  by_cases hj0 : j < 0
  · exact (negativeSlab_mean_small hH hu hl hg hE hz' (a := (j:ℝ))
      (by have hh : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
          linarith)).trans (by linarith)
  · apply positiveSlab_mean_small hH hu hl hg hE hz'
    · exact_mod_cast (by omega : 0 ≤ j)
    · linarith

def closedIntegerStrip (j : ℤ) : Set ℂ :=
  {z | (j:ℝ) ≤ z.re ∧ z.re ≤ (j:ℝ)+1 ∧ 0 ≤ z.im ∧ z.im ≤ Real.pi}

def openIntegerStrip (j : ℤ) : Set ℂ :=
  {z | (j:ℝ) < z.re ∧ z.re < (j:ℝ)+1 ∧ 0 < z.im ∧ z.im < Real.pi}

lemma complex_re_fiber_null (a : ℝ) : volume {z : ℂ | z.re = a} = 0 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton a).prod MeasurableSet.univ).nullMeasurableSet
  simpa [Set.preimage,Measure.volume_eq_prod,Measure.prod_prod] using he

lemma complex_im_fiber_null (a : ℝ) : volume {z : ℂ | z.im = a} = 0 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton a)).nullMeasurableSet
  simpa [Set.preimage,Measure.volume_eq_prod,Measure.prod_prod] using he

lemma closedIntegerStrip_ae_open (j : ℤ) : closedIntegerStrip j =ᵐ[volume] openIntegerStrip j := by
  have hr0 : ∀ᵐ z : ℂ ∂volume, z.re ≠ (j:ℝ) := by
    simpa only [ae_iff,not_not] using complex_re_fiber_null (j:ℝ)
  have hr1 : ∀ᵐ z : ℂ ∂volume, z.re ≠ (j:ℝ)+1 := by
    simpa only [ae_iff,not_not] using complex_re_fiber_null ((j:ℝ)+1)
  have hi0 : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
    simpa only [ae_iff,not_not] using complex_im_fiber_null 0
  have hi1 : ∀ᵐ z : ℂ ∂volume, z.im ≠ Real.pi := by
    simpa only [ae_iff,not_not] using complex_im_fiber_null Real.pi
  filter_upwards [hr0,hr1,hi0,hi1] with z hz0 hz1 hw0 hw1
  apply propext
  change ((j:ℝ) ≤ z.re ∧ z.re ≤ (j:ℝ)+1 ∧ 0 ≤ z.im ∧ z.im ≤ Real.pi) ↔
    ((j:ℝ) < z.re ∧ z.re < (j:ℝ)+1 ∧ 0 < z.im ∧ z.im < Real.pi)
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨lt_of_le_of_ne h0 hz0.symm,lt_of_le_of_ne h1 hz1,
      lt_of_le_of_ne h2 hw0.symm,lt_of_le_of_ne h3 hw1⟩
  · rintro ⟨h0,h1,h2,h3⟩; exact ⟨h0.le,h1.le,h2.le,h3.le⟩

lemma openIntegerStrip_isOpen (j : ℤ) : IsOpen (openIntegerStrip j) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

lemma openIntegerStrip_disjoint : Pairwise (fun i j => Disjoint (openIntegerStrip i) (openIntegerStrip j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    exact (not_lt_of_ge (hi.2.1.le.trans hle)) hj.1
  · have hle : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    exact (not_lt_of_ge (hj.2.1.le.trans hle)) hi.1

def slabShift (j : ℤ) (z : ℂ) : ℂ := (j:ℂ)+z

lemma slabShift_continuous (j : ℤ) : Continuous (slabShift j) := by
  unfold slabShift
  fun_prop

lemma slabShift_isometry (j : ℤ) : Isometry (slabShift j) :=
  (IsometryEquiv.addLeft (j:ℂ)).isometry

lemma slabShift_preimage_closed (j : ℤ) : slabShift j ⁻¹' closedIntegerStrip j =
    cartesianRectangle 0 1 0 Real.pi := by
  ext z
  simp only [slabShift,closedIntegerStrip,cartesianRectangle,mem_preimage,mem_ofPred_eq,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,zero_add]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩

lemma slabShift_preimage_open (j : ℤ) : slabShift j ⁻¹' openIntegerStrip j = openUnitStrip := by
  ext z
  simp only [slabShift,openIntegerStrip,openUnitStrip,mem_preimage,mem_ofPred_eq,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,zero_add]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩

lemma slabShift_preserving_open (j : ℤ) : MeasurePreserving (slabShift j)
    (volume.restrict openUnitStrip) (volume.restrict (openIntegerStrip j)) := by
  have hh := (measurePreserving_add_left (volume : Measure ℂ) (j:ℂ)).restrict_preimage
    (openIntegerStrip_isOpen j).measurableSet
  change MeasurePreserving (slabShift j) (volume.restrict (slabShift j ⁻¹' openIntegerStrip j)) _ at hh
  rwa [slabShift_preimage_open] at hh

lemma slabShift_preserving_closed (j : ℤ) : MeasurePreserving (slabShift j)
    (volume.restrict (cartesianRectangle 0 1 0 Real.pi)) (volume.restrict (closedIntegerStrip j)) := by
  have hm : MeasurableSet (closedIntegerStrip j) := cartesianRectangle_measurable _ _ _ _
  have hh := (measurePreserving_add_left (volume : Measure ℂ) (j:ℂ)).restrict_preimage hm
  change MeasurePreserving (slabShift j) (volume.restrict (slabShift j ⁻¹' closedIntegerStrip j)) _ at hh
  rwa [slabShift_preimage_closed] at hh

lemma gradient_comp_slabShift (u : ℂ → ℝ) (j : ℤ) (z : ℂ) :
    gradient (u ∘ slabShift j) z = gradient u (slabShift j z) := by
  simp only [gradient,Function.comp_def,slabShift,fderiv_comp_add_left]

lemma slabShift_integral (u : ℂ → ℝ) (j : ℤ) :
    (∫ z in cartesianRectangle 0 1 0 Real.pi,u (slabShift j z)) =
      ∫ z in closedIntegerStrip j,u z :=
  (slabShift_preserving_closed j).integral_comp (IsometryEquiv.addLeft (j:ℂ)).toHomeomorph.measurableEmbedding u

lemma slabShift_energy (u : ℂ → ℝ) (j : ℤ) :
    stripDirichletEnergy (gradient (u ∘ slabShift j)) =
      ∫ z in closedIntegerStrip j,‖gradient u z‖^2 := by
  simp only [stripDirichletEnergy,gradient_comp_slabShift]
  rw [(slabShift_preserving_open j).integral_comp (IsometryEquiv.addLeft (j:ℂ)).toHomeomorph.measurableEmbedding (fun z => ‖gradient u z‖^2)]
  exact (setIntegral_congr_set (closedIntegerStrip_ae_open j)).symm

lemma slabShift_mem_strip (j : ℤ) {z : ℂ} (hz : z ∈ openUnitStrip) :
    slabShift j z ∈ fullOpenStrip := by
  simpa [slabShift,fullOpenStrip] using hz.2.2

lemma slabShift_locallyLipschitz {u : ℂ → ℝ}
    (hl : LocallyLipschitzOn fullOpenStrip u) (j : ℤ) :
    LocallyLipschitzOn openUnitStrip (u ∘ slabShift j) := by
  intro z hz
  obtain ⟨K,t,ht,hK⟩ := hl (slabShift_mem_strip j hz)
  rw [nhdsWithin_eq_nhds.mpr (fullOpenStrip_isOpen.mem_nhds (slabShift_mem_strip j hz))] at ht
  refine ⟨K,slabShift j ⁻¹' t,mem_nhdsWithin_of_mem_nhds
    ((slabShift_continuous j).continuousAt.preimage_mem_nhds ht),?_⟩
  intro x hx y hy
  exact (hK hx hy).trans_eq (by rw [(slabShift_isometry j).edist_eq])

lemma slabShift_gradient_memLp {u : ℂ → ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip)) (j : ℤ) :
    MemLp (gradient (u ∘ slabShift j)) 2 (volume.restrict openUnitStrip) := by
  have hs : openIntegerStrip j ⊆ fullOpenStrip := fun _ hz => hz.2.2
  have hh := (hg.mono_measure (Measure.restrict_mono hs le_rfl)).comp_measurePreserving
    (slabShift_preserving_open j)
  have he : gradient (u ∘ slabShift j) = gradient u ∘ slabShift j := funext (gradient_comp_slabShift u j)
  rw [he]
  exact hh

lemma slabShift_source_weakGradient {u : ℂ → ℝ} {H : ℝ}
    (hc : ContinuousOn u fullClosedStrip)
    (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hb : ∀ z, 0 ≤ u z ∧ u z ≤ H) (j : ℤ) :
    SourceIsStripWeakGradient (u ∘ slabShift j) (gradient (u ∘ slabShift j)) := by
  apply locallyLipschitz_source_weakGradient (slabShift_locallyLipschitz hl j) _ (slabShift_gradient_memLp hg j)
  have hcont : ContinuousOn (u ∘ slabShift j) openUnitStrip :=
    hc.comp (slabShift_continuous j).continuousOn (fun z hz =>
      ⟨(slabShift_mem_strip j hz).1.le,(slabShift_mem_strip j hz).2.le⟩)
  exact memLp_of_bounded (Eventually.of_forall fun z => hb (slabShift j z))
    (hcont.aestronglyMeasurable openUnitStrip_isOpen.measurableSet) 2

lemma integerSlab_energy_budget {u : ℂ → ℝ} {H : ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H) :
    (∑' j : ℤ, ENNReal.ofReal (∫ z in closedIntegerStrip j, ‖gradient u z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  have hint := hg.norm.integrable_sq
  have hsub (j : ℤ) : openIntegerStrip j ⊆ fullOpenStrip := fun _ hz => hz.2.2
  have hconv (j : ℤ) : ENNReal.ofReal (∫ z in closedIntegerStrip j, ‖gradient u z‖^2) =
      ∫⁻ z in openIntegerStrip j, ENNReal.ofReal (‖gradient u z‖^2) := by
    rw [setIntegral_congr_set (closedIntegerStrip_ae_open j)]
    exact ofReal_integral_eq_lintegral_ofReal (hint.mono_measure (Measure.restrict_mono (hsub j) le_rfl))
      (Eventually.of_forall fun z => sq_nonneg _)
  simp_rw [hconv]
  rw [← lintegral_iUnion (fun j => (openIntegerStrip_isOpen j).measurableSet) openIntegerStrip_disjoint]
  calc
    _ ≤ ∫⁻ z in fullOpenStrip, ENNReal.ofReal (‖gradient u z‖^2) :=
      lintegral_mono_set (iUnion_subset hsub)
    _ = ENNReal.ofReal (∫ z in fullOpenStrip, ‖gradient u z‖^2) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hE

lemma abstract_slab_exponential_budget {E : ℤ → ℝ} {H C c : ℝ}
    (hH : 0 < H) (hEn : ∀ j, 0 ≤ E j)
    (hEs : (∑' j : ℤ, ENNReal.ofReal (E j)) ≤ ENNReal.ofReal (2*Real.pi*H))
    (hC : 0 ≤ C) (hc : 0 < c) :
    (∑' j : ℤ, ENNReal.ofReal (C*(E j/H^2)*Real.exp (-c*H^2/E j))) ≤
      ENNReal.ofReal ((2*Real.pi*C/H)*Real.exp (-c*H/(2*Real.pi))) := by
  have hv : 0 ≤ 2*Real.pi*H := by positivity
  have hE (j : ℤ) : E j ≤ 2*Real.pi*H := by
    exact (ENNReal.ofReal_le_ofReal_iff hv).mp ((ENNReal.le_tsum j).trans hEs)
  let K := C/H^2*Real.exp (-c*H/(2*Real.pi))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht (j : ℤ) : C*(E j/H^2)*Real.exp (-c*H^2/E j) ≤ E j*K := by
    by_cases hz : E j = 0
    · simp [hz]
    · have hj : 0 < E j := lt_of_le_of_ne (hEn j) (Ne.symm hz)
      have hb : H/(2*Real.pi) ≤ H^2/E j := by
        apply (le_div_iff₀ hj).mpr
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
        nlinarith [mul_le_mul_of_nonneg_left (hE j) hH.le]
      have hex : Real.exp (-c*H^2/E j) ≤ Real.exp (-c*H/(2*Real.pi)) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hb hc.le
        calc
          -c*H^2/E j = -(c*(H^2/E j)) := by ring
          _ ≤ -(c*(H/(2*Real.pi))) := neg_le_neg hh
          _ = -c*H/(2*Real.pi) := by ring
      calc
        _ ≤ C*(E j/H^2)*Real.exp (-c*H/(2*Real.pi)) :=
          mul_le_mul_of_nonneg_left hex (mul_nonneg hC (div_nonneg hj.le (sq_nonneg _)))
        _ = _ := by dsimp [K]; ring
  calc
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (E j*K) := ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (ht j)
    _ = (∑' j : ℤ, ENNReal.ofReal (E j))*ENNReal.ofReal K := by
      calc
        _ = ∑' j : ℤ, ENNReal.ofReal (E j)*ENNReal.ofReal K :=
          tsum_congr (fun j => ENNReal.ofReal_mul (hEn j))
        _ = _ := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (2*Real.pi*H)*ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal ((2*Real.pi*C/H)*Real.exp (-c*H/(2*Real.pi))) := by
      rw [← ENNReal.ofReal_mul hv]
      congr 1
      dsimp [K]
      field_simp [hH.ne']

 

def SourceStripLocalizationTarget : Prop :=
  ∀ C0 α : ℝ, 0 < C0 → 0 < α → ∃ b C c H0 : ℝ,
    0 < b ∧ 0 < C ∧ 0 < c ∧ 0 < H0 ∧
    ∀ H : ℝ, H0 ≤ H → ∀ u : ℂ → ℝ,
    ContinuousOn u {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} →
    LocallyLipschitzOn {z : ℂ | 0 < z.im ∧ z.im < Real.pi} u →
    (∀ z, 0 ≤ u z ∧ u z ≤ H) →
    MemLp (gradient u) 2 (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) →
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient u z‖^2) ≤ 2*Real.pi*H →
    (∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (x+y*Complex.I) = 0) →
    ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ X : Ω → Set ℂ,
      (∀ (j : ℤ) (k : ℕ) (i m : Fin (2^k)),
        P {xi | (X xi ∩ dyadicStripRectangle j k i m).Nonempty} ≤
          ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ)))) →
      P {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*H ∧ u z = H} ≤
        ENNReal.ofReal (C*Real.exp (-c*H))

lemma stripRectangle_zero_eq_cartesian :
    stripRectangle 0 0 1 = cartesianRectangle 0 1 0 Real.pi := by
  ext z
  simp [stripRectangle,cartesianRectangle]

lemma slabShift_average (u : ℂ → ℝ) (j : ℤ) :
    spatialAverage (u ∘ slabShift j) (stripRectangle 0 0 1) =
      Real.pi⁻¹ * ∫ z in closedIntegerStrip j, u z := by
  rw [spatialAverage,stripRectangle_volume]
  simp only [mul_one,ENNReal.ofReal_one,one_mul,ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [stripRectangle_zero_eq_cartesian]
  simp only [Function.comp_apply]
  rw [slabShift_integral,div_eq_mul_inv,mul_comm]

lemma slabShift_dyadic (j : ℤ) (k : ℕ) (i m : Fin (2^k)) :
    slabShift j ⁻¹' dyadicStripRectangle j k i m = dyadicStripRectangle 0 k i m := by
  ext z
  simp only [dyadicStripRectangle,stripRectangle,slabShift,mem_preimage,mem_ofPred_eq,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,zero_add,Int.cast_zero]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩

lemma slabShift_continuousOn {u : ℂ → ℝ}
    (hu : ContinuousOn u fullClosedStrip) (j : ℤ) :
    ContinuousOn (u ∘ slabShift j) (stripRectangle 0 0 1) := by
  apply hu.comp (slabShift_continuous j).continuousOn
  intro z hz
  change 0 ≤ (slabShift j z).im ∧ (slabShift j z).im ≤ Real.pi
  simpa [slabShift,stripRectangle] using hz.2.2

lemma point_integer_slab (z : ℂ) (hz : 0 ≤ z.im ∧ z.im ≤ Real.pi) :
    ∃ w ∈ stripRectangle 0 0 1, slabShift ⌊z.re⌋ w = z := by
  refine ⟨z-(⌊z.re⌋:ℂ),?_,by simp [slabShift]⟩
  have h0 := Int.floor_le z.re
  have h1 := Int.lt_floor_add_one z.re
  simp only [stripRectangle,mem_ofPred_eq,Complex.sub_re,Complex.intCast_re,
    Complex.sub_im,Complex.intCast_im,sub_zero,zero_add,mul_one]
  exact ⟨by linarith,by linarith,hz.1,hz.2⟩

lemma slab_energy_le_total {u : ℂ → ℝ} {H : ℝ}
    (hH : 0 < H)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H) (j : ℤ) :
    (∫ z in closedIntegerStrip j, ‖gradient u z‖^2) ≤ 2*Real.pi*H := by
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    ((ENNReal.le_tsum j).trans (integerSlab_energy_budget hg hE))

 theorem sourceStripLocalization : SourceStripLocalizationTarget := by
  intro C0 α hC0 hα
  obtain ⟨C,c,c0,hC,hc,hc0,hrect⟩ := sourceStripRectangleEnergy C0 α hC0 hα
  obtain ⟨b,Hm,hb,hHm,hmean⟩ := sourceSlabSmallMean
  refine ⟨b,2*Real.pi*C,c/(2*Real.pi),max Hm (max 1 (2*Real.pi/c0)),hb,
    by positivity,by positivity,lt_of_lt_of_le hHm (le_max_left _ _),?_⟩
  intro H hH u hu hl huB hg hE hz Ω mΩ P hP X hhit
  let := hP
  have hHm' : Hm ≤ H := (le_max_left _ _).trans hH
  have hH1 : 1 ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hHc : 2*Real.pi/c0 ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  let E : ℤ → ℝ := fun j => ∫ z in closedIntegerStrip j, ‖gradient u z‖^2
  let A : ℤ → Set Ω := fun j =>
    {xi | (j:ℝ) ≤ b*H ∧ ((slabShift j ⁻¹' X xi) ∩
      {z | z ∈ stripRectangle 0 0 1 ∧ (u ∘ slabShift j) z = H}).Nonempty}
  have hEn (j : ℤ) : 0 ≤ E j := integral_nonneg fun z => sq_nonneg _
  have hEj (j : ℤ) : E j ≤ 2*Real.pi*H := slab_energy_le_total hH0 hg hE j
  have hsmall (j : ℤ) : E j ≤ c0*H^2 := by
    have hhc := (div_le_iff₀ hc0).mp hHc
    exact (hEj j).trans (by nlinarith [mul_le_mul_of_nonneg_right hhc hH0.le])
  have hA (j : ℤ) : P (A j) ≤ ENNReal.ofReal (C*(E j/H^2)*Real.exp (-c*H^2/E j)) := by
    by_cases hj : (j:ℝ) ≤ b*H
    · have ht (k : ℕ) (i m : Fin (2^k)) :
          P {xi | ((slabShift j ⁻¹' X xi) ∩ dyadicStripRectangle 0 k i m).Nonempty} ≤
            ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ))) := by
        apply (measure_mono ?_).trans (hhit j k i m)
        rintro xi ⟨z,hzX,hzQ⟩
        exact ⟨slabShift j z,hzX,by rwa [← slabShift_dyadic j k i m] at hzQ⟩
      have hm : spatialAverage (u ∘ slabShift j) (stripRectangle 0 0 1) ≤ H/2 := by
        rw [slabShift_average]
        exact hmean H hHm' u hu hl hg hE hz j hj
      have hh := hrect H hH0 (u ∘ slabShift j) (gradient (u ∘ slabShift j))
        (slabShift_source_weakGradient hu hl hg huB j) (slabShift_continuousOn hu j)
        (fun z _ => huB (slabShift j z)) hm Ω mΩ P hP (fun xi => slabShift j ⁻¹' X xi) ht
        (by rw [slabShift_energy]; exact hsmall j)
      rw [slabShift_energy] at hh
      apply (measure_mono ?_).trans hh
      exact fun xi hxi => hxi.2
    · have he : A j = ∅ := by ext xi; simp [A,hj]
      rw [he,measure_empty]
      exact bot_le
  have hcover : {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*H ∧ u z = H} ⊆
      ⋃ j : ℤ, A j := by
    rintro xi ⟨z,hzX,hz0,hzπ,hzr,hzu⟩
    obtain ⟨w,hw,heq⟩ := point_integer_slab z ⟨hz0,hzπ⟩
    apply mem_iUnion.mpr
    refine ⟨⌊z.re⌋,⟨(Int.floor_le z.re).trans hzr,?_⟩⟩
    exact ⟨w,by simpa only [mem_preimage,heq] using hzX,hw,by simpa [Function.comp_def,heq] using hzu⟩
  calc
    _ ≤ P (⋃ j : ℤ, A j) := measure_mono hcover
    _ ≤ ∑' j : ℤ, P (A j) := measure_iUnion_le _
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (C*(E j/H^2)*Real.exp (-c*H^2/E j)) := ENNReal.tsum_le_tsum hA
    _ ≤ ENNReal.ofReal ((2*Real.pi*C/H)*Real.exp (-c*H/(2*Real.pi))) :=
      abstract_slab_exponential_budget hH0 hEn (integerSlab_energy_budget hg hE) hC.le hc
    _ ≤ ENNReal.ofReal (2*Real.pi*C*Real.exp (-(c/(2*Real.pi))*H)) := by
      apply ENNReal.ofReal_le_ofReal
      have ht : 2*Real.pi*C/H ≤ 2*Real.pi*C := div_le_self (by positivity) hH1
      have he : -c*H/(2*Real.pi) = -(c/(2*Real.pi))*H := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le

end SLEExactGauge
end

 
end

end OAI
