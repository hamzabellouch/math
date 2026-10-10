import OAI.Analysis.DiskMaximal.WeakLimits

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace NullLocalization
open PlanePotential DiskMoments

def unitRegion : Set ℂ := {x | ‖x‖ ≤ 8}
lemma unitRegion_compact : IsCompact unitRegion := by
  simpa only [unitRegion,Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8
lemma unitRegion_measurable : MeasurableSet unitRegion := unitRegion_compact.measurableSet
lemma unitRegion_finite : volume unitRegion < ⊤ := unitRegion_compact.measure_lt_top

/-- A fixed-radius Poincare inequality derived from the proved Green kernel,
not added as a Sobolev axiom. The subsequent cutoff is one on the radius-four disk. -/
lemma unit_poincare : ∃ P : ℝ, 0 ≤ P ∧ ∀ {g : ℂ → ℝ},
    ContDiff ℝ 1 g → HasCompactSupport g → ∃ c : ℝ,
    (∫ x in unitRegion, ‖g x-c‖) ≤ P*(∫ x in unitRegion, ‖gradient g x‖) := by
  obtain ⟨ψ,B,L,hB,hL,hψ,hψc,hψ1,hψs,hψB,hψL⟩ := exists_kernel_cutoff
  let A : ℝ≥0∞ := ENNReal.ofReal ((2*B*(1+8)^2)^(3/2:ℝ)*(4*Real.pi*(32:ℝ)^(1/2:ℝ)))
  let Z : ℝ≥0∞ := A^(2/3:ℝ)*(volume unitRegion)^(1/3:ℝ)
  have hZ : Z ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) unitRegion_finite.ne)
  refine ⟨Z.toReal,ENNReal.toReal_nonneg,?_⟩
  intro g hg hc
  let c := ∫ z,ψ z*g z
  refine ⟨c,?_⟩
  let β := unitRegion.indicator (gradient g)
  have hgi : Integrable (gradient g) := (continuous_gradient hg).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  have hβ : Integrable β := hgi.indicator unitRegion_measurable
  have hβs : ∀ y, β y≠0 → ‖y‖ ≤ 8 := by
    intro y hy
    by_contra hh
    change y∉unitRegion at hh
    exact hy (indicator_of_notMem hh _)
  have hβv : (∫ y,‖β y‖) = ∫ y in unitRegion,‖gradient g y‖ := by
    rw [← integral_indicator unitRegion_measurable]
    congr 1
    ext y
    exact norm_indicator_eq_indicator_norm _ _
  obtain ⟨D,hD⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hp := green_root_lp hψ.continuous.measurable hψs hψB
    (by norm_num : (0:ℝ)<1+8) hB (by norm_num : (0:ℝ)<8+8) hβ hβs
  have hex : (fun x => ∫ y,inner ℝ (green ψ x y) (β y)) =ᵐ[volume.restrict unitRegion] (fun x => g x-c) := by
    filter_upwards [ae_restrict_mem unitRegion_measurable] with x hx
    calc
      _ = ∫ y,inner ℝ (green ψ x y) (gradient g y) := by
        apply integral_congr_ae
        exact ae_of_all _ (green_restrict_density hψs (by norm_num : (1:ℝ)≤8) _ hx)
      _ = _ := green_gradient_representation hψ.continuous hψc hg
        (fun y => norm_fderiv_le_of_lipschitz ℝ hD (x₀ := y)) hψ1 x
  have hs : eLpNorm (fun x => g x-c) (3/2) (volume.restrict unitRegion) ≤
      A^(2/3:ℝ)*ENNReal.ofReal (∫ y in unitRegion,‖gradient g y‖) := by
    rw [← eLpNorm_congr_ae hex,← hβv]
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (potential_aestronglyMeasurable _ (green_measurable ψ hψ.continuous.measurable) hβ)]
    convert eLpNorm_three_halves_bound _ hp using 1 <;> norm_num [A,unitRegion]
  have hl := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := fun x => g x-c) (μ := volume.restrict unitRegion)
    (show (1:ℝ≥0∞)≤3/2 by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num) (hg.continuous.sub continuous_const).aestronglyMeasurable
  have he : eLpNorm (fun x => g x-c) 1 (volume.restrict unitRegion) ≤
      Z*ENNReal.ofReal (∫ y in unitRegion,‖gradient g y‖) := by
    apply hl.trans
    have hexp : 1/(1:ℝ≥0∞).toReal-1/(3/2:ℝ≥0∞).toReal=(1/3:ℝ) := by norm_num
    rw [hexp,Measure.restrict_apply_univ]
    have hh := mul_le_mul_right hs ((volume unitRegion)^(1/3:ℝ))
    simpa only [Z,mul_assoc,mul_left_comm,mul_comm] using hh
  have hin : IntegrableOn (fun x => g x-c) unitRegion :=
    (hg.continuous.sub continuous_const).continuousOn.integrableOn_compact unitRegion_compact
  rw [eLpNorm_one_eq_lintegral_enorm hin.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hin] at he
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hZ ENNReal.ofReal_ne_top) he
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg _))] using ht
end NullLocalization

namespace NullLocalization
open DiskMoments WeakSobolev

def unitCutoff : ContDiffBump (0:ℂ) := ⟨4,8,by norm_num,by norm_num⟩

lemma unit_localization : ∃ D : ℝ, 0≤D ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∃ (h : ℂ → ℝ) (c : ℝ), ContDiff ℝ 1 h ∧ HasCompactSupport h ∧
    (∀ x, ‖x‖≤4 → h x=g x-c) ∧
    (∫ x,‖gradient h x‖) ≤ D*(∫ x in unitRegion,‖gradient g x‖) := by
  obtain ⟨P,hP,hpoi⟩ := unit_poincare
  obtain ⟨L,hL⟩ := (unitCutoff.contDiff (n := (1:ℕ∞))).lipschitzWith_of_hasCompactSupport unitCutoff.hasCompactSupport one_ne_zero
  refine ⟨1+L*P,by positivity,?_⟩
  intro g hg hc
  obtain ⟨c,hc'⟩ := hpoi hg hc
  let h := fun x => unitCutoff x*(g x-c)
  have hd : ContDiff ℝ 1 h := unitCutoff.contDiff.mul (hg.sub contDiff_const)
  have hs : HasCompactSupport h := unitCutoff.hasCompactSupport.mul_right
  refine ⟨h,c,hd,hs,?_,?_⟩
  · intro x hx
    have he : unitCutoff x=1 := unitCutoff.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,unitCutoff] using hx)
    simp only [h,he,one_mul]
  · have hi : Integrable (gradient h) := (continuous_gradient hd).integrable_of_hasCompactSupport (gradient_hasCompactSupport hs)
    have his : Function.support (fun x => ‖gradient h x‖) ⊆ unitRegion := by
      intro x hx
      have ht : x∈tsupport h := support_fderiv_subset ℝ (by
        intro he
        apply hx
        change ‖gradient h x‖=0
        rw [norm_gradient_fderiv,he,norm_zero])
      have hh : tsupport h ⊆ tsupport (unitCutoff : ℂ → ℝ) := tsupport_mul_subset_left
      have hx' := hh ht
      rw [unitCutoff.tsupport_eq] at hx'
      change ‖x‖≤8
      simpa only [Metric.mem_closedBall,dist_zero_right,unitCutoff] using hx'
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => Function.notMem_support.mp (fun hh => hx (his hh)))]
    have hig : IntegrableOn (fun x => ‖gradient g x‖) unitRegion :=
      ((continuous_gradient hg).norm).continuousOn.integrableOn_compact unitRegion_compact
    have hid : IntegrableOn (fun x => ‖g x-c‖) unitRegion :=
      (hg.continuous.sub continuous_const).norm.continuousOn.integrableOn_compact unitRegion_compact
    have hb (x : ℂ) : ‖gradient h x‖ ≤ ‖gradient g x‖+L*‖g x-c‖ := by
      rw [norm_gradient_fderiv]
      have he := fderiv_mul ((unitCutoff.contDiff (n := (1:ℕ∞))).differentiable one_ne_zero x)
        ((hg.differentiable one_ne_zero x).sub_const c)
      change fderiv ℝ h x = _ at he
      rw [he]
      have hχ : ‖unitCutoff x‖≤1 := by rw [Real.norm_of_nonneg unitCutoff.nonneg]; exact unitCutoff.le_one
      have hχd := norm_fderiv_le_of_lipschitz ℝ hL (x₀ := x)
      calc
        _ ≤ ‖unitCutoff x • fderiv ℝ (fun x => g x-c) x‖+‖(g x-c) • fderiv ℝ (unitCutoff : ℂ → ℝ) x‖ := norm_add_le _ _
        _ ≤ 1*‖fderiv ℝ g x‖+‖g x-c‖*L := by
          rw [norm_smul,norm_smul,fderiv_sub_const]
          exact add_le_add (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)) (mul_le_mul_of_nonneg_left hχd (norm_nonneg _))
        _ = _ := by rw [one_mul,← norm_gradient_fderiv]; ring
    have hm := integral_mono hi.norm.integrableOn (hig.add (hid.const_mul (L:ℝ))) hb
    simp only [Pi.add_apply] at hm
    rw [integral_add hig (hid.const_mul (L:ℝ)),integral_const_mul] at hm
    nlinarith [mul_le_mul_of_nonneg_left hc' L.coe_nonneg]
end NullLocalization

namespace NullLocalization
open DiskMoments PhysicalCells WeakSobolev

def region (p : ℂ) (t : ℝ) : Set ℂ := {x | ‖x-p‖≤8*t}
lemma region_measurable (p : ℂ) (t : ℝ) : MeasurableSet (region p t) :=
  measurableSet_le (continuous_norm.comp (continuous_id.sub continuous_const)).measurable measurable_const

lemma integral_stretch (F : ℂ → ℝ) (p : ℂ) (t : ℝ) :
    (∫ x,F (p+t • x)) = (t^2)⁻¹*(∫ x,F x) := by
  have h := Measure.integral_comp_smul volume (fun x : ℂ => F (p+x)) t
  simpa only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),smul_eq_mul,
    integral_add_left_eq_self] using h

lemma norm_toUnit (p x : ℂ) {t : ℝ} (ht : 0<t) : ‖toUnit p t x‖=‖x-p‖/t := by
  simp only [toUnit,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),div_eq_mul_inv,mul_comm]

lemma comp_stretch_compact {g : ℂ → ℝ} (hc : HasCompactSupport g) (p : ℂ) {t : ℝ} (ht : t≠0) :
    HasCompactSupport (fun x => g (p+t • x)) := by
  exact hc.comp_homeomorph ((Homeomorph.smulOfNeZero t ht).trans (Homeomorph.addLeft p))

lemma comp_toUnit_compact {g : ℂ → ℝ} (hc : HasCompactSupport g) (p : ℂ) {t : ℝ} (ht : t≠0) :
    HasCompactSupport (fun x => g (toUnit p t x)) := by
  exact hc.comp_homeomorph ((Homeomorph.subRight p).trans (Homeomorph.smulOfNeZero t⁻¹ (inv_ne_zero ht)))

lemma gradient_toUnit {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p x : ℂ) (t : ℝ) :
    gradient (fun y => g (toUnit p t y)) x=t⁻¹ • gradient g (toUnit p t x) := by
  have he : (fun y => g (toUnit p t y)) = (fun y => g (-(t⁻¹ • p)+t⁻¹ • y)) := by
    ext y; congr 1; simp only [toUnit,smul_sub]; abel
  rw [he,AffineDensities.gradient_affine hg]
  change t⁻¹ • gradient g (-(t⁻¹ • p)+t⁻¹ • x)=_
  congr 2
  simp only [toUnit,smul_sub]; abel

lemma integral_gradient_toUnit {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) {t : ℝ} (ht : 0<t) :
    (∫ x,‖gradient (fun y => g (toUnit p t y)) x‖)=t*(∫ x,‖gradient g x‖) := by
  simp_rw [gradient_toUnit hg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
  rw [integral_const_mul]
  have he : (∫ x, ‖gradient g (toUnit p t x)‖) = t^2*(∫ x,‖gradient g x‖) := by
    rw [show (fun x => ‖gradient g (toUnit p t x)‖) =
      (fun x => ‖gradient g (-(t⁻¹ • p)+t⁻¹ • x)‖) by ext x; congr 2; simp only [toUnit,smul_sub]; abel]
    rw [integral_stretch (fun z => ‖gradient g z‖) (-(t⁻¹ • p)) t⁻¹,inv_pow,inv_inv]
  rw [he]
  field_simp

lemma local_integral_gradient_stretch {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (p : ℂ) {t : ℝ} (ht : 0<t) :
    (∫ x in unitRegion,‖gradient (fun y => g (p+t • y)) x‖)=
      t⁻¹*(∫ x in region p t,‖gradient g x‖) := by
  simp_rw [AffineDensities.gradient_affine hg,AffineDensities.rescale,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht]
  rw [integral_const_mul,← integral_indicator unitRegion_measurable,
    ← integral_indicator (region_measurable p t)]
  have he : unitRegion.indicator (fun x => ‖gradient g (p+t • x)‖) =
      (fun x => (region p t).indicator (fun z => ‖gradient g z‖) (p+t • x)) := by
    ext x
    have hx : p+t • x∈region p t ↔ x∈unitRegion := by
      change ‖p+t • x-p‖≤8*t ↔ ‖x‖≤8
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      constructor <;> intro hh <;> nlinarith
    by_cases h : x∈unitRegion
    · rw [Set.indicator_of_mem h,Set.indicator_of_mem (hx.mpr h)]
    · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem (fun hh => h (hx.mp hh))]
  rw [he,integral_stretch]
  field_simp

lemma physical_localization : ∃ D : ℝ, 0≤D ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∀ (p : ℂ) {t : ℝ}, 0<t →
    ∃ (h : ℂ → ℝ) (c : ℝ), ContDiff ℝ 1 h ∧ HasCompactSupport h ∧
      (∀ x, ‖x-p‖≤4*t → h x=g x-c) ∧
      (∫ x,‖gradient h x‖) ≤ D*(∫ x in region p t,‖gradient g x‖) := by
  obtain ⟨D,hD,he⟩ := unit_localization
  refine ⟨D,hD,?_⟩
  intro g hg hc p t ht
  let G := fun x => g (p+t • x)
  have ha : ContDiff ℝ 1 (fun x : ℂ => p+t • x) := contDiff_const.add (contDiff_id.const_smul t)
  have hG : ContDiff ℝ 1 G := hg.comp ha
  have hmap : ContDiff ℝ 1 (toUnit p t) := (contDiff_id.sub contDiff_const).const_smul t⁻¹
  obtain ⟨h,c,hd,hs,hh,hb⟩ := he hG (comp_stretch_compact hc p ht.ne')
  refine ⟨fun x => h (toUnit p t x),c,hd.comp hmap,
    comp_toUnit_compact hs p ht.ne',?_,?_⟩
  · intro x hx
    have hx' : ‖toUnit p t x‖≤4 := by rw [norm_toUnit p x ht]; exact (div_le_iff₀ ht).mpr hx
    simpa only [G,affine_toUnit p ht.ne'] using hh _ hx'
  · rw [integral_gradient_toUnit (hd.differentiable one_ne_zero) p ht]
    have he' := mul_le_mul_of_nonneg_left hb ht.le
    rw [local_integral_gradient_stretch (hg.differentiable one_ne_zero) p ht] at he'
    convert he' using 1
    first | rfl | field_simp
end NullLocalization

namespace NullLocalization
open SobolevBand DiskMoments PhysicalCells DyadicHats RadiusEnvelope

lemma band_sub_local {g h : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {a t : ℝ}
    (ha : 0<a) (hat : a≤t) {p x : ℂ} {c : ℝ}
    (hlocal : ∀ y, ‖y-p‖≤4*t → h y=g y-c) (hx : ‖x-p‖<3*t) :
    band h a t x=band g a t x-c := by
  have hav (r : ℝ) (hr : r∈Icc a t) : signedAverage h x r=signedAverage g x r-c := by
    rw [← signedAverage_sub_const hg.continuous c x (ha.trans_le hr.1)]
    unfold signedAverage
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    apply hlocal
    have hn := norm_add_le (y-x) (x-p)
    rw [sub_add_sub_cancel] at hn
    have hd : ‖y-x‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    linarith [hr.2]
  have hi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hi' : Integrable h := hh.continuous.integrable_of_hasCompactSupport hhc
  apply le_antisymm
  · apply band_le hat x
    intro r hr
    rw [hav r hr]
    exact sub_le_sub_right (average_le_band hi ha hr x) c
  · obtain ⟨r,hr,he,_⟩ := attains (u := fun r x => signedAverage g x r) hat x (signedAverage_radius_continuousOn hg x ha)
    rw [show band g a t x=signedAverage g x r from he,← hav r hr]
    exact average_le_band hi' ha hr x

lemma gradient_band_local {g h : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {a t : ℝ}
    (ha : 0<a) (hat : a≤t) {p x : ℂ} {c : ℝ}
    (hlocal : ∀ y, ‖y-p‖≤4*t → h y=g y-c) (hx : ‖x-p‖≤2*t) :
    gradient (band h a t) x=gradient (band g a t) x := by
  have ht : 0<t := ha.trans_le hat
  have he : band h a t =ᶠ[𝓝 x] (fun y => band g a t y-c) := by
    have hn : ‖x-p‖<3*t := by linarith
    filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds hn] with y hy
    exact band_sub_local hg hh hgc hhc ha hat hlocal hy
  apply congrArg (InnerProductSpace.toDual ℝ ℂ).symm
  exact he.fderiv_eq.trans (fderiv_sub_const c)

lemma mem_cell_norm {t : ℝ} (ht : 0<t) {p x : ℂ} (hx : x∈cell p t) : ‖x-p‖≤2*t := by
  have hn := norm_unitCell hx
  change ‖toUnit p t x‖≤2 at hn
  rw [norm_toUnit p x ht] at hn
  exact (div_le_iff₀ ht).mp hn

lemma smooth_local_band : ∃ C : ℝ, 0<C ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∀ {a : ℝ}, 0<a → ∀ m : ℕ, ∀ p : ℂ,
    (∫ x in cell p (2*((2:ℝ)^m*a)), ‖gradient (band g a (2*((2:ℝ)^m*a))) x‖) ≤
      C*(∫ x in region p (2*((2:ℝ)^m*a)), ‖gradient g x‖) := by
  obtain ⟨C,hC,hbound⟩ := smooth_dyadic_bound
  obtain ⟨D,hD,hloc⟩ := physical_localization
  refine ⟨C*(D+1),by positivity,?_⟩
  intro g hg hc a ha m p
  let t := 2*((2:ℝ)^m*a)
  have ht : 0<t := by dsimp only [t]; positivity
  have hat : a≤t := by
    have hp : (1:ℝ)≤2^m := one_le_pow₀ (by norm_num)
    dsimp only [t]; nlinarith
  obtain ⟨h,c,hd,hs,hh,hb⟩ := hloc hg hc p ht
  have hbi := smooth_band_integrable_gradient hd hs ha hat
  calc
    _ = ∫ x in cell p t,‖gradient (band h a t) x‖ := by
      apply setIntegral_congr_fun (cell_measurable p t)
      intro x hx
      change ‖gradient (band g a t) x‖=‖gradient (band h a t) x‖
      rw [gradient_band_local hg hd hc hs ha hat hh (mem_cell_norm ht hx)]
    _ ≤ ∫ x, ‖gradient (band h a t) x‖ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => norm_nonneg _)) hbi.norm
    _ ≤ C*(∫ x,‖gradient h x‖) := hbound hd hs ha m
    _ ≤ C*(D*(∫ x in region p t,‖gradient g x‖)) := mul_le_mul_of_nonneg_left hb hC.le
    _ ≤ C*(D+1)*(∫ x in region p t,‖gradient g x‖) := by
      have h0 : 0 ≤ (∫ x in region p t, ‖gradient g x‖) := integral_nonneg (fun x => norm_nonneg (gradient g x))
      nlinarith
end NullLocalization

namespace NullLocalization
open scoped Classical
open PhysicalCells DyadicHats DirectionNeighbors Finset

lemma region_indices {t : ℝ} (ht : 0<t) (y : ℂ) {p : ℤ×ℤ}
    (hp : y∈region (point t p) t) : p∈window 10 (gridIndex t y) := by
  apply (mem_window_iff ht 10 _ _).mpr
  have hn := mem_cell_norm ht (mem_index_cell ht y)
  have hd := norm_add_le (point t p-y) (y-point t (gridIndex t y))
  rw [sub_add_sub_cancel,norm_sub_rev (point t p) y] at hd
  change ‖y-point t p‖≤8*t at hp
  exact (boxNorm_le_norm _).trans (by norm_num; linarith)

lemma regions_overlap {t : ℝ} (ht : 0<t) (S : Finset (ℤ×ℤ)) (y : ℂ) :
    (∑ p∈S, if y∈region (point t p) t then (1:ℝ) else 0) ≤ 441 := by
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hs : S.filter (fun p => y∈region (point t p) t) ⊆ window 10 (gridIndex t y) := by
    intro p hp; exact region_indices ht y (Finset.mem_filter.mp hp).2
  have h := Finset.card_le_card hs
  rw [card_window] at h
  exact_mod_cast h

def touches (O : Set ℂ) (t : ℝ) (p : ℤ×ℤ) : Prop := (O∩cell (point t p) t).Nonempty

def usedRegion (O : Set ℂ) (t : ℝ) (p : ℤ×ℤ) : Set ℂ := by
  classical
  exact if touches O t p then region (point t p) t else ∅

lemma usedRegion_measurable (O : Set ℂ) (t : ℝ) (p : ℤ×ℤ) : MeasurableSet (usedRegion O t p) := by
  unfold usedRegion
  split_ifs
  · exact region_measurable _ _
  · exact MeasurableSet.empty

lemma usedRegion_subset {O K : Set ℂ} {t : ℝ} (ht : 0<t)
    (hO : O⊆Metric.thickening t K) (p : ℤ×ℤ) : usedRegion O t p ⊆ Metric.thickening (12*t) K := by
  intro y hy
  unfold usedRegion at hy
  split_ifs at hy with hp
  · obtain ⟨z,hzO,hzcell⟩ := hp
    obtain ⟨w,hw,hzw⟩ := Metric.mem_thickening_iff.mp (hO hzO)
    apply Metric.mem_thickening_iff.mpr
    refine ⟨w,hw,?_⟩
    have hz := mem_cell_norm ht hzcell
    change ‖y-point t p‖≤8*t at hy
    have h1 := dist_triangle y (point t p) z
    have h2 := dist_triangle y z w
    simp only [dist_eq_norm] at h1 h2 hzw ⊢
    rw [norm_sub_rev (point t p) z] at h1
    linarith
  · exact hy.elim

lemma usedRegion_budget {O K : Set ℂ} {t : ℝ} (ht : 0<t)
    (hO : O⊆Metric.thickening t K) {F : ℂ → ℝ} (hF : Integrable F) (h0 : ∀ y,0≤F y)
    (S : Finset (ℤ×ℤ)) :
    (∑ p∈S,∫ y in usedRegion O t p,F y) ≤ 441*(∫ y in Metric.thickening (12*t) K,F y) := by
  classical
  let T := Metric.thickening (12*t) K
  have hT : MeasurableSet T := Metric.isOpen_thickening.measurableSet
  have hi (p : ℤ×ℤ) : Integrable ((usedRegion O t p).indicator F) := hF.indicator (usedRegion_measurable _ _ _)
  simp_rw [← integral_indicator (usedRegion_measurable O t _)]
  rw [← integral_finsetSum S (fun p _ => hi p),← integral_indicator hT,← integral_const_mul]
  apply integral_mono (integrable_finsetSum S (fun p _ => hi p)) ((hF.indicator hT).const_mul 441)
  intro y
  dsimp only
  by_cases hy : y∈T
  · rw [Set.indicator_of_mem hy]
    calc
      _ ≤ ∑ p∈S,(if y∈region (point t p) t then (1:ℝ) else 0)*F y := by
        apply Finset.sum_le_sum
        intro p _
        unfold usedRegion
        by_cases hp : touches O t p
        · simp only [ite_eq_left hp,Set.indicator_apply]
          split_ifs <;> simp
        · simp only [ite_eq_right hp,Set.indicator_empty]
          split_ifs
          · simpa using h0 y
          · simp
      _ = (∑ p∈S,if y∈region (point t p) t then (1:ℝ) else 0)*F y := (Finset.sum_mul _ _ _).symm
      _ ≤ 441*F y := mul_le_mul_of_nonneg_right (regions_overlap ht S y) (h0 y)
  · rw [Set.indicator_of_notMem hy,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro p _
    exact Set.indicator_of_notMem (fun hp => hy (usedRegion_subset ht hO p hp)) F
end NullLocalization

namespace NullLocalization
open SobolevBand DiskMoments PhysicalCells DyadicHats

lemma smooth_small_local_budget : ∃ C : ℝ, 0<C ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∀ {a : ℝ}, 0<a → ∀ m : ℕ, ∀ {O K : Set ℂ}, MeasurableSet O →
    O⊆Metric.thickening (2*((2:ℝ)^m*a)) K →
    (∫ x in O,‖gradient (band g a (2*((2:ℝ)^m*a))) x‖) ≤
      C*(∫ x in Metric.thickening (12*(2*((2:ℝ)^m*a))) K,‖gradient g x‖) := by
  classical
  obtain ⟨C,hC,hlocal⟩ := smooth_local_band
  refine ⟨C*441,by positivity,?_⟩
  intro g hg hc a ha m O K hO hOK
  let t := 2*((2:ℝ)^m*a)
  have ht : 0<t := by dsimp only [t]; positivity
  have hat : a≤t := by
    have hpow : (1:ℝ)≤2^m := one_le_pow₀ (by norm_num)
    dsimp only [t]; nlinarith
  let F := fun x => ‖gradient (band g a t) x‖
  let G := fun x => ‖gradient g x‖
  have hF : Integrable F := (smooth_band_integrable_gradient hg hc ha hat).norm
  have hG : Integrable G := ((continuous_gradient hg).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)).norm
  have hF0 x : 0≤F x := norm_nonneg _
  have hG0 x : 0≤G x := norm_nonneg _
  have hi : Integrable (O.indicator F) := hF.indicator hO
  have hi0 x : 0≤O.indicator F x := Set.indicator_nonneg (fun x _ => hF0 x) x
  let B := fun p : ℤ×ℤ => C*(∫ x in usedRegion O t p,G x)
  have hB p : 0≤B p := mul_nonneg hC.le (integral_nonneg hG0)
  have hcell p : (∫⁻ x in cell (point t p) t, ENNReal.ofReal (O.indicator F x)) ≤ ENNReal.ofReal (B p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ hi0)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hp : touches O t p
    · change _ ≤ C*(∫ x in usedRegion O t p,G x)
      rw [usedRegion,ite_eq_left hp]
      apply (integral_mono hi.integrableOn hF.integrableOn (fun x => ?_)).trans (hlocal hg hc ha m (point t p))
      exact Set.indicator_le_self' (fun x _ => hF0 x) x
    · have he : ∀ x∈cell (point t p) t, O.indicator F x=0 := by
        intro x hx
        apply Set.indicator_of_notMem
        intro hxO
        exact hp ⟨x,hxO,hx⟩
      rw [setIntegral_eq_zero_of_forall_eq_zero he]
      exact hB p
  have hbudget (S : Finset (ℤ×ℤ)) : (∑ p∈S,B p) ≤ C*441*(∫ x in Metric.thickening (12*t) K,G x) := by
    simp only [B,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (usedRegion_budget ht hOK hG hG0 S) hC.le).trans_eq (by ring)
  have hb := integral_cell_budget ht (fun x => ENNReal.ofReal (O.indicator F x)) B hB _ hcell hbudget
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hi0),integral_indicator hO] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

end NullLocalization

end

end OAI
