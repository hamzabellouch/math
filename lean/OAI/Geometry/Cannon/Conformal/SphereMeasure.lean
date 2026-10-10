import Mathlib
import OAI.Geometry.Cannon.Conformal.OpenMapMaxSphere

namespace OAI

section
section
section
section
section
section
section
section
section
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

instance sphereMeasurableSpace : MeasurableSpace Sphere := borel Sphere
instance sphereBorelSpace : BorelSpace Sphere := ⟨rfl⟩

def sphereMeasure : Measure Sphere := volume.map (fun z : ℂ => (z:Sphere))

lemma sphereMeasure_apply (S : Set Sphere) :
    sphereMeasure S=volume ((fun z : ℂ => (z:Sphere)) ⁻¹' S) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding.map_apply volume S

lemma chartDomain_ae (f : Sphere ≃ₜ Sphere) (s t : Bool) :
    ∀ᵐ z : ℂ, z ∈ chartDomain s t f := by
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  have hx' : chart t (f (chart s (x:Sphere)))=∞ := by simpa only [chartDomain,mem_ofPred_eq,not_not] using hx
  have hy' : chart t (f (chart s (y:Sphere)))=∞ := by simpa only [chartDomain,mem_ofPred_eq,not_not] using hy
  exact OnePoint.coe_injective ((chart s).injective (f.injective ((chart t).injective (hx'.trans hy'.symm))))

lemma sphere_image_null_of_chart (f : Sphere ≃ₜ Sphere)
    (hN : ∀ S : Set ℂ, volume S=0 →
      volume (inChart false false f '' (S ∩ chartDomain false false f))=0)
    {T : Set Sphere} (hT : sphereMeasure T=0) : sphereMeasure (f '' T)=0 := by
  rw [sphereMeasure_apply] at hT ⊢
  let S := (fun z : ℂ => (z:Sphere)) ⁻¹' T
  have hsub : (fun z : ℂ => (z:Sphere)) ⁻¹' (f '' T) ⊆
      inChart false false f '' (S ∩ chartDomain false false f) ∪ {coordinate (f ∞)} := by
    rintro z ⟨p,hp,he⟩
    induction p using OnePoint.rec with
    | infty =>
      right
      exact (congrArg coordinate he).symm
    | coe w =>
      left
      refine ⟨w,⟨hp,?_⟩,?_⟩
      · change f (w:Sphere) ≠ ∞
        rw [he]
        exact OnePoint.coe_ne_infty z
      · change coordinate (f (w:Sphere))=z
        rw [he,coordinate_coe]
  exact measure_mono_null hsub (measure_union_null (hN S hT) (measure_singleton _))

lemma analytic_sphere_image_null {f : Sphere ≃ₜ Sphere} (hf : IsAnalytic f)
    {T : Set Sphere} (hT : sphereMeasure T=0) : sphereMeasure (f '' T)=0 := by
  apply sphere_image_null_of_chart f _ hT
  intro S hS
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (((hf false false).restrictScalars ℝ).mono inter_subset_right)
    (measure_mono_null inter_subset_left hS)

lemma onePoint_image_null (F : ℂ ≃ₜ ℂ)
    (hF : ∀ S : Set ℂ, volume S=0 → volume (F '' S)=0)
    {T : Set Sphere} (hT : sphereMeasure T=0) :
    sphereMeasure (F.onePointCongr '' T)=0 := by
  apply sphere_image_null_of_chart F.onePointCongr _ hT
  intro S hS
  have he : inChart false false F.onePointCongr=(F : ℂ → ℂ) := by
    funext z
    simp [inChart,chart,coordinate]
  rw [he]
  exact measure_mono_null (image_mono inter_subset_left) (hF S hS)

theorem controlled_sphere_image_null (f : Sphere ≃ₜ Sphere) {η : CannonQM.Distortion}
    (hf : CannonQM.Controlled f η) {T : Set Sphere} (hT : sphereMeasure T=0) :
    sphereMeasure (f '' T)=0 := by
  obtain ⟨M,hM,hMa,hF⟩ := normalized_weakQS f hf
  let F := finiteRestriction (M*f) hM
  have hN := onePoint_image_null F
    (fun S => CannonMetricQC.weakQS_image_null F (by positivity) hF (S:=S)) hT
  have hN' := analytic_sphere_image_null hMa.2 hN
  have he : (M.symm : Sphere → Sphere) ∘ (F.onePointCongr : Sphere → Sphere)=f := by
    rw [show F.onePointCongr=M*f from restriction_extension (M*f) hM]
    funext p
    exact M.symm_apply_apply (f p)
  rw [image_image] at hN'
  change sphereMeasure (((M.symm : Sphere → Sphere) ∘ (F.onePointCongr : Sphere → Sphere)) '' T)=0 at hN'
  rwa [he] at hN'

theorem controlled_sphere_quasiMeasurePreserving (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    Measure.QuasiMeasurePreserving (f : Sphere → Sphere) sphereMeasure sphereMeasure := by
  refine ⟨f.continuous.measurable,?_⟩
  intro S hS
  rw [f.measurableEmbedding.map_apply]
  rw [← show f.symm '' S=f ⁻¹' S from f.toEquiv.image_symm_eq_preimage S]
  exact controlled_sphere_image_null f.symm (hf.inverse f) hS

end CannonMobius

namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma chart_mul_eventually (f g : Sphere ≃ₜ Sphere) {z : ℂ}
    (hz : z ∈ chartDomain false false g) :
    inChart false false (f*g) =ᶠ[𝓝 z]
      (fun w => inChart false false f (inChart false false g w)) := by
  filter_upwards [(isOpen_chartDomain false false g).mem_nhds hz] with w hw
  change coordinate (f (g (w:Sphere)))=coordinate (f (coordinate (g (w:Sphere)):Sphere))
  change g (w:Sphere) ≠ ∞ at hw
  rw [coe_coordinate hw]

lemma chart_symm_domain (f : Sphere ≃ₜ Sphere) {z : ℂ}
    (hz : z ∈ chartDomain false false f) :
    inChart false false f z ∈ chartDomain false false f.symm := by
  change f.symm (coordinate (f (z:Sphere)):Sphere) ≠ ∞
  change f (z:Sphere) ≠ ∞ at hz
  rw [coe_coordinate hz,f.symm_apply_apply]
  exact OnePoint.coe_ne_infty z

lemma chart_symm_comp_eventually (f : Sphere ≃ₜ Sphere) {z : ℂ}
    (hz : z ∈ chartDomain false false f) :
    (fun w => inChart false false f.symm (inChart false false f w)) =ᶠ[𝓝 z] id := by
  filter_upwards [(isOpen_chartDomain false false f).mem_nhds hz] with w hw
  change coordinate (f.symm (coordinate (f (w:Sphere)):Sphere))=w
  change f (w:Sphere) ≠ ∞ at hw
  rw [coe_coordinate hw,f.symm_apply_apply,coordinate_coe]

lemma analytic_chart_bijective (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic)
    {z : ℂ} (hz : z ∈ chartDomain false false f) :
    Function.Bijective (fderiv ℝ (inChart false false f) z) := by
  have hd := (analytic_differentiableAt hf.1 false false hz).restrictScalars ℝ
  have hi := (analytic_differentiableAt hf.2 false false (chart_symm_domain f hz)).restrictScalars ℝ
  have he := ((hi.hasFDerivAt.comp z hd.hasFDerivAt).congr_of_eventuallyEq
    (chart_symm_comp_eventually f hz).symm).unique (hasFDerivAt_id z)
  have hl : Function.LeftInverse (fderiv ℝ (inChart false false f.symm) (inChart false false f z))
      (fderiv ℝ (inChart false false f) z) := by
    intro v
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  exact ⟨hl.injective,LinearMap.injective_iff_surjective.mp hl.injective⟩

lemma analytic_chart_conformal (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic)
    {z : ℂ} (hz : z ∈ chartDomain false false f) :
    IsConformalMap (fderiv ℝ (inChart false false f) z) := by
  have hd := analytic_differentiableAt hf.1 false false hz
  have hbij := analytic_chart_bijective f hf hz
  rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv] at hbij ⊢
  apply isConformalMap_complex_linear
  intro he
  apply (zero_ne_one : (0:ℂ) ≠ 1)
  apply hbij.1
  rw [he]
  rfl

theorem controlled_sphere_ae_differentiable (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ (inChart false false f) z := by
  obtain ⟨M,hM,hMa,hF⟩ := normalized_weakQS f hf
  let F := finiteRestriction (M*f) hM
  filter_upwards [CannonMetricQC.weakQS_ae_differentiable F (by positivity) hF,
    chartDomain_ae f false false] with z hz hdom
  have he (w : ℂ) : (F w:Sphere)=M (f (w:Sphere)) :=
    coe_coordinate (coe_map_ne_infty (M*f) hM w)
  have hMd : F z ∈ chartDomain false false M.symm := by
    change M.symm (F z:Sphere) ≠ ∞
    rw [he,M.symm_apply_apply]
    exact hdom
  have hh := ((analytic_differentiableAt hMa.2 false false hMd).restrictScalars ℝ).comp z hz
  have heq : inChart false false f=inChart false false M.symm ∘ (F : ℂ → ℂ) := by
    funext w
    change coordinate (f (w:Sphere))=coordinate (M.symm (F w:Sphere))
    rw [he,M.symm_apply_apply]
  rw [heq]
  exact hh

end CannonMobius

namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma ae_sphere_iff {P : Sphere → Prop} :
    (∀ᵐ p ∂sphereMeasure, P p) ↔ ∀ᵐ z : ℂ, P (z:Sphere) := by
  simp only [ae_iff,sphereMeasure_apply,preimage_ofPred_eq]

lemma controlled_chart_ae_pullback (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η)
    {P : ℂ → Prop} (hP : ∀ᵐ z : ℂ, P z) :
    ∀ᵐ z : ℂ, P (inChart false false f z) := by
  have hps : ∀ᵐ p ∂sphereMeasure, P (coordinate p) := by
    rw [ae_sphere_iff]
    simpa only [coordinate_coe] using hP
  simpa only [ae_sphere_iff,inChart,chart,Homeomorph.one_apply] using
    (controlled_sphere_quasiMeasurePreserving f hf).ae hps

theorem controlled_sphere_ae_bijective_fderiv (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, Function.Bijective (fderiv ℝ (inChart false false f) z) := by
  filter_upwards [controlled_sphere_ae_differentiable f hf,
    controlled_chart_ae_pullback f hf
      (controlled_sphere_ae_differentiable f.symm (hf.inverse f)),
    chartDomain_ae f false false] with z hz hi hdom
  have he := ((hi.hasFDerivAt.comp z hz.hasFDerivAt).congr_of_eventuallyEq
    (chart_symm_comp_eventually f hdom).symm).unique (hasFDerivAt_id z)
  have hl : Function.LeftInverse
      (fderiv ℝ (inChart false false f.symm) (inChart false false f z))
      (fderiv ℝ (inChart false false f) z) := by
    intro v
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L v) he
  exact ⟨hl.injective,LinearMap.injective_iff_surjective.mp hl.injective⟩

theorem controlled_sphere_ae_chain (f g : Sphere ≃ₜ Sphere)
    {η θ : CannonQM.Distortion} (hf : CannonQM.Controlled f η) (hg : CannonQM.Controlled g θ) :
    ∀ᵐ z : ℂ, fderiv ℝ (inChart false false (f*g)) z =
      (fderiv ℝ (inChart false false f) (inChart false false g z)).comp
        (fderiv ℝ (inChart false false g) z) := by
  filter_upwards [controlled_sphere_ae_differentiable g hg,
    controlled_chart_ae_pullback g hg (controlled_sphere_ae_differentiable f hf),
    chartDomain_ae g false false] with z hz hi hdom
  exact ((hi.hasFDerivAt.comp z hz.hasFDerivAt).congr_of_eventuallyEq (chart_mul_eventually f g hdom)).fderiv

end CannonMobius

end
end
section
noncomputable section

namespace CannonMetricQC
open Filter MeasureTheory
open scoped Topology

lemma WeakQS.derivative_distortion {f : ℂ → ℂ} {H : ℝ} (hf : WeakQS f H)
    {x : ℂ} {A : ℂ →L[ℝ] ℂ} (ha : HasFDerivAt f A x)
    {u v : ℂ} (huv : ‖u‖ ≤ ‖v‖) : ‖A u‖ ≤ H*‖A v‖ := by
  apply le_of_tendsto_of_tendsto (ha.lim_real u |>.norm)
    ((ha.lim_real v |>.norm).const_mul H)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
  have hdist : dist x (x+c⁻¹ • u) ≤ dist x (x+c⁻¹ • v) := by
    simpa only [dist_eq_norm,sub_add_cancel_left,norm_neg,norm_smul]
      using mul_le_mul_of_nonneg_left huv (norm_nonneg c⁻¹)
  have h := hf x (x+c⁻¹ • u) (x+c⁻¹ • v) hdist
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  rw [dist_comm x (x+c⁻¹ • u),dist_comm x (x+c⁻¹ • v)] at hdist
  rw [dist_comm (f x) (f (x+c⁻¹ • u)),dist_comm (f x) (f (x+c⁻¹ • v)),dist_eq_norm,dist_eq_norm] at h
  nlinarith
end CannonMetricQC

noncomputable section
namespace CannonConformal
open Set Topology Metric

abbrev Form := Fin 3 → ℝ
def determinant (q : Form) : ℝ := q 0*q 2-(q 1)^2
def evaluate (q : Form) (x y : ℝ) : ℝ := q 0*x^2+2*q 1*x*y+q 2*y^2
def Positive (q : Form) : Prop := 0 < q 0 ∧ 0 < determinant q
def LowerBound (ε : ℝ) (q : Form) : Prop := ∀ x y : ℝ, ε*(x^2+y^2) ≤ evaluate q x y
def UpperBound (K : ℝ) (q : Form) : Prop := ∀ x y : ℝ, evaluate q x y ≤ K*(x^2+y^2)

lemma determinant_nonneg_of_evaluate {p : Form} (hp : ∀ x y, 0 ≤ evaluate p x y) :
    0 ≤ determinant p := by
  have ha : 0 ≤ p 0 := by simpa [evaluate] using hp 1 0
  have hc : 0 ≤ p 2 := by simpa [evaluate] using hp 0 1
  by_cases hz : p 0=0
  · have h := hp (-(p 2+1)) (p 1)
    have hb : p 1=0 := by
      simp only [evaluate,hz,zero_mul,zero_add] at h
      nlinarith [sq_nonneg (p 1),mul_nonneg hc (sq_nonneg (p 1))]
    simp [determinant,hz,hb]
  · have h := hp (p 1) (-(p 0))
    have ha' : 0 < p 0 := lt_of_le_of_ne ha (Ne.symm hz)
    have hid : evaluate p (p 1) (-p 0)=p 0*determinant p := by
      simp [evaluate,determinant]; ring
    rw [hid] at h
    exact nonneg_of_mul_nonneg_right h ha'

lemma determinant_ge_sq_lower {ε : ℝ} (hε : 0 ≤ ε) {q : Form}
    (hl : LowerBound ε q) : ε^2 ≤ determinant q := by
  let p : Form := ![q 0-ε,q 1,q 2-ε]
  have he (x y : ℝ) : evaluate p x y=evaluate q x y-ε*(x^2+y^2) := by
    simp [p,evaluate]; ring
  have hp := determinant_nonneg_of_evaluate (p:=p) (fun x y => by rw [he]; linarith [hl x y])
  have h0 : ε ≤ q 0 := by simpa [evaluate] using hl 1 0
  have h2 : ε ≤ q 2 := by simpa [evaluate] using hl 0 1
  change 0 ≤ (q 0-ε)*(q 2-ε)-(q 1)^2 at hp
  dsimp [determinant]
  nlinarith

end CannonConformal

namespace CannonMetricQC
open CannonConformal
open scoped ComplexOrder

def derivativeMatrix (A : ℂ →L[ℝ] ℂ) : Fin 4 → ℝ :=
  ![(A 1).re,(A Complex.I).re,(A 1).im,(A Complex.I).im]
def derivativeDet (A : ℂ →L[ℝ] ℂ) : ℝ :=
  (A 1).re*(A Complex.I).im-(A Complex.I).re*(A 1).im

def derivativeForm (A : ℂ →L[ℝ] ℂ) : Form :=
  ![‖A 1‖^2,(A 1).re*(A Complex.I).re+(A 1).im*(A Complex.I).im,‖A Complex.I‖^2]

lemma derivative_apply (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z=z.re • A 1+z.im • A Complex.I := by
  calc
    A z = A (z.re • (1 : ℂ)+z.im • Complex.I) := by
      congr 1
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
    _ = _ := by rw [map_add,map_smul,map_smul]

lemma derivativeForm_evaluate (A : ℂ →L[ℝ] ℂ) (x y : ℝ) :
    evaluate (derivativeForm A) x y=‖A (⟨x,y⟩ : ℂ)‖^2 := by
  rw [derivative_apply,Complex.sq_norm]
  simp [evaluate,derivativeForm,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma derivativeForm_det (A : ℂ →L[ℝ] ℂ) :
    determinant (derivativeForm A)=(derivativeDet A)^2 := by
  simp [determinant,derivativeForm,derivativeDet,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma linear_distortion_scaled {A : ℂ →L[ℝ] ℂ} {H : ℝ}
    (ha : ∀ u v : ℂ, ‖u‖ ≤ ‖v‖ → ‖A u‖ ≤ H*‖A v‖) (u v : ℂ) :
    ‖A u‖*‖v‖ ≤ H*‖A v‖*‖u‖ := by
  by_cases hu : u=0
  · simp [hu]
  have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hn : ‖(‖v‖/‖u‖) • u‖=‖v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    field_simp
  have h := ha ((‖v‖/‖u‖) • u) v hn.le
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at h
  have he : (‖v‖/‖u‖)*‖A u‖=(‖A u‖*‖v‖)/‖u‖ := by ring
  rw [he] at h
  exact (div_le_iff₀ hp).mp h

theorem linear_distortion_jacobian {A : ℂ →L[ℝ] ℂ} {H : ℝ} (hH : 0 < H)
    (ha : ∀ u v : ℂ, ‖u‖ ≤ ‖v‖ → ‖A u‖ ≤ H*‖A v‖) (u : ℂ) :
    ‖A u‖^2 ≤ H^2* |derivativeDet A| * ‖u‖^2 := by
  by_cases hu : u=0
  · simp [hu]
  have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let ε : ℝ := ‖A u‖^2/(H^2*‖u‖^2)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hl : LowerBound ε (derivativeForm A) := by
    intro x y
    let v : ℂ := ⟨x,y⟩
    have hh := linear_distortion_scaled ha u v
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖A u‖*‖v‖) hh 2
    have hv : ‖v‖^2=x^2+y^2 := by rw [Complex.sq_norm]; simp [v,Complex.normSq_apply,pow_two]
    rw [mul_pow,mul_pow,mul_pow,hv] at hs
    rw [derivativeForm_evaluate]
    change ε*(x^2+y^2) ≤ ‖A v‖^2
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < H^2*‖u‖^2)).mpr
    nlinarith only [hs]
  have hd := determinant_ge_sq_lower hε hl
  rw [derivativeForm_det] at hd
  have he : ε ≤ |derivativeDet A| := by
    nlinarith [sq_abs (derivativeDet A),abs_nonneg (derivativeDet A)]
  dsimp [ε] at he
  have he' := (div_le_iff₀ (by positivity : 0 < H^2*‖u‖^2)).mp he
  nlinarith only [he']

lemma WeakQS.derivative_jacobian {f : ℂ → ℂ} {H : ℝ} (hH : 0 < H)
    (hf : WeakQS f H) {x : ℂ} {A : ℂ →L[ℝ] ℂ} (ha : HasFDerivAt f A x) (u : ℂ) :
    ‖A u‖^2 ≤ H^2* |derivativeDet A| * ‖u‖^2 :=
  linear_distortion_jacobian hH (fun _ _ h => hf.derivative_distortion ha h) u

lemma derivativeDet_eq_det (A : ℂ →L[ℝ] ℂ) : derivativeDet A=A.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [derivativeDet,LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr]

lemma derivativeDet_ne_zero {A : ℂ →L[ℝ] ℂ} (hA : Function.Bijective A) :
    derivativeDet A ≠ 0 := by
  rw [derivativeDet_eq_det]
  exact (LinearEquiv.ofBijective A.toLinearMap hA).isUnit_det'.ne_zero
end CannonMetricQC

end
end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory
open scoped OnePoint

lemma chart_normalized_eq (f M : Sphere ≃ₜ Sphere) (hM : (M*f) ∞=∞) :
    inChart false false f=inChart false false M.symm ∘ finiteRestriction (M*f) hM := by
  funext w
  change coordinate (f (w:Sphere))=
    coordinate (M.symm (coordinate ((M*f) (w:Sphere)):Sphere))
  rw [coe_coordinate (coe_map_ne_infty (M*f) hM w)]
  simp only [Homeomorph.mul_apply,Homeomorph.symm_apply_apply]

theorem controlled_sphere_ae_distortion (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, ∀ u v : ℂ, ‖u‖ ≤ ‖v‖ →
      ‖fderiv ℝ (inChart false false f) z u‖ ≤
        (1+2*(η 2:ℝ))*‖fderiv ℝ (inChart false false f) z v‖ := by
  obtain ⟨M,hM,hMa,hF⟩ := normalized_weakQS f hf
  let F := finiteRestriction (M*f) hM
  filter_upwards [CannonMetricQC.weakQS_ae_differentiable F (by positivity) hF,
    chartDomain_ae f false false] with z hz hdom
  have he (w : ℂ) : (F w:Sphere)=M (f (w:Sphere)) :=
    coe_coordinate (coe_map_ne_infty (M*f) hM w)
  have hMd : F z ∈ chartDomain false false M.symm := by
    change M.symm (F z:Sphere) ≠ ∞
    rw [he,M.symm_apply_apply]
    exact hdom
  have hd := (analytic_differentiableAt hMa.2 false false hMd).restrictScalars ℝ
  have hre : fderiv ℝ (inChart false false f) z=
      (fderiv ℝ (inChart false false M.symm) (F z)).comp (fderiv ℝ (F : ℂ → ℂ) z) := by
    rw [chart_normalized_eq f M hM]
    exact (hd.hasFDerivAt.comp z hz.hasFDerivAt).fderiv
  have hc := analytic_chart_conformal M.symm ⟨hMa.2,hMa.1⟩ hMd
  obtain ⟨r,hr,U,hU⟩ := hc
  intro u v huv
  have hh := hF.derivative_distortion hz.hasFDerivAt huv
  rw [hre,hU]
  simpa only [ContinuousLinearMap.comp_apply,smul_apply,
    norm_smul,LinearIsometry.coe_toContinuousLinearMap,U.norm_map,mul_assoc,mul_left_comm] using
    mul_le_mul_of_nonneg_left hh (norm_nonneg r)

theorem controlled_sphere_ae_jacobian_bound (f : Sphere ≃ₜ Sphere)
    {η : CannonQM.Distortion} (hf : CannonQM.Controlled f η) :
    ∀ᵐ z : ℂ, ∀ u : ℂ, ‖fderiv ℝ (inChart false false f) z u‖^2 ≤
      (1+2*(η 2:ℝ))^2* |CannonMetricQC.derivativeDet (fderiv ℝ (inChart false false f) z)| * ‖u‖^2 := by
  filter_upwards [controlled_sphere_ae_distortion f hf] with z hz
  exact CannonMetricQC.linear_distortion_jacobian (by positivity) hz

end CannonMobius

end
end
section
noncomputable section
namespace CannonConformal
open Set MeasureTheory

variable {Γ X : Type*} [Group Γ] [MeasurableSpace X]

def orbitCore (A : Γ →* Equiv.Perm X) (S : Set X) : Set X :=
  {x | ∀ g : Γ, A g x ∈ S}

omit [MeasurableSpace X] in
lemma orbitCore_subset (A : Γ →* Equiv.Perm X) (S : Set X) : orbitCore A S ⊆ S := by
  intro x hx
  simpa using hx 1

omit [MeasurableSpace X] in
lemma orbitCore_invariant (A : Γ →* Equiv.Perm X) (S : Set X) (g : Γ) (x : X) :
    A g x ∈ orbitCore A S ↔ x ∈ orbitCore A S := by
  constructor
  · intro hx h
    simpa only [map_mul,Equiv.Perm.mul_apply,map_inv,Equiv.Perm.inv_def,
      Equiv.symm_apply_apply] using hx (h*g⁻¹)
  · intro hx h
    simpa only [map_mul,Equiv.Perm.mul_apply] using hx (h*g)

lemma orbitCore_measurable [Countable Γ] (A : Γ →* Equiv.Perm X) {S : Set X}
    (hS : MeasurableSet S) (hA : ∀ g, Measurable (A g)) : MeasurableSet (orbitCore A S) := by
  change MeasurableSet {x | ∀ g : Γ, A g x ∈ S}
  simp_rw [ofPred_forall]
  exact MeasurableSet.iInter (fun g => hS.preimage (hA g))

theorem ae_orbitCore [Countable Γ] (A : Γ →* Equiv.Perm X) (μ : Measure X)
    (hA : ∀ g, Measure.QuasiMeasurePreserving (A g) μ μ) {S : Set X}
    (hS : ∀ᵐ x ∂μ, x ∈ S) : ∀ᵐ x ∂μ, x ∈ orbitCore A S := by
  exact ae_all_iff.mpr (fun g => (hA g).ae hS)

theorem invariant_conull_core [Countable Γ] {ι : Type*} [Countable ι]
    (A : Γ →* Equiv.Perm X) (μ : Measure X)
    (hA : ∀ g, Measure.QuasiMeasurePreserving (A g) μ μ)
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hfull : ∀ i, ∀ᵐ x ∂μ, x ∈ S i) :
    ∃ K : Set X, MeasurableSet K ∧ (∀ᵐ x ∂μ, x ∈ K) ∧
      (∀ i, K ⊆ S i) ∧ (∀ g x, A g x ∈ K ↔ x ∈ K) := by
  let T := ⋂ i, S i
  refine ⟨orbitCore A T,orbitCore_measurable A (MeasurableSet.iInter hS)
    (fun g => (hA g).measurable),?_,?_,orbitCore_invariant A T⟩
  · apply ae_orbitCore A μ hA
    simpa only [T,mem_iInter] using ae_all_iff.mpr hfull
  · intro i x hx
    exact Set.mem_iInter.mp (orbitCore_subset A T hx) i

end CannonConformal

end
end
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

def spherePermAction (A : Γ →* (Sphere ≃ₜ Sphere)) : Γ →* Equiv.Perm Sphere where
  toFun g := (A g).toEquiv
  map_one' := by ext p; simp
  map_mul' g h := by ext p; simp

def sphereDerivative (f : Sphere ≃ₜ Sphere) (p : Sphere) : ℂ →L[ℝ] ℂ :=
  fderiv ℝ (inChart false false f) (coordinate p)

def GoodDifferentials (A : Γ →* (Sphere ≃ₜ Sphere)) (H : ℝ) (p : Sphere) : Prop :=
  p ≠ ∞ ∧ ∀ g : Γ, A g p ≠ ∞ ∧
    DifferentiableAt ℝ (inChart false false (A g)) (coordinate p) ∧
    Function.Bijective (sphereDerivative (A g) p) ∧
    ∀ u : ℂ, ‖sphereDerivative (A g) p u‖^2 ≤ H^2* |derivativeDet (sphereDerivative (A g) p)| * ‖u‖^2

theorem controlled_action_derivative_core [Countable Γ]
    (A : Γ →* (Sphere ≃ₜ Sphere)) {η : CannonQM.Distortion}
    (hA : ∀ g, CannonQM.Controlled (A g) η) :
    ∃ K : Set Sphere, MeasurableSet K ∧ (∀ᵐ p ∂sphereMeasure, p ∈ K) ∧
      (∀ g p, A g p ∈ K ↔ p ∈ K) ∧
      ∀ p ∈ K, GoodDifferentials A (1+2*(η 2:ℝ)) p := by
  let P := GoodDifferentials A (1+2*(η 2:ℝ))
  have hp : ∀ᵐ p ∂sphereMeasure, P p := by
    rw [ae_sphere_iff]
    have hall : ∀ᵐ z : ℂ, ∀ g : Γ,
        A g (z:Sphere) ≠ ∞ ∧ DifferentiableAt ℝ (inChart false false (A g)) z ∧
        Function.Bijective (fderiv ℝ (inChart false false (A g)) z) ∧
        ∀ u : ℂ, ‖fderiv ℝ (inChart false false (A g)) z u‖^2 ≤
          (1+2*(η 2:ℝ))^2* |derivativeDet (fderiv ℝ (inChart false false (A g)) z)| * ‖u‖^2 := by
      apply ae_all_iff.mpr
      intro g
      filter_upwards [chartDomain_ae (A g) false false,
        controlled_sphere_ae_differentiable (A g) (hA g),
        controlled_sphere_ae_bijective_fderiv (A g) (hA g),
        controlled_sphere_ae_jacobian_bound (A g) (hA g)] with z hz hd hn hb
      exact ⟨hz,hd,hn,hb⟩
    filter_upwards [hall] with z hz
    exact ⟨OnePoint.coe_ne_infty z,by simpa only [sphereDerivative,coordinate_coe] using hz⟩
  let S : Set Sphere := (toMeasurable sphereMeasure {p | ¬P p})ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSp : ∀ᵐ p ∂sphereMeasure, p ∈ S := by
    rw [ae_iff]
    change sphereMeasure ((toMeasurable sphereMeasure {p | ¬P p})ᶜᶜ)=0
    rw [compl_compl,measure_toMeasurable]
    exact (ae_iff.mp hp)
  have hsub : S ⊆ {p | P p} := by
    intro p hpS
    by_contra hn
    exact hpS (subset_toMeasurable sphereMeasure {p | ¬P p} hn)
  let B := spherePermAction A
  have hBm (g : Γ) : Measure.QuasiMeasurePreserving (B g) sphereMeasure sphereMeasure :=
    controlled_sphere_quasiMeasurePreserving (A g) (hA g)
  refine ⟨CannonConformal.orbitCore B S,
    CannonConformal.orbitCore_measurable B hSm (fun g => (hBm g).measurable),
    CannonConformal.ae_orbitCore B sphereMeasure hBm hSp,?_,?_⟩
  · exact CannonConformal.orbitCore_invariant B S
  · intro p hpK
    exact hsub (CannonConformal.orbitCore_subset B S hpK)

theorem sphereDerivative_mul_on_core (A : Γ →* (Sphere ≃ₜ Sphere))
    {K : Set Sphere} {H : ℝ} (hK : ∀ g p, A g p ∈ K ↔ p ∈ K)
    (hgood : ∀ p ∈ K, GoodDifferentials A H p) {p : Sphere} (hp : p ∈ K) (g h : Γ) :
    sphereDerivative (A (g*h)) p =
      (sphereDerivative (A g) (A h p)).comp (sphereDerivative (A h) p) := by
  have hp0 := (hgood p hp).1
  have hh := (hgood p hp).2 h
  have hg := (hgood (A h p) ((hK h p).mpr hp)).2 g
  have hd : coordinate p ∈ chartDomain false false (A h) := by
    change A h (coordinate p:Sphere) ≠ ∞
    rw [coe_coordinate hp0]
    exact hh.1
  have he : inChart false false (A h) (coordinate p)=coordinate (A h p) := by
    change coordinate (A h (coordinate p:Sphere))=coordinate (A h p)
    rw [coe_coordinate hp0]
  have hgd : DifferentiableAt ℝ (inChart false false (A g)) (inChart false false (A h) (coordinate p)) := by
    rw [he]
    exact hg.2.1
  have hc := (hgd.hasFDerivAt.comp (coordinate p) hh.2.1.hasFDerivAt).congr_of_eventuallyEq
    (chart_mul_eventually (A g) (A h) hd)
  have hder := hc.fderiv
  rw [he,← map_mul] at hder
  exact hder

end CannonMobius

end
end
end
end
end
end
end
end

end OAI
