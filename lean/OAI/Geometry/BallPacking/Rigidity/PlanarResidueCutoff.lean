import Mathlib
import OAI.Geometry.BallPacking.Rigidity.RadialForm

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

def cutoffWedge (f : Plane → ℝ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) : ℝ :=
  fderiv ℝ f z (1,0)*β z (0,1)-fderiv ℝ f z (0,1)*β z (1,0)

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by simp) z) (hβ.differentiable (by simp) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by simp)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

theorem integral_planar_residue_cutoff {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (h0 : g 0=1)
    (hβ : ContDiff ℝ ∞ β) (c : ℝ) :
    (∫ z : Plane,-cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z))=
      (∫ z : Plane,g (radiusSq z)*planarCurl β z)-c*Real.pi := by
  have hgs : ContDiff ℝ ∞ (fun z : Plane => g (radiusSq z)) := hg.comp radiusSq_smooth
  have hgc := HasCompactSupport.comp_radiusSq hc
  have hdi : Integrable (fun z : Plane => deriv g (radiusSq z)) := ((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.comp_radiusSq hc.deriv)
  have hni : Integrable (fun z : Plane => -cutoffWedge (fun y => g (radiusSq y)) β z) :=
    (cutoffWedge_integrable hgs hgc hβ).neg
  rw [integral_add hni (hdi.const_mul c),integral_neg,
    integral_cutoffWedge hgs hgc hβ,neg_neg,integral_const_mul]
  have hi := integral_radial_derivative hg hc
  rw [integral_const_mul,h0,mul_one] at hi
  have hid : (∫ z : Plane,deriv g (radiusSq z))= -Real.pi := by linarith
  rw [hid]
  ring

theorem cutoffWedge_radial_angular {g : ℝ → ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (hz : radiusSq z≠0) :
    cutoffWedge (fun y => g (radiusSq y)) angularOneForm z=2*deriv g (radiusSq z) := by
  have hd := (hg.hasDerivAt.comp_hasFDerivAt z (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  unfold cutoffWedge
  rw [hd]
  simp only [smul_apply,smul_eq_mul,planarDot_apply,angularOneForm,
    planarArea_apply]
  unfold radiusSq at hz ⊢
  field_simp
  ring

theorem planar_residue_defect {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (hβ : DifferentiableAt ℝ β z)
    (hz : radiusSq z≠0) (c : ℝ) :
    planarCurl (fun y => (1-g (radiusSq y)) • (β y-(c/2) • angularOneForm y)) z-
      (1-g (radiusSq z))*planarCurl (fun y => β y-(c/2) • angularOneForm y) z=
      -cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z) := by
  have hgs := hg.comp z (radiusSq_hasFDerivAt z).differentiableAt
  have hrs := (differentiableAt_const (c := (1:ℝ))).sub hgs
  have hbs := hβ.sub ((angularOneForm_contDiffAt hz).differentiableAt (by simp) |>.const_smul (c/2))
  change DifferentiableAt ℝ (fun y => 1-g (radiusSq y)) z at hrs
  change DifferentiableAt ℝ (fun y => β y-(c/2) • angularOneForm y) z at hbs
  change DifferentiableAt ℝ (fun y => g (radiusSq y)) z at hgs
  rw [planarCurl_spatial_smul hrs hbs,add_sub_cancel_right]
  have hd := (hasFDerivAt_const (1:ℝ) z).sub hgs.hasFDerivAt
  change HasFDerivAt (fun y => 1-g (radiusSq y)) _ z at hd
  have he : cutoffWedge (fun y => 1-g (radiusSq y)) (fun y => β y-(c/2) • angularOneForm y) z=
      -cutoffWedge (fun y => g (radiusSq y)) β z+(c/2)*cutoffWedge (fun y => g (radiusSq y)) angularOneForm z := by
    unfold cutoffWedge
    rw [hd.fderiv]
    simp only [sub_apply,zero_apply,smul_apply,smul_eq_mul]
    ring
  rw [he,cutoffWedge_radial_angular hg hz]
  ring

def radialAnnulus (r R : ℝ) : Set Plane := {z | r≤radiusSq z ∧ radiusSq z≤R}

theorem radialAnnulus_compact (r R : ℝ) : IsCompact (radialAnnulus r R) := by
  have hc : IsClosed (radialAnnulus r R) :=
    (isClosed_le continuous_const radiusSq_smooth.continuous).inter
      (isClosed_le radiusSq_smooth.continuous continuous_const)
  apply ((isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1))).prod
    (isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1)))).of_isClosed_subset hc
  intro z hz
  have hb : z.1^2+z.2^2≤|R| := hz.2.trans (le_abs_self R)
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2,abs_nonneg R]

theorem radialAnnulus_ne_zero {r R : ℝ} (hr : 0<r) {z : Plane}
    (hz : z∈radialAnnulus r R) : z≠0 := by
  intro h
  subst z
  have : r≤0 := by simpa [radiusSq] using hz.1
  linarith

theorem radialAnnulus_radius_ne_zero {r R : ℝ} (hr : 0<r) {z : Plane}
    (hz : z∈radialAnnulus r R) : radiusSq z≠0 := ne_of_gt (lt_of_lt_of_le hr hz.1)

theorem radiusSq_complex (z : Plane) : Complex.normSq (Complex.equivRealProdCLM.symm z)=radiusSq z := by
  change z.1*z.1+z.2*z.2=z.1^2+z.2^2
  ring

 theorem radialAnnulus_coordinate_bound {r R : ℝ} (hR : 0≤R) {z : Plane}
    (hz : z∈radialAnnulus r R) : |z.1|≤Real.sqrt R ∧ |z.2|≤Real.sqrt R := by
  have hs := Real.sq_sqrt hR
  have hp := Real.sqrt_nonneg R
  have hb := hz.2
  change z.1^2+z.2^2≤R at hb
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg z.1,sq_nonneg z.2]

 theorem radialAnnulus_real_volume_le {r R : ℝ} (hR : 0≤R) :
    volume.real (radialAnnulus r R)≤4*R := by
  have hsub : radialAnnulus r R⊆Icc (-Real.sqrt R) (Real.sqrt R) ×ˢ
      Icc (-Real.sqrt R) (Real.sqrt R) := by
    intro z hz
    have he := radialAnnulus_coordinate_bound hR hz
    exact ⟨abs_le.mp he.1,abs_le.mp he.2⟩
  have hv : volume (Icc (-Real.sqrt R) (Real.sqrt R) ×ˢ
      Icc (-Real.sqrt R) (Real.sqrt R) : Set Plane)=ENNReal.ofReal (4*R) := by
    change (volume.prod volume) _=_
    rw [Measure.prod_prod,Real.volume_Icc,←ENNReal.ofReal_mul (by linarith [Real.sqrt_nonneg R])]
    congr 1
    nlinarith [Real.sq_sqrt hR]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans_eq hv)
  simpa only [Measure.real,ENNReal.toReal_ofReal (by positivity : 0≤4*R)] using hb

 theorem cutoffWedge_radial_apply {g : ℝ → ℝ} {z : Plane}
    (hg : DifferentiableAt ℝ g (radiusSq z)) (β : Plane → Plane →L[ℝ] ℝ) :
    cutoffWedge (fun y => g (radiusSq y)) β z=
      2*deriv g (radiusSq z)*(z.1*β z (0,1)-z.2*β z (1,0)) := by
  have hd := (hg.hasDerivAt.comp_hasFDerivAt z (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  unfold cutoffWedge
  rw [hd]
  simp only [smul_apply,smul_eq_mul,planarDot_apply,mul_one,mul_zero,add_zero,zero_add]
  ring

 theorem cutoffWedge_radial_bound {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane} {r R K M : ℝ} (hg : DifferentiableAt ℝ g (radiusSq z))
    (hR : 0≤R) (hK : 0≤K) (_hM : 0≤M) (hz : z∈radialAnnulus r R)
    (hd : |deriv g (radiusSq z)|≤K) (hβ : ‖β z‖≤M) :
    |cutoffWedge (fun y => g (radiusSq y)) β z|≤4*K*Real.sqrt R*M := by
  have hb0 : |β z (1,0)|≤M := by
    have h := (β z).le_opNorm ((1:ℝ),(0:ℝ))
    simpa only [Real.norm_eq_abs,Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,mul_one] using h.trans
      (by simpa using hβ)
  have hb1 : |β z (0,1)|≤M := by
    have h := (β z).le_opNorm ((0:ℝ),(1:ℝ))
    simpa only [Real.norm_eq_abs,Prod.norm_def,norm_one,norm_zero,max_eq_right zero_le_one,mul_one] using h.trans
      (by simpa using hβ)
  have hz' := radialAnnulus_coordinate_bound hR hz
  have hx : |z.1*β z (0,1)|≤Real.sqrt R*M := by
    rw [abs_mul]
    exact mul_le_mul hz'.1 hb1 (abs_nonneg _) (Real.sqrt_nonneg _)
  have hy : |z.2*β z (1,0)|≤Real.sqrt R*M := by
    rw [abs_mul]
    exact mul_le_mul hz'.2 hb0 (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [cutoffWedge_radial_apply hg,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hd' := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤2)
  calc
    _≤(2*K)*(2*Real.sqrt R*M) :=
      mul_le_mul hd' ((abs_sub _ _).trans (by linarith)) (abs_nonneg _)
        (by positivity)
    _=_ := by ring

 theorem bounded_residue_error_integral {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M e c : ℝ}
    (hg : ∀ z∈radialAnnulus r R,DifferentiableAt ℝ g (radiusSq z))
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : 0≤e)
    (hd : ∀ z∈radialAnnulus r R,|deriv g (radiusSq z)|≤K)
    (hβ : ∀ z∈radialAnnulus r R,‖β z‖≤M)
    (hc : ∀ z∈radialAnnulus r R,|d z-c|≤e) :
    |∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
      (d z-c)*deriv g (radiusSq z)|≤(4*K*Real.sqrt R*M+e*K)*(4*R) := by
  have hbound (z : Plane) (hz : z∈radialAnnulus r R) :
      ‖cutoffWedge (fun y => g (radiusSq y)) β z-(d z-c)*deriv g (radiusSq z)‖≤
        4*K*Real.sqrt R*M+e*K := by
    rw [Real.norm_eq_abs]
    apply (abs_sub _ _).trans
    apply add_le_add (cutoffWedge_radial_bound (hg z hz) hR hK hM hz (hd z hz) (hβ z hz))
    rw [abs_mul]
    exact mul_le_mul (hc z hz) (hd z hz) (abs_nonneg _) he
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (radialAnnulus_compact r R).measure_lt_top hbound
  exact (show |∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
    (d z-c)*deriv g (radiusSq z)|≤_ from hi).trans
      (mul_le_mul_of_nonneg_left (radialAnnulus_real_volume_le hR) (by positivity))

theorem radialCutoff_deriv_zero_off_annulus {g : ℝ → ℝ} {r R : ℝ}
    (hr : 0<r) (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {z : Plane} (hz : z∉radialAnnulus r R) : deriv g (radiusSq z)=0 := by
  change ¬(r≤radiusSq z ∧ radiusSq z≤R) at hz
  rcases not_and_or.mp hz with hl|hh
  · have he : g=ᶠ[𝓝 (radiusSq z)] fun _ => 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show radiusSq z∈Ioo (-r) r from ⟨lt_of_lt_of_le (neg_neg_of_pos hr) (radiusSq_nonneg z),lt_of_not_ge hl⟩)] with t ht
      exact h1 t ht
    rw [he.deriv_eq,deriv_const]
  · have he : g=ᶠ[𝓝 (radiusSq z)] fun _ => 0 := by
      filter_upwards [isOpen_Ioi.mem_nhds (show R<radiusSq z from lt_of_not_ge hh)] with t ht
      exact image_eq_zero_of_notMem_tsupport (fun hs => not_le_of_gt (show R<t from ht) (show t≤R from h0 hs))
    rw [he.deriv_eq,deriv_const]

theorem planarResidueDensity_zero_off {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (β : Plane → Plane →L[ℝ] ℝ) (c : ℝ) {z : Plane} (hz : z∉radialAnnulus r R) :
    -cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z)=0 := by
  have hd := ((hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun y => g (radiusSq y)) z=_ at hd
  rw [radialCutoff_deriv_zero_off_annulus hr h1 h0 hz,zero_smul] at hd
  simp only [cutoffWedge,hd,zero_apply,zero_mul,sub_zero,neg_zero,
    radialCutoff_deriv_zero_off_annulus hr h1 h0 hz,mul_zero,add_zero]

theorem integral_planar_residue_annulus {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (c : ℝ) :
    (∫ z in radialAnnulus r R,-cutoffWedge (fun y => g (radiusSq y)) β z+c*deriv g (radiusSq z))=
      (∫ z : Plane,g (radiusSq z)*planarCurl β z)-c*Real.pi := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => planarResidueDensity_zero_off hg hr h1 h0 β c hz)]
  exact integral_planar_residue_cutoff hg hc (h1 0 ⟨neg_neg_of_pos hr,hr⟩) hβ c

def shrinkingCutoff (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ := g (((n:ℝ)+1)*t)

theorem shrinkingCutoff_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (shrinkingCutoff g n) := hg.comp (contDiff_const.mul contDiff_id)

theorem shrinkingCutoff_compact {g : ℝ → ℝ} (hg : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (shrinkingCutoff g n) := by
  have hh := hg.comp_homeomorph (Homeomorph.smulOfNeZero (α := ℝ) ((n:ℝ)+1) (by positivity))
  change HasCompactSupport (fun t : ℝ => g (((n:ℝ)+1)*t))
  simpa only [Function.comp_def,Homeomorph.smulOfNeZero_apply,smul_eq_mul] using hh

theorem shrinkingCutoff_one {g : ℝ → ℝ} {r : ℝ}
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (n : ℕ) :
    ∀ t∈Ioo (-(r/((n:ℝ)+1))) (r/((n:ℝ)+1)),shrinkingCutoff g n t=1 := by
  intro t ht
  apply h1
  have hn : 0<(n:ℝ)+1 := by positivity
  constructor
  · have hh : (-r)/((n:ℝ)+1)<t := by simpa only [neg_div] using ht.1
    have h := (div_lt_iff₀ hn).mp hh
    linarith
  · have h := (lt_div_iff₀ hn).mp ht.2
    nlinarith

theorem shrinkingCutoff_tsupport {g : ℝ → ℝ} {R : ℝ}
    (hR : 0≤R) (h0 : tsupport g⊆Iic R) (n : ℕ) :
    tsupport (shrinkingCutoff g n)⊆Iic R := by
  apply closure_minimal _ isClosed_Iic
  intro t ht
  by_contra hn
  have htR : R<t := lt_of_not_ge hn
  have hnt : R<((n:ℝ)+1)*t := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  change g (((n:ℝ)+1)*t)≠0 at ht
  exact ht (image_eq_zero_of_notMem_tsupport (f := g) (fun hx => not_le_of_gt hnt (h0 hx)))

theorem shrinkingCutoff_eventually_zero {g : ℝ → ℝ} (hc : HasCompactSupport g)
    {t : ℝ} (ht : 0<t) : ∀ᶠ n in atTop,shrinkingCutoff g n t=0 := by
  obtain ⟨B,_hB,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hz : ∀ᶠ s : ℝ in atTop,g s=0 := by
    filter_upwards [eventually_gt_atTop B] with s hs
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hb := hbound s h
    have hsn := le_abs_self s
    rw [Real.norm_eq_abs] at hb
    linarith
  have hseq : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const ht
  exact hseq.eventually hz

theorem radiusSq_pos {z : Plane} (hz : z≠0) : 0<radiusSq z := by
  have hn := radiusSq_nonneg z
  by_contra hh
  have he : radiusSq z=0 := le_antisymm (le_of_not_gt hh) hn
  apply hz
  apply Prod.ext <;> change _=0 <;> dsimp only [radiusSq] at he <;>
    nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem tendsto_shrinking_regular_residue {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hbound : ∀ t,g t∈Icc (0:ℝ) 1)
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β) :
    Tendsto (fun n => ∫ z : Plane,shrinkingCutoff g n (radiusSq z)*planarCurl β z)
      atTop (𝓝 0) := by
  have hi : Integrable (planarCurl β) := (planarCurl_contDiff hβ).continuous.integrable_of_hasCompactSupport (planarCurl_compact hβc)
  have h := tendsto_integral_of_dominated_convergence (fun z => ‖planarCurl β z‖)
    (f := fun _ : Plane => (0:ℝ))
    (fun n => (((shrinkingCutoff_smooth hg n).comp radiusSq_smooth).mul
      (planarCurl_contDiff hβ)).continuous.aestronglyMeasurable) hi.norm
    (fun n => Filter.Eventually.of_forall (fun z => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [Real.norm_eq_abs]
        change |g (((n:ℝ)+1)*radiusSq z)|≤1
        rw [abs_of_nonneg (hbound _).1]
        exact (hbound _).2))) (by
      have hne : ∀ᵐ z : Plane,z≠0 := by
        apply ae_iff.mpr
        simp
      filter_upwards [hne] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [shrinkingCutoff_eventually_zero hc (radiusSq_pos hz)] with n hn
      change 0=shrinkingCutoff g n (radiusSq z)*planarCurl β z
      rw [hn,zero_mul])
  simpa only [integral_zero,Function.comp_apply] using h

 theorem integral_annular_radial_derivative {g : ℝ → ℝ} {r R : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
    (∫ z in radialAnnulus r R,c*deriv g (radiusSq z))= -c*Real.pi := by
  have h := integral_planar_residue_annulus hg hc hr h1 h0
    (β := fun _ : Plane => (0 : Plane →L[ℝ] ℝ)) contDiff_const c
  simpa [cutoffWedge,planarCurl] using h

 theorem continuousOn_cutoffWedge_radial {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {U : Set Plane} (hg : ContDiff ℝ ∞ g) (hβ : ContinuousOn β U) :
    ContinuousOn (cutoffWedge (fun y => g (radiusSq y)) β) U := by
  have hs : ContDiff ℝ ∞ (fun y => g (radiusSq y)) := hg.comp radiusSq_smooth
  unfold cutoffWedge
  exact (((hs.fderiv_right (m := ∞) (by simp)).continuous.continuousOn.clm_apply continuousOn_const).mul
    (hβ.clm_apply continuousOn_const)).sub
    (((hs.fderiv_right (m := ∞) (by simp)).continuous.continuousOn.clm_apply continuousOn_const).mul
    (hβ.clm_apply continuousOn_const))

 theorem variable_flux_error_bound {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M e c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hβc : ContinuousOn β (radialAnnulus r R)) (hdc : ContinuousOn d (radialAnnulus r R))
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : 0≤e)
    (hd : ∀ z∈radialAnnulus r R,|deriv g (radiusSq z)|≤K)
    (hβ : ∀ z∈radialAnnulus r R,‖β z‖≤M)
    (hc : ∀ z∈radialAnnulus r R,|d z-c|≤e) :
    |(∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
      d z*deriv g (radiusSq z))-c*Real.pi|≤(4*K*Real.sqrt R*M+e*K)*(4*R) := by
  have hder : ContinuousOn (fun z => deriv g (radiusSq z)) (radialAnnulus r R) :=
    ((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).continuousOn
  have hi1 : IntegrableOn (fun z => cutoffWedge (fun y => g (radiusSq y)) β z-
      d z*deriv g (radiusSq z)) (radialAnnulus r R) volume :=
    ((continuousOn_cutoffWedge_radial hg hβc).sub (hdc.mul hder)).integrableOn_compact
    (radialAnnulus_compact r R)
  have hi2 : IntegrableOn (fun z => c*deriv g (radiusSq z)) (radialAnnulus r R) volume :=
    (continuousOn_const.mul hder).integrableOn_compact (radialAnnulus_compact r R)
  have heq : (∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
      (d z-c)*deriv g (radiusSq z))=
      (∫ z in radialAnnulus r R,cutoffWedge (fun y => g (radiusSq y)) β z-
        d z*deriv g (radiusSq z))-c*Real.pi := by
    have hf : (fun z => cutoffWedge (fun y => g (radiusSq y)) β z-(d z-c)*deriv g (radiusSq z))=
      fun z => (cutoffWedge (fun y => g (radiusSq y)) β z-d z*deriv g (radiusSq z))+
        c*deriv g (radiusSq z) := by funext z; ring
    rw [hf,integral_add hi1 hi2,integral_annular_radial_derivative hg hgc hr h1 h0]
    ring
  rw [←heq]
  exact bounded_residue_error_integral (fun z _ => hg.differentiable (by simp) _) hR hK hM he hd hβ hc

 theorem shrinkingCutoff_tsupport_scaled {g : ℝ → ℝ} {R : ℝ}
    (h0 : tsupport g⊆Iic R) (n : ℕ) :
    tsupport (shrinkingCutoff g n)⊆Iic (R/((n:ℝ)+1)) := by
  apply closure_minimal _ isClosed_Iic
  intro t ht
  by_contra hn
  have htR : R<((n:ℝ)+1)*t := by
    have h := (div_lt_iff₀ (by positivity : 0<(n:ℝ)+1)).mp (lt_of_not_ge hn)
    linarith
  change g (((n:ℝ)+1)*t)≠0 at ht
  exact ht (image_eq_zero_of_notMem_tsupport (f := g) (fun hx => not_le_of_gt htR (h0 hx)))

 theorem shrinkingCutoff_deriv {g : ℝ → ℝ} (hg : Differentiable ℝ g) (n : ℕ) (t : ℝ) :
    deriv (shrinkingCutoff g n) t=((n:ℝ)+1)*deriv g (((n:ℝ)+1)*t) := by
  have h := (hg _).hasDerivAt.comp t ((hasDerivAt_id t).const_mul ((n:ℝ)+1))
  change deriv (fun y => g (((n:ℝ)+1)*y)) t=_
  simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using h.deriv

 theorem shrinking_variable_flux_error {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M e c : ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : 0≤e)
    (hd : ∀ t : ℝ,|deriv g t|≤K) (n : ℕ)
    (hβc : ContinuousOn β (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hdc : ContinuousOn d (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hβ : ∀ z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),‖β z‖≤M)
    (hc : ∀ z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),|d z-c|≤e) :
    |(∫ z in radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),
      cutoffWedge (fun y => shrinkingCutoff g n (radiusSq y)) β z-
        d z*deriv (shrinkingCutoff g n) (radiusSq z))-c*Real.pi|≤
      16*K*R*M*Real.sqrt (R/((n:ℝ)+1))+4*e*K*R := by
  have hn : 0<(n:ℝ)+1 := by positivity
  have hb := variable_flux_error_bound (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n)
    (div_pos hr hn) (shrinkingCutoff_one h1 n) (shrinkingCutoff_tsupport_scaled h0 n)
    hβc hdc (div_nonneg hR hn.le) (mul_nonneg hn.le hK) hM he
    (K := ((n:ℝ)+1)*K)
    (fun z _ => by
      rw [shrinkingCutoff_deriv (hg.differentiable (by simp)),abs_mul,abs_of_pos hn]
      exact mul_le_mul_of_nonneg_left (hd _) hn.le) hβ hc
  convert hb using 1
  field_simp [hn.ne']
  ring

 theorem tendsto_shrinking_variable_flux {g : ℝ → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {d : Plane → ℝ} {r R K M c : ℝ} {e : ℕ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hr : 0<r)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hR : 0≤R) (hK : 0≤K) (hM : 0≤M) (he : ∀ n,0≤e n)
    (het : Tendsto e atTop (𝓝 0)) (hd : ∀ t : ℝ,|deriv g t|≤K)
    (hβc : ∀ n : ℕ,ContinuousOn β (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hdc : ∀ n : ℕ,ContinuousOn d (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hβ : ∀ (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → ‖β z‖≤M)
    (hc : ∀ (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → |d z-c|≤e n) :
    Tendsto (fun n : ℕ => ∫ z in radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)),
      cutoffWedge (fun y => shrinkingCutoff g n (radiusSq y)) β z-
        d z*deriv (shrinkingCutoff g n) (radiusSq z)) atTop (𝓝 (c*Real.pi)) := by
  have hRt : Tendsto (fun n : ℕ => R/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using
      (tendsto_const_nhds (x := R)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n : ℕ => 16*K*R*M*Real.sqrt (R/((n:ℝ)+1))+4*e n*K*R)
      atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := 16*K*R*M)).mul hRt.sqrt).add
      (((tendsto_const_nhds (x := (4:ℝ))).mul het).mul_const K |>.mul_const R)
    simpa only [Real.sqrt_zero,mul_zero,zero_mul,add_zero] using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [Real.norm_eq_abs]
  exact shrinking_variable_flux_error hg hgc hr h1 h0 hR hK hM (he n) hd n
    (hβc n) (hdc n) (hβ n) (hc n)

end SymplecticBallPacking.Hamiltonian
end

end OAI
