import Mathlib
import OAI.Geometry.BallPacking.Rigidity.CorrectedInfinity
import OAI.Geometry.BallPacking.Holder.MarkedFrame

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open SymplecticBallPacking.Hamiltonian (Plane)
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

lemma analyticAt_dslope_zero {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (dslope h 0) 0 := by
  obtain ⟨P,hP⟩ := hh
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩

lemma infinityGerm_affine_reconstruction (u : ℂ → Phase n) (a : Phase n) {z : ℂ} (hz : z≠0) :
    u z=z • a+dslope (infinityGerm u a) 0 z⁻¹ := by
  rw [dslope_of_ne _ (inv_ne_zero hz),slope,sub_zero]
  simp only [infinityGerm,inv_ne_zero hz,ite_false,inv_inv,ite_true,vsub_eq_sub]
  rw [smul_sub,smul_smul,mul_inv_cancel₀ hz,one_smul]
  abel

lemma analytic_inverse_angular_fderiv_limit {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0) :
    Tendsto (fun z : ℂ => fderiv ℝ (fun w : ℂ => h w⁻¹) z (Complex.I*z))
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hc : ContDiffAt ℝ ∞ h 0 := hh.contDiffAt.restrict_scalars ℝ
  have hdh : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹) (cocompact ℂ) (𝓝 (fderiv ℝ h 0)) :=
    (hc.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  apply hvec.congr'
  filter_upwards [hi.eventually hd,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
  have hid := (hasDerivAt_inv hz0).hasFDerivAt.restrictScalars ℝ
  have hder := hz.hasFDerivAt.comp z hid
  change HasFDerivAt (fun w : ℂ => h w⁻¹) _ z at hder
  rw [hder.fderiv]
  change fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)=
    fderiv ℝ h z⁻¹ ((Complex.I*z) • (-(z^2)⁻¹))
  rw [smul_eq_mul]
  congr 1
  field_simp

theorem AffineLineCurve.affine_correction_at_infinity {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ (a : Phase n) (h : ℂ → Phase n), a≠0 ∧ AnalyticAt ℂ h 0 ∧
      (∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) := by
  obtain ⟨a,ha,hh,_⟩ := hu.analytic_at_infinity hJc
  exact ⟨a,dslope (infinityGerm u a) 0,ha,analyticAt_dslope_zero hh,
    fun _ hz => infinityGerm_affine_reconstruction u a hz⟩

def affineCorrection (u : ℂ → Phase n) (a : Phase n) (z : ℂ) : Phase n := u z-z • a

lemma affineCorrection_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    ContDiff ℝ ∞ (affineCorrection u a) := hu.sub (contDiff_id.smul contDiff_const)

lemma affineCorrection_locally_inverse {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) {z : ℂ} (hz : z≠0) :
    affineCorrection u a =ᶠ[𝓝 z] fun w : ℂ => h w⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
  rw [affineCorrection,he w hw]
  abel

lemma affineCorrection_limit {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (affineCorrection u a) (cocompact ℂ) (𝓝 (h 0)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  apply (hh.continuousAt.tendsto.comp hi).congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  exact ((affineCorrection_locally_inverse he hz).self_of_nhds).symm

lemma affineCorrection_angular_fderiv_limit {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : ℂ => fderiv ℝ (affineCorrection u a) z (Complex.I*z))
      (cocompact ℂ) (𝓝 0) := by
  apply (analytic_inverse_angular_fderiv_limit hh).congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  rw [(affineCorrection_locally_inverse he hz).fderiv_eq]

lemma affineCorrection_primitive_flux_zero {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : ℂ => stdOmega n (affineCorrection u a z)
      (fderiv ℝ (affineCorrection u a) z (Complex.I*z))) (cocompact ℂ) (𝓝 0) := by
  have hv := affineCorrection_limit hh he
  have hd := affineCorrection_angular_fderiv_limit hh he
  have ho : Tendsto (fun z => stdOmega n (affineCorrection u a z))
      (cocompact ℂ) (𝓝 (stdOmega n (h 0))) := (stdOmega n).continuous.continuousAt.tendsto.comp hv
  simpa only [Function.comp_def,map_zero] using
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (ho.prodMk_nhds hd)

end HigherDimensionalBallPacking.Rigidity

end
noncomputable section
open scoped ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}
local instance ceInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ceInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def defectEnergy (A : End n) (v : Phase n) : ℝ :=
  stdDot n ((A-standardJ n) v) ((A-standardJ n) v)

def symplecticEnergy (A : End n) (v : Phase n) : ℝ := stdOmega n v (A v)

lemma defectEnergy_nonneg (A : End n) (v : Phase n) : 0≤defectEnergy A v := stdDot_nonneg _

lemma defectEnergy_standard (v : Phase n) : defectEnergy (standardJ n) v=0 := by
  simp only [defectEnergy,sub_self,zero_apply,map_zero]

lemma defectEnergy_smul (A : End n) (r : ℝ) (v : Phase n) :
    defectEnergy A (r • v)=r^2*defectEnergy A v := by
  simp only [defectEnergy,map_smul,smul_apply,smul_eq_mul]
  ring

lemma symplecticEnergy_smul (A : End n) (r : ℝ) (v : Phase n) :
    symplecticEnergy A (r • v)=r^2*symplecticEnergy A v := by
  simp only [symplecticEnergy,map_smul,smul_apply,smul_eq_mul]
  ring

lemma symplecticEnergy_pos {A : End n} (hA : Compatible A) {v : Phase n} (hv : v≠0) :
    0<symplecticEnergy A v := by
  rw [symplecticEnergy,stdOmega_apply]
  exact hA.2.2 v hv

lemma defectEnergy_continuous : Continuous (fun z : End n × Phase n => defectEnergy z.1 z.2) := by
  have h : Continuous (fun z : End n × Phase n => (z.1-standardJ n) z.2) :=
    (continuous_fst.sub continuous_const).clm_apply continuous_snd
  exact (((stdDot n).continuous.comp h).clm_apply h)

lemma symplecticEnergy_continuous : Continuous (fun z : End n × Phase n => symplecticEnergy z.1 z.2) := by
  exact ((stdOmega n).continuous.comp continuous_snd).clm_apply (continuous_fst.clm_apply continuous_snd)

lemma energyRatio_continuousOn {X : Type*} [TopologicalSpace X]
    {K : Set X} {A : X → End n} (hAc : ContinuousOn A K)
    (hA : ∀ x∈K, Compatible (A x)) :
    ContinuousOn (fun z : X × Phase n => defectEnergy (A z.1) z.2 / symplecticEnergy (A z.1) z.2)
      (K ×ˢ Metric.sphere (0:Phase n) 1) := by
  have hpair : ContinuousOn (fun z : X × Phase n => (A z.1,z.2))
      (K ×ˢ Metric.sphere (0:Phase n) 1) :=
    (hAc.comp continuous_fst.continuousOn (fun _ h => h.1)).prodMk continuous_snd.continuousOn
  apply (defectEnergy_continuous.comp_continuousOn hpair).div
    (symplecticEnergy_continuous.comp_continuousOn hpair)
  intro z hz
  apply (symplecticEnergy_pos (hA z.1 hz.1) ?_).ne'
  have hn : ‖z.2‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz.2
  exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)

lemma energyRatio_bounded_on_sphere {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A : X → End n} (hAc : ContinuousOn A K)
    (hA : ∀ x∈K, Compatible (A x)) :
    ∃ B : ℝ, 0<B ∧ ∀ x∈K, ∀ v : Phase n, ‖v‖=1 →
      defectEnergy (A x) v≤B*symplecticEnergy (A x) v := by
  let f (z : X × Phase n) : ℝ := defectEnergy (A z.1) z.2 / symplecticEnergy (A z.1) z.2
  have hf : ContinuousOn f (K ×ˢ Metric.sphere (0:Phase n) 1) := energyRatio_continuousOn hAc hA
  have hL : IsCompact (K ×ˢ Metric.sphere (0:Phase n) 1) := hK.prod (isCompact_sphere _ _)
  obtain ⟨B,hB,hbound⟩ := (hL.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  refine ⟨B,hB,?_⟩
  intro x hx v hv
  have hwL : (x,v)∈K ×ˢ Metric.sphere (0:Phase n) 1 :=
    ⟨hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hv⟩
  have hnorm := hbound (f (x,v)) ⟨(x,v),hwL,rfl⟩
  have hb : f (x,v)≤B := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)
  have hv0 : v≠0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  exact (div_le_iff₀ (symplecticEnergy_pos (hA x hx) hv0)).mp hb

lemma energyRatio_extend_from_sphere {A : End n} {B : ℝ}
    (hB : ∀ w : Phase n, ‖w‖=1 → defectEnergy A w≤B*symplecticEnergy A w)
    (v : Phase n) : defectEnergy A v≤B*symplecticEnergy A v := by
  by_cases hv : v=0
  · subst v
    simp [defectEnergy,symplecticEnergy]
  let w : Phase n := ‖v‖⁻¹ • v
  have hnv : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hw : ‖w‖=1 := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hnv]
  have hratio := hB w hw
  rw [show w=‖v‖⁻¹ • v from rfl,defectEnergy_smul,symplecticEnergy_smul] at hratio
  have hp : 0<(‖v‖⁻¹)^2 := sq_pos_of_ne_zero (inv_ne_zero hnv)
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    (‖v‖⁻¹)^2*defectEnergy A v ≤ B*((‖v‖⁻¹)^2*symplecticEnergy A v) := hratio
    _ = (‖v‖⁻¹)^2*(B*symplecticEnergy A v) := by ring

lemma exists_defectEnergy_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A : X → End n} (hAc : ContinuousOn A K)
    (hA : ∀ x∈K, Compatible (A x)) :
    ∃ C : ℝ, 0<C ∧ ∀ x∈K, ∀ v : Phase n,
      defectEnergy (A x) v≤C*symplecticEnergy (A x) v := by
  obtain ⟨B,hB,hbound⟩ := energyRatio_bounded_on_sphere hK hAc hA
  exact ⟨B,hB,fun x hx v => energyRatio_extend_from_sphere (hbound x hx) v⟩

end HigherDimensionalBallPacking.Rigidity

end
noncomputable section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

lemma outerProfile_one_before {A t : ℝ} (ht : 0≤t) (htA : t≤A) (hA : 0<A) :
    outerProfile A t=1 := by
  have h1 : 1≤t+2 := by linarith
  have h2 : (t-A)/A≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htA) hA.le
  simp only [outerProfile,Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2,sub_zero,mul_one]

lemma radiusSq_pos_bound_of_compact {K : Set Plane} (hK : IsCompact K) :
    ∃ A : ℝ, 0<A ∧ ∀ z∈K, radiusSq z<A := by
  obtain ⟨B,hB,hb⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  refine ⟨B+1,by linarith,?_⟩
  intro z hz
  have hh := hb (radiusSq z) ⟨z,hz,rfl⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (radiusSq_nonneg z)] at hh
  linarith

lemma integral_compact_le_infinity_flux {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcurl : ∀ z, 0≤planarCurl β z) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k))
    {e : Plane → ℝ} (he : Continuous e) (hc : HasCompactSupport e)
    (hle : ∀ z, e z≤planarCurl β z) : (∫ z, e z)≤2*Real.pi*k := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hp : 0<2*Real.pi := by positivity
  have heps : k<k+ε/(2*Real.pi) := lt_add_of_pos_right _ (div_pos hε hp)
  have hev : ∀ᶠ z in cocompact Plane, β z (planeRotation z)≤k+ε/(2*Real.pi) :=
    (hlim.eventually (eventually_lt_nhds heps)).mono fun _ h => h.le
  obtain ⟨K,hK,hKb⟩ := mem_cocompact.mp hev
  obtain ⟨A,hA,hbound⟩ := radiusSq_pos_bound_of_compact (hK.union hc)
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hdom (z : Plane) : e z≤g (radiusSq z)*planarCurl β z := by
    by_cases hz : z∈tsupport e
    · have hga : g (radiusSq z)=1 :=
        outerProfile_one_before (radiusSq_nonneg z) (hbound z (Or.inr hz)).le hA
      rw [hga,one_mul]
      exact hle z
    · rw [image_eq_zero_of_notMem_tsupport hz]
      exact mul_nonneg (outerProfile_nonneg A _) (hcurl z)
  have hcomp (z : Plane) :
      2*deriv g (radiusSq z)*(k+ε/(2*Real.pi))≤
        cutoffWedge (fun y => g (radiusSq y)) β z := by
    rw [cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z)=0
    · simp only [hd,mul_zero,zero_mul,le_refl]
    have hzA : A≤radiusSq z := by
      by_contra! h
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) h)
    have hzK : z∉K := by
      intro hz
      exact (not_lt_of_ge hzA) (hbound z (Or.inl hz))
    exact mul_le_mul_of_nonpos_left (hKb hzK)
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z)))
  have hdi : Integrable (fun z : Plane => 2*deriv g (radiusSq z)*(k+ε/(2*Real.pi))) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2).mul_const _
  have hwi := cutoffWedge_integrable (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ
  have hgi : Integrable (fun z => g (radiusSq z)*planarCurl β z) :=
    ((hg.continuous.comp radiusSq_smooth.continuous).mul
      (planarCurl_contDiff hβ).continuous).integrable_of_hasCompactSupport
        ((HasCompactSupport.comp_radiusSq hgc).mul_right)
  have hmass := integral_mono (he.integrable_of_hasCompactSupport hc) hgi hdom
  have hflux := integral_mono hdi hwi hcomp
  have hg0 : g 0=1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hgc,hg0,mul_one] at hflux
  rw [integral_cutoffWedge (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ] at hflux
  dsimp only [Function.comp_def] at hflux
  have heq : (2*Real.pi)*(k+ε/(2*Real.pi))=2*Real.pi*k+ε := by
    field_simp
  nlinarith only [hmass,hflux,heq]

theorem AffineLineCurve.compact_density_mass_le_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S<capacity x → J x=standardJ n)
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    {e : Plane → ℝ} (he : Continuous e) (hc : HasCompactSupport e)
    (hle : ∀ z, e z≤curveDensity S T u z) : (∫ z, e z)≤1 := by
  have hh := integral_compact_le_infinity_flux (curvePrimitive_smooth hST hu.1)
    (fun z => (curvePrimitive_curl hST hu.1 z).symm ▸ curveDensity_nonneg hST hT hJ hout hu.2.1 z)
    (hu.radial_infinity_limit hJc hST) he hc
    (fun z => (curvePrimitive_curl hST hu.1 z).symm ▸ hle z)
  have heq : 2*Real.pi*(1/(2*Real.pi))=1 := by field_simp
  exact heq ▸ hh

end HigherDimensionalBallPacking.Rigidity

end
noncomputable section
open scoped Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma entire_affine_of_asymptote {f : ℂ → E} (hf : Differentiable ℂ f) {a : E}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • f z) (cocompact ℂ) (𝓝 a)) (z : ℂ) :
    f z=f 0+z • a := by
  have hs : Differentiable ℂ (dslope f 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ) (c := (0:ℂ))
      univ_mem).mpr hf.differentiableOn)
  have hi : Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have ht : Tendsto (dslope f 0) (cocompact ℂ) (𝓝 a) := by
    have hsub := ha.sub (hi.smul_const (f 0))
    simp only [zero_smul,sub_zero] at hsub
    apply hsub.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with w hw
    have hw0 : w≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hw
    rw [dslope_of_ne f hw0,slope_def_module,sub_zero,smul_sub]
  have hvalue := sub_smul_dslope f 0 z
  rw [sub_zero,hs.apply_eq_of_tendsto_cocompact z ht] at hvalue
  exact (sub_eq_iff_eq_add.mp hvalue.symm).trans (add_comm _ _)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end
noncomputable section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance transInst1 : NormedAddCommGroup (HMap D E) := inferInstance
local instance transInst2 : NormedSpace ℝ (HMap D E) := inferInstance
local instance transInst3 : NormedAddCommGroup (COne D E) := inferInstance
local instance transInst4 : NormedSpace ℝ (COne D E) := inferInstance

def holderTranslate (t : D) (u : HMap D E) : HMap D E :=
  ofBound (fun z => valueCLM _ u (z+t))
    ((valueCLM _ u).continuous.comp (continuous_id.add continuous_const))
    ‖u‖ ‖u‖ (fun z => norm_value_le u _) (norm_nonneg u) (by
      intro x y
      simpa only [dist_add_right] using norm_sub_value_le u (x+t) (y+t))

omit [NormedSpace ℝ D] in
@[simp] lemma holderTranslate_value [NormedSpace ℝ D] (t : D) (u : HMap D E) (z : D) :
    valueCLM _ (holderTranslate t u) z = valueCLM _ u (z+t) := rfl

omit [NormedSpace ℝ D] in
lemma holderTranslate_norm_le [NormedSpace ℝ D] (t : D) (u : HMap D E) : ‖holderTranslate t u‖ ≤ ‖u‖ := by
  apply (norm_le_of_bounds _ (norm_nonneg u) (norm_nonneg u) ?_ ?_).trans (max_self _).le
  · intro z; exact norm_value_le u _
  · intro x y
    simpa only [holderTranslate_value,dist_add_right] using norm_sub_value_le u (x+t) (y+t)

def jetTranslate (t : D) (u : COne D E) : COne D E :=
  ⟨(holderTranslate t (jetValueCLM _ u),holderTranslate t (jetDerivCLM _ u)),by
    intro z
    have h := (c_hasFDerivAt u (z+t)).comp z ((hasFDerivAt_id z).add_const t)
    change HasFDerivAt (fun x => cValue u (x+t)) (cDeriv u (z+t)) z
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using h⟩

@[simp] lemma jetTranslate_value (t : D) (u : COne D E) (z : D) :
    cValue (jetTranslate t u) z = cValue u (z+t) := rfl

@[simp] lemma jetTranslate_deriv (t : D) (u : COne D E) (z : D) :
    cDeriv (jetTranslate t u) z = cDeriv u (z+t) := rfl

lemma jetTranslate_norm_le (t : D) (u : COne D E) : ‖jetTranslate t u‖ ≤ ‖u‖ := by
  change max ‖holderTranslate t (jetValueCLM _ u)‖ ‖holderTranslate t (jetDerivCLM _ u)‖ ≤ _
  exact max_le ((holderTranslate_norm_le _ _).trans (jetValue_norm_le u))
    ((holderTranslate_norm_le _ _).trans (jetDeriv_norm_le u))

lemma cValue_norm_diff_le (u : COne D E) (x y : D) :
    ‖cValue u x-cValue u y‖ ≤ ‖u‖*dist x y := by
  rw [dist_eq_norm]
  exact norm_sub_le_of_deriv_bound (c_differentiable u)
    (fun z => by rw [c_fderiv]; exact c_deriv_bound u z) x y

lemma translate_value_norm (u : COne D E) (t z : D) :
    ‖valueCLM _ (holderTranslate t (jetValueCLM _ u)-jetValueCLM _ u) z‖ ≤ ‖u‖*‖t‖ := by
  change ‖cValue u (z+t)-cValue u z‖ ≤ _
  simpa only [dist_eq_norm,add_sub_cancel_left] using cValue_norm_diff_le u (z+t) z

lemma translate_value_lipschitz (u : COne D E) (t x y : D) :
    ‖valueCLM _ (holderTranslate t (jetValueCLM _ u)-jetValueCLM _ u) x-
      valueCLM _ (holderTranslate t (jetValueCLM _ u)-jetValueCLM _ u) y‖ ≤ 2*‖u‖*dist x y := by
  change ‖(cValue u (x+t)-cValue u x)-(cValue u (y+t)-cValue u y)‖ ≤ _
  rw [show (cValue u (x+t)-cValue u x)-(cValue u (y+t)-cValue u y) =
    (cValue u (x+t)-cValue u (y+t))-(cValue u x-cValue u y) by abel]
  have h₁ := cValue_norm_diff_le u (x+t) (y+t)
  rw [dist_add_right] at h₁
  exact (norm_sub_le _ _).trans (by linarith [cValue_norm_diff_le u x y])

lemma jetValue_translate_tendsto (u : COne D E) :
    Tendsto (fun t => holderTranslate t (jetValueCLM _ u)) (𝓝 0) (𝓝 (jetValueCLM _ u)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_small_of_small_value (X := D) (E := E)
    (show 0 ≤ 2*‖u‖ by positivity) hε
  have ht : Tendsto (fun t : D => ‖u‖*‖t‖) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun t : D => ‖u‖*‖t‖) := continuous_const.mul continuous_norm
    simpa only [norm_zero,mul_zero] using h.tendsto (0:D)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with t ht
  rw [dist_eq_norm]
  exact hd _ (fun z => (translate_value_norm u t z).trans ht.le) (translate_value_lipschitz u t)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
