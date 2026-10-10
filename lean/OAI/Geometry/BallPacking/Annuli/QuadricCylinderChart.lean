import Mathlib
import OAI.Geometry.BallPacking.Annuli.SurfacePathPositivity

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

def transverseCylinder : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
    HandleCylinder (Surface m) ∞ :=
  (cylinderComplexDiffeomorph.trans
    Complex.equivRealProdCLM.toDiffeomorph.toPartialDiffeomorph).trans (transverseDiffeomorph m)

@[simp] theorem transverseCylinder_apply (q : HandleCylinder) :
    transverseCylinder m q=transverseAnnulusInverse m (cylinderComplexMap q) := rfl

@[simp] theorem transverseCylinder_symm_apply (x : Surface m) :
    (transverseCylinder m).symm x=cylinderComplexInverse (transverseCoordinate m x.val) := by
  change cylinderComplexInverse (Complex.equivRealProdCLM.symm
    (Complex.equivRealProdCLM (transverseCoordinate m x.val)))=_
  rw [ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem transverseCylinder_source : (transverseCylinder m).source=
    cylinderComplexMap ⁻¹' transverseAnnulusDomain m := by
  ext q
  simp [transverseCylinder,PartialDiffeomorph.trans,cylinderComplexDiffeomorph,
    Diffeomorph.toPartialDiffeomorph,transverseDiffeomorph_source]
  change Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (cylinderComplexMap q))∈transverseAnnulusDomain m ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem transverseCylinder_core (u : Circle) : (0,u)∈(transverseCylinder m).source := by
  rw [transverseCylinder_source]
  exact unitCircle_subset_transverseDomain m (by simp)

theorem exists_transverseCylinderWidth : ∃ a : ℝ,0<a ∧
    Icc (-a) a ×ˢ (univ : Set Circle)⊆(transverseCylinder m).source := by
  have hc : ({0}:Set ℝ) ×ˢ (univ : Set Circle)⊆(transverseCylinder m).source := by
    rintro ⟨s,u⟩ ⟨hs,_⟩
    have hs' : s=0 := hs
    subst s
    exact transverseCylinder_core m u
  obtain ⟨U,V,hU,_,h0,hV,hUV⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_univ : IsCompact (univ : Set Circle)) (transverseCylinder m).open_source hc
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0 (mem_singleton 0)))
  refine ⟨ε/2,half_pos hε,?_⟩
  rintro ⟨s,u⟩ ⟨hs,_⟩
  apply hUV
  refine ⟨hball ?_,hV (mem_univ u)⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
  constructor <;> linarith [hs.1,hs.2]

def transverseCylinderWidth : ℝ := (exists_transverseCylinderWidth m).choose

theorem transverseCylinderWidth_pos : 0<transverseCylinderWidth m :=
  (exists_transverseCylinderWidth m).choose_spec.1

theorem transverseCylinderWidth_subset :
    Icc (-transverseCylinderWidth m) (transverseCylinderWidth m) ×ˢ (univ : Set Circle)⊆
      (transverseCylinder m).source := (exists_transverseCylinderWidth m).choose_spec.2

theorem transverseCylinder_compact : IsCompact ((transverseCylinder m) ''
    (Icc (-transverseCylinderWidth m) (transverseCylinderWidth m) ×ˢ (univ : Set Circle))) :=
  (isCompact_Icc.prod isCompact_univ).image_of_continuousOn
    ((transverseCylinder m).contMDiffOn_toFun.continuousOn.mono (transverseCylinderWidth_subset m))

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped Topology
open Set Function

def complexClosedAnnulus (ε : ℝ) : Set ℂ := {z | 1-ε≤‖z‖ ∧ ‖z‖≤1+ε}

theorem complexClosedAnnulus_isCompact (ε : ℝ) : IsCompact (complexClosedAnnulus ε) := by
  apply (isCompact_closedBall (0:ℂ) (1+ε)).of_isClosed_subset
  · exact isClosed_le continuous_const continuous_norm |>.inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2

theorem complex_normalize_dist {z : ℂ} (hz : z≠0) :
    dist z (‖z‖⁻¹ • z)=|‖z‖-1| := by
  rw [dist_eq_norm,show z-‖z‖⁻¹ • z=(1-‖z‖⁻¹) • z by module,norm_smul,
    Real.norm_eq_abs]
  calc
    |1-‖z‖⁻¹| * ‖z‖ = |(1-‖z‖⁻¹)*‖z‖| := by
      rw [abs_mul,abs_of_nonneg (norm_nonneg z)]
    _ = |‖z‖-1| := by
      congr 1
      field_simp [norm_ne_zero_iff.mpr hz]

theorem exists_complexClosedAnnulus_subset {U : Set ℂ} (hU : IsOpen U)
    (hs : Metric.sphere (0:ℂ) 1⊆U) :
    ∃ ε : ℝ,0<ε ∧ ε<1/2 ∧ complexClosedAnnulus ε⊆U := by
  obtain ⟨δ,hδ,hδU⟩ := (isCompact_sphere (0:ℂ) 1).exists_cthickening_subset_open hU hs
  let ε := min (δ/2) (1/4)
  have hε : 0<ε := lt_min (half_pos hδ) (by norm_num)
  have hεδ : ε≤δ := (min_le_left _ _).trans (half_le_self hδ.le)
  have hεh : ε<1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨ε,hε,hεh,?_⟩
  intro z hz
  have hzn : 0<‖z‖ := by linarith [hz.1]
  have hz0 : z≠0 := norm_pos_iff.mp hzn
  have hyn : ‖‖z‖⁻¹ • z‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hzn),inv_mul_cancel₀ hzn.ne']
  have hyd : dist z (‖z‖⁻¹ • z)≤δ := by
    rw [complex_normalize_dist hz0]
    exact (abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩ : |‖z‖-1|≤ε).trans hεδ
  apply hδU
  apply Metric.mem_cthickening_of_dist_le z (‖z‖⁻¹ • z) δ (Metric.sphere (0:ℂ) 1)
  · simpa only [Metric.mem_sphere,dist_zero_right] using hyn
  · exact hyd

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

abbrev RadialPlane := ℝ × ℝ

def planeRadiusSq (x : RadialPlane) : ℝ := x.1^2+x.2^2

def planeRadialStep (ε : ℝ) (x : RadialPlane) : ℝ :=
  Real.smoothTransition ((planeRadiusSq x-(1-ε)^2)/((1+ε)^2-(1-ε)^2))

def planeClosedAnnulus (ε : ℝ) : Set RadialPlane :=
  Complex.equivRealProdCLM.symm ⁻¹' complexClosedAnnulus ε

theorem planeRadiusSq_norm (x : RadialPlane) :
    planeRadiusSq x=‖Complex.equivRealProdCLM.symm x‖^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [planeRadiusSq,Complex.normSq_apply,pow_two]

theorem planeRadialStep_smooth (ε : ℝ) : ContDiff ℝ ∞ (planeRadialStep ε) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_fst.pow 2).add (contDiff_snd.pow 2)).sub contDiff_const |>.div_const _)

theorem planeClosedAnnulus_compact (ε : ℝ) : IsCompact (planeClosedAnnulus ε) := by
  have he : planeClosedAnnulus ε=Complex.equivRealProdCLM '' complexClosedAnnulus ε := by
    ext x
    constructor
    · intro hx
      exact ⟨Complex.equivRealProdCLM.symm x,hx,Complex.equivRealProdCLM.apply_symm_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [planeClosedAnnulus,mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hz
  rw [he]
  exact (complexClosedAnnulus_isCompact ε).image Complex.equivRealProdCLM.continuous

theorem planeRadialStep_zero {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {x : RadialPlane}
    (hx : ‖Complex.equivRealProdCLM.symm x‖≤1-ε) : planeRadialStep ε x=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hd : 0<(1+ε)^2-(1-ε)^2 := by nlinarith
  apply div_nonpos_of_nonpos_of_nonneg _ hd.le
  rw [planeRadiusSq_norm]
  nlinarith [norm_nonneg (Complex.equivRealProdCLM.symm x)]

theorem planeRadialStep_one {ε : ℝ} (hε : 0<ε) {x : RadialPlane}
    (hx : 1+ε≤‖Complex.equivRealProdCLM.symm x‖) : planeRadialStep ε x=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hd : 0<(1+ε)^2-(1-ε)^2 := by nlinarith
  rw [le_div_iff₀ hd]
  rw [planeRadiusSq_norm]
  nlinarith

theorem planeRadialDifferential_zero {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (x : RadialPlane) (hx : x∉planeClosedAnnulus ε) :
    manifoldScalarDifferential (E := RadialPlane) (planeRadialStep ε) x=0 := by
  have hn := continuous_norm.comp Complex.equivRealProdCLM.symm.continuous
  change ¬(1-ε≤‖Complex.equivRealProdCLM.symm x‖ ∧
    ‖Complex.equivRealProdCLM.symm x‖≤1+ε) at hx
  by_cases hl : ‖Complex.equivRealProdCLM.symm x‖<1-ε
  · have he : planeRadialStep ε =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [(isOpen_lt hn continuous_const).mem_nhds hl] with y hy
      exact planeRadialStep_zero hε hε1 hy.le
    exact he.mfderiv_eq.trans (by
      simp only [mfderiv_const,ContinuousLinearMap.comp_zero]
      rfl)
  · have hu : 1+ε<‖Complex.equivRealProdCLM.symm x‖ :=
      lt_of_not_ge (fun h => hx ⟨le_of_not_gt hl,h⟩)
    have he : planeRadialStep ε =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
      filter_upwards [(isOpen_lt continuous_const hn).mem_nhds hu] with y hy
      exact planeRadialStep_one hε hy.le
    exact he.mfderiv_eq.trans (by
      simp only [mfderiv_const,ContinuousLinearMap.comp_zero]
      rfl)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem exists_annulusWidth : ∃ ε : ℝ,0<ε ∧ ε<1/2 ∧
    planeClosedAnnulus ε⊆(annulusDiffeomorph m).source := by
  obtain ⟨ε,hε,hε1,hU⟩ := exists_complexClosedAnnulus_subset (annulusDomain_isOpen m)
    (fun z hz => unitCircle_subset_domain m (by simpa only [Metric.mem_sphere,dist_zero_right] using hz))
  refine ⟨ε,hε,hε1,?_⟩
  intro x hx
  rw [annulusDiffeomorph_source]
  exact hU hx

def annulusWidth : ℝ := (exists_annulusWidth m).choose

theorem annulusWidth_pos : 0<annulusWidth m := (exists_annulusWidth m).choose_spec.1

theorem annulusWidth_lt : annulusWidth m<1/2 := (exists_annulusWidth m).choose_spec.2.1

theorem annulusWidth_subset : planeClosedAnnulus (annulusWidth m)⊆(annulusDiffeomorph m).source :=
  (exists_annulusWidth m).choose_spec.2.2

def compactDualForm : ManifoldOneForm RealModel (Surface m) :=
  handlePushforwardOneForm (annulusDiffeomorph m)
    (manifoldScalarDifferential (planeRadialStep (annulusWidth m)))

theorem compactDualForm_smooth : SmoothOneFormFamily (fun _ : ℝ => compactDualForm m) := by
  apply handlePushforwardOneForm_smooth (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
  · exact manifoldScalarDifferential_smooth (planeRadialStep_smooth _).contMDiff
  · exact planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num))

theorem compactDualForm_compact : HasCompactSupport (compactDualForm m) := by
  exact handlePushforwardOneForm_compact (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
    (planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num)))

theorem compactDualForm_closed (x : Surface m) : manifoldExteriorOneForm (compactDualForm m) x=0 := by
  apply handlePushforwardOneForm_closed (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
  · exact manifoldScalarDifferential_smooth (planeRadialStep_smooth _).contMDiff
  · exact planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num))
  · exact manifoldScalarDifferential_closed (planeRadialStep_smooth _).contMDiff

theorem compactDualForm_pullback {x : RealModel} (hx : x∈(annulusDiffeomorph m).source) :
    manifoldPullbackOneForm (fun _ => compactDualForm m) (annulusDiffeomorph m) 0 x=
      manifoldScalarDifferential (E := RealModel) (planeRadialStep (annulusWidth m)) x :=
  handlePushforwardOneForm_pullback (annulusDiffeomorph m) _ hx

theorem compactDualForm_support : tsupport (compactDualForm m)⊆
    (annulusDiffeomorph m) '' planeClosedAnnulus (annulusWidth m) :=
  handlePushforwardOneForm_tsupport (annulusDiffeomorph m)
    (planeClosedAnnulus_compact (annulusWidth m)) (annulusWidth_subset m)
    (planeRadialDifferential_zero (annulusWidth_pos m)
      (lt_trans (annulusWidth_lt m) (by norm_num)))

def transversePoint (θ : ℝ) : Affine (m+2) :=
  ((Real.cos θ : ℂ),fun j => if j=0 then Complex.I*(Real.sin θ : ℂ)
    else Complex.I*(Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ))

theorem transversePoint_mem (θ : ℝ) : transversePoint m θ∈locus (parameters m) := by
  rw [mem_locus]
  intro j
  have hc := Real.cos_sq_le_one θ
  by_cases hj : j=0
  · subst j
    simp only [transversePoint,↓reduceIte,parameters_zero,mul_pow,Complex.I_sq]
    have he := Real.sin_sq_add_cos_sq θ
    have heC : (Real.sin θ : ℂ)^2+(Real.cos θ : ℂ)^2=1 := by exact_mod_cast he
    linear_combination -heC
  · have hn : 0≤(j.val : ℝ)+1-Real.cos θ^2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) j.val]
    have he := Real.sq_sqrt hn
    have heC : (Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ)^2=
        (j.val : ℂ)+1-(Real.cos θ : ℂ)^2 := by exact_mod_cast he
    simp only [transversePoint,ite_eq_right hj,mul_pow,Complex.I_sq,parameters]
    rw [heC]
    ring

def transverseCycle (θ : ℝ) : Surface m := ⟨transversePoint m θ,transversePoint_mem m θ⟩

theorem transverseCycle_periodic : Function.Periodic (transverseCycle m) (2*Real.pi) := by
  intro θ
  apply Subtype.ext
  simp only [transverseCycle,transversePoint,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem transversePoint_smooth : ContDiff ℝ ∞ (transversePoint m) := by
  apply ContDiff.prodMk
  · exact Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  · apply contDiff_pi.mpr
    intro j
    by_cases hj : j=0
    · simp only [ite_eq_left hj]
      exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp Real.contDiff_sin)
    · simp only [ite_eq_right hj]
      apply contDiff_const.mul
      apply Complex.ofRealCLM.contDiff.comp
      have hp : ∀ θ : ℝ,0<(j.val : ℝ)+1-Real.cos θ^2 := by
        intro θ
        have hjp : 0<j.val := Fin.pos_iff_ne_zero.mpr hj
        have hr : 0<(j.val : ℝ) := by exact_mod_cast hjp
        nlinarith [Real.cos_sq_le_one θ]
      exact (contDiff_const.sub (Real.contDiff_cos.pow 2)).sqrt (fun θ => (hp θ).ne')

theorem transverseCycle_smooth : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,RealModel) ∞ (transverseCycle m) := by
  intro θ
  rw [← contMDiffWithinAt_univ]
  exact real_contMDiffWithinAt_of_ambient (parameters m) (transversePoint_smooth m).contDiffAt.contDiffWithinAt

@[simp] theorem transversePoint_first (θ : ℝ) : (transversePoint m θ).1=(Real.cos θ : ℂ) := rfl

@[simp] theorem transversePoint_zero (θ : ℝ) : (transversePoint m θ).2 0=Complex.I*(Real.sin θ : ℂ) := by
  simp [transversePoint]

@[simp] theorem transversePoint_one (θ : ℝ) : (transversePoint m θ).2 1=
    Complex.I*(Real.sqrt (1+Real.sin θ^2) : ℂ) := by
  have he : (2:ℝ)-Real.cos θ^2=1+Real.sin θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hj : (1 : Fin (m+2))≠0 := by simp
  simp only [transversePoint,ite_eq_right hj,Fin.val_one,Nat.cast_one,one_add_one_eq_two]
  rw [he]

theorem transverseCycle_coordinate (θ : ℝ) :
    annulusCoordinate m (transverseCycle m θ).val=
      Complex.I*((Real.sin θ+Real.sqrt (1+Real.sin θ^2) : ℝ) : ℂ) := by
  change (transversePoint m θ).2 0+(transversePoint m θ).2 1=_
  rw [transversePoint_zero,transversePoint_one,Complex.ofReal_add,mul_add]

theorem transverseCycle_branch_iff (θ : ℝ) :
    transverseCycle m θ∈annulusBranch m ↔ 0<Real.cos θ := by
  constructor
  · intro h
    exact h.2.1
  · intro h
    have hb : baseSquare (annulusCoordinate m (transverseCycle m θ).val)=(Real.cos θ : ℂ)^2 :=
      baseSquare_coordinate m (transversePoint_mem m θ)
    refine ⟨⟨annulusCoordinate_ne_zero m (transversePoint_mem m θ),?_,?_⟩,h,?_⟩
    · rw [hb,← Complex.ofReal_pow,Complex.ofReal_re]
      positivity
    · intro j hj
      rw [hb]
      simp only [parameters,Complex.sub_re,Complex.add_re,Complex.natCast_re,
        Complex.one_re,← Complex.ofReal_pow,Complex.ofReal_re]
      have hjp : (1:ℝ)<j.val := by exact_mod_cast hj
      nlinarith [Real.cos_sq_le_one θ]
    · intro j hj
      have hj0 : j≠0 := by intro he; subst j; simp at hj
      change 0<(if j=0 then Complex.I*(Real.sin θ : ℂ)
        else Complex.I*(Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ)).im
      simp only [ite_eq_right hj0,Complex.mul_im,Complex.I_re,Complex.I_im,
        zero_mul,one_mul,zero_add,Complex.ofReal_re]
      apply Real.sqrt_pos.mpr
      have hjp : (1:ℝ)<j.val := by exact_mod_cast hj
      nlinarith [Real.cos_sq_le_one θ]

def transverseRadius (θ : ℝ) : ℝ := Real.sin θ+Real.sqrt (1+Real.sin θ^2)

theorem transverseRadius_pos (θ : ℝ) : 0<transverseRadius θ := by
  have hp : 0<1+Real.sin θ^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn := Real.sqrt_pos.mpr hp
  unfold transverseRadius
  nlinarith

theorem transverseCycle_coord_norm (θ : ℝ) :
    ‖annulusCoordinate m (transverseCycle m θ).val‖=transverseRadius θ := by
  rw [transverseCycle_coordinate,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
    Real.norm_eq_abs]
  exact abs_of_pos (transverseRadius_pos θ)

theorem transverseRadius_smooth : ContDiff ℝ ∞ transverseRadius :=
  Real.contDiff_sin.add ((contDiff_const.add (Real.contDiff_sin.pow 2)).sqrt
    (fun θ => ne_of_gt (by positivity)))

theorem transverseRadius_lower : transverseRadius (-(Real.pi/2))<1/2 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : 0≤Real.sqrt 2 := Real.sqrt_nonneg 2
  norm_num [transverseRadius,Real.sin_neg,Real.sin_pi_div_two]
  nlinarith

theorem transverseRadius_upper : 3/2<transverseRadius (Real.pi/2) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : 0≤Real.sqrt 2 := Real.sqrt_nonneg 2
  norm_num [transverseRadius,Real.sin_pi_div_two]
  nlinarith

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def curveOneForm (α : ManifoldOneForm E M) (q : ℝ → M) (t : ℝ) : ℝ :=
  α (q t) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) q t 1)

theorem curveOneForm_smooth {α : ManifoldOneForm E M} {q : ℝ → M}
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) : ContDiff ℝ ∞ (curveOneForm α q) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hs := (euclideanPullbackOneForm_contDiffAt (α := fun _ => α) (g := q) (p := (0,t)) hα (hq t)).comp t
    (contDiffAt_const.prodMk contDiffAt_id)
  exact hs.clm_apply contDiffAt_const

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem curveOneForm_scalar {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    {q : ℝ → M} (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ q) (t : ℝ) :
    curveOneForm (manifoldScalarDifferential (E := E) f) q t=deriv (f ∘ q) t := by
  have hd := mfderiv_comp t (hf.mdifferentiableAt (by simp)) (hq.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  exact (congrArg (fun D : ℝ →L[ℝ] ℝ => D 1) hd).symm

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
theorem curveOneForm_pushforward_scalar
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    {q : ℝ → N} (hq : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,F) ∞ q)
    {t : ℝ} (ht : q t∈e.target) :
    curveOneForm (handlePushforwardOneForm e (manifoldScalarDifferential (E := E) f)) q t=
      deriv (f ∘ e.symm ∘ q) t := by
  have hi := e.symm.mdifferentiableAt (by simp) ht
  have hq' := hq.mdifferentiableAt (x := t) (by simp)
  have hd₁ := mfderiv_comp t hi hq'
  have hd₂ := mfderiv_comp t (hf.mdifferentiableAt (by simp)) (hi.comp t hq')
  rw [mfderiv_eq_fderiv] at hd₂
  rw [hd₁] at hd₂
  change (extendManifoldOneForm (E := F) e.target
    (manifoldPullbackOneForm (E := E) (F := F) (fun _ => manifoldScalarDifferential (E := E) f) e.symm 0) (q t))
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) q t 1)=_
  rw [extendManifoldOneForm_inside ht]
  exact (congrArg (fun D : ℝ →L[ℝ] ℝ => D 1) hd₂).symm

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

def transverseRealCoordinate (θ : ℝ) : RealModel :=
  Complex.equivRealProdCLM (annulusCoordinate m (transverseCycle m θ).val)

def transverseStep (θ : ℝ) : ℝ := planeRadialStep (annulusWidth m) (transverseRealCoordinate m θ)

def dualAlongCycle (θ : ℝ) : ℝ := curveOneForm (compactDualForm m) (transverseCycle m) θ

theorem transverseRealCoordinate_smooth : ContDiff ℝ ∞ (transverseRealCoordinate m) :=
  Complex.equivRealProdCLM.contDiff.comp
    (((annulusCoordinate m).restrictScalars ℝ).contDiff.comp (transversePoint_smooth m))

theorem transverseStep_smooth : ContDiff ℝ ∞ (transverseStep m) :=
  (planeRadialStep_smooth _).comp (transverseRealCoordinate_smooth m)

theorem dualAlongCycle_smooth : ContDiff ℝ ∞ (dualAlongCycle m) :=
  curveOneForm_smooth (compactDualForm_smooth m) (transverseCycle_smooth m)

theorem dualAlongCycle_zero {θ : ℝ} (hθ : Real.cos θ≤0) : dualAlongCycle m θ=0 := by
  have ht : transverseCycle m θ∉(annulusDiffeomorph m).target := by
    rw [annulusDiffeomorph_target,transverseCycle_branch_iff]
    exact not_lt.mpr hθ
  change (extendManifoldOneForm (annulusDiffeomorph m).target _ (transverseCycle m θ)) _=0
  rw [extendManifoldOneForm_outside ht]
  rfl

theorem dualAlongCycle_deriv {θ : ℝ} (hθ : 0<Real.cos θ) :
    dualAlongCycle m θ=deriv (transverseStep m) θ := by
  have ht : transverseCycle m θ∈(annulusDiffeomorph m).target := by
    rw [annulusDiffeomorph_target,transverseCycle_branch_iff]
    exact hθ
  exact curveOneForm_pushforward_scalar (annulusDiffeomorph m)
    (planeRadialStep_smooth _).contMDiff (transverseCycle_smooth m) ht

theorem transverseStep_lower : transverseStep m (-(Real.pi/2))=0 := by
  apply planeRadialStep_zero (annulusWidth_pos m) (lt_trans (annulusWidth_lt m) (by norm_num))
  change ‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM _)‖≤_
  rw [ContinuousLinearEquiv.symm_apply_apply,transverseCycle_coord_norm]
  linarith [transverseRadius_lower,annulusWidth_lt m]

theorem transverseStep_upper : transverseStep m (Real.pi/2)=1 := by
  apply planeRadialStep_one (annulusWidth_pos m)
  change _≤‖Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM _)‖
  rw [ContinuousLinearEquiv.symm_apply_apply,transverseCycle_coord_norm]
  linarith [transverseRadius_upper,annulusWidth_lt m]

theorem dualAlongCycle_integral_first :
    ∫ θ in -(Real.pi/2)..Real.pi/2,dualAlongCycle m θ=1 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤Real.pi/2)
    (transverseStep_smooth m).continuous.continuousOn
    (fun θ hθ => ?_)
    ((dualAlongCycle_smooth m).continuous.intervalIntegrable _ _)
  · simpa only [transverseStep_lower,transverseStep_upper,sub_zero] using he
  · rw [dualAlongCycle_deriv m (Real.cos_pos_of_mem_Ioo hθ)]
    exact ((transverseStep_smooth m).differentiable (by simp) θ).hasDerivAt

theorem dualAlongCycle_integral_second :
    ∫ θ in Real.pi/2..Real.pi+Real.pi/2,dualAlongCycle m θ=0 := by
  calc
    _ = ∫ θ in Real.pi/2..Real.pi+Real.pi/2,(0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi/2≤Real.pi+Real.pi/2)] at hθ
      exact dualAlongCycle_zero m (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 hθ.2)
    _ = 0 := by simp

theorem compactDualForm_period :
    ∫ θ in -(Real.pi/2)..Real.pi+Real.pi/2,
      curveOneForm (compactDualForm m) (transverseCycle m) θ=1 := by
  have hi := (dualAlongCycle_smooth m).continuous
  change ∫ θ in -(Real.pi/2)..Real.pi+Real.pi/2,dualAlongCycle m θ=1
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := Real.pi/2) (hi.intervalIntegrable _ _) (hi.intervalIntegrable _ _),
    dualAlongCycle_integral_first,dualAlongCycle_integral_second,add_zero]

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end

end OAI
