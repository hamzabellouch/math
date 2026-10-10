import Mathlib
import OAI.Geometry.BallPacking.Necessity.HolderCompletion

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} {E F : Type v} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 
def sectionApply (M : K →ᵇ (E →L[ℝ] F)) (v : K →ᵇ E) : K →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => M z (v z)) (M.continuous.clm_apply v.continuous)
    (‖M‖*‖v‖) (fun z => (M z).le_opNorm (v z) |>.trans
      (mul_le_mul (M.norm_coe_le_norm z) (v.norm_coe_le_norm z)
        (norm_nonneg (v z)) (norm_nonneg M)))

theorem sectionApply_norm (M : K →ᵇ (E →L[ℝ] F)) (v : K →ᵇ E) :
    ‖sectionApply M v‖ ≤ ‖M‖*‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg M) (norm_nonneg v))).mpr
  intro z
  exact (M z).le_opNorm (v z) |>.trans
    (mul_le_mul (M.norm_coe_le_norm z) (v.norm_coe_le_norm z)
      (norm_nonneg (v z)) (norm_nonneg M))

def sectionCLM (M : K →ᵇ (E →L[ℝ] F)) : (K →ᵇ E) →L[ℝ] (K →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := sectionApply M
      map_add' := fun v w => by ext z; exact (M z).map_add _ _
      map_smul' := fun c v => by ext z; exact (M z).map_smul c (v z) }
    ‖M‖ (sectionApply_norm M)

@[simp] theorem sectionCLM_apply (M : K →ᵇ (E →L[ℝ] F)) (v : K →ᵇ E) (z : K) :
    sectionCLM M v z = M z (v z) := rfl

def sectionOperatorCLM : (K →ᵇ (E →L[ℝ] F)) →L[ℝ] ((K →ᵇ E) →L[ℝ] (K →ᵇ F)) :=
  LinearMap.mkContinuous
    { toFun := sectionCLM
      map_add' := fun M N => by ext v z; rfl
      map_smul' := fun c M => by ext v z; rfl }
    1 (fun M => by
      change ‖sectionCLM M‖ ≤ 1*‖M‖
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M) (sectionApply_norm M))

@[simp] theorem sectionOperatorCLM_apply (M : K →ᵇ (E →L[ℝ] F)) :
    sectionOperatorCLM M = sectionCLM M := rfl

 

def superposeBCF (f : E →ᵇ F) (base : C(K,E)) (v : K →ᵇ E) : K →ᵇ F :=
  f.compContinuous ⟨fun z => base z + v z, base.continuous.add v.continuous⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem superposeBCF_apply (f : E →ᵇ F) (base : C(K,E)) (v : K →ᵇ E) (z : K) :
    superposeBCF f base v z = f (base z + v z) := rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem superposeBCF_uniformContinuous (f : E →ᵇ F)
    (hf : UniformContinuous (f : E → F)) (base : C(K,E)) :
    UniformContinuous (superposeBCF f base) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by positivity)
  refine ⟨δ,hδ,fun v w hvw => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le (by positivity : 0≤ε/2)).mpr
  intro z
  change ‖f (base z+v z)-f (base z+w z)‖≤ε/2
  have hh : dist (base z+v z) (base z+w z)<δ := by
    rw [dist_add_left, dist_eq_norm]
    exact ((v-w).norm_coe_le_norm z).trans_lt (by simpa only [dist_eq_norm] using hvw)
  simpa only [dist_eq_norm] using (hfδ hh).le

 

theorem superposeBCF_hasFDerivAt (f : E →ᵇ F) (g : E →ᵇ (E →L[ℝ] F))
    (hfg : ∀ x, HasFDerivAt (f : E → F) (g x) x)
    (hg : UniformContinuous (g : E → E →L[ℝ] F)) (base : C(K,E)) (v : K →ᵇ E) :
    HasFDerivAt (superposeBCF f base) (sectionCLM (superposeBCF g base v)) v := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hgδ⟩ := Metric.uniformContinuous_iff.mp hg ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : K →ᵇ E) hδ] with h hh
  have hhn : ‖h‖<δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro z
  change ‖f (base z+(v z+h z))-f (base z+v z)-g (base z+v z) (h z)‖≤ε*‖h‖
  have hbound : ∀ x ∈ Metric.ball (base z+v z) δ, ‖g x-g (base z+v z)‖≤ε := by
    intro x hx
    simpa only [dist_eq_norm] using (hgδ hx).le
  have hy : base z+(v z+h z)∈Metric.ball (base z+v z) δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,
      show base z+(v z+h z)-(base z+v z)=h z by abel] using
      (h.norm_coe_le_norm z).trans_lt hhn
  have hb := (convex_ball (base z+v z) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x _ => (hfg x).hasFDerivWithinAt) hbound
    (Metric.mem_ball_self hδ) hy
  have hc : ‖f (base z+(v z+h z))-f (base z+v z)-g (base z+v z) (h z)‖≤ε*‖h z‖ := by
    simpa only [show base z+(v z+h z)-(base z+v z)=h z by abel] using hb
  exact hc.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm z) hε.le)

 
def compactCoefficient (f : E → F) (hf : Continuous f) (hc : HasCompactSupport f) : E →ᵇ F :=
  ({ toFun := f, continuous_toFun := hf, hasCompactSupport' := hc } :
    CompactlySupportedContinuousMap E F).toBoundedContinuousFunction

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem compactCoefficient_apply (f : E → F) (hf : Continuous f)
    (hc : HasCompactSupport f) (x : E) : compactCoefficient f hf hc x = f x := rfl

theorem compactSuperpose_contDiff_nat (m : ℕ) {f : E → F}
    (hf : ContDiff ℝ m f) (hc : HasCompactSupport f) (base : C(K,E)) :
    ContDiff ℝ m (superposeBCF (compactCoefficient f hf.continuous hc) base) := by
  induction m generalizing F with
  | zero =>
    exact contDiff_zero.mpr
      (superposeBCF_uniformContinuous _
        (hf.continuous.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty) base).continuous
  | succ m ih =>
    have hdf : ContDiff ℝ m (fderiv ℝ f) := hf.fderiv_right (by simp)
    let g : E →ᵇ (E →L[ℝ] F) :=
      compactCoefficient (fderiv ℝ f) hdf.continuous (hc.fderiv ℝ)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun v => sectionOperatorCLM (superposeBCF g base v),?_,?_⟩
    · have hi : ContDiff ℝ m (superposeBCF g base) := ih hdf (hc.fderiv ℝ)
      exact sectionOperatorCLM.contDiff.comp hi
    · intro v
      apply superposeBCF_hasFDerivAt
      · intro x
        exact (hf.differentiable (by simp) x).hasFDerivAt
      · exact hdf.continuous.uniformContinuous_of_tendsto_cocompact (hc.fderiv ℝ).is_zero_at_infty

theorem compactSuperpose_contDiff {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (base : C(K,E)) :
    ContDiff ℝ ∞ (superposeBCF (compactCoefficient f hf.continuous hc) base) := by
  apply contDiff_infty.mpr
  intro m
  exact compactSuperpose_contDiff_nat m (contDiff_infty.mp hf m) hc base

 

def adaptedJSection (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) (v : K →ᵇ E) : K →ᵇ (E →L[ℝ] E) :=
  BoundedContinuousFunction.const K J₀ +
    superposeBCF (compactCoefficient (fun x => J x-J₀)
      (hJ.continuous.sub continuous_const) hc) base v

@[simp] theorem adaptedJSection_apply (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) (v : K →ᵇ E) (z : K) :
    adaptedJSection J J₀ hJ hc base v z = J (base z+v z) := by
  change J₀ + (J (base z+v z)-J₀) = _
  abel

theorem adaptedJSection_contDiff (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) : ContDiff ℝ ∞ (adaptedJSection J J₀ hJ hc base) := by
  exact contDiff_const.add (compactSuperpose_contDiff (hJ.sub contDiff_const) hc base)

local instance : NormedAddCommGroup (K →ᵇ (ℂ →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ (K →ᵇ (ℂ →L[ℝ] E)) := inferInstance

 
def jetSectionEval (w : ℂ) : (K →ᵇ (ℂ →L[ℝ] E)) →L[ℝ] (K →ᵇ E) :=
  ((ContinuousLinearMap.apply ℝ E) w).compLeftContinuousBounded K

@[simp] theorem jetSectionEval_apply (w : ℂ) (A : K →ᵇ (ℂ →L[ℝ] E)) (z : K) :
    jetSectionEval w A z = A z w := rfl

 

def bcfCRJet (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) (p : (K →ᵇ E) × (K →ᵇ (ℂ →L[ℝ] E))) : K →ᵇ E :=
  jetSectionEval Complex.I p.2 -
    sectionCLM (adaptedJSection J J₀ hJ hc base p.1) (jetSectionEval 1 p.2)

@[simp] theorem bcfCRJet_apply (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) (p : (K →ᵇ E) × (K →ᵇ (ℂ →L[ℝ] E))) (z : K) :
    bcfCRJet J J₀ hJ hc base p z = p.2 z Complex.I - J (base z+p.1 z) (p.2 z 1) := by
  change p.2 z Complex.I - adaptedJSection J J₀ hJ hc base p.1 z (p.2 z 1) = _
  rw [adaptedJSection_apply]

theorem bcfCRJet_contDiff (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) : ContDiff ℝ ∞ (bcfCRJet J J₀ hJ hc base) := by
  have hop : ContDiff ℝ ∞ (fun v : K →ᵇ E =>
      sectionCLM (adaptedJSection J J₀ hJ hc base v)) := by
    exact (sectionOperatorCLM (K := K) (E := E) (F := E)).contDiff.comp
      (adaptedJSection_contDiff J J₀ hJ hc base)
  exact ((jetSectionEval (K := K) (E := E) Complex.I).contDiff.comp contDiff_snd).sub
    ((hop.comp contDiff_fst).clm_apply
      ((jetSectionEval (K := K) (E := E) 1).contDiff.comp contDiff_snd))

 

theorem bcfCRJet_fderiv (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E)
    (hJ : ContDiff ℝ ∞ J) (hc : HasCompactSupport (fun x => J x-J₀))
    (base : C(K,E)) (p h : (K →ᵇ E) × (K →ᵇ (ℂ →L[ℝ] E))) (z : K) :
    fderiv ℝ (bcfCRJet J J₀ hJ hc base) p h z =
      h.2 z Complex.I - (fderiv ℝ J (base z+p.1 z) (h.1 z)) (p.2 z 1) -
        J (base z+p.1 z) (h.2 z 1) := by
  let P := (K →ᵇ E) × (K →ᵇ (ℂ →L[ℝ] E))
  have hf : HasFDerivAt (fun q : P => base z+q.1 z)
      ((BoundedContinuousFunction.evalCLM ℝ z).comp (ContinuousLinearMap.fst ℝ _ _)) p := by
    convert (hasFDerivAt_const (base z) p).add
      ((BoundedContinuousFunction.evalCLM ℝ (β := E) z).hasFDerivAt.comp p
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p))) using 1
    all_goals first | rfl | simp only [zero_add]
  have hs : HasFDerivAt (fun q : P => q.2 z)
      ((BoundedContinuousFunction.evalCLM ℝ z).comp (ContinuousLinearMap.snd ℝ _ _)) p :=
    (BoundedContinuousFunction.evalCLM ℝ (β := ℂ →L[ℝ] E) z).hasFDerivAt.comp p
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hdJ := ((hJ.differentiable (by simp)) (base z+p.1 z)).hasFDerivAt.comp p hf
  have hdI := hs.clm_apply (hasFDerivAt_const Complex.I p)
  have hd1 := hs.clm_apply (hasFDerivAt_const (1:ℂ) p)
  have hd := hdI.sub (hdJ.clm_apply hd1)
  have hb := (BoundedContinuousFunction.evalCLM ℝ z).hasFDerivAt.comp p
    (((bcfCRJet_contDiff J J₀ hJ hc base).differentiable (by simp)) p).hasFDerivAt
  have he : (fun q : P => bcfCRJet J J₀ hJ hc base q z) =
      (fun q : P => q.2 z Complex.I - J (base z+q.1 z) (q.2 z 1)) := by
    funext q
    exact bcfCRJet_apply J J₀ hJ hc base q z
  change HasFDerivAt (fun q : P => bcfCRJet J J₀ hJ hc base q z) _ p at hb
  rw [he] at hb
  have hder := congrArg (fun L : P →L[ℝ] E => L h) (hb.unique hd)
  simp only [ContinuousLinearMap.comp_apply,BoundedContinuousFunction.evalCLM_apply,
    sub_apply,add_apply,ContinuousLinearMap.flip_apply,zero_apply,map_zero,zero_add,
    Function.comp_def,
      sub_add_eq_sub_sub_swap] at hder
  convert hder using 1
  rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

def pairLeft (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    (K →ᵇ G) →L[ℝ] (OffDiagonal K →ᵇ G) :=
  BoundedContinuousFunction.compContinuousCLM G ℝ
    ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

def pairRight (G : Type v) [NormedAddCommGroup G] [NormedSpace ℝ G] :
    (K →ᵇ G) →L[ℝ] (OffDiagonal K →ᵇ G) :=
  BoundedContinuousFunction.compContinuousCLM G ℝ
    ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

@[simp] theorem pairLeft_apply (v : K →ᵇ E) (z : OffDiagonal K) : pairLeft E v z = v z.val.1 := rfl
@[simp] theorem pairRight_apply (v : K →ᵇ E) (z : OffDiagonal K) : pairRight E v z = v z.val.2 := rfl

theorem pairLeft_norm (v : K →ᵇ E) : ‖pairLeft E v‖ ≤ ‖v‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _
theorem pairRight_norm (v : K →ᵇ E) : ‖pairRight E v‖ ≤ ‖v‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _

theorem holderValue_norm (α : ℝ) (v : HolderSpace K E α) : ‖holderValue α v‖ ≤ ‖v‖ :=
  le_max_left _ _
theorem holderDifference_norm (α : ℝ) (v : HolderSpace K E α) : ‖holderDifference α v‖ ≤ ‖v‖ :=
  le_max_right _ _

def holderApply (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) (v : HolderSpace K E α) :
    HolderSpace K F α :=
  ⟨(sectionCLM (holderValue α M) (holderValue α v),
    sectionCLM (holderDifference α M) (pairLeft E (holderValue α v)) +
      sectionCLM (pairRight (E →L[ℝ] F) (holderValue α M)) (holderDifference α v)), by
    intro z
    change M.val.1 z.val.1 (v.val.1 z.val.1)-M.val.1 z.val.2 (v.val.1 z.val.2) =
      (dist z.val.1 z.val.2)^α •
        (M.val.2 z (v.val.1 z.val.1)+M.val.1 z.val.2 (v.val.2 z))
    calc
      _ = (M.val.1 z.val.1-M.val.1 z.val.2) (v.val.1 z.val.1) +
          M.val.1 z.val.2 (v.val.1 z.val.1-v.val.1 z.val.2) := by
        simp only [sub_apply,map_sub]
        abel
      _ = _ := by
        rw [M.property z,v.property z]
        simp only [smul_apply,map_smul,smul_add]⟩

@[simp] theorem holderApply_value (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α)
    (v : HolderSpace K E α) (x : K) :
    holderValue α (holderApply α M v) x = holderValue α M x (holderValue α v x) := rfl

theorem holderApply_norm (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) (v : HolderSpace K E α) :
    ‖holderApply α M v‖ ≤ 2*‖M‖*‖v‖ := by
  apply max_le
  · exact (sectionApply_norm _ _).trans ((mul_le_mul (holderValue_norm α M) (holderValue_norm α v)
      (norm_nonneg _) (norm_nonneg _)).trans (by nlinarith [norm_nonneg M,norm_nonneg v]))
  · refine (norm_add_le _ _).trans ?_
    have h1 := (sectionApply_norm (holderDifference α M) (pairLeft E (holderValue α v))).trans
      (mul_le_mul (holderDifference_norm α M) ((pairLeft_norm _).trans (holderValue_norm α v))
        (norm_nonneg _) (norm_nonneg _))
    have h2 := (sectionApply_norm (pairRight (E →L[ℝ] F) (holderValue α M)) (holderDifference α v)).trans
      (mul_le_mul ((pairRight_norm _).trans (holderValue_norm α M)) (holderDifference_norm α v)
        (norm_nonneg _) (norm_nonneg _))
    exact (add_le_add h1 h2).trans_eq (by ring)

def holderCLM (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) :
    HolderSpace K E α →L[ℝ] HolderSpace K F α :=
  LinearMap.mkContinuous
    { toFun := holderApply α M
      map_add' := by
        intro v w
        apply holderValue_injective α
        ext x
        exact (M.val.1 x).map_add _ _
      map_smul' := by
        intro c v
        apply holderValue_injective α
        ext x
        exact (M.val.1 x).map_smul c (v.val.1 x) }
    (2*‖M‖) (holderApply_norm α M)

@[simp] theorem holderCLM_apply (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α)
    (v : HolderSpace K E α) (x : K) :
    holderValue α (holderCLM α M v) x = holderValue α M x (holderValue α v x) := rfl

def holderOperatorLinear (α : ℝ) :
    HolderSpace K (E →L[ℝ] F) α →ₗ[ℝ] (HolderSpace K E α →L[ℝ] HolderSpace K F α) where
  toFun M := holderCLM α M
  map_add' := by
    intro M N
    apply ContinuousLinearMap.ext
    intro v
    apply holderValue_injective α
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' := by
    intro c M
    apply ContinuousLinearMap.ext
    intro v
    apply holderValue_injective α
    apply BoundedContinuousFunction.ext
    intro x
    rfl

theorem holderCLM_norm_bound (α : ℝ) (M : HolderSpace K (E →L[ℝ] F) α) :
    ‖holderCLM α M‖ ≤ 2*‖M‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (holderApply_norm α M)

def holderOperatorCLM (α : ℝ) :
    HolderSpace K (E →L[ℝ] F) α →L[ℝ] (HolderSpace K E α →L[ℝ] HolderSpace K F α) :=
  LinearMap.mkContinuous (holderOperatorLinear (K := K) (E := E) (F := F) α) 2
    (holderCLM_norm_bound α)

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {K E : Type*} [MetricSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holder_norm_le_of_estimate (α : ℝ) (u : HolderSpace K E α) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (h0 : ∀ x, ‖holderValue α u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue α u x-holderValue α u y‖ ≤ H*(dist x y)^α) :
    ‖u‖ ≤ max A H := by
  change max ‖u.val.1‖ ‖u.val.2‖ ≤ _
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hA).mpr h0
  · apply (BoundedContinuousFunction.norm_le hH).mpr
    intro z
    have hh := h1 z.val.1 z.val.2
    rw [holderSpace_relation α u _ _ z.property,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (mul_comm _ _))
      (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α)

 

lemma holder_third_interpolation (u : HolderSpace K E ((1:ℝ)/3)) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (h0 : ∀ x, ‖holderValue ((1:ℝ)/3) u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ L*dist x y) :
    ‖u‖ ≤ max A ((2*A)^((2:ℝ)/3)*L^((1:ℝ)/3)) := by
  apply holder_norm_le_of_estimate _ _ hA (by positivity) h0
  intro x y
  have hb : ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ 2*A :=
    (norm_sub_le _ _).trans (by linarith [h0 x,h0 y])
  calc
    ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ =
      ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖^((2:ℝ)/3)*
        ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖^((1:ℝ)/3) := by
          rw [←Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
          norm_num
    _ ≤ (2*A)^((2:ℝ)/3)*(L*dist x y)^((1:ℝ)/3) := by
      gcongr
      exact h1 x y
    _ = ((2*A)^((2:ℝ)/3)*L^((1:ℝ)/3))*(dist x y)^((1:ℝ)/3) := by
      rw [Real.mul_rpow hL dist_nonneg,mul_assoc]

lemma holder_third_small_sup (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : HolderSpace K E ((1:ℝ)/3),
      (∀ x, ‖holderValue ((1:ℝ)/3) u x‖ ≤ δ) →
      (∀ x y, ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ L*dist x y) →
      ‖u‖ < ε := by
  let φ : ℝ → ℝ := fun t => max t ((2*t)^((2:ℝ)/3)*L^((1:ℝ)/3))
  have hc : Continuous φ := continuous_id.max
    (((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)).comp
      (continuous_const.mul continuous_id)).mul continuous_const)
  have hφ : φ 0=0 := by simp [φ,Real.zero_rpow (by norm_num : (2:ℝ)/3≠0)]
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro u h0 h1
  have hh : φ (δ/2) < ε := by
    have ht := hd (show dist (δ/2) 0 < δ by simpa [Real.dist_eq,abs_of_pos (half_pos hδ),abs_of_pos hδ] using half_lt_self hδ)
    rw [hφ,dist_zero_right] at ht
    exact (le_abs_self _).trans_lt ht
  exact (holder_third_interpolation u (half_pos hδ).le hL h0 h1).trans_lt hh

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance

 

def holderLipschitzSet (R M : ℝ) (L : NNReal) : Set (HolderSpace ℂ E ((1:ℝ)/3)) :=
  {u | (∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) u x=0) ∧
    ‖holderValue ((1:ℝ)/3) u‖ ≤ M ∧ LipschitzWith L (holderValue ((1:ℝ)/3) u)}

def holderDiskRestrict (R : ℝ) :
    HolderSpace ℂ E ((1:ℝ)/3) →L[ℝ] (Metric.closedBall (0:ℂ) R →ᵇ E) :=
  (BoundedContinuousFunction.compContinuousCLM E ℝ ⟨Subtype.val,continuous_subtype_val⟩).comp
    (holderValue ((1:ℝ)/3))

@[simp] lemma holderDiskRestrict_apply (R : ℝ) (u : HolderSpace ℂ E ((1:ℝ)/3))
    (x : Metric.closedBall (0:ℂ) R) : holderDiskRestrict R u x=holderValue ((1:ℝ)/3) u x := rfl

lemma holderDiskRestrict_uniformInducing (R M : ℝ) (L : NNReal) :
    IsUniformInducing (fun u : holderLipschitzSet (E := E) R M L => holderDiskRestrict R u.val) := by
  rw [Metric.isUniformInducing_iff]
  refine ⟨(holderDiskRestrict (E := E) R).uniformContinuous.comp uniformContinuous_subtype_val,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := holder_third_small_sup (K := ℂ) (E := E) (2*L) ε (by positivity) hε
  refine ⟨δ,hδ,?_⟩
  intro u v huv
  rw [Subtype.dist_eq,dist_eq_norm]
  apply hd (u.val-v.val)
  · intro x
    simp only [map_sub,BoundedContinuousFunction.sub_apply]
    by_cases hx : ‖x‖≤R
    · let z : Metric.closedBall (0:ℂ) R := ⟨x,by simpa using hx⟩
      have hh := BoundedContinuousFunction.dist_coe_le_dist
        (f := holderDiskRestrict R u.val) (g := holderDiskRestrict R v.val) z
      have hh' : ‖holderValue ((1:ℝ)/3) u.val x - holderValue ((1:ℝ)/3) v.val x‖ ≤
          dist (holderDiskRestrict R u.val) (holderDiskRestrict R v.val) := by
        simpa only [dist_eq_norm,holderDiskRestrict_apply] using hh
      exact hh'.trans huv.le
    · rw [u.property.1 x (lt_of_not_ge hx),v.property.1 x (lt_of_not_ge hx),sub_self,norm_zero]
      exact hδ.le
  · intro x y
    have hh := (u.property.2.2.sub v.property.2.2).dist_le_mul x y
    simpa only [map_sub,BoundedContinuousFunction.sub_apply,Pi.sub_apply,dist_eq_norm,
      NNReal.coe_add,two_mul] using hh

 

lemma holderLipschitzSet_totallyBounded [ProperSpace E] (R M : ℝ) (L : NNReal) :
    TotallyBounded (holderLipschitzSet (E := E) R M L) := by
  let A := holderLipschitzSet (E := E) R M L
  let K := Metric.closedBall (0:ℂ) R
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) R)
  let f : A → K →ᵇ E := fun u => holderDiskRestrict R u.val
  have he : Equicontinuous ((↑) : Set.range f → K → E) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ L
    intro g
    obtain ⟨u,hu⟩ := g.property
    rw [←hu]
    change LipschitzWith L (fun x : K => holderValue ((1:ℝ)/3) u.val x.val)
    simpa only [mul_one,Function.comp_def] using u.property.2.2.comp (LipschitzWith.subtype_val K)
  have hc : IsCompact (closure (Set.range f)) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0:E) M) (isCompact_closedBall _ _) (Set.range f)
    (by
      intro g x hg
      obtain ⟨u,rfl⟩ := hg
      rw [Metric.mem_closedBall,dist_zero_right]
      exact ((holderValue ((1:ℝ)/3) u.val).norm_coe_le_norm x.val).trans u.property.2.1) he
  have ht : TotallyBounded (univ : Set A) :=
    (totallyBounded_image_iff (holderDiskRestrict_uniformInducing R M L)).mp
      (by simpa only [image_univ] using hc.totallyBounded.subset subset_closure)
  have hti := ht.image uniformContinuous_subtype_val
  simpa only [image_univ,Subtype.range_coe] using hti

lemma holderLipschitzSet_isCompact_closure [ProperSpace E] [CompleteSpace E]
    (R M : ℝ) (L : NNReal) : IsCompact (closure (holderLipschitzSet (E := E) R M L)) :=
  (holderLipschitzSet_totallyBounded R M L).closure.isCompact_of_isClosed isClosed_closure

end HigherDimensionalBallPacking.Rigidity

end

end OAI
