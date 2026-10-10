import Mathlib
import OAI.Geometry.BallPacking.Surfaces.QuadricOrientation

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
open scoped BigOperators
section
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
  (ε : Fin m → Bool)

def realInfinityChart : OpenPartialHomeomorph RealModel (locus a) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans (infinityChart a ε).symm

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_source :
    (realInfinityChart a ε).source=Complex.equivRealProdCLM.symm ⁻¹' infinityDomain a := by
  simp [realInfinityChart]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_target : (realInfinityChart a ε).target=infinityBranch a ε := by
  simp [realInfinityChart]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_apply (x : RealModel) :
    realInfinityChart a ε x=infinityInverse a ε (Complex.equivRealProdCLM.symm x) := rfl

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
@[simp] theorem realInfinityChart_symm_apply (x : locus a) :
    (realInfinityChart a ε).symm x=Complex.equivRealProdCLM x.val.1⁻¹ := rfl

theorem realInfinityChart_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realInfinityChart a ε) (realInfinityChart a ε).source := by
  intro x hx
  rw [realInfinityChart_source] at hx
  apply real_contMDiffWithinAt_of_ambient
  have hc := ((infinityPoint_contDiffAt a ε hx).restrict_scalars ℝ).comp x
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  apply hc.contDiffWithinAt.congr
  · intro y hy
    have hyD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
      simpa only [realInfinityChart_source,mem_preimage] using hy
    rw [realInfinityChart_apply,infinityInverse_val a ε hyD.1]
    rfl
  · rw [realInfinityChart_apply,infinityInverse_val a ε hx.1]
    rfl

theorem realInfinityChart_symm_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (realInfinityChart a ε).symm
      (realInfinityChart a ε).target := by
  intro x hx
  rw [realInfinityChart_target] at hx
  have hi : ContDiffAt ℂ ∞ (fun z : ℂ => z⁻¹) x.val.1 := contDiffAt_id.inv hx.1
  have hp := (ContinuousLinearMap.fst ℝ ℂ (Fin m → ℂ)).contDiff.contMDiff.comp
    (real_inclusion_contMDiff a)
  exact (Complex.equivRealProdCLM.contDiff.contMDiff.contMDiffAt.comp x
    (((hi.restrict_scalars ℝ).contMDiffAt).comp x hp.contMDiffAt)).contMDiffWithinAt

def infinityDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    RealModel (locus a) ∞ where
  __ := realInfinityChart a ε
  contMDiffOn_toFun := realInfinityChart_smooth a ε
  contMDiffOn_invFun := realInfinityChart_symm_smooth a ε

@[simp] theorem infinityDiffeomorph_source :
    (infinityDiffeomorph a ε).source=Complex.equivRealProdCLM.symm ⁻¹' infinityDomain a :=
  realInfinityChart_source a ε

@[simp] theorem infinityDiffeomorph_target :
    (infinityDiffeomorph a ε).target=infinityBranch a ε := realInfinityChart_target a ε

theorem infinity_transition_differentiable (c : locus a) {z : ℂ}
    (hz : z∈infinityDomain a) :
    DifferentiableAt ℂ (((normalChartAt a c).sliceChart c) ∘ (infinityChart a ε).symm) z := by
  let n := normalChartAt a c
  have hs := (curveCoordinate n.coordinate).contDiff.contDiffAt.comp z
    (infinityPoint_contDiffAt a ε hz)
  apply (hs.differentiableAt (by simp)).congr_of_eventuallyEq
  filter_upwards [(infinityDomain_open a).mem_nhds hz] with t ht
  change curveCoordinate n.coordinate ((infinityInverse a ε t).val)=_
  rw [infinityInverse_val a ε ht.1]
  rfl

theorem infinity_transition_inverse_differentiable (c : locus a) {z : ℂ}
    (hz : z∈((normalChartAt a c).sliceChart c).target)
    (hn : (((normalChartAt a c).sliceChart c).symm z).val.1≠0) :
    DifferentiableAt ℂ ((infinityChart a ε) ∘ ((normalChartAt a c).sliceChart c).symm) z := by
  have hs := ((normalChartAt a c).sliceChart_inverse_smooth c).contDiffAt
    (((normalChartAt a c).sliceChart c).open_target.mem_nhds hz)
  exact hs.differentiableAt (by simp) |>.fst |>.inv hn

theorem infinityDiffeomorph_positive : PositivePartialChart (infinityDiffeomorph a ε) := by
  intro c y hy hc
  let n := normalChartAt a c
  let e := (infinityChart a ε).symm.trans (n.sliceChart c)
  have hchart : chartAt Plane c=realChart a c := rfl
  have hc' : infinityDiffeomorph a ε y∈(n.sliceChart c).source := by
    simpa only [mfld_simps,hchart,realChart_source] using hc
  have hy' : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hye : Complex.equivRealProdCLM.symm y∈e.source := ⟨hy',hc'⟩
  have hn : (((n.sliceChart c).symm ((n.sliceChart c) (infinityDiffeomorph a ε y))).val.1)≠0 := by
    rw [(n.sliceChart c).left_inv hc']
    exact ((infinityChart a ε).map_target hy').1
  have h := holomorphic_partialHomeomorph_orientation e hye
    (infinity_transition_differentiable a ε c hy')
    (infinity_transition_inverse_differentiable a ε c (n.sliceChart c |>.map_source hc') hn)
  simpa only [e,mfld_simps,hchart,realChart,realInfinityChart,
    infinityDiffeomorph,Function.comp_def,OpenPartialHomeomorph.trans_apply,
    ContinuousLinearEquiv.coe_toHomeomorph] using h

end
section

variable {m : ℕ} {a : Fin m → ℂ}
namespace NormalChart
variable (e : NormalChart a) (x : locus a)

def inclusionChart (z : ℂ) : Affine m := (e.sliceChart x).symm z

theorem inclusionChart_smooth : ContDiffOn ℂ ∞ (e.inclusionChart x) (e.sliceChart x).target :=
  e.sliceChart_inverse_smooth x

theorem inclusionChart_coordinate {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    curveCoordinate e.coordinate (e.inclusionChart x z)=z :=
  (e.sliceChart x).right_inv hz

theorem inclusionChart_derivative_leftInverse {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    (curveCoordinate e.coordinate).comp (fderiv ℂ (e.inclusionChart x) z)=
      ContinuousLinearMap.id ℂ ℂ := by
  have hd := ((e.inclusionChart_smooth x).contDiffAt ((e.sliceChart x).open_target.mem_nhds hz)).differentiableAt (by simp)
  have hh : (curveCoordinate e.coordinate ∘ e.inclusionChart x)=ᶠ[𝓝 z] id := by
    filter_upwards [(e.sliceChart x).open_target.mem_nhds hz] with y hy
    exact e.inclusionChart_coordinate x hy
  simpa only [fderiv_comp z (curveCoordinate e.coordinate).differentiableAt hd,
    ContinuousLinearMap.fderiv,fderiv_id] using hh.fderiv_eq (𝕜 := ℂ)

theorem inclusionChart_derivative_injective {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    Injective (fderiv ℂ (e.inclusionChart x) z) := by
  intro v w hvw
  have h := congrArg (curveCoordinate e.coordinate) hvw
  have he := e.inclusionChart_derivative_leftInverse x hz
  have h' : ∀ u,curveCoordinate e.coordinate (fderiv ℂ (e.inclusionChart x) z u)=u :=
    fun u => congrArg (fun L : ℂ→L[ℂ]ℂ => L u) he
  rwa [h' v,h' w] at h

theorem inclusionChart_derivative_one_ne {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    fderiv ℂ (e.inclusionChart x) z 1≠0 := by
  intro h
  exact one_ne_zero ((e.inclusionChart_derivative_injective x hz) (by simpa using h))

end NormalChart

end
section

variable {m : ℕ}

def projectionDomain (a : Fin m → ℂ) (R : ℝ) : Set (locus a) :=
  {x | ‖x.val.1‖≤R}

theorem projectionDomain_closed (a : Fin m → ℂ) (R : ℝ) :
    IsClosed (projectionDomain a R) :=
  isClosed_le ((continuous_fst.comp continuous_subtype_val).norm) continuous_const

theorem fibre_norm_bound {a : Fin m → ℂ} {x : Affine m} (hx : x∈locus a)
    {R : ℝ} (hR : 0≤R) (ht : ‖x.1‖≤R) (j : Fin m) :
    ‖x.2 j‖≤R^2+‖a j‖+1 := by
  have he := congrArg norm (mem_locus.mp hx j)
  rw [norm_pow] at he
  have hle := norm_sub_le (x.1^2) (a j)
  rw [norm_pow,←he] at hle
  have ht2 : ‖x.1‖^2≤R^2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr ht
  have hA : 0≤R^2+‖a j‖ := add_nonneg (sq_nonneg R) (norm_nonneg _)
  nlinarith [sq_nonneg (‖x.2 j‖-1),norm_nonneg (x.2 j)]

theorem projectionDomain_compact (a : Fin m → ℂ) (R : ℝ) :
    IsCompact (projectionDomain a R) := by
  by_cases hR : 0≤R
  · let A : ℝ := R^2+∑ j,‖a j‖+1
    let S : Set (Affine m) := locus a ∩ {x | ‖x.1‖≤R}
    have hc : IsClosed S := (locus_isClosed a).inter (isClosed_le continuous_fst.norm continuous_const)
    have hb : Bornology.IsBounded S := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨max R A,?_⟩
      intro x hx
      rw [Prod.norm_def]
      apply max_le
      · exact hx.2.trans (le_max_left _ _)
      · apply (pi_norm_le_iff_of_nonneg (le_trans (by positivity : 0≤R) (le_max_left R A))).mpr
        intro j
        have ha : ‖a j‖≤∑ k,‖a k‖ := Finset.single_le_sum (fun k _ => norm_nonneg (a k)) (Finset.mem_univ j)
        exact (fibre_norm_bound hx.1 hR hx.2 j).trans
          ((by dsimp [A]; linarith : R^2+‖a j‖+1≤A).trans (le_max_right _ _))
    have hcomp : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc,hb⟩
    have hpre := (locus_isClosed a).isClosedEmbedding_subtypeVal.isCompact_preimage hcomp
    convert hpre using 1
    ext x
    change (‖x.val.1‖≤R) ↔ (x.val∈locus a ∧ ‖x.val.1‖≤R)
    exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  · have he : projectionDomain a R=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hR ((norm_nonneg x.val.1).trans hx)
    rw [he]
    exact isCompact_empty

theorem projectionDomain_nested (a : Fin m → ℂ) {R S : ℝ} (hRS : R<S) :
    projectionDomain a R⊆interior (projectionDomain a S) := by
  have ho : IsOpen {x : locus a | ‖x.val.1‖<S} :=
    isOpen_lt ((continuous_fst.comp continuous_subtype_val).norm) continuous_const
  have hs : {x : locus a | ‖x.val.1‖<S}⊆projectionDomain a S := fun x (hx : ‖x.val.1‖<S) => hx.le
  intro x hx
  exact interior_maximal hs ho (lt_of_le_of_lt hx hRS)

theorem projectionDomain_cover (a : Fin m → ℂ) (R : ℝ) :
    (⋃ ℓ : ℕ,projectionDomain a (R+ℓ))=univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨ℓ,hℓ⟩ := exists_nat_gt (‖x.val.1‖-R)
  exact mem_iUnion.mpr ⟨ℓ,by change ‖x.val.1‖≤R+ℓ; linarith⟩

end

variable {m : ℕ} {a : Fin m → ℂ}

def curveProjection (a : Fin m → ℂ) (x : locus a) : ℂ := x.val.1

theorem curveProjection_continuous (a : Fin m → ℂ) : Continuous (curveProjection a) :=
  continuous_fst.comp continuous_subtype_val

theorem curveProjection_proper (a : Fin m → ℂ) : IsProperMap (curveProjection a) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨curveProjection_continuous a,?_⟩
  intro K hK
  obtain ⟨R,_hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  exact (projectionDomain_compact a R).of_isClosed_subset
    (hK.isClosed.preimage (curveProjection_continuous a)) (fun x hx => hbound _ hx)

private theorem square_not_locally_constant (z c : ℂ) :
    ¬ ∀ᶠ w in 𝓝 z,w^2=c := by
  intro h
  have hf : AnalyticOnNhd ℂ (fun w : ℂ => w^2) univ := fun w _ => analyticAt_id.pow 2
  have he : (fun w : ℂ => w^2)=(fun _ : ℂ => c) :=
    hf.eq_of_eventuallyEq analyticOnNhd_const h
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  norm_num at h0 h1
  exact zero_ne_one (h0.trans h1.symm)

namespace NormalChart
variable (e : NormalChart a) (x : locus a)

theorem projectionChart_nonconstant {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    ¬ ∀ᶠ w in 𝓝 z,(e.inclusionChart x w).1=(e.inclusionChart x z).1 := by
  intro h
  have hc : ∀ᶠ w in 𝓝 z,curveCoordinate e.coordinate (e.inclusionChart x w)=w := by
    filter_upwards [(e.sliceChart x).open_target.mem_nhds hz] with w hw
    exact e.inclusionChart_coordinate x hw
  cases he : e.coordinate with
  | none =>
    have hh : ∀ᶠ w in 𝓝 z,w^2=((e.inclusionChart x z).1)^2 := by
      filter_upwards [h,hc] with w hw hc
      rw [he] at hc
      change (e.inclusionChart x w).1=w at hc
      rw [← hc,hw]
    exact square_not_locally_constant z _ hh
  | some j =>
    have hh : ∀ᶠ w in 𝓝 z,w^2=((e.inclusionChart x z).1)^2-a j := by
      filter_upwards [h,hc] with w hw hc
      rw [he] at hc
      change (e.inclusionChart x w).2 j=w at hc
      rw [← hc]
      have hmem := mem_locus.mp ((e.sliceChart x).symm w).property j
      change (e.inclusionChart x w).2 j ^ 2=(e.inclusionChart x w).1^2-a j at hmem
      rw [hmem,hw]
    exact square_not_locally_constant z _ hh

theorem projectionChart_open_at {z : ℂ} (hz : z∈(e.sliceChart x).target) :
    𝓝 ((e.inclusionChart x z).1) ≤ map (fun w => (e.inclusionChart x w).1) (𝓝 z) := by
  have hd := ((e.inclusionChart_smooth x).fst.differentiableOn (by simp)).analyticOnNhd
    (e.sliceChart x).open_target
  exact (hd z hz).eventually_constant_or_nhds_le_map_nhds.resolve_left
    (e.projectionChart_nonconstant x hz)
end NormalChart

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveProjection_open : IsOpenMap (curveProjection a) := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  let e := (normalChartAt a x).sliceChart x
  have hx : x∈e.source := mem_normalChartAt a x
  have h := (normalChartAt a x).projectionChart_open_at x (e.map_source hx)
  change 𝓝 (curveProjection a (e.symm (e x))) ≤ map (curveProjection a ∘ e.symm) (𝓝 (e x)) at h
  rw [e.left_inv hx,← map_map,e.symm_map_nhds_eq hx] at h
  exact h

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter Bornology

def inverseComplementCutoff (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  if z=0 then 1 else 1-f z⁻¹

theorem inverseComplementCutoff_one_near_zero {f : ℂ → ℝ} (hc : HasCompactSupport f) :
    inverseComplementCutoff f=ᶠ[𝓝 0] fun _ => 1 := by
  have he : f=ᶠ[cobounded ℂ] 0 := by
    simpa only [Metric.cobounded_eq_cocompact,coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp hc
  have hp := he.comp_tendsto (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  filter_upwards [eventually_nhdsWithin_iff.mp hp] with z hz
  by_cases h : z=0
  · simp only [inverseComplementCutoff,h,↓reduceIte]
  · have hzero : f z⁻¹=0 := hz h
    simp only [inverseComplementCutoff,h,↓reduceIte,hzero,sub_zero]

theorem inverseComplementCutoff_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (inverseComplementCutoff f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    exact contDiffAt_const.congr_of_eventuallyEq (inverseComplementCutoff_one_near_zero hc)
  · have he : inverseComplementCutoff f=ᶠ[𝓝 z] fun w => 1-f w⁻¹ := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
      exact ite_eq_right (show w≠0 from hw)
    exact (contDiffAt_const.sub (hf.contDiffAt.comp z (contDiffAt_inv ℝ hz))).congr_of_eventuallyEq he

theorem inverseComplementCutoff_compact {f : ℂ → ℝ} (h1 : f=ᶠ[𝓝 0] fun _ => 1) :
    HasCompactSupport (inverseComplementCutoff f) := by
  apply hasCompactSupport_iff_eventuallyEq.mpr
  rw [coclosedCompact_eq_cocompact]
  have hi : Tendsto (Inv.inv : ℂ → ℂ) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hn : ∀ᶠ z : ℂ in cocompact ℂ,z≠0 :=
    isCompact_singleton.compl_mem_cocompact
  filter_upwards [h1.comp_tendsto hi,hn] with z hz hnz
  have hval : f z⁻¹=1 := hz
  simp only [inverseComplementCutoff,hnz,↓reduceIte,hval,sub_self,Pi.zero_apply]

theorem inverseComplementCutoff_range {f : ℂ → ℝ} (hf : ∀ z,f z∈Icc (0:ℝ) 1) (z : ℂ) :
    inverseComplementCutoff f z∈Icc (0:ℝ) 1 := by
  by_cases hz : z=0
  · simp [inverseComplementCutoff,hz]
  · simp only [inverseComplementCutoff,hz,↓reduceIte,mem_Icc]
    have h := hf z⁻¹
    constructor <;> linarith [h.1,h.2]

theorem complex_normSq_smooth : ContDiff ℝ ∞ (Complex.normSq : ℂ → ℝ) := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re+z.im*z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem HasCompactSupport.comp_complex_normSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : ℂ => g (Complex.normSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (B+1))
  intro z hz
  by_contra hgz
  have hb := hbound (Complex.normSq z) (subset_tsupport g hgz)
  rw [Real.norm_eq_abs,abs_of_nonneg (Complex.normSq_nonneg z),Complex.normSq_eq_norm_sq] at hb
  apply hz
  rw [Metric.mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg z,sq_nonneg (‖z‖-1)]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveProjection_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℂ) ∞ (curveProjection a) :=
  (ContinuousLinearMap.fst ℝ ℂ (Fin m → ℂ)).contDiff.contMDiff.comp
    (real_inclusion_contMDiff a)

def curveEndCutoff (g : ℝ → ℝ) (x : locus a) : ℝ :=
  inverseComplementCutoff (fun z : ℂ => g (Complex.normSq z)) (curveProjection a x)

theorem curveEndCutoff_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,ℝ) ∞ (curveEndCutoff a g) :=
  (inverseComplementCutoff_smooth (hg.comp complex_normSq_smooth)
    (HasCompactSupport.comp_complex_normSq hc)).contMDiff.comp (curveProjection_smooth a)

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_compact {g : ℝ → ℝ} (h1 : g=ᶠ[𝓝 0] fun _ => 1) :
    HasCompactSupport (curveEndCutoff a g) := by
  have hn : (fun z : ℂ => g (Complex.normSq z))=ᶠ[𝓝 0] fun _ => 1 :=
    h1.comp_tendsto (by
      have ht := complex_normSq_smooth.continuous.continuousAt (x := (0:ℂ))
      change Tendsto (Complex.normSq : ℂ → ℝ) (𝓝 0) (𝓝 (Complex.normSq 0)) at ht
      simpa only [map_zero] using ht)
  have hc := inverseComplementCutoff_compact hn
  apply HasCompactSupport.intro ((curveProjection_proper a).isCompact_preimage hc)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := inverseComplementCutoff (fun z : ℂ => g (Complex.normSq z))) hx

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_range {g : ℝ → ℝ} (hg : ∀ t,g t∈Icc (0:ℝ) 1) (x : locus a) :
    curveEndCutoff a g x∈Icc (0:ℝ) 1 :=
  inverseComplementCutoff_range (fun z => hg (Complex.normSq z)) _

theorem curveEndCutoff_infinity (g : ℝ → ℝ) (ε : Fin m → Bool) {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) :
    curveEndCutoff a g (infinityDiffeomorph a ε y)=1-g (radiusSq y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hval : (infinityDiffeomorph a ε y).val=infinityPoint a ε (Complex.equivRealProdCLM.symm y) :=
    infinityInverse_val a ε hD.1
  unfold curveEndCutoff inverseComplementCutoff curveProjection
  rw [hval]
  simp only [infinityPoint,inv_ne_zero hD.1,↓reduceIte,inv_inv]
  congr 2
  change y.1*y.1+y.2*y.2=y.1^2+y.2^2
  ring

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
