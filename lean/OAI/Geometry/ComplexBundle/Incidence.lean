import OAI.Geometry.ComplexBundle.GrassmannManifold
import OAI.Geometry.ComplexBundle.Kernel

namespace OAI

noncomputable section

/-! Linear incidence equations and their graph-coordinate kernel bundles. -/

section
open Module
namespace Kaplansky.Incidence
variable {E F V : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]

def restrictQuotient (S : Submodule ℂ E) (U : Submodule ℂ F) :
    (E →ₗ[ℂ] F) →ₗ[ℂ] (S →ₗ[ℂ] F ⧸ U) where
  toFun T := U.mkQ.comp (T.comp S.subtype)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem restrictQuotient_surjective (S : Submodule ℂ E) (U : Submodule ℂ F) :
    Function.Surjective (restrictQuotient S U) := by
  obtain ⟨C,hC⟩ := S.exists_isCompl
  obtain ⟨lift,hlift⟩ := U.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr U.mkQ_surjective)
  intro T
  refine ⟨lift.comp (T.comp (S.projectionOnto C hC)),?_⟩
  ext x
  change U.mkQ (lift (T (S.projectionOnto C hC x.val)))=T x
  rw [Submodule.projectionOnto_apply_left]
  exact congrArg (fun L : (F ⧸ U) →ₗ[ℂ] (F ⧸ U) => L (T x)) hlift

/-- The q-fold evaluation/restriction/quotient map used by the incidence locus. -/
def tupleRestriction {q : ℕ} (S : Submodule ℂ E) (U : Submodule ℂ F)
    (ev : V →ₗ[ℂ] (Fin q → E →ₗ[ℂ] F)) :
    V →ₗ[ℂ] (Fin q → S →ₗ[ℂ] F ⧸ U) where
  toFun v i := restrictQuotient S U (ev v i)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem tupleRestriction_surjective {q : ℕ} (S : Submodule ℂ E) (U : Submodule ℂ F)
    (ev : V →ₗ[ℂ] (Fin q → E →ₗ[ℂ] F)) (hev : Function.Surjective ev) :
    Function.Surjective (tupleRestriction S U ev) := by
  intro T
  choose L hL using (fun i => restrictQuotient_surjective S U (T i))
  obtain ⟨v,hv⟩ := hev L
  refine ⟨v,?_⟩
  funext i
  change restrictQuotient S U (ev v i)=T i
  rw [hv,hL]

theorem mem_tupleRestriction_ker {q : ℕ} (S : Submodule ℂ E) (U : Submodule ℂ F)
    (ev : V →ₗ[ℂ] (Fin q → E →ₗ[ℂ] F)) (v : V) :
    v ∈ LinearMap.ker (tupleRestriction S U ev) ↔
      ∀ i, ∀ x ∈ S, ev v i x ∈ U := by
  change (fun i => U.mkQ.comp ((ev v i).comp S.subtype))=0 ↔ _
  constructor
  · intro h i x hx
    have he := congrArg (fun T : Fin q → S →ₗ[ℂ] F ⧸ U => T i ⟨x,hx⟩) h
    exact (Submodule.Quotient.mk_eq_zero U).mp he
  · intro h
    funext i
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero U).mpr (h i x.val x.property)

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem incidence_target_finrank (q : ℕ) (S : Submodule ℂ E) (U : Submodule ℂ F) :
    finrank ℂ (Fin q → S →ₗ[ℂ] F ⧸ U)=
      q * finrank ℂ S * (finrank ℂ F-finrank ℂ U) := by
  have hU := U.finrank_quotient_add_finrank
  have hQ : finrank ℂ (F ⧸ U)=finrank ℂ F-finrank ℂ U := by omega
  simp [Module.finrank_pi_fintype,Module.finrank_linearMap,hQ, Nat.mul_assoc]

/-- Exact rank-nullity for the actual incidence fiber in the parameter space V. -/
theorem incidence_kernel_finrank [FiniteDimensional ℂ V] {q : ℕ}
    (S : Submodule ℂ E) (U : Submodule ℂ F)
    (ev : V →ₗ[ℂ] (Fin q → E →ₗ[ℂ] F)) (hev : Function.Surjective ev) :
    finrank ℂ (LinearMap.ker (tupleRestriction S U ev))=
      finrank ℂ V-q * finrank ℂ S * (finrank ℂ F-finrank ℂ U) := by
  have h := (tupleRestriction S U ev).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (tupleRestriction_surjective S U ev hev),
    finrank_top, incidence_target_finrank] at h
  omega

theorem incidence_kernel_real_finrank [FiniteDimensional ℂ V] {q : ℕ}
    (S : Submodule ℂ E) (U : Submodule ℂ F)
    (ev : V →ₗ[ℂ] (Fin q → E →ₗ[ℂ] F)) (hev : Function.Surjective ev) :
    finrank ℝ (LinearMap.ker (tupleRestriction S U ev))=
      2*(finrank ℂ V-q * finrank ℂ S * (finrank ℂ F-finrank ℂ U)) := by
  rw [finrank_real_of_complex,incidence_kernel_finrank S U ev hev]

end Kaplansky.Incidence

end

section
open scoped ContDiff
namespace Kaplansky.Incidence
variable {s k t l : ℕ}
open ComplexGrassmann

/-- The quotient coordinate of a graph t-plane, (u,v) ↦ v-bu. -/
def graphQuotient (b : GraphSlope t l) : GraphAmbient t l →L[ℂ] GraphVertical l :=
  ContinuousLinearMap.snd ℂ _ _ - b.comp (ContinuousLinearMap.fst ℂ _ _)

@[simp] theorem graphQuotient_apply (b : GraphSlope t l) (v : GraphAmbient t l) :
    graphQuotient b v=v.2-b v.1 := rfl

theorem graphQuotient_zero_iff (b : GraphSlope t l) (v : GraphAmbient t l) :
    graphQuotient b v=0 ↔ v ∈ b.toLinearMap.graph := sub_eq_zero

theorem graphQuotient_surjective (b : GraphSlope t l) : Function.Surjective (graphQuotient b) := by
  intro w
  exact ⟨(0,w),by simp⟩

def graphRestriction (a : GraphSlope s k) (b : GraphSlope t l) :
    (GraphAmbient s k →L[ℂ] GraphAmbient t l) →L[ℂ]
      (GraphHorizontal s →L[ℂ] GraphVertical l) :=
  ((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient t l) (GraphVertical l))
    (graphQuotient b)).comp
      ((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient s k) (GraphAmbient t l)).flip
        (graphInclusion a))

@[simp] theorem graphRestriction_apply (a : GraphSlope s k) (b : GraphSlope t l)
    (T : GraphAmbient s k →L[ℂ] GraphAmbient t l) (v : GraphHorizontal s) :
    graphRestriction a b T v=graphQuotient b (T (v,a v)) := by
  simp [graphRestriction]

/-- The zero equation for these smooth coordinates is exactly preservation of
S into U, with S and U the actual graph subspaces. -/
theorem graphRestriction_zero_iff (a : GraphSlope s k) (b : GraphSlope t l)
    (T : GraphAmbient s k →L[ℂ] GraphAmbient t l) :
    graphRestriction a b T=0 ↔ ∀ v ∈ a.toLinearMap.graph, T v ∈ b.toLinearMap.graph := by
  constructor
  · intro h v hv
    have he := congrArg (fun Q : GraphHorizontal s →L[ℂ] GraphVertical l => Q v.1) h
    have hv' : v.2=a v.1 := hv
    have hvv : (v.1,a v.1)=v := Prod.ext rfl hv'.symm
    rw [graphRestriction_apply,hvv] at he
    exact (graphQuotient_zero_iff b (T v)).mp he
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    simpa only [graphRestriction_apply,zero_apply] using
      (graphQuotient_zero_iff b (T (v,a v))).mpr (h _ rfl)

/-- A concrete right inverse: place the requested quotient map in the lower
left block and set all other blocks to zero. -/
theorem graphRestriction_surjective (a : GraphSlope s k) (b : GraphSlope t l) :
    Function.Surjective (graphRestriction a b) := by
  intro C
  refine ⟨(ContinuousLinearMap.inr ℂ _ _).comp
    (C.comp (ContinuousLinearMap.fst ℂ _ _)),?_⟩
  ext v
  simp [graphRestriction_apply]

theorem graphQuotient_smooth : ContDiff ℂ ∞ (graphQuotient (t := t) (l := l)) :=
  contDiff_const.sub (contDiff_id.clm_comp contDiff_const)

theorem graphInclusion_smooth : ContDiff ℂ ∞ (graphInclusion (s := s) (k := k)) :=
  contDiff_const.add (contDiff_const.clm_comp contDiff_id)

theorem graphRestriction_smooth : ContDiff ℂ ∞
    (fun p : GraphSlope s k × GraphSlope t l => graphRestriction p.1 p.2) := by
  have hq : ContDiff ℂ ∞ (fun p : GraphSlope s k × GraphSlope t l => graphQuotient p.2) :=
    graphQuotient_smooth.comp contDiff_snd
  have hi : ContDiff ℂ ∞ (fun p : GraphSlope s k × GraphSlope t l => graphInclusion p.1) :=
    graphInclusion_smooth.comp contDiff_fst
  exact (((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient t l)
    (GraphVertical l)).contDiff.comp hq)).clm_comp
    (((ContinuousLinearMap.compL ℂ (GraphHorizontal s) (GraphAmbient s k)
      (GraphAmbient t l)).flip.contDiff).comp hi)

theorem graphRestriction_smooth_real : ContDiff ℝ ∞
    (fun p : GraphSlope s k × GraphSlope t l => graphRestriction p.1 p.2) :=
  (graphRestriction_smooth (s := s) (k := k) (t := t) (l := l)).restrict_scalars ℝ

end Kaplansky.Incidence

end

open scoped ContDiff Manifold
namespace Kaplansky.Incidence
open ComplexGrassmann SmoothKernel
variable {s k t l q : ℕ}

abbrev TupleAmbient (q s k t l : ℕ) :=
  Fin q → GraphAmbient s k →L[ℂ] GraphAmbient t l
abbrev TupleTarget (q s l : ℕ) := Fin q → GraphHorizontal s →L[ℂ] GraphVertical l

def tupleGraphRestriction (a : GraphSlope s k) (b : GraphSlope t l) :
    TupleAmbient q s k t l →L[ℂ] TupleTarget q s l :=
  ContinuousLinearMap.pi (fun i => (graphRestriction a b).comp (ContinuousLinearMap.proj i))

theorem tupleGraphRestriction_surjective (a : GraphSlope s k) (b : GraphSlope t l) :
    Function.Surjective (tupleGraphRestriction (q := q) a b) := by
  intro C
  choose T hT using fun i => graphRestriction_surjective a b (C i)
  exact ⟨T,funext hT⟩

theorem tupleGraphRestriction_smooth : ContDiff ℂ ∞
    (fun p : GraphSlope s k × GraphSlope t l => tupleGraphRestriction (q := q) p.1 p.2) := by
  apply contDiff_clm_apply_iff.mpr
  intro T
  apply contDiff_pi.mpr
  intro i
  exact graphRestriction_smooth.clm_apply contDiff_const

theorem tupleTarget_finrank : Module.finrank ℂ (TupleTarget q s l)=q*s*l := by
  have h : Module.finrank ℂ (GraphHorizontal s →L[ℂ] GraphVertical l)=s*l :=
    graph_slope_complex_finrank
  simp [TupleTarget,Module.finrank_pi_fintype,h,Nat.mul_assoc]

variable {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (ev : Y → V →L[ℂ] TupleAmbient q s k t l)

/-- The actual linear family whose zero set is the local incidence locus. -/
def graphEvaluation (p : Y × (GraphSlope s k × GraphSlope t l)) : V →L[ℂ] TupleTarget q s l :=
  (tupleGraphRestriction p.2.1 p.2.2).comp (ev p.1)

theorem graphEvaluation_smooth (he : ContDiff ℝ ∞ ev) : ContDiff ℝ ∞ (graphEvaluation ev) := by
  have hc : ContDiff ℂ ∞ (fun p :
      (TupleAmbient q s k t l →L[ℂ] TupleTarget q s l) × (V →L[ℂ] TupleAmbient q s k t l) =>
      p.1.comp p.2) := contDiff_fst.clm_comp contDiff_snd
  exact (hc.restrict_scalars ℝ).comp
    (((tupleGraphRestriction_smooth (q := q) (s := s) (k := k) (t := t) (l := l)).restrict_scalars ℝ).comp
      contDiff_snd |>.prodMk (he.comp contDiff_fst))

def graphFamily (he : ContDiff ℝ ∞ ev) (hs : ∀ y, Function.Surjective (ev y)) :
    SurjectiveFamily (Y × (GraphSlope s k × GraphSlope t l)) V (TupleTarget q s l) where
  map := graphEvaluation ev
  continuous := (graphEvaluation_smooth ev he).continuous
  surjective p := (tupleGraphRestriction_surjective p.2.1 p.2.2).comp (hs p.1)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
theorem graphEvaluation_zero_iff (p : Y × (GraphSlope s k × GraphSlope t l)) (v : V) :
    graphEvaluation ev p v=0 ↔ ∀ i, ∀ x ∈ p.2.1.toLinearMap.graph,
      ev p.1 v i x ∈ p.2.2.toLinearMap.graph := by
  constructor
  · intro h i
    have hi := congrArg (fun T : TupleTarget q s l => T i) h
    exact (graphRestriction_zero_iff p.2.1 p.2.2 (ev p.1 v i)).mp hi
  · intro h
    funext i
    exact (graphRestriction_zero_iff p.2.1 p.2.2 (ev p.1 v i)).mpr (h i)

variable [FiniteDimensional ℂ V]

theorem graph_kernel_finrank (he : ContDiff ℝ ∞ ev) (hs : ∀ y, Function.Surjective (ev y))
    (p : Y × (GraphSlope s k × GraphSlope t l)) :
    Module.finrank ℂ (LinearMap.ker (graphEvaluation ev p).toLinearMap)=
      Module.finrank ℂ V-q*s*l := by
  have h := (graphFamily ev he hs).kernel_finrank p
  change Module.finrank ℂ (LinearMap.ker (graphEvaluation ev p).toLinearMap) =
    Module.finrank ℂ V - Module.finrank ℂ (TupleTarget q s l) at h
  rw [tupleTarget_finrank] at h
  exact h

theorem graph_kernel_bundle_smooth (he : ContDiff ℝ ∞ ev) (hs : ∀ y, Function.Surjective (ev y)) :
    (graphFamily ev he hs).realCore.IsContMDiff
      𝓘(ℝ,Y × (GraphSlope s k × GraphSlope t l)) ∞ :=
  (graphFamily ev he hs).realCore_isContMDiff (graphEvaluation_smooth ev he)

omit [FiniteDimensional ℂ V] in
theorem incidence_model_finrank [FiniteDimensional ℝ Y] : Module.finrank ℝ
    ((Y × (GraphSlope s k × GraphSlope t l)) × KernelModel V (TupleTarget q s l))=
      Module.finrank ℝ Y+2*s*k+2*t*l+2*(Module.finrank ℂ V-q*s*l) := by
  simp only [Module.finrank_prod,graph_slope_real_finrank,
    SurjectiveFamily.kernel_model_real_finrank,tupleTarget_finrank]
  omega

end Kaplansky.Incidence

end

end OAI
