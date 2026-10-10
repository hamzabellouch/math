import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularCurvaturePrimitive

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem annularCylinderScalar_differential_cover {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) (v : Plane) :
    manifoldScalarDifferential (E := CylinderModel) (annularCylinderScalar F p) (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=
      fderiv ℝ (fun z => F (p,z)) q v := by
  have hs := annularCylinderScalar_smoothAt hV hI hF hper hp (z := cylinderCover q) hq
  have hd := mfderiv_comp q (hs.mdifferentiableAt (by simp))
    (cylinderCover_smooth.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have he : (annularCylinderScalar F p ∘ cylinderCover) =ᶠ[𝓝 q] (fun z => F (p,z)) := by
    filter_upwards [(hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ from ⟨hq,mem_univ _⟩)] with z hz
    exact annularScalarDescent_turn (hper p hp z.1 hz.1) z.2
  rw [he.fderiv_eq] at hd
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L v) hd.symm

variable [FiniteDimensional ℝ P]

theorem normalized_annular_scalar_intrinsic {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hclosed : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0)) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent (normalizedAnnularPrimitive a A B β)) ((V ×ˢ I) ×ˢ univ) ∧
    (∀ p∈V,∀ z : HandleCylinder,z.1∈I → ∀ v : CylinderModel,
      manifoldScalarDifferential (E := CylinderModel) (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) z v=
        annularCylinderScalar A p z*v.1+
          (annularCylinderScalar B p z-annularMean a B p*circlePeriodicDescent β z.2)*
            circleAngular z.2 v.2) := by
  obtain ⟨hF,hFp,hFd⟩ := annular_normalization hV hI hc ha hA hB hβ hpβ hβint hpA hpB hclosed
  refine ⟨annularScalarDescent_smoothOn hV hI hF hFp,?_⟩
  intro p hp z hz v
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  let u : Plane := (v.1,circleAngular (circleTurn q.2) v.2)
  have hd := annularCylinderScalar_differential_cover hV hI hF hFp hp (q := q) hz u
  have hL : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u=v :=
    cylinderCover_derivative_right_inverse q v
  have hval : manifoldScalarDifferential (E := CylinderModel)
      (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) (cylinderCover q) v=
      A (p,q)*u.1+(B (p,q)-annularMean a B p*β q.2)*u.2 := by
    calc
      _ = manifoldScalarDifferential (E := CylinderModel)
          (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) (cylinderCover q)
          (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u) := congrArg _ hL.symm
      _ = _ := hd.trans (hFd p hp q hz u)
  have hAv : annularCylinderScalar A p (cylinderCover q)=A (p,q) :=
    annularScalarDescent_turn (hpA p hp q.1 hz) q.2
  have hBv : annularCylinderScalar B p (cylinderCover q)=B (p,q) :=
    annularScalarDescent_turn (hpB p hp q.1 hz) q.2
  have hβv := circlePeriodicDescent_turn hpβ q.2
  rw [← hq,hAv,hBv]
  change _=A (p,q)*v.1+(B (p,q)-annularMean a B p*circlePeriodicDescent β (circleTurn q.2))*
    circleAngular (circleTurn q.2) v.2
  rw [hβv]
  exact hval


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem closed_cylinder_cover_equation {I : Set ℝ} (hI : IsOpen I)
    {α : ManifoldOneForm CylinderModel HandleCylinder} {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ))
    (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ))
    (hα : ∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm α (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)))
    (hclosed : ∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm α z=0)
    (hrep : ∀ q : Plane,q.1∈I →
      euclideanPullbackOneForm (fun _ => α) cylinderCover (0,q)=planarCovector (A q) (B q))
    {q : Plane} (hq : q.1∈I) :
    fderiv ℝ A q (0,1)=fderiv ℝ B q (1,0) := by
  have hn := (hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ from ⟨hq,mem_univ _⟩)
  have he : (fun y => euclideanPullbackOneForm (fun _ => α) cylinderCover (0,y))
      =ᶠ[𝓝 q] (fun y => planarCovector (A y) (B y)) := by
    filter_upwards [hn] with y hy
    exact hrep y hy.1
  have hd := euclidean_manifold_pullback_exterior_at
    (g := cylinderCover) cylinderCover_smooth.contMDiffAt (hα q hq)
  rw [hclosed (cylinderCover q) hq] at hd
  have hz : euclideanExteriorOneForm (fun y => planarCovector (A y) (B y)) q=0 := by
    have hder : fderiv ℝ (fun y => euclideanPullbackOneForm (fun _ => α) cylinderCover (0,y)) q=
        fderiv ℝ (fun y => planarCovector (A y) (B y)) q := he.fderiv_eq
    unfold euclideanExteriorOneForm at hd ⊢
    rw [hder] at hd
    exact hd
  rw [planarCovector_exterior_at (hA.contDiffAt hn) (hB.contDiffAt hn)] at hz
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ => Ω (1,0) (0,1)) hz
  simp only [smul_apply,smul_eq_mul,planarArea_apply,mul_one,mul_zero,
    sub_zero,zero_apply] at hv
  linarith

variable [FiniteDimensional ℝ P]

theorem closed_cylinder_normalized_potential {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    {A B : P × Plane → ℝ} {β : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ)))
    (hβ : ContDiff ℝ ∞ β) (hpβ : Periodic β 1)
    (hβint : (∫ t in (0:ℝ)..1,β t)=1)
    (hpA : ∀ p∈V,∀ s∈I,Periodic (fun t => A (p,(s,t))) 1)
    (hpB : ∀ p∈V,∀ s∈I,Periodic (fun t => B (p,(s,t))) 1)
    (hα : ∀ p∈V,∀ q : Plane,q.1∈I → ContDiffAt ℝ ∞
      (chartOneForm (α p) (cylinderCover q))
      (extChartAt 𝓘(ℝ,CylinderModel) (cylinderCover q) (cylinderCover q)))
    (hclosed : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → manifoldExteriorOneForm (α p) z=0)
    (hrep : ∀ p∈V,∀ q : Plane,q.1∈I →
      euclideanPullbackOneForm (fun _ => α p) cylinderCover (0,q)=
        planarCovector (A (p,q)) (B (p,q))) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent (normalizedAnnularPrimitive a A B β)) ((V ×ˢ I) ×ˢ univ) ∧
    (∀ p∈V,∀ z : HandleCylinder,z.1∈I → ∀ v : CylinderModel,
      manifoldScalarDifferential (E := CylinderModel)
        (annularCylinderScalar (normalizedAnnularPrimitive a A B β) p) z v=
          α p z v-annularMean a B p*circlePeriodicDescent β z.2*circleAngular z.2 v.2) := by
  have hc' : ∀ p∈V,∀ s∈I,∀ t,
      fderiv ℝ (fun z => A (p,z)) (s,t) (0,1)=
      fderiv ℝ (fun z => B (p,z)) (s,t) (1,0) := by
    intro p hp s hs t
    exact closed_cylinder_cover_equation hI
      (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩))
      (hα p hp) (hclosed p hp) (hrep p hp) hs
  obtain ⟨hs,hd⟩ := normalized_annular_scalar_intrinsic hV hI hc ha hA hB
    hβ hpβ hβint hpA hpB hc'
  refine ⟨hs,?_⟩
  intro p hp z hz v
  rw [hd p hp z hz v]
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  let u : Plane := (v.1,circleAngular (circleTurn q.2) v.2)
  have hL : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u=v :=
    cylinderCover_derivative_right_inverse q v
  have hr := congrArg (fun L : Plane →L[ℝ] ℝ => L u) (hrep p hp q hz)
  change α p (cylinderCover q)
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q u)=_
    at hr
  rw [hL] at hr
  have hAv : annularCylinderScalar A p (cylinderCover q)=A (p,q) :=
    annularScalarDescent_turn (hpA p hp q.1 hz) q.2
  have hBv : annularCylinderScalar B p (cylinderCover q)=B (p,q) :=
    annularScalarDescent_turn (hpB p hp q.1 hz) q.2
  rw [← hq,hAv,hBv,hr]
  simp only [planarCovector_apply,u,cylinderCover]
  ring


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem circleTurn_period_one : Periodic circleTurn 1 := by
  intro t
  exact (circleTurn_eq_iff (t+1) t).2 ⟨1,by simp⟩

theorem cylinderCover_period_one (q : Plane) :
    cylinderCover (q+(0,1))=cylinderCover q := by
  apply Prod.ext
  · simp [cylinderCover]
  · exact circleTurn_period_one q.2

theorem cylinderCover_derivative_period_one (q : Plane) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover (q+(0,1))=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q := by
  have hT : HasFDerivAt (fun z : Plane => z+(0,1)) (ContinuousLinearMap.id ℝ Plane) q :=
    (hasFDerivAt_id q).add_const (0,1)
  have hd := ((cylinderCover_smooth.mdifferentiableAt (by simp)
    (x := q+(0,1))).hasMFDerivAt.comp q
    (hasMFDerivAt_iff_hasFDerivAt.mpr hT)).mfderiv
  have he : cylinderCover ∘ (fun z : Plane => z+(0,1))=cylinderCover :=
    funext cylinderCover_period_one
  rw [he] at hd
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun D : Plane →L[ℝ] CylinderModel => D v) hd
  exact hv.symm

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def cylinderFormA (α : P → ManifoldOneForm CylinderModel HandleCylinder) (q : P × Plane) : ℝ :=
  parameterEuclideanPullbackOneForm α cylinderCover q (1,0)

def cylinderFormB (α : P → ManifoldOneForm CylinderModel HandleCylinder) (q : P × Plane) : ℝ :=
  parameterEuclideanPullbackOneForm α cylinderCover q (0,1)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem cylinderForm_rep (α : P → ManifoldOneForm CylinderModel HandleCylinder)
    (p : P) (q : Plane) :
    euclideanPullbackOneForm (fun _ => α p) cylinderCover (0,q)=
      planarCovector (cylinderFormA α (p,q)) (cylinderFormB α (p,q)) := by
  let L := parameterEuclideanPullbackOneForm α cylinderCover (p,q)
  change L=planarCovector (L (1,0)) (L (0,1))
  apply ContinuousLinearMap.ext
  intro v
  have hv : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  rw [show L v=L (v.1 • (1,0)+v.2 • (0,1)) from congrArg L hv]
  simp only [map_add,map_smul,smul_eq_mul,planarCovector_apply]
  ring

theorem cylinderForm_coefficients_smooth {V : Set P} {I : Set ℝ}
    {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    (hα : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z)) :
    ContDiffOn ℝ ∞ (cylinderFormA α) (V ×ˢ (I ×ˢ univ)) ∧
      ContDiffOn ℝ ∞ (cylinderFormB α) (V ×ˢ (I ×ˢ univ)) := by
  have hs : ∀ q∈V ×ˢ (I ×ˢ (univ : Set ℝ)),
      ContDiffAt ℝ ∞ (parameterEuclideanPullbackOneForm α cylinderCover) q := by
    intro q hq
    exact parameterEuclideanPullbackOneForm_contDiffAt
      (hα q.1 hq.1 (cylinderCover q.2) hq.2.1) cylinderCover_smooth.contMDiffAt
  exact ⟨fun q hq => ((hs q hq).clm_apply contDiffAt_const).contDiffWithinAt,
    fun q hq => ((hs q hq).clm_apply contDiffAt_const).contDiffWithinAt⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem cylinderForm_coefficients_periodic
    (α : P → ManifoldOneForm CylinderModel HandleCylinder) (p : P) (s : ℝ) :
    Periodic (fun t => cylinderFormA α (p,(s,t))) 1 ∧
      Periodic (fun t => cylinderFormB α (p,(s,t))) 1 := by
  have he (t : ℝ) : parameterEuclideanPullbackOneForm α cylinderCover (p,(s,t+1))=
      parameterEuclideanPullbackOneForm α cylinderCover (p,(s,t)) := by
    have hq : (s,t+1)=(s,t)+(0,1) := by ext <;> simp
    unfold parameterEuclideanPullbackOneForm
    rw [hq,cylinderCover_period_one,cylinderCover_derivative_period_one]
  exact ⟨fun t => congrArg (fun L : Plane →L[ℝ] ℝ => L (1,0)) (he t),
    fun t => congrArg (fun L : Plane →L[ℝ] ℝ => L (0,1)) (he t)⟩

def cylinderFormPeriod (a : ℝ) (α : P → ManifoldOneForm CylinderModel HandleCylinder) (p : P) : ℝ :=
  annularMean a (cylinderFormB α) p

variable [FiniteDimensional ℝ P]
theorem cylinderFormPeriod_smooth {V : Set P} {I : Set ℝ} (hV : IsOpen V)
    {a : ℝ} (ha : a∈I) {α : P → ManifoldOneForm CylinderModel HandleCylinder}
    (hα : ∀ p∈V,∀ z : HandleCylinder,z.1∈I → ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z)) :
    ContDiffOn ℝ ∞ (cylinderFormPeriod a α) V :=
  annularMean_smooth hV ha (cylinderForm_coefficients_smooth hα).2


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

section Naturality
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N Q : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [TopologicalSpace Q] [ChartedSpace G Q]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem handlePushforwardOneForm_comp_apply
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (α : ManifoldOneForm E M) {g : Q → M} {x : Q}
    (hx : g x∈e.source) (hg : MDifferentiableAt 𝓘(ℝ,G) 𝓘(ℝ,E) g x) (v : G) :
    handlePushforwardOneForm e α (e (g x))
      (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) (e ∘ g) x v) =
      α (g x) (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) g x v) := by
  have hd := mfderiv_comp x (e.mdifferentiableAt (by simp) hx) hg
  have he := handlePushforwardOneForm_pullback e α hx
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,E) g x v)) he
  rw [hd]
  exact hev
end Naturality

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N] [T2Space N]

def globalHandleForm
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,F) HandleTorus N ∞)
    (f : Circle → ℝ) : ManifoldOneForm F N :=
  handlePushforwardOneForm e (torusHandleForm f)

theorem globalHandleForm_properties
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,F) HandleTorus N ∞)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hs : tsupport (torusHandleForm f) ⊆ e.source) :
    SmoothOneFormFamily (fun _ : ℝ => globalHandleForm e f) ∧
      HasCompactSupport (globalHandleForm e f) ∧
      tsupport (globalHandleForm e f) ⊆ e '' tsupport (torusHandleForm f) ∧
      ∀ y, manifoldExteriorOneForm (globalHandleForm e f) y=0 := by
  have hK : IsCompact (tsupport (torusHandleForm f)) := isClosed_closure.isCompact
  have hz : ∀ x, x∉tsupport (torusHandleForm f) → torusHandleForm f x=0 :=
    fun _ hx => image_eq_zero_of_notMem_tsupport hx
  exact ⟨handlePushforwardOneForm_smooth e hK hs (torusHandleForm_smooth hf) hz,
    handlePushforwardOneForm_compact e hK hs hz,
    handlePushforwardOneForm_tsupport e hK hs hz,
    handlePushforwardOneForm_closed e hK hs (torusHandleForm_smooth hf) hz
      (torusHandleForm_closed hf)⟩

omit [IsManifold 𝓘(ℝ,F) ∞ N] [T2Space N] in

theorem globalHandleForm_annular
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,F) HandleTorus N ∞)
    (f : Circle → ℝ) {z : HandleCylinder} (hz : torusAnnulusMap z∈e.source)
    (v : CylinderModel) :
    globalHandleForm e f (e (torusAnnulusMap z))
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,F) (e ∘ torusAnnulusMap) z v) =
      weightedCircleAngular f z.2 v.2 := by
  rw [globalHandleForm,handlePushforwardOneForm_comp_apply e _ hz
    (torusAnnulusMap_smooth.mdifferentiableAt (by simp))]
  exact torusAnnulus_pullback f z v

omit [IsManifold 𝓘(ℝ,F) ∞ N] [T2Space N] in

theorem globalHandleForm_period
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,F) HandleTorus N ∞)
    {f : Circle → ℝ} (hf : (∫ t in (0:ℝ)..1,f (circleTurn t))=1)
    {z : Circle} (hz : ∀ t,transverseTorusCircle z t∈e.source) :
    (∫ t in (0:ℝ)..1, globalHandleForm e f (e (transverseTorusCircle z t))
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) (e ∘ transverseTorusCircle z) t 1))=1 := by
  have he : ∀ t : ℝ, globalHandleForm e f (e (transverseTorusCircle z t))
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) (e ∘ transverseTorusCircle z) t 1) = f (circleTurn t) := by
    intro t
    rw [globalHandleForm]
    exact (handlePushforwardOneForm_comp_apply e (torusHandleForm f) (hz t)
      ((transverseTorusCircle_smooth z).mdifferentiableAt (by simp)) 1).trans
        ((torusHandleForm_transverse f z t 1).trans (mul_one _))
  refine Eq.trans ?_ hf
  apply intervalIntegral.integral_congr
  intro t _
  exact he t

theorem exists_global_handle_form {a : ℝ} (ha : a<1/2) :
    ∃ (f : Circle → ℝ) (U : Set HandleTorus),
      ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f ∧ (∀ z,0≤f z) ∧
      IsOpen U ∧ handlePuncture∈U ∧ Disjoint U (compactHandleBand a) ∧
      ∀ e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,F) HandleTorus N ∞,
        Uᶜ⊆e.source →
        SmoothOneFormFamily (fun _ : ℝ => globalHandleForm e f) ∧
        HasCompactSupport (globalHandleForm e f) ∧
        tsupport (globalHandleForm e f) ⊆ e.target ∧
        (∀ y,manifoldExteriorOneForm (globalHandleForm e f) y=0) ∧
        (∀ s∈Icc (-a) a, (∫ t in (0:ℝ)..1,
          globalHandleForm e f (e (transverseTorusCircle (circleTurn s) t))
            (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) (e ∘ transverseTorusCircle (circleTurn s)) t 1))=1) := by
  obtain ⟨f,U,hf,hpos,_,hU,hp,hband,hsupp,hJ⟩ := exists_torus_handle_away_from_puncture ha
  refine ⟨f,U,hf,hpos,hU,hp,hband,?_⟩
  intro e he
  have hs : tsupport (torusHandleForm f) ⊆ e.source := by
    intro x hx
    apply he
    exact fun hxU => Set.disjoint_left.mp hsupp hxU hx
  obtain ⟨hsm,hcomp,hsp,hd⟩ := globalHandleForm_properties e hf hs
  refine ⟨hsm,hcomp,?_,hd,?_⟩
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := hsp hy
    exact e.map_source (hs hx)
  · intro s hs
    have hper : (∫ t in (0:ℝ)..1,f (circleTurn t))=1 := by
      refine Eq.trans ?_ (hJ (circleTurn s))
      apply intervalIntegral.integral_congr
      intro t _
      exact ((torusHandleForm_transverse f (circleTurn s) t 1).trans (mul_one _)).symm
    apply globalHandleForm_period e hper
    intro t
    apply he
    intro hx
    exact Set.disjoint_left.mp hband hx ⟨(s,circleTurn t),⟨hs,mem_univ _⟩,rfl⟩

end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

section Restriction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

def restrictHandleDiffeomorph
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    (U : Set M) (hU : IsOpen U) : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞ where
  __ := e.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := e.contMDiffOn.mono inter_subset_left
  contMDiffOn_invFun := e.symm.contMDiffOn.mono inter_subset_left
end Restriction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def handleAnnularChart
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞ :=
  restrictHandleDiffeomorph (torusAnnulus.trans e) (Ioo (-a) a ×ˢ univ)
    (isOpen_Ioo.prod isOpen_univ)

@[simp] theorem handleAnnularChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (z : HandleCylinder) : handleAnnularChart e a z=e (torusAnnulusMap z) := rfl

theorem handleAnnularChart_source
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {a : ℝ} (ha : a<1/2) (he : compactHandleBand a⊆e.source) :
    (handleAnnularChart e a).source=Ioo (-a) a ×ˢ univ := by
  apply inter_eq_right.mpr
  intro z hz
  refine ⟨?_,he ?_⟩
  · change z.1∈Ioo (-(1/2)) (1/2) ∧ z.2∈(univ : Set Circle)
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,mem_univ _⟩
  · exact ⟨z,⟨⟨hz.1.1.le,hz.1.2.le⟩,mem_univ _⟩,rfl⟩

theorem handleAnnularChart_pullback
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (f : Circle → ℝ) {z : HandleCylinder}
    (hz : z∈(handleAnnularChart e a).source) (v : CylinderModel) :
    globalHandleForm e f (handleAnnularChart e a z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) z v)=
      f z.2*circleAngular z.2 v.2 := by
  exact globalHandleForm_annular e f hz.1.2 v

theorem handleAnnularChart_compact [T2Space M]
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {a b : ℝ} (hab : b<a) (he : compactHandleBand a⊆e.source) :
    IsCompact (e '' compactHandleBand b) := by
  apply (compactHandleBand_isCompact b).image_of_continuousOn
  apply e.contMDiffOn.continuousOn.mono
  intro x hx
  apply he
  obtain ⟨z,hz,rfl⟩ := hx
  exact ⟨z,⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,mem_univ _⟩,rfl⟩

theorem handleAnnularChart_compact_subset
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {a b : ℝ} (ha : a<1/2) (hab : b<a) (he : compactHandleBand a⊆e.source) :
    e '' compactHandleBand b⊆(handleAnnularChart e a).target := by
  rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
  apply (handleAnnularChart e a).map_source
  rw [handleAnnularChart_source e ha he]
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,mem_univ _⟩

end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem circleTurn_sub (s t : ℝ) : circleTurn (s-t)=circleTurn s/circleTurn t := by
  simp only [circleTurn,mul_sub,Circle.exp_sub]

def positiveCircleArgument (z : Circle) : ℝ :=
  shortCircleArgument (z/circleTurn (1/2))+1/2

theorem positiveCircleArgument_turn {s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    positiveCircleArgument (circleTurn s)=s := by
  unfold positiveCircleArgument
  rw [← circleTurn_sub,shortCircleArgument_turn (show s-1/2∈Ioo (-(1/2):ℝ) (1/2) by
    constructor <;> linarith [hs.1,hs.2])]
  ring

theorem circleTurn_positiveCircleArgument (z : Circle) :
    circleTurn (positiveCircleArgument z)=z := by
  rw [positiveCircleArgument,circleTurn_add,circleTurn_shortCircleArgument,div_mul_cancel]

theorem positiveCircleArgument_smooth {s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ positiveCircleArgument (circleTurn s) := by
  have hi : ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,CircleModel) ∞
      (fun z : Circle => z/circleTurn (1/2)) (circleTurn s) :=
    contMDiffAt_id.div contMDiffAt_const
  have hslit : ((circleTurn s/circleTurn (1/2) : Circle) : ℂ)∈Complex.slitPlane := by
    rw [← circleTurn_sub]
    apply circleTurn_short_slit
    constructor <;> linarith [hs.1,hs.2]
  exact ((shortCircleArgument_smooth_at hslit).comp (circleTurn s) hi).add contMDiffAt_const

def positiveCircleCoordinate : PartialDiffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) ℝ Circle ∞ where
  toFun := circleTurn
  invFun := positiveCircleArgument
  source := Ioo (0:ℝ) 1
  target := circleTurn '' Ioo (0:ℝ) 1
  map_source' s hs := ⟨s,hs,rfl⟩
  map_target' := by
    rintro z ⟨s,hs,rfl⟩
    rwa [positiveCircleArgument_turn hs]
  left_inv' := fun _ hs => positiveCircleArgument_turn hs
  right_inv' := fun _ _ => circleTurn_positiveCircleArgument _
  open_source := isOpen_Ioo
  open_target := circleTurn_isOpenMap _ isOpen_Ioo
  contMDiffOn_toFun := circleTurn_smooth.contMDiffOn
  contMDiffOn_invFun := by
    rintro z ⟨s,hs,rfl⟩
    exact (positiveCircleArgument_smooth hs).contMDiffWithinAt

theorem shortCircleArgument_bounds (z : Circle) :
    -(1/2:ℝ)<shortCircleArgument z ∧ shortCircleArgument z≤1/2 := by
  have hp : 0<2*Real.pi := by positivity
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [Complex.neg_pi_lt_arg (z : ℂ)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [Complex.arg_le_pi (z : ℂ)]

theorem positiveCircleCoordinate_target : positiveCircleCoordinate.target=({1}ᶜ : Set Circle) := by
  ext z
  constructor
  · rintro ⟨s,hs,rfl⟩ hz
    have he : circleTurn s=circleTurn 0 := by simpa only [mem_singleton_iff,circleTurn,mul_zero,Circle.exp_zero] using hz
    obtain ⟨m,hm⟩ := (circleTurn_eq_iff s 0).mp he
    have hlo : (0:ℤ) < m := by exact_mod_cast (show (0:ℝ) < m by linarith [hs.1])
    have hhi : m < (1:ℤ) := by exact_mod_cast (show (m:ℝ)<1 by linarith [hs.2])
    omega
  · intro hz
    have hb := shortCircleArgument_bounds z
    have hne : shortCircleArgument z≠0 := by
      intro he
      apply hz
      have hc := circleTurn_shortCircleArgument z
      rw [he] at hc
      simpa only [mem_singleton_iff,circleTurn,mul_zero,Circle.exp_zero] using hc.symm
    by_cases hpos : 0<shortCircleArgument z
    · exact ⟨shortCircleArgument z,⟨hpos,by linarith [hb.2]⟩,circleTurn_shortCircleArgument z⟩
    · refine ⟨shortCircleArgument z+1,⟨by linarith [hb.1],by
          have hn : shortCircleArgument z<0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
          linarith⟩,?_⟩
      rw [circleTurn_period_one,circleTurn_shortCircleArgument]

def torusRectangleInverse (z : HandleTorus) : Plane :=
  (shortCircleArgument z.1,positiveCircleArgument z.2)

theorem torusRectangleInverse_smooth {z : HandleTorus}
    (hz : z∈circleBandCoordinate.target ×ˢ positiveCircleCoordinate.target) :
    ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,Plane) ∞ torusRectangleInverse z := by
  have hf := circleBandCoordinate.contMDiffOn_invFun.contMDiffAt
    (circleBandCoordinate.open_target.mem_nhds hz.1)
  have hg := positiveCircleCoordinate.contMDiffOn_invFun.contMDiffAt
    (positiveCircleCoordinate.open_target.mem_nhds hz.2)
  have hp : ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
      (Prod.fst : HandleTorus → Circle) z := torus_fst_smooth.contMDiffAt
  have hq : ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
      (Prod.snd : HandleTorus → Circle) z := torus_snd_smooth.contMDiffAt
  exact (contMDiffAt_prod_module_iff _).2 ⟨hf.comp z hp,hg.comp z hq⟩

def torusRectangle : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) Plane HandleTorus ∞ where
  toFun := torusTurns
  invFun := torusRectangleInverse
  source := circleBandCoordinate.source ×ˢ positiveCircleCoordinate.source
  target := circleBandCoordinate.target ×ˢ positiveCircleCoordinate.target
  map_source' _z hz := ⟨circleBandCoordinate.map_source hz.1,positiveCircleCoordinate.map_source hz.2⟩
  map_target' _z hz := ⟨circleBandCoordinate.map_target hz.1,positiveCircleCoordinate.map_target hz.2⟩
  left_inv' _z hz := Prod.ext (circleBandCoordinate.left_inv hz.1) (positiveCircleCoordinate.left_inv hz.2)
  right_inv' _z hz := Prod.ext (circleBandCoordinate.right_inv hz.1) (positiveCircleCoordinate.right_inv hz.2)
  open_source := circleBandCoordinate.open_source.prod positiveCircleCoordinate.open_source
  open_target := circleBandCoordinate.open_target.prod positiveCircleCoordinate.open_target
  contMDiffOn_toFun := torusTurns_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (torusRectangleInverse_smooth hz).contMDiffWithinAt


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

def positiveCircleClock (b : ℝ) (z : Circle) : ℝ :=
  circleClockDensity b (z/circleTurn (1/2))

theorem positiveCircleClock_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (positiveCircleClock b) :=
  (circleClockDensity_smooth hb hsmall).comp (contMDiff_id.div contMDiff_const)

theorem positiveCircleClock_nonneg {b : ℝ} (hb : 0<b) (z : Circle) :
    0≤positiveCircleClock b z := circleClockDensity_nonneg hb _

theorem positiveCircleClock_turn {b s : ℝ} (hs : s∈Ioo (0:ℝ) 1) :
    positiveCircleClock b (circleTurn s)=deriv (intervalClock (-b) b) (s-1/2) := by
  unfold positiveCircleClock
  rw [←circleTurn_sub,circleClockDensity_turn (show s-1/2∈Ioo (-(1/2):ℝ) (1/2) by
    constructor <;> linarith [hs.1,hs.2])]

theorem positiveCircleClock_tsupport {b : ℝ} (hb : 0<b) :
    tsupport (positiveCircleClock b)⊆circleTurn '' Icc (1/2-b) (1/2+b) := by
  apply closure_minimal _ (isCompact_Icc.image circleTurn_smooth.continuous).isClosed
  intro z hz
  obtain ⟨s,hs,he⟩ := circleClockDensity_support hb hz
  refine ⟨s+1/2,⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
  rw [circleTurn_add,he,div_mul_cancel]

theorem positiveCircleClock_cut {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    tsupport (positiveCircleClock b)⊆({1}ᶜ : Set Circle) := by
  intro z hz
  rw [←positiveCircleCoordinate_target]
  obtain ⟨s,hs,rfl⟩ := positiveCircleClock_tsupport hb hz
  exact ⟨s,⟨by linarith [hs.1],by linarith [hs.2]⟩,rfl⟩

theorem positiveCircleClock_pos {b s : ℝ} (hb : 0<b) (hsmall : b<1/2)
    (hs : s∈Ioo (1/2-b) (1/2+b)) : 0<positiveCircleClock b (circleTurn s) := by
  rw [positiveCircleClock_turn (show s∈Ioo (0:ℝ) 1 by constructor <;> linarith [hs.1,hs.2])]
  exact intervalClock_deriv_pos (by linarith) ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem positiveCircleClock_integral {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    (∫ s in (0:ℝ)..1,positiveCircleClock b (circleTurn s))=1 := by
  let T : ℝ → ℝ := fun s => intervalClock (-b) b (s-1/2)
  have hd (s : ℝ) : HasDerivAt T (deriv (intervalClock (-b) b) (s-1/2)) s := by
    have hh := (((intervalClock_smooth (-b) b).differentiable (by simp) (s-1/2)).hasDerivAt.comp s
      ((hasDerivAt_id s).sub_const (1/2)))
    convert hh using 1 <;> first | rfl | ring
  rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤1)
    (fun s hs => positiveCircleClock_turn hs)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((intervalClock_deriv_smooth (-b) b).continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)]
  dsimp [T]
  rw [intervalClock_one (by linarith : -b<b) (by linarith),
    intervalClock_zero (by linarith : -b<b) (by linarith)]
  norm_num


end

section
open scoped ContDiff Topology
open Set Function

theorem positiveCircleClock_inverse {b : ℝ} (hb : 0<b) (hsmall : b<1/2) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ ∞ g (Ioo (0:ℝ) 1) ∧
      (∀ T∈Ioo (0:ℝ) 1,g T∈Ioo (1/2-b) (1/2+b)) ∧
      (∀ t∈Ioo (1/2-b) (1/2+b),g (intervalClock (-b) b (t-1/2))=t) ∧
      (∀ T∈Ioo (0:ℝ) 1,intervalClock (-b) b (g T-1/2)=T) ∧
      (∀ T∈Ioo (0:ℝ) 1,0<deriv g T ∧
        positiveCircleClock b (circleTurn (g T))*deriv g T=1) := by
  have hab : -b<b := by linarith
  obtain ⟨g,hg,hl,hr⟩ := intervalClock_smooth_inverse hab
  let G : ℝ → ℝ := fun T => g T+1/2
  have hGs : ContDiffOn ℝ ∞ G (Ioo (0:ℝ) 1) := hg.add contDiffOn_const
  have hmem (T : ℝ) (hT : T∈Ioo (0:ℝ) 1) : G T∈Ioo (1/2-b) (1/2+b) := by
    have hh := (hr T hT).1
    dsimp [G]
    constructor <;> linarith [hh.1,hh.2]
  refine ⟨G,hGs,hmem,?_,?_,?_⟩
  · intro t ht
    dsimp [G]
    rw [hl _ (show t-1/2∈Ioo (-b) b from ⟨by linarith [ht.1],by linarith [ht.2]⟩)]
    ring
  · intro T hT
    simpa only [G,add_sub_cancel_right] using (hr T hT).2
  · intro T hT
    have hpos := intervalClock_deriv_pos hab (hr T hT).1
    have he : ∀ᶠ S in 𝓝 T,intervalClock (-b) b (g S)=S := by
      filter_upwards [isOpen_Ioo.mem_nhds hT] with S hS
      exact (hr S hS).2
    have hd := HasDerivAt.of_local_left_inverse
      (hg.contDiffAt (isOpen_Ioo.mem_nhds hT)).continuousAt
      ((intervalClock_smooth (-b) b).differentiable (by simp) (g T)).hasDerivAt
      (ne_of_gt hpos) he
    have hGd : HasDerivAt G (deriv (intervalClock (-b) b) (g T))⁻¹ T := hd.add_const (1/2)
    rw [hGd.deriv]
    refine ⟨inv_pos.mpr hpos,?_⟩
    rw [positiveCircleClock_turn (show G T∈Ioo (0:ℝ) 1 by
      have hm := hmem T hT
      constructor <;> linarith [hm.1,hm.2])]
    simp only [G,add_sub_cancel_right,mul_inv_cancel₀ (ne_of_gt hpos)]


end


open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def angularReparam (g : ℝ → ℝ) (p : Plane × E) : Plane × E :=
  ((p.1.1,g p.1.2),p.2)

theorem angularReparam_fderiv {g : ℝ → ℝ} {p : Plane × E}
    (hg : DifferentiableAt ℝ g p.1.2) (v : Plane × E) :
    fderiv ℝ (angularReparam g) p v=((v.1.1,deriv g p.1.2*v.1.2),v.2) := by
  have hd := (((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
    (hg.hasDerivAt.comp_hasFDerivAt p ((hasFDerivAt_snd (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (angularReparam g) _ p at hd
  rw [hd.fderiv]
  rfl

theorem baseCoefficient_fderiv_at {a : Plane → ℝ} {p : Plane × E}
    (ha : DifferentiableAt ℝ a p.1) (v : Plane × E) :
    fderiv ℝ (baseCoefficient a) p v=fderiv ℝ a p.1 v.1 := by
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v)
    ((ha.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).fderiv)

theorem firstBaseCoefficient_fderiv_at {a : ℝ × E → ℝ} {p : Plane × E}
    (ha : DifferentiableAt ℝ a (p.1.1,p.2)) (v : Plane × E) :
    fderiv ℝ (firstBaseCoefficient a) p v=fderiv ℝ a (p.1.1,p.2) (v.1.1,v.2) := by
  exact congrArg (fun L : (Plane × E) →L[ℝ] ℝ => L v)
    ((ha.hasFDerivAt.comp p (((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))).fderiv)

theorem weightedSecondCoefficient_fderiv_at {b w : Plane → ℝ} {G : ℝ × E → ℝ}
    {p : Plane × E} (hb : DifferentiableAt ℝ b p.1) (hw : DifferentiableAt ℝ w p.1)
    (hG : DifferentiableAt ℝ G (p.1.1,p.2)) (v : Plane × E) :
    fderiv ℝ (weightedSecondCoefficient b w G) p v =
      fderiv ℝ b p.1 v.1+fderiv ℝ w p.1 v.1*G (p.1.1,p.2)+
        w p.1*fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2) := by
  have hbD : DifferentiableAt ℝ (baseCoefficient b) p := hb.comp p differentiableAt_fst
  have hwD : DifferentiableAt ℝ (baseCoefficient w) p := hw.comp p differentiableAt_fst
  have hcoord : DifferentiableAt ℝ (fun q : Plane × E => (q.1.1,q.2)) p := by fun_prop
  have hgD : DifferentiableAt ℝ (firstBaseCoefficient G) p := hG.comp p hcoord
  change fderiv ℝ (baseCoefficient b+baseCoefficient w*firstBaseCoefficient G) p v = _
  rw [fderiv_add hbD (hwD.mul hgD),fderiv_mul hwD hgD]
  simp only [add_apply,smul_apply,smul_eq_mul,baseCoefficient_fderiv_at hb,
    baseCoefficient_fderiv_at hw,firstBaseCoefficient_fderiv_at hG,baseCoefficient,firstBaseCoefficient]
  ring

def normalizedAreaDensity (A B : Plane → ℝ) (g : ℝ → ℝ) (q : Plane) : ℝ :=
  (fderiv ℝ B (q.1,g q.2) (1,0)-fderiv ℝ A (q.1,g q.2) (0,1))*deriv g q.2

theorem plane_covector_decomp (L : Plane →L[ℝ] ℝ) (v : Plane) :
    L v=v.1*L (1,0)+v.2*L (0,1) := by
  have he : v=v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul]

theorem angularReparam_weighted_pullback (Ω : E →L[ℝ] E →L[ℝ] ℝ)
    {A B : Plane → ℝ} {w g : ℝ → ℝ} {G : ℝ × E → ℝ} {p : Plane × E}
    (hA : DifferentiableAt ℝ A (p.1.1,g p.1.2))
    (hB : DifferentiableAt ℝ B (p.1.1,g p.1.2))
    (hw : DifferentiableAt ℝ w (g p.1.2)) (hg : DifferentiableAt ℝ g p.1.2)
    (hG : DifferentiableAt ℝ G (p.1.1,p.2)) (hnorm : w (g p.1.2)*deriv g p.1.2=1)
    (v z : Plane × E) :
    horizontalCoupling Ω (baseCoefficient A) (weightedSecondCoefficient B (fun q => w q.2) G)
      (angularReparam g p) (fderiv ℝ (angularReparam g) p v) (fderiv ℝ (angularReparam g) p z) =
      Ω v.2 z.2+normalizedAreaDensity A B g p.1*(v.1.1*z.1.2-v.1.2*z.1.1)+
        fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2)*z.1.2-
        v.1.2*fderiv ℝ G (p.1.1,p.2) (z.1.1,z.2) := by
  have hwp : DifferentiableAt ℝ (fun q : Plane => w q.2) (p.1.1,g p.1.2) := hw.comp (p.1.1,g p.1.2) differentiableAt_snd
  have hAp : DifferentiableAt ℝ (baseCoefficient A) (angularReparam g p) := hA.comp (angularReparam g p) differentiableAt_fst
  have hcoord : DifferentiableAt ℝ (fun q : Plane × E => (q.1.1,q.2)) (angularReparam g p) := by fun_prop
  have hBw : DifferentiableAt ℝ (baseCoefficient B) (angularReparam g p) :=
    hB.comp (angularReparam g p) differentiableAt_fst
  have hww : DifferentiableAt ℝ (baseCoefficient (fun q => w q.2)) (angularReparam g p) := by
    exact (hw.hasDerivAt.comp_hasFDerivAt (angularReparam g p)
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (p.1.1,g p.1.2))).comp (angularReparam g p)
        (hasFDerivAt_fst (𝕜 := ℝ) (p := angularReparam g p)))).differentiableAt
  have hGw : DifferentiableAt ℝ (firstBaseCoefficient G) (angularReparam g p) :=
    hG.comp (angularReparam g p) hcoord
  have hBp : DifferentiableAt ℝ (weightedSecondCoefficient B (fun q => w q.2) G) (angularReparam g p) :=
    hBw.add (hww.mul hGw)
  have hwd (u : Plane) : fderiv ℝ (fun q : Plane => w q.2) (p.1.1,g p.1.2) u=deriv w (g p.1.2)*u.2 := by
    have hd : HasFDerivAt (fun q : Plane => w q.2)
        (deriv w (g p.1.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) (p.1.1,g p.1.2) :=
      hw.hasDerivAt.comp_hasFDerivAt (p.1.1,g p.1.2) (hasFDerivAt_snd (𝕜 := ℝ) (p := (p.1.1,g p.1.2)))
    exact congrArg (fun L : Plane →L[ℝ] ℝ => L u) hd.fderiv
  rw [angularReparam_fderiv hg,angularReparam_fderiv hg]
  simp only [horizontalCoupling,add_apply,ContinuousLinearMap.bilinearComp_apply,
    euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    horizontalOneForm_fderiv hAp hBp]
  change Ω v.2 z.2 + _ = _
  rw [baseCoefficient_fderiv_at (p := angularReparam g p) hA,
    baseCoefficient_fderiv_at (p := angularReparam g p) hA,
    weightedSecondCoefficient_fderiv_at (p := angularReparam g p) hB hwp hG,
    weightedSecondCoefficient_fderiv_at (p := angularReparam g p) hB hwp hG]
  simp only [angularReparam,hwd,normalizedAreaDensity]
  rw [plane_covector_decomp (fderiv ℝ A (p.1.1,g p.1.2)) (v.1.1,deriv g p.1.2*v.1.2),
    plane_covector_decomp (fderiv ℝ A (p.1.1,g p.1.2)) (z.1.1,deriv g p.1.2*z.1.2),
    plane_covector_decomp (fderiv ℝ B (p.1.1,g p.1.2)) (v.1.1,deriv g p.1.2*v.1.2),
    plane_covector_decomp (fderiv ℝ B (p.1.1,g p.1.2)) (z.1.1,deriv g p.1.2*z.1.2)]
  linear_combination (fderiv ℝ G (p.1.1,p.2) (v.1.1,v.2)*z.1.2-
    v.1.2*fderiv ℝ G (p.1.1,p.2) (z.1.1,z.2))*hnorm



end PackingSufficiencySupport.Hamiltonian
end

end OAI
