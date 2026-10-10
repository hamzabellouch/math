import Mathlib
import OAI.Geometry.BallPacking.Annuli.QuadricNormalizedCycle

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_normalized_primitive_on_annular_chart
    {V : Set P} {I : Set ℝ} {K : Set M}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞)
    (he_source : e.source=I ×ˢ univ) (hK : IsCompact K) (hKA : K⊆e.target)
    {Γ N : P → ManifoldOneForm E M} {β : ManifoldOneForm E M}
    (hΓ : ∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hN : ∀ p∈V,∀ x∈e.target,ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (N q.1) x q.2) (p,extChartAt 𝓘(ℝ,E) x x))
    (hcurv : ∀ p∈V,∀ x∈e.target,manifoldExteriorOneForm (Γ p) x=manifoldExteriorOneForm (N p) x)
    (hβ : ∀ c,ContDiffOn ℝ ∞ (chartOneForm β c) (extChartAt 𝓘(ℝ,E) c).target)
    (hβclosed : ∀ x,manifoldExteriorOneForm β x=0) (hβcompact : HasCompactSupport β)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1,f (circleTurn t))=1)
    (hβcoord : ∀ z∈e.source,∀ v : CylinderModel,
      β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=f z.2*circleAngular z.2 v.2) :
    ∃ (Γ₁ : P → ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L⊆e.target ∧ IsOpen W ∧ K⊆W ∧ W⊆e.target ∧
      (∀ c,ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (Γ₁ q.1) c q.2)
        (V ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) ∧
      (∀ p,support (Γ₁ p-Γ p)⊆tsupport β∪L) ∧
      (∀ p,HasCompactSupport (Γ₁ p-Γ p)) ∧
      (∀ p∈V,∀ x,manifoldExteriorOneForm (Γ₁ p) x=manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p∈V,∀ x∈W,Γ₁ p x=N p x) := by
  let δ : P → ManifoldOneForm E M := fun p => Γ p-N p
  let α := parameterManifoldPullbackOneForm (E := E) (F := CylinderModel) δ e
  have hΓat (p : P) (hp : p∈V) (x : M) : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (Γ q.1) x q.2) (p,extChartAt 𝓘(ℝ,E) x x) :=
    (hΓ x).contDiffAt ((hV.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      ⟨hp,(extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)⟩)
  have hδ (p : P) (hp : p∈V) (x : M) (hx : x∈e.target) : ContDiffAt ℝ ∞
      (fun q : P × E => chartOneForm (δ q.1) x q.2) (p,extChartAt 𝓘(ℝ,E) x x) := by
    apply ((hΓat p hp x).sub (hN p hp x hx)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun q => chartOneForm_sub (Γ q.1) (N q.1) x q.2)
  have hδclosed (p : P) (hp : p∈V) (x : M) (hx : x∈e.target) :
      manifoldExteriorOneForm (δ p) x=0 := by
    change manifoldExteriorOneForm (Γ p-N p) x=0
    rw [manifoldExteriorOneForm_sub_at (α := Γ p) (β := N p) (x := x)
      ((hΓat p hp x).comp _ (contDiffAt_const.prodMk contDiffAt_id))
      ((hN p hp x hx).comp _ (contDiffAt_const.prodMk contDiffAt_id)),hcurv p hp x hx]
    ext u v
    simp
  have hsrc (z : HandleCylinder) (hz : z.1∈I) : z∈e.source := by
    rw [he_source]; exact ⟨hz,mem_univ _⟩
  have hα (p : P) (hp : p∈V) (z : HandleCylinder) (hz : z.1∈I) : ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z) :=
    parameterManifoldPullbackOneForm_contDiffAt (α := δ) (g := e)
      (hδ p hp (e z) (e.map_source (hsrc z hz))) (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))
  have hclosed (p : P) (hp : p∈V) (z : HandleCylinder) (hz : z.1∈I) :
      manifoldExteriorOneForm (α p) z=0 := by
    change manifoldExteriorOneForm (manifoldPullbackOneForm (E := E) (F := CylinderModel) (fun _ => δ p) e 0) z=0
    rw [manifold_pullback_exterior_at (α := δ p) (g := e) (b := z)
      ((hδ p hp (e z) (e.map_source (hsrc z hz))).comp _ (contDiffAt_const.prodMk contDiffAt_id))
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))]
    dsimp only [manifoldPullbackTwoForm]
    rw [hδclosed p hp (e z) (e.map_source (hsrc z hz))]
    rfl
  have hmem (x : M) (hx : x∈e.target) : (e.symm x).1∈I := by
    have hm := e.map_target hx
    rw [he_source] at hm
    exact hm.1
  obtain ⟨F,hF,hFd⟩ := exists_intrinsic_annular_coordinate_potential hV hI e.open_target hc ha
    hα hclosed hf hfint e.symm.contMDiffOn hmem
  have hFd' : ∀ p∈V,∀ x∈e.target,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        Γ p x-N p x-cylinderFormPeriod a α p • β x := by
    intro p hp x hx
    apply ContinuousLinearMap.ext
    intro v
    rw [hFd p hp x hx v]
    have hd := parameterManifoldPullbackOneForm_inverse_apply e δ p hx v
    change α p (e.symm x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v)=_ at hd
    rw [hd]
    have hbc := hβcoord (e.symm x) (e.map_target hx)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v)
    have hb := parameterManifoldPullbackOneForm_inverse_apply e (fun _ : P => β) p hx v
    change β (e (e.symm x)) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e (e.symm x)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v))=β x v at hb
    rw [hb] at hbc
    simp only [δ,Pi.sub_apply,sub_apply,smul_apply,smul_eq_mul]
    rw [hbc]
    ring
  exact exists_normalized_manifold_primitive_neighborhood hV hK e.open_target hKA
    hΓ hβ hβclosed hβcompact (cylinderFormPeriod_smooth hV ha hα) hF hFd'

end

def cylinderClockPrimitive (S : ℝ → ℝ) (f : Circle → ℝ) :
    ManifoldOneForm CylinderModel HandleCylinder :=
  weightedCylinderAngular (fun z => S z.1*f z.2)

theorem cylinderClockPrimitive_smoothAt {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (z : HandleCylinder) :
    ContDiffAt ℝ ∞ (chartOneForm (cylinderClockPrimitive S f) z)
      (extChartAt 𝓘(ℝ,CylinderModel) z z) := by
  have hp : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (Prod.fst : HandleCylinder → ℝ) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
    exact contMDiff_fst
  exact weightedCylinderAngular_smoothAt
    (((hS.contMDiff.comp hp).mul (hf.comp cylinder_snd_smooth)).contMDiffAt)

theorem cylinderClockPrimitive_exterior_cover {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (q : Plane) :
    (manifoldExteriorOneForm (cylinderClockPrimitive S f) (cylinderCover q)).bilinearComp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)=
      (deriv S q.1*f (circleTurn q.2)) • planarArea := by
  have hn := euclidean_manifold_pullback_exterior_at cylinderCover_smooth.contMDiffAt
    (cylinderClockPrimitive_smoothAt hS hf (cylinderCover q))
  have he : (fun y => euclideanPullbackOneForm (fun _ => cylinderClockPrimitive S f) cylinderCover (0,y))=
      (fun y => planarCovector 0 (S y.1*f (circleTurn y.2))) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    change (S y.1*f (circleTurn y.2))*cylinderAngular (cylinderCover y)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover y v)=_
    rw [cylinderAngular_cover]
    simp only [planarCovector_apply,zero_mul,zero_add]
  have hc : ContDiff ℝ ∞ (fun y : Plane => S y.1*f (circleTurn y.2)) :=
    (hS.comp contDiff_fst).mul (((hf.comp circleTurn_smooth).contDiff).comp contDiff_snd)
  have hd : deriv (fun s => S s*f (circleTurn q.2)) q.1=deriv S q.1*f (circleTurn q.2) :=
    ((hS.differentiable (by simp) q.1).hasDerivAt.mul_const _).deriv
  calc
    _ = euclideanExteriorOneForm
        (fun y => euclideanPullbackOneForm (fun _ => cylinderClockPrimitive S f) cylinderCover (0,y)) q := hn.symm
    _ = _ := by
      rw [he,planarCovector_exterior contDiff_const hc,hd,deriv_const,sub_zero]

theorem cylinderClockPrimitive_exterior {S : ℝ → ℝ} (hS : ContDiff ℝ ∞ S)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (z : HandleCylinder) :
    manifoldExteriorOneForm (cylinderClockPrimitive S f) z=
      (deriv S z.1*f z.2) • cylinderAreaForm z := by
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  rw [← hq]
  let D : Plane →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
  have he : (manifoldExteriorOneForm (cylinderClockPrimitive S f) (cylinderCover q)).bilinearComp D D=
      (deriv S q.1*f (circleTurn q.2)) • planarArea :=
    cylinderClockPrimitive_exterior_cover hS hf q
  have hd (u : CylinderModel) : D (u.1,circleAngular (circleTurn q.2) u.2)=u :=
    cylinderCover_derivative_right_inverse q u
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    Ω (v.1,circleAngular (circleTurn q.2) v.2) (w.1,circleAngular (circleTurn q.2) w.2)) he
  simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,smul_eq_mul] at hv
  rw [hd v,hd w] at hv
  simpa only [planarArea_apply,cylinderAreaForm_apply,cylinderCover,smul_apply,smul_eq_mul] using hv

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_compact_annular_dual_normalization
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞)
    {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I) (he : e.source=I ×ˢ univ)
    {a : ℝ} (ha : a∈I) {K : Set M} (hK : IsCompact K) (hKA : K⊆e.target)
    {β : ManifoldOneForm E M} (hβ : SmoothOneFormFamily (fun _ : ℝ => β))
    (hclosed : ∀ x,manifoldExteriorOneForm β x=0) (hcompact : HasCompactSupport β)
    (hperiod : cylinderFormPeriod a (parameterManifoldPullbackOneForm (fun _ : ℝ => β) e) 0=1)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    ∃ (β' : ManifoldOneForm E M) (L W : Set M),
      IsCompact L ∧ L⊆e.target ∧ IsOpen W ∧ K⊆W ∧ W⊆e.target ∧
      SmoothOneFormFamily (fun _ : ℝ => β') ∧ HasCompactSupport β' ∧
      (∀ x,manifoldExteriorOneForm β' x=0) ∧
      support (β'-β)⊆L ∧
      ∀ z∈e.source,e z∈W → ∀ v : CylinderModel,
        β' (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=
          f z.2*circleAngular z.2 v.2 := by
  let α := parameterManifoldPullbackOneForm (E := E) (F := CylinderModel) (fun _ : ℝ => β) e
  have hβat (p : ℝ) (x : M) : ContDiffAt ℝ ∞
      (fun q : ℝ × E => chartOneForm β x q.2) (p,extChartAt 𝓘(ℝ,E) x x) :=
    (hβ x).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)⟩)
  have hsrc (z : HandleCylinder) (hz : z.1∈I) : z∈e.source := by
    rw [he]; exact ⟨hz,mem_univ _⟩
  have hα (p : ℝ) (_hp : p∈(univ : Set ℝ)) (z : HandleCylinder) (hz : z.1∈I) : ContDiffAt ℝ ∞
      (fun q : ℝ × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z) :=
    parameterManifoldPullbackOneForm_contDiffAt (hβat p (e z))
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))
  have hαclosed (p : ℝ) (_hp : p∈(univ : Set ℝ)) (z : HandleCylinder) (hz : z.1∈I) :
      manifoldExteriorOneForm (α p) z=0 := by
    change manifoldExteriorOneForm (manifoldPullbackOneForm (E := E) (F := CylinderModel) (fun _ => β) e 0) z=0
    rw [manifold_pullback_exterior_at (α := β) (g := e) (b := z)
      ((hβat p (e z)).comp _ (contDiffAt_const.prodMk contDiffAt_id))
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))]
    dsimp only [manifoldPullbackTwoForm]
    rw [hclosed]
    rfl
  have hmem (x : M) (hx : x∈e.target) : (e.symm x).1∈I := by
    have hm := e.map_target hx
    rw [he] at hm
    exact hm.1
  obtain ⟨F,hF,hFd⟩ := exists_intrinsic_annular_coordinate_potential isOpen_univ hI
    e.open_target hc ha hα hαclosed hf hfint e.symm.contMDiffOn hmem
  let N : ℝ → ManifoldOneForm E M := fun _ => manifoldPullbackOneForm
    (fun _ => cylinderClockPrimitive (fun _ => 1) f) e.symm 0
  have hFd' : ∀ p∈(univ : Set ℝ),∀ x∈e.target,
      manifoldScalarDifferential (E := E) (fun y => F (p,y)) x=
        β x-N p x-(0:ℝ) • (0 : ManifoldOneForm E M) x := by
    intro p hp x hx
    apply ContinuousLinearMap.ext
    intro v
    rw [hFd p hp x hx v]
    have hd := parameterManifoldPullbackOneForm_inverse_apply e (fun _ : ℝ => β) p hx v
    change α p (e.symm x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v)=_ at hd
    rw [hd]
    have hp' : cylinderFormPeriod a α p=1 := hperiod
    rw [hp',one_mul]
    simp only [N, sub_apply, zero_smul, sub_zero, manifoldPullbackOneForm,
      cylinderClockPrimitive, weightedCylinderAngular, one_mul, manifoldMapDifferential]
    change β x v - _ = β x v - f (e.symm x).2 *
      cylinderAngular (e.symm x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) e.symm x v)
    erw [cylinderAngular_apply]
  have hz : ∀ c,ContDiffOn ℝ ∞ (chartOneForm (0 : ManifoldOneForm E M) c)
      (extChartAt 𝓘(ℝ,E) c).target := by
    intro c
    simpa only [show chartOneForm (0 : ManifoldOneForm E M) c=(fun _ => 0) from
      funext (chartOneForm_zero c)] using (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : E => (0 : E →L[ℝ] ℝ)) (extChartAt 𝓘(ℝ,E) c).target)
  obtain ⟨Γ,L,W,hL,hLA,hW,hKW,hWA,hΓ,hsp,hcp,hd,hn⟩ :=
    exists_normalized_manifold_primitive_neighborhood (E := E) (M := M)
      (Γ := fun _ : ℝ => β) (N := N) (β := 0) (a := fun _ => 0) isOpen_univ hK e.open_target hKA
      hβ hz (fun x => manifoldExteriorOneForm_zero x) (HasCompactSupport.zero)
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ => (0:ℝ)) univ) hF hFd'
  refine ⟨Γ 0,L,W,hL,hLA,hW,hKW,hWA,?_,?_,?_,?_,?_⟩
  · intro c
    exact (hΓ c).comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun q hq => ⟨mem_univ _,hq.2⟩)
  · have hp := (hcp 0).add hcompact
    simpa only [sub_add_cancel] using hp
  · intro x
    rw [hd 0 (mem_univ _) x,hclosed]
  · simpa only [tsupport_zero,empty_union] using hsp 0
  · intro z hz' hw v
    rw [hn 0 (mem_univ _) (e z) hw]
    have hi := parameterManifoldPullbackOneForm_inverse_apply e.symm
      (fun _ : ℝ => cylinderClockPrimitive (fun _ => 1) f) 0 hz' v
    change (N 0 (e z)) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=_
    rw [show N 0 (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) e z v)=
      cylinderClockPrimitive (fun _ => 1) f z v from hi]
    simp only [cylinderClockPrimitive,weightedCylinderAngular,smul_apply,smul_eq_mul,
      one_mul,cylinderAngular_apply]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

instance surfaceSigmaCompact : SigmaCompactSpace (Surface m) := by
  exact IsClosed.sigmaCompactSpace (locus_isClosed (parameters m))

def restrictedTransverseCylinder (a : ℝ) :
    PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) HandleCylinder (Surface m) ∞ :=
  restrictHandleDiffeomorph (transverseCylinder m) (Ioo (-a) a ×ˢ univ)
    (isOpen_Ioo.prod isOpen_univ)

theorem restrictedTransverseCylinder_source {a : ℝ}
    (ha : a≤transverseCylinderWidth m) :
    (restrictedTransverseCylinder m a).source=Ioo (-a) a ×ˢ univ := by
  apply inter_eq_right.mpr
  intro z hz
  exact transverseCylinderWidth_subset m ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩

theorem exists_actual_compact_normalized_dual_fixed
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    ∃ (a : ℝ) (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
      HandleCylinder (Surface m) ∞) (β : ManifoldOneForm RealModel (Surface m)),
      a=transverseCylinderWidth m/2 ∧
      e=restrictedTransverseCylinder m (transverseCylinderWidth m/2) ∧
      0<a ∧ e.source=Ioo (-a) a ×ˢ univ ∧ IsCompact (closure e.target) ∧
      SmoothOneFormFamily (fun _ : ℝ => β) ∧ HasCompactSupport β ∧
      (∀ x,manifoldExteriorOneForm β x=0) ∧
      ∀ z∈e.source,∀ v : CylinderModel,
        β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) e z v)=
          f z.2*circleAngular z.2 v.2 := by
  let a := transverseCylinderWidth m
  have ha : 0<a := transverseCylinderWidth_pos m
  let e := restrictedTransverseCylinder m a
  have he : e.source=Ioo (-a) a ×ˢ univ := restrictedTransverseCylinder_source m le_rfl
  let K := e '' (Icc (-a/2) (a/2) ×ˢ (univ : Set Circle))
  have hsub : Icc (-a/2) (a/2) ×ˢ (univ : Set Circle)⊆e.source := by
    intro z hz
    rw [he]
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_univ).image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono hsub)
  have hKA : K⊆e.target := image_subset_iff.mpr (fun z hz => e.map_source (hsub hz))
  have hp : cylinderFormPeriod 0
      (parameterManifoldPullbackOneForm (fun _ : ℝ => compactDualForm m) e) 0=1 :=
    cylinderDualForm_period m 0
  obtain ⟨β,L,W,_,_,_,hKW,_,hβ,hcp,hcl,_,hn⟩ := exists_compact_annular_dual_normalization
    e isOpen_Ioo (convex_Ioo (-a) a) he (show (0:ℝ)∈Ioo (-a) a by constructor <;> linarith)
    hK hKA (compactDualForm_smooth m) (compactDualForm_closed m) (compactDualForm_compact m) hp hf hfi
  let d := restrictedTransverseCylinder m (a/2)
  have hd : d.source=Ioo (-(a/2)) (a/2) ×ˢ univ :=
    restrictedTransverseCylinder_source m (by dsimp [a]; linarith [transverseCylinderWidth_pos m])
  have hdK : d.target⊆K := by
    intro x hx
    obtain ⟨z,hz,hzx⟩ := d.toPartialEquiv.surjOn hx
    rw [hd] at hz
    exact ⟨z,⟨⟨by linarith [hz.1.1],hz.1.2.le⟩,hz.2⟩,hzx⟩
  refine ⟨a/2,d,β,rfl,rfl,half_pos ha,hd,hK.of_isClosed_subset isClosed_closure
    (closure_minimal hdK hK.isClosed),hβ,hcp,hcl,?_⟩
  intro z hz v
  have hzK : z∈Icc (-a/2) (a/2) ×ˢ (univ : Set Circle) := by
    rw [hd] at hz
    exact ⟨⟨by linarith [hz.1.1],hz.1.2.le⟩,hz.2⟩
  exact hn z (hsub hzK) (hKW ⟨z,hzK,rfl⟩) v

theorem exists_actual_compact_normalized_dual
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    ∃ (a : ℝ) (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel)
      HandleCylinder (Surface m) ∞) (β : ManifoldOneForm RealModel (Surface m)),
      0<a ∧ e.source=Ioo (-a) a ×ˢ univ ∧ IsCompact (closure e.target) ∧
      SmoothOneFormFamily (fun _ : ℝ => β) ∧ HasCompactSupport β ∧
      (∀ x,manifoldExteriorOneForm β x=0) ∧
      ∀ z∈e.source,∀ v : CylinderModel,
        β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) e z v)=
          f z.2*circleAngular z.2 v.2 := by
  obtain ⟨a,e,β,_,_,h⟩ := exists_actual_compact_normalized_dual_fixed m hf hfi
  exact ⟨a,e,β,h⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

structure AnnularHandleData (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] where
  width : ℝ
  width_pos : 0<width
  chart : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞
  source_eq : chart.source=Ioo (-width) width ×ˢ univ
  compact_target : IsCompact (closure chart.target)
  clock : Circle → ℝ
  clock_smooth : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ clock
  clock_nonneg : ∀ z,0≤clock z
  clock_support : tsupport clock⊆({1}ᶜ : Set Circle)
  clock_integral : (∫ t in (0:ℝ)..1,clock (circleTurn t))=1
  dual : ManifoldOneForm E M
  dual_smooth : SmoothOneFormFamily (fun _ : ℝ => dual)
  dual_compact : HasCompactSupport dual
  dual_closed : ∀ x,manifoldExteriorOneForm dual x=0
  dual_pullback : ∀ z∈chart.source,∀ v : CylinderModel,
    dual (chart z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) chart z v)=
      clock z.2*circleAngular z.2 v.2

namespace AnnularHandleData

def band (b : ℝ) : Set HandleCylinder := Icc (-b) b ×ˢ univ

def core (H : AnnularHandleData E M) (b : ℝ) : Set HandleCylinder :=
  Icc (-b) b ×ˢ tsupport H.clock

theorem band_compact (b : ℝ) : IsCompact (band b) := isCompact_Icc.prod isCompact_univ

theorem core_compact (H : AnnularHandleData E M) (b : ℝ) : IsCompact (H.core b) :=
  isCompact_Icc.prod (isClosed_tsupport H.clock).isCompact

theorem core_subset_band (H : AnnularHandleData E M) (b : ℝ) : H.core b⊆band b :=
  prod_mono_right (subset_univ _)

theorem band_subset_source (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    band b⊆H.chart.source := by
  rw [H.source_eq]
  intro z hz
  exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩

theorem image_band_compact (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    IsCompact (H.chart '' band b) :=
  (band_compact b).image_of_continuousOn
    (H.chart.contMDiffOn.continuousOn.mono (H.band_subset_source hb))

theorem image_core_compact (H : AnnularHandleData E M) {b : ℝ} (hb : b<H.width) :
    IsCompact (H.chart '' H.core b) :=
  (H.core_compact b).image_of_continuousOn
    (H.chart.contMDiffOn.continuousOn.mono ((H.core_subset_band b).trans (H.band_subset_source hb)))

end AnnularHandleData
end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

theorem exists_fixed_annularHandleData (m : ℕ) :
    ∃ H : AnnularHandleData RealModel (Surface m),
      H.width=transverseCylinderWidth m/2 ∧
      H.chart=restrictedTransverseCylinder m (transverseCylinderWidth m/2) ∧
      H.clock=positiveCircleClock (1/4) := by
  let f := positiveCircleClock (1/4)
  have hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f := positiveCircleClock_smooth (by norm_num) (by norm_num)
  have hfi : (∫ t in (0:ℝ)..1,f (circleTurn t))=1 := positiveCircleClock_integral (by norm_num) (by norm_num)
  obtain ⟨a,e,β,hae,hee,ha,he,hec,hβ,hcp,hcl,hpb⟩ :=
    exists_actual_compact_normalized_dual_fixed m hf hfi
  exact ⟨⟨a,ha,e,he,hec,f,hf,positiveCircleClock_nonneg (by norm_num),
    positiveCircleClock_cut (by norm_num) (by norm_num),hfi,β,hβ,hcp,hcl,hpb⟩,hae,hee,rfl⟩

theorem exists_annularHandleData (m : ℕ) : Nonempty (AnnularHandleData RealModel (Surface m)) :=
  ⟨(exists_fixed_annularHandleData m).choose⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def cylinderRadialForm (b : ℝ) : ManifoldOneForm CylinderModel HandleCylinder :=
  manifoldScalarDifferential (fun z : HandleCylinder => intervalClock (-b) b z.1)

theorem cylinder_fst_smooth :
    ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (Prod.fst : HandleCylinder → ℝ) := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
  exact contMDiff_fst

theorem cylinderRadialForm_smooth (b : ℝ) (c : HandleCylinder) :
    ContDiffOn ℝ ∞ (chartOneForm (cylinderRadialForm b) c)
      (extChartAt 𝓘(ℝ,CylinderModel) c).target :=
  manifoldScalarDifferential_smooth ((intervalClock_smooth (-b) b).contMDiff.comp cylinder_fst_smooth) c

theorem cylinderRadialForm_apply (b : ℝ) (z : HandleCylinder) (v : CylinderModel) :
    cylinderRadialForm b z v=deriv (intervalClock (-b) b) z.1*v.1 := by
  unfold cylinderRadialForm manifoldScalarDifferential
  change mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) (intervalClock (-b) b ∘ Prod.fst) z v=_
  rw [mfderiv_comp z ((intervalClock_smooth (-b) b).contMDiff.mdifferentiableAt (by simp))
    (cylinder_fst_smooth.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  have he : mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) (Prod.fst : HandleCylinder → ℝ) z=
      ContinuousLinearMap.fst ℝ ℝ CircleModel := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod]
    exact mfderiv_fst
  rw [he]
  change fderiv ℝ (intervalClock (-b) b) z.1 v.1=_
  exact fderiv_eq_deriv_mul

theorem cylinderRadialForm_zero {b : ℝ} (hb : 0<b) {z : HandleCylinder}
    (hz : z∉AnnularHandleData.band b) : cylinderRadialForm b z=0 := by
  have hn : z.1∉Icc (-b) b := fun hk => hz ⟨hk,mem_univ _⟩
  have hd : deriv (intervalClock (-b) b) z.1=0 := by
    simp only [mem_Icc,not_and_or,not_le] at hn
    rcases hn with h|h
    · exact intervalClock_deriv_zero_left (by linarith) h
    · exact intervalClock_deriv_zero_right (by linarith) h
  apply ContinuousLinearMap.ext
  intro v
  simp [cylinderRadialForm_apply,hd]

theorem cylinderRadialForm_closed (b : ℝ) (z : HandleCylinder) :
    manifoldExteriorOneForm (cylinderRadialForm b) z=0 :=
  manifoldScalarDifferential_closed ((intervalClock_smooth (-b) b).contMDiff.comp cylinder_fst_smooth) z

end PackingSufficiencySupport.Hamiltonian
end

end OAI
