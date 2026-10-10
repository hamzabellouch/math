import Mathlib
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Bracket Integrability. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

universe u
namespace SplitTangent
section

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

open Filter Topology
namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)
abbrev Field := ∀ x : X.Carrier, Tangent X x

def projectField (V : Field (X := X)) : Field (X := X) :=
  fun x => S.projector x (V x)

def complementAt (x : X.Carrier) : Tangent X x →L[ℂ] Tangent X x :=
  ContinuousLinearMap.id ℂ (Tangent X x) - S.projector x

@[simp] theorem complementAt_apply (x : X.Carrier) (v : Tangent X x) :
    S.complementAt x v = v - S.projector x v := rfl

@[simp] theorem complementAt_projector (x : X.Carrier) (v : Tangent X x) :
    S.complementAt x (S.projector x v) = 0 := by
  simp only [complementAt_apply, S.idempotent, sub_self]

@[simp] theorem projectField_add (V W : Field (X := X)) :
    S.projectField (V + W) = S.projectField V + S.projectField W := by
  funext x; exact map_add (S.projector x) (V x) (W x)

@[simp] theorem projectField_smul (f : X.Carrier → ℂ) (V : Field (X := X)) :
    S.projectField (f • V) = f • S.projectField V := by
  funext x; exact map_smul (S.projector x) (f x) (V x)

theorem mdifferentiableAt_projectField {V : Field (X := X)} {x : X.Carrier}
    (hV : MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,V y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x) :
    MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,S.projectField V y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x :=
  (S.holomorphic.mdifferentiable (by simp)).mdifferentiableAt.comp x hV

 

def bracketOperation (x : X.Carrier) (V W : Field (X := X)) : Tangent X x :=
  S.complementAt x (VectorField.mlieBracket (ModelWithCorners X)
    (S.projectField V) (S.projectField W) x)

theorem bracketOperation_tensorial_left (x : X.Carrier) (W : Field (X := X)) :
    TensorialAt (ModelWithCorners X) (Model X) (fun V => S.bracketOperation x V W) x := by
  constructor
  · intro f V hf hV
    simp only [bracketOperation, projectField_smul]
    rw [VectorField.mlieBracket_smul_left hf (S.mdifferentiableAt_projectField hV)]
    simp only [map_add, map_smul, projectField, complementAt_projector, smul_zero, zero_add]
  · intro V V' hV hV'
    simp only [bracketOperation, projectField_add]
    rw [VectorField.mlieBracket_add_left (S.mdifferentiableAt_projectField hV)
      (S.mdifferentiableAt_projectField hV'), map_add]

theorem bracketOperation_tensorial_right (x : X.Carrier) (V : Field (X := X)) :
    TensorialAt (ModelWithCorners X) (Model X) (S.bracketOperation x V) x := by
  constructor
  · intro f W hf hW
    simp only [bracketOperation, projectField_smul]
    rw [VectorField.mlieBracket_smul_right hf (S.mdifferentiableAt_projectField hW)]
    simp only [map_add, map_smul, projectField, complementAt_projector, smul_zero, zero_add]
  · intro W W' hW hW'
    simp only [bracketOperation, projectField_add]
    rw [VectorField.mlieBracket_add_right (S.mdifferentiableAt_projectField hW)
      (S.mdifferentiableAt_projectField hW'), map_add]

 

def bracketTensor (x : X.Carrier) : Tangent X x →L[ℂ] Tangent X x →L[ℂ] Tangent X x :=
  TensorialAt.mkHom₂ (S.bracketOperation x) x
    (fun W _ => S.bracketOperation_tensorial_left x W)
    (fun V _ => S.bracketOperation_tensorial_right x V)

theorem bracketTensor_apply {V W : Field (X := X)} {x : X.Carrier}
    (hV : MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,V y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x)
    (hW : MDifferentiableAt (ModelWithCorners X)
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      (fun y => (⟨y,W y⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) x) :
    S.bracketTensor x (V x) (W x) = S.bracketOperation x V W :=
  TensorialAt.mkHom₂_apply _ _ hV hW

theorem mem_first_iff (x : X.Carrier) (v : Tangent X x) :
    v ∈ S.first x ↔ S.projector x v = v := by
  constructor
  · rintro ⟨w, rfl⟩; exact S.idempotent x w
  · intro hv; exact ⟨v,hv⟩

theorem mem_first_iff_complement_eq_zero (x : X.Carrier) (v : Tangent X x) :
    v ∈ S.first x ↔ S.complementAt x v = 0 := by
  rw [mem_first_iff, complementAt_apply, sub_eq_zero, eq_comm]

theorem holomorphicSectionOn_projectField {V : Field (X := X)} {U : Set X.Carrier}
    (hV : HolomorphicSectionOn X V U) : HolomorphicSectionOn X (S.projectField V) U :=
  S.holomorphic.comp_contMDiffOn hV

 

theorem integrable_first_of_bracketTensor_eq_zero
    (hB : ∀ x, S.bracketTensor x = 0) : Integrable X S.first := by
  intro U hU V W hV hW hPV hPW x hx
  have hV' := (hV x hx).contMDiffAt (hU.mem_nhds hx)
  have hW' := (hW x hx).contMDiffAt (hU.mem_nhds hx)
  have he := S.bracketTensor_apply (hV'.mdifferentiableAt (by simp))
    (hW'.mdifferentiableAt (by simp))
  rw [hB x] at he
  have hEV : S.projectField V =ᶠ[nhds x] V :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => (S.mem_first_iff y _).mp (hPV y hy))
  have hEW : S.projectField W =ᶠ[nhds x] W :=
    Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => (S.mem_first_iff y _).mp (hPW y hy))
  have hb := hEV.mlieBracketWithin_vectorField_eq_nhds (I := ModelWithCorners X)
    (s := Set.univ) hEW
  rw [VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_univ] at hb
  rw [mem_first_iff_complement_eq_zero, VectorField.mlieBracketWithin_of_isOpen hU hx]
  simpa only [bracketOperation, hb, zero_apply] using he.symm

 

theorem bracketTensor_eq_zero_of_integrable_first (hI : Integrable X S.first) :
    ∀ x, S.bracketTensor x = 0 := by
  intro x
  ext v w
  let V := FiberBundle.extend (Model X) v
  let W := FiberBundle.extend (Model X) w
  obtain ⟨U, hUn, hVU⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ω) (ModelWithCorners X) (Model X) v
  obtain ⟨U', hUn', hWU'⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ω) (ModelWithCorners X) (Model X) w
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (Filter.inter_mem hUn hUn')
  have hV : HolomorphicSectionOn X V O := hVU.mono (fun y hy => (hOsub hy).1)
  have hW : HolomorphicSectionOn X W O := hWU'.mono (fun y hy => (hOsub hy).2)
  have hmem := hI O hO (S.projectField V) (S.projectField W)
    (S.holomorphicSectionOn_projectField hV) (S.holomorphicSectionOn_projectField hW)
    (fun y _ => ⟨V y,rfl⟩) (fun y _ => ⟨W y,rfl⟩) x hxO
  rw [S.mem_first_iff_complement_eq_zero,
    VectorField.mlieBracketWithin_of_isOpen hO hxO] at hmem
  have he := S.bracketTensor_apply
    ((hV x hxO).contMDiffAt (hO.mem_nhds hxO) |>.mdifferentiableAt (by simp))
    ((hW x hxO).contMDiffAt (hO.mem_nhds hxO) |>.mdifferentiableAt (by simp))
  simpa [V, W, bracketOperation, hmem] using he

theorem integrable_first_iff_bracketTensor_eq_zero :
    Integrable X S.first ↔ ∀ x, S.bracketTensor x = 0 :=
  ⟨S.bracketTensor_eq_zero_of_integrable_first, S.integrable_first_of_bracketTensor_eq_zero⟩

 

theorem holomorphicSectionOn_bracketOperation {V W : Field (X := X)}
    {U : Set X.Carrier} (hU : IsOpen U)
    (hV : HolomorphicSectionOn X V U) (hW : HolomorphicSectionOn X W U) :
    HolomorphicSectionOn X (fun x => S.bracketOperation x V W) U := by
  have hPV := S.holomorphicSectionOn_projectField hV
  have hPW := S.holomorphicSectionOn_projectField hW
  have hbr : HolomorphicSectionOn X
      (VectorField.mlieBracketWithin (ModelWithCorners X) (S.projectField V) (S.projectField W) U) U := by
    intro x hx
    exact (hPV x hx).mlieBracketWithin_vectorField (hPW x hx)
      (hU.uniqueMDiffOn (I := ModelWithCorners X)) hx (by simp)
  have hbr' : HolomorphicSectionOn X
      (VectorField.mlieBracket (ModelWithCorners X) (S.projectField V) (S.projectField W)) U := by
    apply hbr.congr
    intro x hx
    simp only [VectorField.mlieBracketWithin_of_isOpen hU hx]
  exact hbr'.sub_section (S.holomorphicSectionOn_projectField hbr')

theorem holomorphicSectionOn_bracketTensor_apply {V W : Field (X := X)}
    {U : Set X.Carrier} (hU : IsOpen U)
    (hV : HolomorphicSectionOn X V U) (hW : HolomorphicSectionOn X W U) :
    HolomorphicSectionOn X (fun x => S.bracketTensor x (V x) (W x)) U := by
  apply (S.holomorphicSectionOn_bracketOperation hU hV hW).congr
  intro x hx
  congr 1
  exact S.bracketTensor_apply
    ((hV x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
    ((hW x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))

theorem range_complementAt (x : X.Carrier) :
    LinearMap.range (S.complementAt x).toLinearMap = S.second x := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change S.projector x (w - S.projector x w) = 0
    rw [map_sub, S.idempotent, sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v - S.projector x v = v
    rw [show S.projector x v = 0 from hv, sub_zero]

theorem ker_complementAt (x : X.Carrier) :
    LinearMap.ker (S.complementAt x).toLinearMap = S.first x := by
  ext v
  exact (S.mem_first_iff_complement_eq_zero x v).symm

theorem holomorphic_complement : ContMDiff
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun v : TangentBundle (ModelWithCorners X) X.Carrier =>
      (⟨v.proj, S.complementAt v.proj v.2⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) := by
  intro v
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hid : ContMDiffAt ((ModelWithCorners X).prod 𝓘(ℂ, Model X))
      ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
      (id : TangentBundle (ModelWithCorners X) X.Carrier → _) v := contMDiffAt_id
  have h1 := (contMDiffAt_totalSpace.mp hid).2
  have h2 := (contMDiffAt_totalSpace.mp (S.holomorphic v)).2
  apply (h1.sub h2).congr_of_eventuallyEq
  let e := trivializationAt (Model X) (Tangent X) v.proj
  have hbase : ∀ᶠ w : TangentBundle (ModelWithCorners X) X.Carrier in nhds v,
      w.proj ∈ e.baseSet :=
    (FiberBundle.continuous_proj (F := Model X) (E := Tangent X)).continuousAt.eventually
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' v.proj))
  filter_upwards [hbase] with w hw
  exact (e.linear ℂ hw).map_sub _ _

 

def swap : TangentSplitting X where
  projector := S.complementAt
  idempotent := by
    intro x v
    simp only [complementAt_apply, map_sub, S.idempotent, sub_self, sub_zero]
  holomorphic := S.holomorphic_complement
  first_positive := by
    intro x
    rw [S.range_complementAt]
    exact S.second_positive x
  second_positive := by
    intro x
    rw [S.ker_complementAt]
    exact S.first_positive x

@[simp] theorem swap_first : S.swap.first = S.second := by
  funext x; exact S.range_complementAt x

@[simp] theorem swap_second : S.swap.second = S.first := by
  funext x; exact S.ker_complementAt x

 

theorem integrable_both_iff_bracketTensors_eq_zero :
    (Integrable X S.first ∧ Integrable X S.second) ↔
      (∀ x, S.bracketTensor x = 0) ∧ (∀ x, S.swap.bracketTensor x = 0) := by
  rw [S.integrable_first_iff_bracketTensor_eq_zero,
    ← S.swap_first, S.swap.integrable_first_iff_bracketTensor_eq_zero]

end TangentSplitting

namespace AnalyticContinuation

variable {M E F : Type*} [TopologicalSpace M] [PreconnectedSpace M]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

 

theorem eq_univ_of_local_analytic_zero_locus {Z : Set M}
    (hlocal : ∀ x : M, ∃ e : OpenPartialHomeomorph M E, x ∈ e.source ∧
      ∃ f : E → F, AnalyticOnNhd ℂ f e.target ∧
        ∀ y ∈ e.source, y ∈ Z ↔ f (e y) = 0)
    (hne : (interior Z).Nonempty) : Z = univ := by
  have hc : IsClosed (interior Z) := by
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨e, hxe, f, hf, he⟩ := hlocal x
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) r
    have hU : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
    have hxU : x ∈ U := ⟨hxe, Metric.mem_ball_self hr⟩
    obtain ⟨y, hyU, hyI⟩ := mem_closure_iff.mp hx U hU hxU
    have hyE : e y ∈ Metric.ball (e x) r := hyU.2
    have him : IsOpen (e '' (U ∩ interior Z)) :=
      e.isOpen_image_of_subset_source (hU.inter isOpen_interior)
        (fun z hz => hz.1.1)
    have hey : e y ∈ e '' (U ∩ interior Z) := ⟨y,⟨hyU,hyI⟩,rfl⟩
    have hzero : f =ᶠ[nhds (e y)] 0 := by
      apply Filter.eventually_of_mem (him.mem_nhds hey)
      rintro z ⟨a,⟨haU,haI⟩,rfl⟩
      exact (he a haU.1).mp (interior_subset haI)
    have hball := (hf.mono hrsub).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (e x) r).isPreconnected hyE hzero
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hU.mem_nhds hxU)
    intro z hz
    exact (he z hz.1).mpr (hball hz.2)
  have hI : interior Z = univ := (show IsClopen (interior Z) from ⟨hc,isOpen_interior⟩).eq_univ hne
  exact univ_subset_iff.mp (hI ▸ (interior_subset : interior Z ⊆ Z))

end AnalyticContinuation

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

 

theorem bracketTensor_local_analytic_zero_locus (x : X.Carrier) :
    ∃ e : OpenPartialHomeomorph X.Carrier (Model X), x ∈ e.source ∧
      ∃ f : Model X → (Fin X.dim → Fin X.dim → Model X),
        AnalyticOnNhd ℂ f e.target ∧
        ∀ y ∈ e.source, S.bracketTensor y = 0 ↔ f (e y) = 0 := by
  let t := trivializationAt (Model X) (Tangent X) x
  let b := Pi.basisFun ℂ (Fin X.dim)
  let c := chartAt (Model X) x
  let e := c.restr t.baseSet
  let H := fun (y : X.Carrier) (i j : Fin X.dim) =>
    (t ⟨y,S.bracketTensor y (t.localFrame b i y) (t.localFrame b j y)⟩).2
  have hframe (i : Fin X.dim) : HolomorphicSectionOn X (t.localFrame b i) t.baseSet :=
    t.contMDiffOn_localFrame_baseSet ω b i
  have hH (i j : Fin X.dim) : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ, Model X) ω
      (fun y => H y i j) t.baseSet :=
    t.contMDiffOn_section_baseSet_iff.mp
      (S.holomorphicSectionOn_bracketTensor_apply t.open_baseSet (hframe i) (hframe j))
  have hsrc : e.source = c.source ∩ t.baseSet := c.restr_source' _ t.open_baseSet
  have htarg : e.target = c.target ∩ c.symm ⁻¹' t.baseSet := by
    rw [OpenPartialHomeomorph.restr_target, t.open_baseSet.interior_eq]
  refine ⟨e, ?_, (fun z => H (c.symm z)), ?_, ?_⟩
  · rw [hsrc]
    exact ⟨mem_chart_source (Model X) x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  · intro z hz
    rw [htarg] at hz
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    have hc : ContMDiffAt 𝓘(ℂ,Model X) (ModelWithCorners X) ω c.symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) x) hz.1
    exact ((hH i j).contMDiffAt (t.open_baseSet.mem_nhds hz.2) |>.comp z hc).contDiffAt.analyticAt
  · intro y hy
    rw [hsrc] at hy
    change S.bracketTensor y = 0 ↔ H (c.symm (c y)) = 0
    rw [c.left_inv hy.1]
    have hHval (i j : Fin X.dim) :
        H y i j = t.linearEquivAt ℂ y hy.2
          (S.bracketTensor y ((t.basisAt b hy.2) i) ((t.basisAt b hy.2) j)) := by
      simp only [H, Bundle.Trivialization.localFrame_apply_of_mem_baseSet t b hy.2,
        Bundle.Trivialization.linearEquivAt_apply]
    constructor
    · intro hz
      funext i j
      rw [hHval, hz]
      change (t.linearEquivAt ℂ y hy.2) 0 = 0
      exact map_zero _
    · intro hz
      apply ContinuousLinearMap.coe_injective
      apply (t.basisAt b hy.2).ext
      intro i
      apply ContinuousLinearMap.coe_injective
      apply (t.basisAt b hy.2).ext
      intro j
      have h := congrFun (congrFun hz i) j
      rw [hHval] at h
      apply (t.linearEquivAt ℂ y hy.2).injective
      change (t.linearEquivAt ℂ y hy.2) _ = (t.linearEquivAt ℂ y hy.2) 0
      rw [map_zero]
      exact h

 
theorem bracketTensor_eq_zero_of_open [ConnectedSpace X.Carrier]
    {U : Set X.Carrier} (hU : IsOpen U) (hne : U.Nonempty)
    (hB : ∀ x ∈ U, S.bracketTensor x = 0) : ∀ x, S.bracketTensor x = 0 := by
  have hne' : (interior {x | S.bracketTensor x = 0}).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨x, interior_maximal hB hU hx⟩
  have heq := AnalyticContinuation.eq_univ_of_local_analytic_zero_locus
    (S.bracketTensor_local_analytic_zero_locus) hne'
  intro x
  exact (Set.eq_univ_iff_forall.mp heq) x

end TangentSplitting
end

section

 

structure RationalFamily (X T : ComplexManifold.{u}) where
  finite : ℂ × T.Carrier → X.Carrier
  infinity : ℂ × T.Carrier → X.Carrier
  finite_holomorphic : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
    (ModelWithCorners X) ω finite
  infinity_holomorphic : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
    (ModelWithCorners X) ω infinity
  overlap : ∀ z : ℂ, z ≠ 0 → ∀ τ, finite (z,τ) = infinity (z⁻¹,τ)

 

structure CurveTangentSection {X : ComplexManifold.{u}} (g : RationalCurve X) where
  finite : ∀ z : ℂ, Tangent X (g.finite z)
  infinity : ∀ z : ℂ, Tangent X (g.infinity z)
  finite_holomorphic : ContMDiff 𝓘(ℂ, ℂ)
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun z => (⟨g.finite z, finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
  infinity_holomorphic : ContMDiff 𝓘(ℂ, ℂ)
    ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
    (fun z => (⟨g.infinity z, infinity z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))
  overlap : ∀ z : ℂ, z ≠ 0 → finite z = infinity z⁻¹

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

def curve (τ : T.Carrier) : RationalCurve X where
  finite z := G.finite (z,τ)
  infinity z := G.infinity (z,τ)
  finite_holomorphic := G.finite_holomorphic.comp (contMDiff_id.prodMk contMDiff_const)
  infinity_holomorphic := G.infinity_holomorphic.comp (contMDiff_id.prodMk contMDiff_const)
  overlap z hz := G.overlap z hz τ

 

def parameterDerivative (H : ℂ × T.Carrier → X.Carrier)
    (τ : T.Carrier) (v : Tangent T τ) (z : ℂ) : Tangent X (H (z,τ)) :=
  mfderiv (ModelWithCorners T) (ModelWithCorners X) (fun t => H (z,t)) τ v

lemma parameterDerivative_eq {H : ℂ × T.Carrier → X.Carrier}
    (hH : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T)) (ModelWithCorners X) ω H)
    (τ : T.Carrier) (v : Tangent T τ) (z : ℂ) :
    parameterDerivative H τ v z =
      mfderiv (𝓘(ℂ, ℂ).prod (ModelWithCorners T)) (ModelWithCorners X) H (z,τ) (0,v) := by
  have he := mfderiv_comp τ (hH.mdifferentiable (by simp) (z,τ))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id :
      MDifferentiableAt (ModelWithCorners T) (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
        (fun t : T.Carrier => (z,t)) τ)
  unfold parameterDerivative
  rw [show (fun t => H (z,t)) = H ∘ (fun t => (z,t)) from rfl, he, mfderiv_prod_right]
  rfl

lemma parameterDerivative_holomorphic {H : ℂ × T.Carrier → X.Carrier}
    (hH : ContMDiff (𝓘(ℂ, ℂ).prod (ModelWithCorners T)) (ModelWithCorners X) ω H)
    (τ : T.Carrier) (v : Tangent T τ) :
    ContMDiff 𝓘(ℂ, ℂ) ((ModelWithCorners X).prod 𝓘(ℂ, Model X)) ω
      (fun z => (⟨H (z,τ), parameterDerivative H τ v z⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) := by
  have hz : ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun z : ℂ => (⟨z,0⟩ : TangentBundle 𝓘(ℂ, ℂ) ℂ)) :=
    Bundle.contMDiff_zeroSection ℂ (TangentSpace 𝓘(ℂ, ℂ))
  have hc : ContMDiff 𝓘(ℂ, ℂ)
      ((ModelWithCorners T).prod 𝓘(ℂ, Model T)) ω
      (fun _ : ℂ => (⟨τ,v⟩ : TangentBundle (ModelWithCorners T) T.Carrier)) := contMDiff_const
  have hp := hz.prodMk hc
  have hq := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℂ, ℂ)) (I' := ModelWithCorners T)).comp hp
  have hr := (hH.contMDiff_tangentMap (m := ω) (by simp)).comp hq
  convert hr using 1
  funext z
  simp only [Function.comp_apply, tangentMap]
  change (⟨H (z,τ), parameterDerivative H τ v z⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier) =
    ⟨H (z,τ), mfderiv (𝓘(ℂ, ℂ).prod (ModelWithCorners T))
      (ModelWithCorners X) H (z,τ) (0,v)⟩
  rw [parameterDerivative_eq hH]

 

def derivativeSection (τ : T.Carrier) (v : Tangent T τ) : CurveTangentSection (G.curve τ) where
  finite := parameterDerivative G.finite τ v
  infinity := parameterDerivative G.infinity τ v
  finite_holomorphic := parameterDerivative_holomorphic G.finite_holomorphic τ v
  infinity_holomorphic := parameterDerivative_holomorphic G.infinity_holomorphic τ v
  overlap z hz := by
    unfold parameterDerivative
    rw [show (fun t => G.finite (z,t)) = (fun t => G.infinity (z⁻¹,t)) from funext (G.overlap z hz)]
    rfl

 
def twoPointEvaluation (a b : ℂ) (τ : T.Carrier) : X.Carrier × X.Carrier :=
  (G.finite (a,τ), G.finite (b,τ))

lemma twoPointEvaluation_holomorphic (a b : ℂ) :
    ContMDiff (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X)) ω
      (G.twoPointEvaluation a b) :=
  (G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)).prodMk
    (G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id))

lemma twoPointEvaluation_derivative (a b : ℂ) (τ : T.Carrier) (v : Tangent T τ) :
    mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
      (G.twoPointEvaluation a b) τ v =
      ((G.derivativeSection τ v).finite a, (G.derivativeSection τ v).finite b) := by
  change (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
    (fun t => (G.finite (a,t), G.finite (b,t))) τ) v =
    (parameterDerivative G.finite τ v a, parameterDerivative G.finite τ v b)
  have h (z : ℂ) : MDifferentiableAt (ModelWithCorners T) (ModelWithCorners X)
      (fun t => G.finite (z,t)) τ :=
    (G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp) τ
  rw [mfderiv_prodMk (h a) (h b)]
  rfl

 

theorem exists_section_endpoints {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (v : Tangent X (G.finite (a,τ))) (w : Tangent X (G.finite (b,τ))) :
    ∃ σ : CurveTangentSection (G.curve τ), σ.finite a = v ∧ σ.finite b = w := by
  obtain ⟨u,hu⟩ := hs (v,w)
  rw [G.twoPointEvaluation_derivative] at hu
  exact ⟨G.derivativeSection τ u, congrArg Prod.fst hu, congrArg Prod.snd hu⟩

end RationalFamily

namespace CurveTangentSection
variable {X : ComplexManifold.{u}} {g : RationalCurve X}

 

def project (S : TangentSplitting X) (σ : CurveTangentSection g) : CurveTangentSection g where
  finite z := S.projector (g.finite z) (σ.finite z)
  infinity z := S.projector (g.infinity z) (σ.infinity z)
  finite_holomorphic := S.holomorphic.comp σ.finite_holomorphic
  infinity_holomorphic := S.holomorphic.comp σ.infinity_holomorphic
  overlap z hz := by rw [g.overlap z hz, σ.overlap z hz]

lemma project_mem_first_finite (S : TangentSplitting X) (σ : CurveTangentSection g) (z : ℂ) :
    (σ.project S).finite z ∈ S.first (g.finite z) := ⟨σ.finite z,rfl⟩

lemma project_mem_first_infinity (S : TangentSplitting X) (σ : CurveTangentSection g) (z : ℂ) :
    (σ.project S).infinity z ∈ S.first (g.infinity z) := ⟨σ.infinity z,rfl⟩

end CurveTangentSection

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

 

theorem exists_first_section_zero_value (S : TangentSplitting X) {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (w : Tangent X (G.finite (b,τ))) (hw : w ∈ S.first (G.finite (b,τ))) :
    ∃ σ : CurveTangentSection (G.curve τ),
      (∀ z, σ.finite z ∈ S.first ((G.curve τ).finite z)) ∧
      (∀ z, σ.infinity z ∈ S.first ((G.curve τ).infinity z)) ∧
      σ.finite a = 0 ∧ σ.finite b = w := by
  obtain ⟨σ,ha,hb⟩ := G.exists_section_endpoints hs 0 w
  refine ⟨σ.project S,σ.project_mem_first_finite S,σ.project_mem_first_infinity S,?_,?_⟩
  · change S.projector _ (σ.finite a) = 0
    change S.projector (G.finite (a,τ)) (σ.finite a) = 0
    rw [ha]
    exact (S.projector _).map_zero
  · change S.projector _ (σ.finite b) = w
    rw [hb]
    exact (S.mem_first_iff _ w).mp hw

end RationalFamily

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma localFrame_sum (t : Trivialization (Model X)
    (Bundle.TotalSpace.proj : TangentBundle (ModelWithCorners X) X.Carrier → X.Carrier))
    [MemTrivializationAtlas t] {x : X.Carrier} (hx : x ∈ t.baseSet) (v : Tangent X x) :
    ∑ i : Fin X.dim, (t ⟨x,v⟩).2 i • t.localFrame (Pi.basisFun ℂ (Fin X.dim)) i x = v := by
  have h := (t.basisAt (Pi.basisFun ℂ (Fin X.dim)) hx).sum_repr v
  simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet t _ hx,
    Bundle.Trivialization.basisAt, Module.Basis.map_repr,
    Bundle.Trivialization.linearEquivAt_apply] using h

 

lemma bracketTensor_holomorphic_along {g : ℂ → X.Carrier}
    (hg : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω g)
    (v w : ∀ z : ℂ, Tangent X (g z))
    (hv : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)))
    (hw : ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,w z⟩ : TangentBundle (ModelWithCorners X) X.Carrier))) :
    ContMDiff 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g z,S.bracketTensor (g z) (v z) (w z)⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)) := by
  intro z
  let t := trivializationAt (Model X) (Tangent X) (g z)
  let b := Pi.basisFun ℂ (Fin X.dim)
  have hz : g z ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' (g z)
  have hsrc (v' : Tangent X (g z)) : (⟨g z,v'⟩ : TangentBundle (ModelWithCorners X) X.Carrier) ∈ t.source := by
    simpa only [t.mem_source] using hz
  apply (t.contMDiffAt_iff (f := fun q => (⟨g q,S.bracketTensor (g q) (v q) (w q)⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mpr
  refine ⟨hg z,?_⟩
  have hv' := ((t.contMDiffAt_iff (f := fun q => (⟨g q,v q⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mp (hv z)).2
  have hw' := ((t.contMDiffAt_iff (f := fun q => (⟨g q,w q⟩ :
    TangentBundle (ModelWithCorners X) X.Carrier)) (hsrc _)).mp (hw z)).2
  let H := fun (x : X.Carrier) (i j : Fin X.dim) =>
    (t ⟨x,S.bracketTensor x (t.localFrame b i x) (t.localFrame b j x)⟩).2
  have hframe (i : Fin X.dim) : HolomorphicSectionOn X (t.localFrame b i) t.baseSet :=
    t.contMDiffOn_localFrame_baseSet ω b i
  have hH (i j : Fin X.dim) : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,Model X) ω
      (fun x => H x i j) t.baseSet :=
    t.contMDiffOn_section_baseSet_iff.mp
      (S.holomorphicSectionOn_bracketTensor_apply t.open_baseSet (hframe i) (hframe j))
  let T := fun z : ℂ => ∑ i : Fin X.dim, ∑ j : Fin X.dim,
    ((t ⟨g z,v z⟩).2 i * (t ⟨g z,w z⟩).2 j) • H (g z) i j
  have hT : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω T z := by
    apply ContMDiffAt.sum
    intro i hi
    apply ContMDiffAt.sum
    intro j hj
    apply ContMDiffAt.smul (I := 𝓘(ℂ,ℂ))
      (f := fun q => (t ⟨g q,v q⟩).2 i * (t ⟨g q,w q⟩).2 j)
      (g := fun q => H (g q) i j)
    · exact ((contMDiffAt_pi_space.mp hv') i).mul ((contMDiffAt_pi_space.mp hw') j)
    · exact ((hH i j (g z) hz).contMDiffAt (t.open_baseSet.mem_nhds hz)).comp z (hg z)
  have he : (fun z => (t ⟨g z,S.bracketTensor (g z) (v z) (w z)⟩).2) =ᶠ[nhds z] T := by
    filter_upwards [(hg z).continuousAt.eventually (t.open_baseSet.mem_nhds hz)] with q hq
    have hvq := localFrame_sum t hq (v q)
    have hwq := localFrame_sum t hq (w q)
    change (t.linearEquivAt ℂ (g q) hq) (S.bracketTensor (g q) (v q) (w q)) = _
    conv_lhs => rw [←hvq,←hwq]
    simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    simp only [T,H,b,Bundle.Trivialization.linearEquivAt_apply,mul_comm]
  exact hT.congr_of_eventuallyEq he

end TangentSplitting

namespace CurveTangentSection
variable {X : ComplexManifold.{u}} {g : RationalCurve X}

 
def bracket (S : TangentSplitting X) (v w : CurveTangentSection g) : CurveTangentSection g where
  finite z := S.bracketTensor (g.finite z) (v.finite z) (w.finite z)
  infinity z := S.bracketTensor (g.infinity z) (v.infinity z) (w.infinity z)
  finite_holomorphic := S.bracketTensor_holomorphic_along g.finite_holomorphic
    v.finite w.finite v.finite_holomorphic w.finite_holomorphic
  infinity_holomorphic := S.bracketTensor_holomorphic_along g.infinity_holomorphic
    v.infinity w.infinity v.infinity_holomorphic w.infinity_holomorphic
  overlap z hz := by
    rw [g.overlap z hz,v.overlap z hz,w.overlap z hz]

end CurveTangentSection

open Filter

 
theorem twoChart_holomorphic_constant {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f k : ℂ → V} (hf : Differentiable ℂ f) (hk : ContinuousAt k 0)
    (he : ∀ z : ℂ, z ≠ 0 → f z = k z⁻¹) (z w : ℂ) : f z = f w := by
  have ht : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (nhds 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (nhds 0))
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    mem_cocompact.mpr ⟨{0},isCompact_singleton,by intro z hz; simpa using hz⟩
  have hlim : Tendsto f (cocompact ℂ) (nhds (k 0)) :=
    (hk.tendsto.comp ht).congr' (hz.mono fun z hz => (he z hz).symm)
  rw [hf.apply_eq_of_tendsto_cocompact z hlim,hf.apply_eq_of_tendsto_cocompact w hlim]

namespace RationalCurve
variable {X : ComplexManifold.{u}}
def constant (x : X.Carrier) : RationalCurve X where
  finite := fun _ => x
  infinity := fun _ => x
  finite_holomorphic := contMDiff_const
  infinity_holomorphic := contMDiff_const
  overlap _ _ := rfl
end RationalCurve

namespace CurveTangentSection
variable {X : ComplexManifold.{u}}
 
theorem constant_finite (x : X.Carrier) (σ : CurveTangentSection (RationalCurve.constant x))
    (z w : ℂ) : σ.finite z = σ.finite w := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let f := fun q : ℂ => (t ⟨x,σ.finite q⟩).2
  let k := fun q : ℂ => (t ⟨x,σ.infinity q⟩).2
  have hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω f := by
    intro q
    exact ((t.contMDiffAt_iff (f := fun q => (⟨x,σ.finite q⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp
      (σ.finite_holomorphic q)).2
  have hk : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Model X) ω k := by
    intro q
    exact ((t.contMDiffAt_iff (f := fun q => (⟨x,σ.infinity q⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)) (by simpa only [t.mem_source] using hx)).mp
      (σ.infinity_holomorphic q)).2
  have he : ∀ q : ℂ, q ≠ 0 → f q = k q⁻¹ := by
    intro q hq
    exact congrArg (fun v : Tangent X x => (t ⟨x,v⟩).2) (σ.overlap q hq)
  apply (t.linearEquivAt ℂ x hx).injective
  exact twoChart_holomorphic_constant
    ((contMDiff_iff_contDiff.mp hf).differentiable (by simp)) hk.continuous.continuousAt he z w
end CurveTangentSection

namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

lemma bracketTensor_projectors (x : X.Carrier) (v w : Tangent X x) :
    S.bracketTensor x (S.projector x v) (S.projector x w) = S.bracketTensor x v w := by
  let V := FiberBundle.extend (Model X) v
  let W := FiberBundle.extend (Model X) w
  have hV := FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) v
  have hW := FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) w
  have h1 := S.bracketTensor_apply (S.mdifferentiableAt_projectField hV)
    (S.mdifferentiableAt_projectField hW)
  have h2 := S.bracketTensor_apply hV hW
  have he (U : Field (X := X)) : S.projectField (S.projectField U) = S.projectField U := by
    funext y
    exact S.idempotent y (U y)
  have h3 : S.bracketOperation x (S.projectField (FiberBundle.extend (Model X) v))
      (S.projectField (FiberBundle.extend (Model X) w)) =
      S.bracketOperation x (FiberBundle.extend (Model X) v) (FiberBundle.extend (Model X) w) := by
    simp only [bracketOperation,he]
  simpa [projectField] using h1.trans (h3.trans h2.symm)

lemma complementAt_bracketTensor (x : X.Carrier) (v w : Tangent X x) :
    S.complementAt x (S.bracketTensor x v w) = S.bracketTensor x v w := by
  have h := S.bracketTensor_apply
    (FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) v)
    (FiberBundle.mdifferentiableAt_extend (ModelWithCorners X) (Model X) w)
  simp only [FiberBundle.extend_apply_self] at h
  rw [h]
  simp [bracketOperation,complementAt_apply,map_sub,S.idempotent]

end TangentSplitting
end


 

structure CurveBundleMap {X : ComplexManifold.{u}} (g h : RationalCurve X) where
  finite : ∀ z, Tangent X (g.finite z) →L[ℂ] Tangent X (h.finite z)
  infinity : ∀ z, Tangent X (g.infinity z) →L[ℂ] Tangent X (h.infinity z)
  overlap : ∀ z : ℂ, z ≠ 0 → finite z = infinity z⁻¹
  finite_holomorphic : ∀ (U : Set ℂ), IsOpen U → ∀ v : ∀ z, Tangent X (g.finite z),
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.finite z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U →
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨h.finite z,finite z (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U
  infinity_holomorphic : ∀ (U : Set ℂ), IsOpen U → ∀ v : ∀ z, Tangent X (g.infinity z),
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨g.infinity z,v z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U →
    ContMDiffOn 𝓘(ℂ,ℂ) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨h.infinity z,infinity z (v z)⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) U

namespace CurveBundleMap
variable {X : ComplexManifold.{u}} {g h : RationalCurve X}
def mapSection (A : CurveBundleMap g h) (σ : CurveTangentSection g) : CurveTangentSection h where
  finite z := A.finite z (σ.finite z)
  infinity z := A.infinity z (σ.infinity z)
  finite_holomorphic := contMDiffOn_univ.mp
    (A.finite_holomorphic univ isOpen_univ σ.finite σ.finite_holomorphic.contMDiffOn)
  infinity_holomorphic := contMDiffOn_univ.mp
    (A.infinity_holomorphic univ isOpen_univ σ.infinity σ.infinity_holomorphic.contMDiffOn)
  overlap z hz := by rw [A.overlap z hz,σ.overlap z hz]; rfl
end CurveBundleMap

 

structure NormalizedFactorTransport {X : ComplexManifold.{u}}
    (S : TangentSplitting X) (g : RationalCurve X) (b : ℂ) where
  factor : RationalCurve X
  diagonal : factor.finite b = g.finite b
  firstMap : CurveBundleMap g factor
  secondMap : CurveBundleMap factor (RationalCurve.constant (g.finite b))
  first_normalized : firstMap.finite b = S.projector (g.finite b)
  second_normalized : secondMap.finite b = S.complementAt (g.finite b)

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

 

theorem bracketTensor_zero_of_transport (S : TangentSplitting X) {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D : NormalizedFactorTransport S (G.curve τ) b) :
    S.bracketTensor (G.finite (b,τ)) = 0 := by
  ext v w
  obtain ⟨σ,haσ,hbσ⟩ := G.exists_section_endpoints hs 0 v
  obtain ⟨ζ,haζ,hbζ⟩ := G.exists_section_endpoints hs 0 w
  let σ' := D.firstMap.mapSection σ
  let ζ' := D.firstMap.mapSection ζ
  let β := CurveTangentSection.bracket S σ' ζ'
  let κ := D.secondMap.mapSection β
  have hk := CurveTangentSection.constant_finite ((G.curve τ).finite b) κ b a
  have hka : κ.finite a = 0 := by
    change D.secondMap.finite a (S.bracketTensor (D.factor.finite a)
      (D.firstMap.finite a (σ.finite a)) (D.firstMap.finite a (ζ.finite a))) = 0
    have hσ0 : D.firstMap.finite a (σ.finite a) = 0 :=
      (congrArg (D.firstMap.finite a) haσ).trans (map_zero _)
    have hζ0 : D.firstMap.finite a (ζ.finite a) = 0 :=
      (congrArg (D.firstMap.finite a) haζ).trans (map_zero _)
    rw [hσ0,hζ0]
    simp
  have hkb : κ.finite b = S.bracketTensor (G.finite (b,τ)) v w := by
    change D.secondMap.finite b (S.bracketTensor (D.factor.finite b)
      (D.firstMap.finite b (σ.finite b)) (D.firstMap.finite b (ζ.finite b))) = _
    rw [D.first_normalized,D.second_normalized,D.diagonal,hbσ,hbζ]
    change S.complementAt (G.finite (b,τ))
      (S.bracketTensor (G.finite (b,τ)) (S.projector (G.finite (b,τ)) v)
        (S.projector (G.finite (b,τ)) w)) = S.bracketTensor (G.finite (b,τ)) v w
    rw [S.bracketTensor_projectors,S.complementAt_bracketTensor]
  rw [hka,hkb] at hk
  exact hk

 

theorem integrable_first_of_transport [ConnectedSpace X.Carrier]
    (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D : ∀ τ, NormalizedFactorTransport S (G.curve τ) b)
    {U : Set X.Carrier} (hU : IsOpen U) (hn : U.Nonempty)
    (himage : U ⊆ Set.range (fun τ => G.finite (b,τ))) : Integrable X S.first := by
  apply S.integrable_first_of_bracketTensor_eq_zero
  apply S.bracketTensor_eq_zero_of_open hU hn
  intro x hx
  obtain ⟨τ,rfl⟩ := himage hx
  exact G.bracketTensor_zero_of_transport S (hs τ) (D τ)

end RationalFamily
end SplitTangent

open scoped Topology
open Filter
namespace SplitTangent

 

lemma map_nhds_eq_of_surjective_mfderiv {T X : ComplexManifold.{u}}
    {f : T.Carrier → X.Carrier} {t : T.Carrier}
    (hf : ContMDiffAt (ModelWithCorners T) (ModelWithCorners X) ω f t)
    (hs : Function.Surjective (mfderiv (ModelWithCorners T) (ModelWithCorners X) f t)) :
    Filter.map f (𝓝 t) = 𝓝 (f t) := by
  let e := extChartAt (ModelWithCorners T) t
  let d := extChartAt (ModelWithCorners X) (f t)
  let W := d ∘ f ∘ e.symm
  have hw : ContDiffAt ℂ ω W (e t) := by
    simpa [W,e,d,ModelWithCorners,contDiffWithinAt_univ] using (contMDiffAt_iff.mp hf).2
  have hder : mfderiv (ModelWithCorners T) (ModelWithCorners X) f t =
      fderiv ℂ W (e t) := by
    simp [mfderiv,hf.mdifferentiableAt (by simp),writtenInExtChartAt,W,e,d,ModelWithCorners]
    rfl
  have hmap : Filter.map W (𝓝 (e t)) = 𝓝 (W (e t)) :=
    (hw.hasStrictFDerivAt (by simp)).map_nhds_eq_of_surj
      (LinearMap.range_eq_top.mpr (hder ▸ hs))
  have he : Filter.map e.symm (𝓝 (e t)) = 𝓝 t := by
    simpa [e,ModelWithCorners] using
      (map_extChartAt_symm_nhdsWithin_range (I := ModelWithCorners T) t)
  have hd : Filter.map d.symm (𝓝 (d (f t))) = 𝓝 (f t) := by
    simpa [d,ModelWithCorners] using
      (map_extChartAt_symm_nhdsWithin_range (I := ModelWithCorners X) (f t))
  have hwet : W (e t) = d (f t) := by
    simp [W,e]
  have heq : d.symm ∘ W =ᶠ[𝓝 (e t)] f ∘ e.symm := by
    have hct : ContinuousAt (f ∘ e.symm) (e t) := by
      have hc : ContinuousAt f (e.symm (e t)) := by simpa [e] using hf.continuousAt
      exact hc.comp (continuousAt_extChartAt_symm (I := ModelWithCorners T) t)
    have hm : ∀ᶠ z in 𝓝 (e t), f (e.symm z) ∈ d.source := by
      apply hct.eventually
      simpa [e,d] using extChartAt_source_mem_nhds (I := ModelWithCorners X) (f t)
    filter_upwards [hm] with z hz
    exact d.left_inv hz
  calc
    Filter.map f (𝓝 t) = Filter.map (f ∘ e.symm) (𝓝 (e t)) := by rw [← he,Filter.map_map]
    _ = Filter.map (d.symm ∘ W) (𝓝 (e t)) := Filter.map_congr heq.symm
    _ = 𝓝 (f t) := by rw [← Filter.map_map,hmap,hwet,hd]

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

lemma endpoint_derivative_surjective {a b : ℂ} {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    Function.Surjective (mfderiv (ModelWithCorners T) (ModelWithCorners X)
      (fun t => G.finite (b,t)) τ) := by
  intro w
  obtain ⟨v,hv⟩ := hs (0,w)
  have hh := congrArg Prod.snd hv
  rw [G.twoPointEvaluation_derivative] at hh
  exact ⟨v,hh⟩

 
lemma endpoint_range_open {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ)) :
    IsOpen (Set.range (fun τ => G.finite (b,τ))) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨τ,rfl⟩ := hx
  have hf : ContMDiffAt (ModelWithCorners T) (ModelWithCorners X) ω
      (fun t => G.finite (b,t)) τ :=
    (G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt
  have hm := map_nhds_eq_of_surjective_mfderiv hf (G.endpoint_derivative_surjective (hs τ))
  rw [← hm]
  exact Filter.mem_map.mpr (by simp)

 

theorem integrable_first_of_submersive_transport [ConnectedSpace X.Carrier]
    [Nonempty T.Carrier] (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D : ∀ τ, NormalizedFactorTransport S (G.curve τ) b) : Integrable X S.first := by
  exact G.integrable_first_of_transport S hs D (G.endpoint_range_open hs)
    (Set.range_nonempty _) (fun _ h => h)

end RationalFamily
end SplitTangent

namespace SplitTangent.RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)
 

theorem integrable_both_of_submersive_transport [ConnectedSpace X.Carrier]
    [Nonempty T.Carrier] (S : TangentSplitting X) {a b : ℂ}
    (hs : ∀ τ, Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation a b) τ))
    (D₁ : ∀ τ, NormalizedFactorTransport S (G.curve τ) b)
    (D₂ : ∀ τ, NormalizedFactorTransport S.swap (G.curve τ) b) :
    Integrable X S.first ∧ Integrable X S.second := by
  refine ⟨G.integrable_first_of_submersive_transport S hs D₁,?_⟩
  simpa only [TangentSplitting.swap_first] using
    G.integrable_first_of_submersive_transport S.swap hs D₂
end SplitTangent.RationalFamily

end

end OAI
