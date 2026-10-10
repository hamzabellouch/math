import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace OAI

noncomputable section

/-! Graph charts and atlas of the complex Grassmannian. -/

section
open scoped BigOperators
namespace Kaplansky.ComplexGrassmann

abbrev GraphHorizontal (s : ℕ) := Fin s → ℂ
abbrev GraphVertical (k : ℕ) := Fin k → ℂ
abbrev GraphAmbient (s k : ℕ) := GraphHorizontal s × GraphVertical k
abbrev GraphMap (s k : ℕ) := GraphHorizontal s →ₗ[ℂ] GraphVertical k
abbrev Components (s k : ℕ) := Fin (s+k) → ℂ
abbrev GraphFrame (s k : ℕ) := Components s k ≃ₗ[ℂ] GraphAmbient s k

/-- Actual complex s-planes in complex dimension s+k. -/
def Grassmann (s k : ℕ) := {P : Submodule ℂ (Components s k) // Module.finrank ℂ P=s}

variable {s k : ℕ}

/-- The usual graph chart, transported by an arbitrary linear splitting. -/
def graphPlane (F : (GraphFrame s k)) (A : (GraphMap s k)) : Submodule ℂ (Components s k) :=
  A.graph.comap F.toLinearMap

@[simp] theorem mem_graphPlane (F : (GraphFrame s k)) (A : (GraphMap s k)) (z : (Components s k)) :
    z ∈ graphPlane F A ↔ (F z).2=A (F z).1 := Iff.rfl

def graphPlaneEquiv (F : (GraphFrame s k)) (A : (GraphMap s k)) : (GraphHorizontal s) ≃ₗ[ℂ] graphPlane F A where
  toFun v := ⟨F.symm (v,A v),by simp⟩
  invFun z := (F z.val).1
  left_inv v := by simp
  right_inv z := by
    apply Subtype.ext
    apply F.injective
    change F (F.symm ((F z.val).1,A (F z.val).1))=F z.val
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl z.property.symm
  map_add' v w := by
    apply Subtype.ext
    change F.symm (v+w,A (v+w))=F.symm (v,A v)+F.symm (w,A w)
    rw [map_add]
    exact F.symm.map_add (v,A v) (w,A w)
  map_smul' c v := by
    apply Subtype.ext
    change F.symm (c • v,A (c • v))=c • F.symm (v,A v)
    rw [map_smul]
    exact F.symm.map_smul c (v,A v)

theorem graphPlane_finrank (F : (GraphFrame s k)) (A : (GraphMap s k)) : Module.finrank ℂ (graphPlane F A)=s := by
  rw [← (graphPlaneEquiv F A).finrank_eq]
  simp

def graphPoint (F : (GraphFrame s k)) (A : (GraphMap s k)) : (Grassmann s k) := ⟨graphPlane F A,graphPlane_finrank F A⟩

theorem graphPlane_injective (F : (GraphFrame s k)) : Function.Injective (graphPlane F) := by
  intro A B h
  apply LinearMap.ext
  intro v
  have hz : F.symm (v,A v) ∈ graphPlane F B := by
    rw [← h]
    simp
  simpa using hz

/-- A plane is in a splitting's graph domain exactly when its projection to
the horizontal factor is bijective. This is independent of its chosen basis. -/
def InGraphChart (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) : Prop :=
  Function.Bijective (fun z : P => (F z.val).1)

theorem graphPlane_inChart (F : (GraphFrame s k)) (A : (GraphMap s k)) : InGraphChart F (graphPlane F A) :=
  (graphPlaneEquiv F A).symm.bijective

def graphProjection (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) : P →ₗ[ℂ] (GraphHorizontal s) :=
  (LinearMap.fst ℂ (GraphHorizontal s) (GraphVertical k)).comp (F.toLinearMap.comp P.subtype)

def graphCoordinate (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) (h : InGraphChart F P) : (GraphMap s k) :=
  (LinearMap.snd ℂ (GraphHorizontal s) (GraphVertical k)).comp (F.toLinearMap.comp
    (P.subtype.comp (LinearEquiv.ofBijective (graphProjection F P) h).symm.toLinearMap))

theorem graphCoordinate_plane (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) (h : InGraphChart F P) :
    graphPlane F (graphCoordinate F P h)=P := by
  let e := LinearEquiv.ofBijective (graphProjection F P) h
  have he (z : P) : e z=(F z.val).1 := rfl
  have hi (v : (GraphHorizontal s)) : (F (e.symm v).val).1=v := e.apply_symm_apply v
  ext z
  constructor
  · intro hz
    have hzz : z=(e.symm (F z).1).val := by
      apply F.injective
      exact Prod.ext (hi _).symm hz
    rw [hzz]
    exact (e.symm _).property
  · intro hz
    change (F z).2=(F (e.symm (F z).1).val).2
    have hh : e.symm (F z).1=⟨z,hz⟩ := e.symm_apply_apply ⟨z,hz⟩
    rw [hh]

theorem inGraphChart_iff (F : (GraphFrame s k)) (P : Submodule ℂ (Components s k)) :
    InGraphChart F P ↔ ∃ A : (GraphMap s k), P=graphPlane F A := by
  constructor
  · intro h
    exact ⟨graphCoordinate F P h,(graphCoordinate_plane F P h).symm⟩
  · rintro ⟨A,rfl⟩
    exact graphPlane_inChart F A

/-- Every actual s-plane is the center of a graph chart. -/
theorem graph_charts_cover (P : Submodule ℂ (Components s k)) (hP : Module.finrank ℂ P=s) :
    ∃ F : (GraphFrame s k), graphPlane F 0=P := by
  obtain ⟨Q,hQ⟩ := P.exists_isCompl
  have hsum := Submodule.finrank_add_eq_of_isCompl hQ
  have hV : Module.finrank ℂ (Components s k)=s+k := by simp [Components]
  have hq : Module.finrank ℂ Q=k := by omega
  obtain ⟨ep⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq (R := ℂ)
    (M := (GraphHorizontal s)) (M' := P)).mpr (by simp [hP])
  obtain ⟨eq⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq (R := ℂ)
    (M := (GraphVertical k)) (M' := Q)).mpr (by simp [hq])
  let e : (GraphAmbient s k) ≃ₗ[ℂ] (Components s k) :=
    (ep.prodCongr eq).trans (P.prodEquivOfIsCompl Q hQ)
  refine ⟨e.symm,?_⟩
  ext z
  constructor
  · intro hz
    have hv : (e.symm z).2=0 := hz
    have he : z=e ((e.symm z).1,0) := by
      rw [← hv]
      exact (e.apply_symm_apply z).symm
    rw [he]
    change ((ep (e.symm z).1 : P) : (Components s k))+((eq 0 : Q) : (Components s k)) ∈ P
    simp
  · intro hz
    have he : e (ep.symm ⟨z,hz⟩,0)=z := by simp [e,Submodule.coe_prodEquivOfIsCompl']
    have hi := congrArg e.symm he
    simp only [LinearEquiv.symm_apply_apply] at hi
    change (e.symm z).2=0
    exact (congrArg Prod.snd hi).symm

theorem graph_model_finrank : Module.finrank ℂ (GraphMap s k)=s*k := by
  simp [GraphMap,GraphHorizontal,GraphVertical,Module.finrank_linearMap]

end Kaplansky.ComplexGrassmann

end

section
open scoped ContDiff
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

abbrev GraphSlope (s k : ℕ) := (GraphHorizontal s) →L[ℂ] (GraphVertical k)

def graphInclusion (A : (GraphSlope s k)) : (GraphHorizontal s) →L[ℂ] (GraphAmbient s k) :=
  ContinuousLinearMap.inl ℂ (GraphHorizontal s) (GraphVertical k)+
    (ContinuousLinearMap.inr ℂ (GraphHorizontal s) (GraphVertical k)).comp A

@[simp] theorem graphInclusion_apply (A : (GraphSlope s k)) (v : (GraphHorizontal s)) : graphInclusion A v=(v,A v) := by
  simp [graphInclusion]

def graphTransport (F G : (GraphFrame s k)) : (GraphAmbient s k) →L[ℂ] (GraphAmbient s k) :=
  (F.symm.trans G).toContinuousLinearEquiv.toContinuousLinearMap

def graphTop (F G : (GraphFrame s k)) (A : (GraphSlope s k)) : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) :=
  (ContinuousLinearMap.fst ℂ (GraphHorizontal s) (GraphVertical k)).comp ((graphTransport F G).comp (graphInclusion A))

def graphBottom (F G : (GraphFrame s k)) (A : (GraphSlope s k)) : (GraphSlope s k) :=
  (ContinuousLinearMap.snd ℂ (GraphHorizontal s) (GraphVertical k)).comp ((graphTransport F G).comp (graphInclusion A))

@[simp] theorem graphTop_apply (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (v : (GraphHorizontal s)) :
    graphTop F G A v=(G (F.symm (v,A v))).1 := by simp [graphTop,graphTransport]

@[simp] theorem graphBottom_apply (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (v : (GraphHorizontal s)) :
    graphBottom F G A v=(G (F.symm (v,A v))).2 := by simp [graphBottom,graphTransport]

/-- The exact change of graph slope: bottom block times inverse top block. -/
def graphTransition (F G : (GraphFrame s k)) (A : (GraphSlope s k)) : (GraphSlope s k) :=
  (graphBottom F G A).comp (Ring.inverse (graphTop F G A))

theorem graphTop_contDiff (F G : (GraphFrame s k)) : ContDiff ℂ ∞ (graphTop F G) := by
  exact contDiff_const.clm_comp (contDiff_const.clm_comp
    (contDiff_const.add (contDiff_const.clm_comp contDiff_id)))

theorem graphBottom_contDiff (F G : (GraphFrame s k)) : ContDiff ℂ ∞ (graphBottom F G) := by
  exact contDiff_const.clm_comp (contDiff_const.clm_comp
    (contDiff_const.add (contDiff_const.clm_comp contDiff_id)))

theorem graphOverlap_open (F G : (GraphFrame s k)) : IsOpen {A : (GraphSlope s k) | IsUnit (graphTop F G A)} :=
  Units.isOpen.preimage (graphTop_contDiff F G).continuous

theorem graphTransition_contDiffAt (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (hA : IsUnit (graphTop F G A)) :
    ContDiffAt ℂ ∞ (graphTransition F G) A := by
  obtain ⟨u,hu⟩ := hA
  have hinv : ContDiffAt ℂ ∞ Ring.inverse (graphTop F G A) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℂ u
  exact (graphBottom_contDiff F G).contDiffAt.clm_comp (hinv.comp A (graphTop_contDiff F G).contDiffAt)

theorem graphTop_inverse_apply (F G : (GraphFrame s k)) (A : (GraphSlope s k))
    (hA : IsUnit (graphTop F G A)) (v : (GraphHorizontal s)) :
    graphTop F G A (Ring.inverse (graphTop F G A) v)=v := by
  have h := congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v)
    (Ring.mul_inverse_cancel (graphTop F G A) hA)
  exact h

theorem graphTop_inverse_apply' (F G : (GraphFrame s k)) (A : (GraphSlope s k))
    (hA : IsUnit (graphTop F G A)) (v : (GraphHorizontal s)) :
    Ring.inverse (graphTop F G A) (graphTop F G A v)=v := by
  have h := congrArg (fun L : (GraphHorizontal s) →L[ℂ] (GraphHorizontal s) => L v)
    (Ring.inverse_mul_cancel (graphTop F G A) hA)
  exact h

/-- On overlap, the rational transition describes the identical actual plane. -/
theorem graphTransition_plane (F G : (GraphFrame s k)) (A : (GraphSlope s k)) (hA : IsUnit (graphTop F G A)) :
    graphPlane G (graphTransition F G A).toLinearMap=graphPlane F A.toLinearMap := by
  ext z
  constructor
  · intro hz
    let v := Ring.inverse (graphTop F G A) (G z).1
    have htop : (G (F.symm (v,A v))).1=(G z).1 := by
      simpa only [graphTop_apply] using graphTop_inverse_apply F G A hA (G z).1
    have hbottom : (G z).2=(G (F.symm (v,A v))).2 := by
      change (G z).2=graphBottom F G A v at hz
      simpa only [graphBottom_apply] using hz
    have he : z=F.symm (v,A v) := G.injective (Prod.ext htop.symm hbottom)
    rw [he]
    simp
  · intro hz
    have he : F.symm ((F z).1,A (F z).1)=z := by
      apply F.injective
      rw [LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hz.symm
    have htop : graphTop F G A (F z).1=(G z).1 := by rw [graphTop_apply,he]
    change (G z).2=graphBottom F G A (Ring.inverse (graphTop F G A) (G z).1)
    rw [← htop,graphTop_inverse_apply' F G A hA,graphBottom_apply,he]

theorem inGraphChart_iff_unit (F G : (GraphFrame s k)) (A : (GraphSlope s k)) :
    InGraphChart G (graphPlane F A.toLinearMap) ↔ IsUnit (graphTop F G A) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  let e := graphPlaneEquiv F A.toLinearMap
  have he : (fun v : (GraphHorizontal s) => (G (e v).val).1)=graphTop F G A := by
    funext v
    simp [graphTop_apply,e,graphPlaneEquiv]
  constructor
  · intro h
    rw [← he]
    exact h.comp e.bijective
  · intro h
    rw [← he] at h
    have hh := h.comp e.symm.bijective
    change Function.Bijective (fun z : graphPlane F A.toLinearMap => (G z.val).1)
    convert! hh using 1
    funext z
    change (G z.val).1=(G (e (e.symm z)).val).1
    rw [e.apply_symm_apply]

end Kaplansky.ComplexGrassmann

end

open scoped ContDiff
open Set
namespace Kaplansky.ComplexGrassmann
variable {s k : ℕ}

def slopePoint (F : (GraphFrame s k)) (A : (GraphSlope s k)) : (Grassmann s k) := graphPoint F A.toLinearMap

theorem slopePoint_injective (F : (GraphFrame s k)) : Function.Injective (slopePoint F) := by
  intro A B h
  have he := graphPlane_injective F (congrArg Subtype.val h)
  exact ContinuousLinearMap.coe_injective he

def slopeCoordinate (F : (GraphFrame s k)) (P : (Grassmann s k)) : (GraphSlope s k) := by
  classical
  exact if h : InGraphChart F P.val then (graphCoordinate F P.val h).toContinuousLinearMap else 0

theorem slopePoint_coordinate (F : (GraphFrame s k)) (P : (Grassmann s k)) (h : InGraphChart F P.val) :
    slopePoint F (slopeCoordinate F P)=P := by
  apply Subtype.ext
  simp only [slopeCoordinate,dite_eq_left h,slopePoint,graphPoint]
  exact graphCoordinate_plane F P.val h

theorem slopeCoordinate_point (F : (GraphFrame s k)) (A : (GraphSlope s k)) :
    slopeCoordinate F (slopePoint F A)=A := by
  apply slopePoint_injective F
  exact slopePoint_coordinate F _ (graphPlane_inChart F A.toLinearMap)

/-- The (Grassmann s k) topology is specified by its full graph atlas on actual
subspaces. The following theorems verify that these maps are open charts. -/
instance grassmannTopology : TopologicalSpace (Grassmann s k) where
  IsOpen U := ∀ F : (GraphFrame s k), IsOpen (slopePoint F ⁻¹' U)
  isOpen_univ := by intro F; simp
  isOpen_inter := by intro s t hs ht F; exact (hs F).inter (ht F)
  isOpen_sUnion := by
    intro S hS F
    rw [sUnion_eq_biUnion,preimage_iUnion]
    apply isOpen_iUnion
    intro s
    rw [preimage_iUnion]
    exact isOpen_iUnion (fun hs => hS s hs F)

theorem slopePoint_continuous (F : (GraphFrame s k)) : Continuous (slopePoint F) := by
  apply continuous_def.mpr
  intro s hs
  exact hs F

theorem slopePoint_image_preimage (F G : (GraphFrame s k)) (U : Set (GraphSlope s k)) :
    slopePoint G ⁻¹' (slopePoint F '' U)=
      {A : (GraphSlope s k) | IsUnit (graphTop G F A)} ∩ graphTransition G F ⁻¹' U := by
  ext A
  constructor
  · rintro ⟨B,hB,he⟩
    have hp : graphPlane F B.toLinearMap=graphPlane G A.toLinearMap := congrArg Subtype.val he
    have hc : InGraphChart F (graphPlane G A.toLinearMap) := by
      rw [← hp]
      exact graphPlane_inChart F B.toLinearMap
    have hu := (inGraphChart_iff_unit G F A).mp hc
    have ht : graphTransition G F A=B := by
      apply slopePoint_injective F
      apply Subtype.ext
      exact (graphTransition_plane G F A hu).trans hp.symm
    refine ⟨hu,?_⟩
    change graphTransition G F A ∈ U
    rw [ht]
    exact hB
  · rintro ⟨hu,hU⟩
    refine ⟨graphTransition G F A,hU,?_⟩
    apply Subtype.ext
    exact graphTransition_plane G F A hu

theorem slopePoint_isOpenMap (F : (GraphFrame s k)) : IsOpenMap (slopePoint F) := by
  intro U hU G
  rw [slopePoint_image_preimage]
  have hc : ContinuousOn (graphTransition G F) {A | IsUnit (graphTop G F A)} :=
    fun A hA => (graphTransition_contDiffAt G F A hA).continuousAt.continuousWithinAt
  exact hc.isOpen_inter_preimage (graphOverlap_open G F) hU

def graphPartialEquiv (F : (GraphFrame s k)) : PartialEquiv (GraphSlope s k) (Grassmann s k) where
  toFun := slopePoint F
  invFun := slopeCoordinate F
  source := univ
  target := {P | InGraphChart F P.val}
  map_source' A _ := graphPlane_inChart F A.toLinearMap
  map_target' _ _ := mem_univ _
  left_inv' A _ := slopeCoordinate_point F A
  right_inv' P h := slopePoint_coordinate F P h

/-- A genuine open chart, with all s*k complex graph coordinates as its target. -/
def grassmannChart (F : (GraphFrame s k)) : OpenPartialHomeomorph (Grassmann s k) (GraphSlope s k) :=
  (OpenPartialHomeomorph.ofContinuousOpen (graphPartialEquiv F)
    (slopePoint_continuous F).continuousOn (slopePoint_isOpenMap F) isOpen_univ).symm

@[simp] theorem grassmannChart_source (F : (GraphFrame s k)) :
    (grassmannChart F).source={P | InGraphChart F P.val} := rfl

@[simp] theorem grassmannChart_target (F : (GraphFrame s k)) : (grassmannChart F).target=univ := rfl

@[simp] theorem grassmannChart_apply (F : (GraphFrame s k)) (P : (Grassmann s k)) :
    grassmannChart F P=slopeCoordinate F P := rfl

@[simp] theorem grassmannChart_symm_apply (F : (GraphFrame s k)) (A : (GraphSlope s k)) :
    (grassmannChart F).symm A=slopePoint F A := rfl

theorem grassmann_atlas_covers (P : (Grassmann s k)) : ∃ F : (GraphFrame s k), P ∈ (grassmannChart F).source := by
  obtain ⟨F,hF⟩ := graph_charts_cover P.val P.property
  refine ⟨F,?_⟩
  change InGraphChart F P.val
  rw [← hF]
  exact graphPlane_inChart F 0

theorem grassmann_chart_transition (F G : (GraphFrame s k)) (A : (GraphSlope s k))
    (hA : IsUnit (graphTop F G A)) :
    grassmannChart G ((grassmannChart F).symm A)=graphTransition F G A := by
  apply slopePoint_injective G
  rw [grassmannChart_apply,grassmannChart_symm_apply,
    slopePoint_coordinate G _ ((inGraphChart_iff_unit F G A).mpr hA)]
  apply Subtype.ext
  exact (graphTransition_plane F G A hA).symm

/-- Smoothness on every actual chart overlap, with no assumed transition law. -/
theorem grassmann_chart_transition_smooth (F G : (GraphFrame s k)) :
    ContDiffOn ℂ ∞ (fun A => grassmannChart G ((grassmannChart F).symm A))
      {A | IsUnit (graphTop F G A)} := by
  apply (show ContDiffOn ℂ ∞ (graphTransition F G) {A | IsUnit (graphTop F G A)} from
    fun A hA => (graphTransition_contDiffAt F G A hA).contDiffWithinAt).congr
  intro A hA
  exact grassmann_chart_transition F G A hA

end Kaplansky.ComplexGrassmann

end

end OAI
