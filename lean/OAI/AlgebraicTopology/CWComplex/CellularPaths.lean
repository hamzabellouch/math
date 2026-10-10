import OAI.AlgebraicTopology.CWComplex.Collar
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp] theorem homologyOneMap_const (y : Y) : homologyOneMap (ContinuousMap.const X y) = 0 := by
  apply LinearMap.ext
  intro h
  obtain ⟨z,rfl⟩ := (boundaries (univ : Set X)).mkQ_surjective h
  change (boundaries univ).mkQ (cycleMap (ContinuousMap.const X y) _ z) = 0
  have he : cycleMap (ContinuousMap.const X y) (mapsTo_univ _ _) z = 0 := by
    apply Subtype.ext
    exact pushN₁_const y z.val
  rw [he,map_zero]

variable {J : Type*} (y₀ : Y)

def fiberInclusion (j : J) : C(Y,(Σ _ : J,Y)) := ⟨@Sigma.mk J (fun _ : J => Y) j,by exact @continuous_sigmaMk J (fun _ : J => Y) (fun _ => inferInstance) j⟩
def fiberProjection (j : J) : C((Σ _ : J,Y),Y) :=
  ⟨fun z => if z.1 = j then z.2 else y₀,continuous_sigma (fun k => by
    dsimp only
    by_cases h : k = j
    · simp only [h,ite_true]
      exact continuous_id
    · simp only [ite_eq_right h]
      exact continuous_const)⟩

@[simp] theorem fiberProjection_inclusion (j k : J) :
    (fiberProjection y₀ j).comp (fiberInclusion k) =
      if k = j then ContinuousMap.id Y else ContinuousMap.const Y y₀ := by
  ext y
  by_cases h : k = j <;> simp [fiberProjection,fiberInclusion,h]

theorem pushN₁_fiber_cube (j : J) (σ : Cube₁ (Σ _ : J,Y)) :
    pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) (gen₁ σ)) =
      if (σ 0).1 = j then gen₁ σ else 0 := by
  obtain ⟨k,g,hg,he⟩ := σ.continuous.exists_lift_sigma
  have he₀ : (σ 0).1 = k := congrArg Sigma.fst (congrFun he 0)
  by_cases h : k = j
  · have hh := he₀.trans h
    rw [ite_eq_left hh,← pushN₁_comp]
    rw [pushN₁_gen]
    change gen₁ (((fiberInclusion j).comp (fiberProjection y₀ j)).comp σ) = gen₁ σ
    congr 1
    apply ContinuousMap.ext
    intro t
    rw [ContinuousMap.comp_apply,ContinuousMap.comp_apply,congrFun he t]
    subst j
    simp only [Function.comp_apply,fiberProjection,fiberInclusion,ContinuousMap.coe_mk,ite_true]
  · rw [ite_eq_right (fun hh => h (he₀.symm.trans hh))]
    have hc : (fiberProjection y₀ j).comp σ = ContinuousMap.const I y₀ := by
      ext t
      rw [ContinuousMap.comp_apply,congrFun he t]
      exact ite_eq_right h
    rw [pushN₁_gen]
    rw [hc]
    have hz : gen₁ (ContinuousMap.const I y₀) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨y₀,rfl⟩)
    rw [hz,map_zero]

variable (e : HomologyOne Y ≃ₗ[ℤ] ℤ)

def sigmaHomologyBasisMap : (J →₀ ℤ) →ₗ[ℤ] HomologyOne (Σ _ : J,Y) :=
  Finsupp.linearCombination ℤ (fun j => homologyOneMap (fiberInclusion j) (e.symm 1))

theorem sigmaHomologyBasis_coeff (c : J →₀ ℤ) (j : J) :
    e (homologyOneMap (fiberProjection y₀ j) (sigmaHomologyBasisMap e c)) = c j := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,Finsupp.add_apply,hc,hd]
  | single k n =>
    rw [sigmaHomologyBasisMap,Finsupp.linearCombination_single,map_smul,map_smul]
    rw [← LinearMap.comp_apply,← homologyOneMap_comp,fiberProjection_inclusion]
    by_cases h : k = j
    · subst k
      simp
    · simp [h,Finsupp.single_eq_of_ne (Ne.symm h)]

include y₀ in
theorem sigmaHomologyBasis_injective : Function.Injective (sigmaHomologyBasisMap (J:=J) e) := by
  intro a b h
  ext j
  rw [← sigmaHomologyBasis_coeff y₀ e a j,← sigmaHomologyBasis_coeff y₀ e b j,h]

theorem finite_fiber_decomposition (c : C₁ (Σ _ : J,Y)) :
    ∃ S : Finset J, ∑ j ∈ S, pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) ((D₁ _).mkQ c)) = (D₁ _).mkQ c := by
  classical
  let S := c.support.image (fun σ => (σ 0).1)
  refine ⟨S,?_⟩
  have hgen (σ : Cube₁ (Σ _ : J,Y)) (hσ : σ ∈ c.support) :
      ∑ j ∈ S, pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) (gen₁ σ)) = gen₁ σ := by
    simp_rw [pushN₁_fiber_cube]
    rw [Finset.sum_ite_eq]
    exact ite_eq_left (Finset.mem_image.mpr ⟨σ,hσ,rfl⟩)
  have hn (σ : Cube₁ (Σ _ : J,Y)) (m : ℤ) : (D₁ _).mkQ (Finsupp.single σ m) = m • gen₁ σ := by
    rw [← Finsupp.smul_single_one,map_smul]; rfl
  have hz : (D₁ _).mkQ c = ∑ σ ∈ c.support, c σ • gen₁ σ := by
    conv_lhs => rw [← Finsupp.sum_single c]
    simp only [Finsupp.sum,map_sum,hn]
  rw [hz]
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← Finset.smul_sum]
  exact congrArg (c σ • ·) (hgen σ hσ)

include y₀ in
theorem sigmaHomologyBasis_surjective : Function.Surjective (sigmaHomologyBasisMap (J:=J) e) := by
  intro h
  obtain ⟨z,rfl⟩ := (boundaries (univ : Set (Σ _ : J,Y))).mkQ_surjective h
  obtain ⟨c,hc⟩ := (D₁ _).mkQ_surjective z.val
  obtain ⟨S,hS⟩ := finite_fiber_decomposition y₀ c
  rw [hc] at hS
  let d : J →₀ ℤ := ∑ j ∈ S, Finsupp.single j (e (homologyOneMap (fiberProjection y₀ j) ((boundaries univ).mkQ z)))
  refine ⟨d,?_⟩
  change sigmaHomologyBasisMap e (∑ j ∈ S, Finsupp.single j _) = _
  simp only [map_sum,sigmaHomologyBasisMap,Finsupp.linearCombination_single]
  have he (w : HomologyOne Y) : e w • e.symm 1 = w := by
    apply e.injective
    simp
  have he' (j : J) : e (homologyOneMap (fiberProjection y₀ j) ((boundaries univ).mkQ z)) •
      homologyOneMap (fiberInclusion j) (e.symm 1) =
      homologyOneMap (fiberInclusion j) (homologyOneMap (fiberProjection y₀ j) ((boundaries univ).mkQ z)) := by
    rw [← map_smul,he]
  simp_rw [he']
  simp only [homologyOneMap,homologyMap_mk,← map_sum]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change ∑ j ∈ S, pushN₁ (fiberInclusion j) (pushN₁ (fiberProjection y₀ j) z.val) = z.val
  exact hS

/-- The integral H1 basis of an arbitrary disjoint union of copies of a space
with H1=Z; all chains and decompositions have genuinely finite support. -/
def sigmaHomologyBasis : (J →₀ ℤ) ≃ₗ[ℤ] HomologyOne (Σ _ : J,Y) :=
  LinearEquiv.ofBijective (sigmaHomologyBasisMap e)
    ⟨sigmaHomologyBasis_injective y₀ e,sigmaHomologyBasis_surjective y₀ e⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X G : Type*} [TopologicalSpace X] [Group G]

structure TwoPotential (U V : Set X) where
  left : X → G
  right : X → G
  agree : ∀ γ : Cube₁ X, Set.range γ ⊆ U ∩ V →
    (left (γ 0))⁻¹ * left (γ 1) = (right (γ 0))⁻¹ * right (γ 1)

namespace TwoPotential
variable {U V : Set X} (a : TwoPotential (G:=G) U V)

def value (γ : Cube₁ X) : G := if Set.range γ ⊆ U then (a.left (γ 0))⁻¹ * a.left (γ 1)
  else (a.right (γ 0))⁻¹ * a.right (γ 1)

theorem value_left (γ : Cube₁ X) (h : Set.range γ ⊆ U) :
    a.value γ = (a.left (γ 0))⁻¹ * a.left (γ 1) := ite_eq_left h

theorem value_right (γ : Cube₁ X) (h : Set.range γ ⊆ V) :
    a.value γ = (a.right (γ 0))⁻¹ * a.right (γ 1) := by
  unfold value
  split_ifs with hU
  · exact a.agree γ (fun x hx => ⟨hU hx,h hx⟩)
  · rfl

theorem value_const (x : X) : a.value (ContinuousMap.const I x) = 1 := by
  unfold value
  split_ifs <;> simp

theorem small_either {Y : Type*} [MetricSpace Y] (γ : C(Y,X))
    (h : γ ∈ CubicalMesh.small ({U,V} : Set (Set X))) : Set.range γ ⊆ U ∨ Set.range γ ⊆ V := by
  rcases h with ⟨W,hW,hγ⟩
  simp only [mem_insert_iff,mem_singleton_iff] at hW
  rcases hW with rfl | rfl
  · exact Or.inl hγ
  · exact Or.inr hγ

def system : Local (G:=G) ({U,V} : Set (Set X)) where
  value := a.value
  constant := a.value_const
  split := by
    intro γ h
    rcases small_either γ h with h | h
    · rw [a.value_left γ h,a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
      group
    · rw [a.value_right γ h,a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
      group
  square := by
    intro σ h
    rcases small_either σ h with h | h
    · rw [a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      simp only [edge₁,edge₂,ContinuousMap.coe_mk]
      group
    · rw [a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      simp only [edge₁,edge₂,ContinuousMap.coe_mk]
      group

theorem cover_open (hU : IsOpen U) (hV : IsOpen V) : ∀ W ∈ ({U,V} : Set (Set X)), IsOpen W := by
  rintro W (rfl | rfl)
  · exact hU
  · exact hV

omit [TopologicalSpace X] in
theorem cover_univ (hUV : U ∪ V = univ) : ⋃₀ ({U,V} : Set (Set X)) = univ := by
  simpa only [sUnion_insert,sUnion_singleton] using hUV

def transport (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) : Cube₁ X → G :=
  a.system.transport (cover_open hU hV) (cover_univ hUV)

theorem transport_left (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (γ : Cube₁ X) (hγ : Set.range γ ⊆ U) :
    a.transport hU hV hUV γ = (a.left (γ 0))⁻¹ * a.left (γ 1) := by
  rw [transport,a.system.transport_small _ _ ⟨U,by simp,hγ⟩]
  exact a.value_left γ hγ

theorem transport_right (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (γ : Cube₁ X) (hγ : Set.range γ ⊆ V) :
    a.transport hU hV hUV γ = (a.right (γ 0))⁻¹ * a.right (γ 1) := by
  rw [transport,a.system.transport_small _ _ ⟨V,by simp,hγ⟩]
  exact a.value_right γ hγ

end TwoPotential
end EilenbergGanea.PathTransport

namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every path component is simply connected; no connectedness is imposed. -/
def ThinPaths (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ (x y : Y) (p p' : Path x y), Path.Homotopic p p'

def componentRoot (x : Y) : Y := (ZerothHomotopy.mk x).out

def componentStem (x : Y) : Path (componentRoot x) x :=
  (Quotient.exact (Quotient.out_eq (ZerothHomotopy.mk x)) : Joined (componentRoot x) x).somePath

theorem componentRoot_eq {x y : Y} (p : Path x y) : componentRoot x = componentRoot y :=
  congrArg Quotient.out (ZerothHomotopy.sound p)

variable {r : X} (q : ∀ x, Path r x)

def potential (f : C(Y,X)) (x : Y) : (FundamentalGroup X r)ᵐᵒᵖ :=
  basedPath q ((componentStem x).map f.continuous)

theorem potential_path (hY : ThinPaths Y) (f : C(Y,X)) {x y : Y} (p : Path x y) :
    holonomy q (p.map f.continuous).toContinuousMap = (potential q f x)⁻¹ * potential q f y := by
  have h := (hY _ _ ((componentStem x).trans p)
    ((componentStem y).cast (componentRoot_eq p) rfl)).map f
  have he := basedPath_homotopic q h
  rw [Path.map_trans,basedPath_trans] at he
  have hy : basedPath q (((componentStem y).cast (componentRoot_eq p) rfl).map f.continuous) = potential q f y :=
    basedPath_congr q _ _ (fun _ => rfl)
  rw [hy] at he
  rw [holonomy_path]
  exact (eq_inv_mul_iff_mul_eq.mpr he)

variable (U V : Set X)

def inclusion (U : Set X) : C(U,X) := ⟨Subtype.val,continuous_subtype_val⟩

def gauge (x : X) : (FundamentalGroup X r)ᵐᵒᵖ :=
  if h : x ∈ U then potential q (inclusion U) ⟨x,h⟩
  else if h : x ∈ V then potential q (inclusion V) ⟨x,h⟩ else 1

def overlapValue (x : (U ∩ V : Set X)) : (FundamentalGroup X r)ᵐᵒᵖ :=
  potential q (inclusion V) ⟨x.val,x.property.2⟩ *
    (potential q (inclusion U) ⟨x.val,x.property.1⟩)⁻¹

theorem overlapValue_path (hU : ThinPaths U) (hV : ThinPaths V)
    {x y : (U ∩ V : Set X)} (p : Path x y) : overlapValue q U V x = overlapValue q U V y := by
  let pU : Path (⟨x.val,x.property.1⟩ : U) ⟨y.val,y.property.1⟩ :=
    p.map (continuous_subtype_val.subtype_mk (fun z => z.property.1))
  let pV : Path (⟨x.val,x.property.2⟩ : V) ⟨y.val,y.property.2⟩ :=
    p.map (continuous_subtype_val.subtype_mk (fun z => z.property.2))
  have h₁ := potential_path q hU (inclusion U) pU
  have h₂ := potential_path q hV (inclusion V) pV
  have he : (potential q (inclusion U) ⟨x.val,x.property.1⟩)⁻¹ * potential q (inclusion U) ⟨y.val,y.property.1⟩ =
      (potential q (inclusion V) ⟨x.val,x.property.2⟩)⁻¹ * potential q (inclusion V) ⟨y.val,y.property.2⟩ :=
    h₁.symm.trans h₂
  unfold overlapValue
  have hh := congrArg (fun z => potential q (inclusion V) ⟨x.val,x.property.2⟩ * z *
    (potential q (inclusion U) ⟨y.val,y.property.1⟩)⁻¹) he
  simpa only [mul_assoc,inv_mul_cancel,mul_inv_cancel,mul_one,one_mul,mul_inv_cancel_left] using hh

def evaluation (hU : ThinPaths U) (hV : ThinPaths V) :
    FreeGroup (ZerothHomotopy (U ∩ V : Set X)) →* (FundamentalGroup X r)ᵐᵒᵖ :=
  FreeGroup.lift (ZerothHomotopy.lift (overlapValue q U V) (fun _ _ p => overlapValue_path q U V hU hV p))

def rightLabel (x : X) : FreeGroup (ZerothHomotopy (U ∩ V : Set X)) :=
  if h : x ∈ U ∩ V then FreeGroup.of (ZerothHomotopy.mk ⟨x,h⟩) else 1

@[simp] theorem rightLabel_overlap (x : (U ∩ V : Set X)) :
    rightLabel U V x.val = FreeGroup.of (ZerothHomotopy.mk x) := dite_eq_left x.property

def labels : TwoPotential (G:=FreeGroup (ZerothHomotopy (U ∩ V : Set X))) U V where
  left := fun _ => 1
  right := rightLabel U V
  agree := by
    intro γ hγ
    let p : Path (⟨γ 0,hγ ⟨0,rfl⟩⟩ : (U ∩ V : Set X)) ⟨γ 1,hγ ⟨1,rfl⟩⟩ :=
      ⟨⟨fun t => ⟨γ t,hγ ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩,rfl,rfl⟩
    simp only [inv_one,mul_one]
    have hh : rightLabel U V (γ 0) = rightLabel U V (γ 1) := by
      rw [rightLabel_overlap U V ⟨γ 0,hγ ⟨0,rfl⟩⟩,
        rightLabel_overlap U V ⟨γ 1,hγ ⟨1,rfl⟩⟩]
      exact congrArg FreeGroup.of (ZerothHomotopy.sound p)
    rw [hh,inv_mul_cancel]

end EilenbergGanea.ForestCover

namespace EilenbergGanea.PathTransport
open Set CubicalSingular ForestCover
variable {X G : Type*} [TopologicalSpace X] [Group G]

def liftCube {Y : Type*} [TopologicalSpace Y] (U : Set X) (γ : C(Y,X))
    (h : Set.range γ ⊆ U) : C(Y,U) := ⟨fun t => ⟨γ t,h ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩

structure LeftPotential (U V : Set X) (r : U) (q : ∀ x : U, Path r x) (ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G) where
  right : X → G
  agree : ∀ (γ : Cube₁ X) (hc : Set.range γ ⊆ U ∩ V),
    ρ (holonomy q (liftCube U γ (fun _ hx => (hc hx).1))) = (right (γ 0))⁻¹ * right (γ 1)

namespace LeftPotential
variable {U V : Set X} {r : U} {q : ∀ x : U, Path r x} {ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G}
variable (a : LeftPotential U V r q ρ)

def value (γ : Cube₁ X) : G := if h : Set.range γ ⊆ U then ρ (holonomy q (liftCube U γ h))
  else (a.right (γ 0))⁻¹ * a.right (γ 1)

theorem value_left (γ : Cube₁ X) (h : Set.range γ ⊆ U) :
    a.value γ = ρ (holonomy q (liftCube U γ h)) := dite_eq_left h

theorem value_right (γ : Cube₁ X) (h : Set.range γ ⊆ V) :
    a.value γ = (a.right (γ 0))⁻¹ * a.right (γ 1) := by
  unfold value
  split_ifs with hU
  · exact a.agree γ (fun x hx => ⟨hU hx,h hx⟩)
  · rfl

def system : Local (G:=G) ({U,V} : Set (Set X)) where
  value := a.value
  constant := by
    intro x
    unfold value
    split_ifs with h
    · have he : liftCube U (ContinuousMap.const I x) h = ContinuousMap.const I ⟨x,h ⟨0,rfl⟩⟩ := rfl
      rw [he,holonomy_const,map_one]
    · simp
  split := by
    intro γ h
    rcases TwoPotential.small_either γ h with h | h
    · rw [a.value_left γ h,a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      exact (congrArg ρ (holonomy_split q (liftCube U γ h))).trans (map_mul ρ _ _)
    · rw [a.value_right γ h,a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half false t,ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨half true t,ht⟩)]
      simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
      group
  square := by
    intro σ h
    rcases TwoPotential.small_either σ h with h | h
    · rw [a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_left _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      exact (map_mul ρ _ _).symm.trans ((congrArg ρ (holonomy_square q (liftCube U σ h))).trans (map_mul ρ _ _))
    · rw [a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,0),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(1,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(0,t),ht⟩),
        a.value_right _ (fun _ ⟨t,ht⟩ => h ⟨(t,1),ht⟩)]
      simp only [edge₁,edge₂,ContinuousMap.coe_mk]
      group

variable (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)

theorem transport_left (γ : Cube₁ X) (hγ : Set.range γ ⊆ U) :
    a.system.transport (TwoPotential.cover_open hU hV) (TwoPotential.cover_univ hc) γ =
      ρ (holonomy q (liftCube U γ hγ)) := by
  rw [a.system.transport_small _ _ ⟨U,by simp,hγ⟩]
  exact a.value_left γ hγ

end LeftPotential

@[simp] theorem basedPath_symm {r x y : X} (q : ∀ z, Path r z) (p : Path x y) :
    basedPath q p.symm = (basedPath q p)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← basedPath_trans]
  exact (basedPath_homotopic q (Path.Homotopic.symm_trans p)).trans (basedPath_refl q _)

variable {U V : Set X} {r : U} (q : ∀ x : U, Path r x) (ρ : (FundamentalGroup U r)ᵐᵒᵖ →* G)

def capInclusion : C((U ∩ V : Set X),U) := ⟨fun z => ⟨z.val,z.property.1⟩,continuous_subtype_val.subtype_mk _⟩

def KillsOverlap : Prop := ∀ (z : (U ∩ V : Set X)) (p : Path z z), ρ (basedPath q (p.map capInclusion.continuous)) = 1

theorem overlap_potential_path (hk : KillsOverlap (V:=V) q ρ)
    {x y : (U ∩ V : Set X)} (p : Path x y) :
    ρ (basedPath q (p.map capInclusion.continuous)) =
      (ρ (potential q capInclusion x))⁻¹ * ρ (potential q capInclusion y) := by
  let sy := (componentStem y).cast (componentRoot_eq p) rfl
  have h := hk (componentRoot x) (((componentStem x).trans p).trans sy.symm)
  rw [Path.map_trans,Path.map_trans,← Path.map_symm] at h
  simp only [basedPath_trans,basedPath_symm,map_mul,map_inv] at h
  have he : basedPath q (sy.map capInclusion.continuous) = potential q capInclusion y :=
    basedPath_congr q _ _ (fun _ => rfl)
  rw [he] at h
  change ρ (potential q capInclusion x) * _ * (ρ (potential q capInclusion y))⁻¹ = 1 at h
  apply eq_inv_mul_iff_mul_eq.mpr
  exact mul_inv_eq_one.mp h

def overlapPotential (x : X) : G :=
  if h : x ∈ U ∩ V then ρ (potential q capInclusion ⟨x,h⟩) else 1

@[simp] theorem overlapPotential_cap (x : (U ∩ V : Set X)) :
    overlapPotential (V:=V) q ρ x.val = ρ (potential q capInclusion x) := dite_eq_left x.property

def patched (hk : KillsOverlap (V:=V) q ρ) : LeftPotential U V r q ρ where
  right := overlapPotential q ρ
  agree γ hc := by
    let p := cubePath (liftCube (U ∩ V) γ hc)
    rw [overlapPotential_cap q ρ ⟨γ 0,hc ⟨0,rfl⟩⟩,overlapPotential_cap q ρ ⟨γ 1,hc ⟨1,rfl⟩⟩]
    exact overlap_potential_path q ρ hk p

/-- The actual finite-grid van-Kampen kernel inclusion, obtained by extending
all representations annihilating overlap loops. No presentation axiom is used. -/
theorem kernel_killed (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    (hk : KillsOverlap (V:=V) q ρ) (p : Path r r)
    (hp : (p.map continuous_subtype_val).Homotopic (Path.refl r.val)) :
    ρ (basedPath q p) = 1 := by
  let a := patched q ρ hk
  have he := a.system.transport_homotopy (TwoPotential.cover_open hU hV) (TwoPotential.cover_univ hc) hp.some
  change a.system.transport _ _ (p.map continuous_subtype_val).toContinuousMap =
    a.system.transport _ _ (ContinuousMap.const I r.val) at he
  rw [a.system.transport_const] at he
  rw [LeftPotential.transport_left a hU hV hc _ (fun _ ⟨t,ht⟩ => ht ▸ (p t).property)] at he
  have hh : liftCube U (p.map continuous_subtype_val).toContinuousMap (fun _ ⟨t,ht⟩ => ht ▸ (p t).property) = p.toContinuousMap := by
    ext t; rfl
  simpa only [hh,holonomy_path] using he

end EilenbergGanea.PathTransport

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r : X} (q : ∀ y, Path r y)

def basedHom (f : C(Y,X)) (y : Y) : (FundamentalGroup Y y)ᵐᵒᵖ →* (FundamentalGroup X r)ᵐᵒᵖ where
  toFun w := based q ((FundamentalGroup.map f y) w.unop)
  map_one' := by
    change based q ((FundamentalGroup.map f y) 1) = 1
    rw [map_one]
    exact based_refl q _
  map_mul' u v := by
    change based q ((FundamentalGroup.map f y) (v.unop * u.unop)) = _
    rw [map_mul]
    exact based_trans q _ _

@[simp] theorem basedHom_loop (f : C(Y,X)) {y : Y} (p : Path y y) :
    basedHom q f y (MulOpposite.op (asClass p)) = basedPath q (p.map f.continuous) := rfl

/-- Conjugation transfers annihilation of based loops to every base point. -/
theorem kills_loops_of_root [PathConnectedSpace Y] (f : C(Y,X)) (y₀ : Y)
    (ρ : (FundamentalGroup X r)ᵐᵒᵖ →* G)
    (h : ∀ p : Path y₀ y₀, ρ (basedPath q (p.map f.continuous)) = 1)
    {y : Y} (p : Path y y) : ρ (basedPath q (p.map f.continuous)) = 1 := by
  let s := (PathConnectedSpace.joined y₀ y).somePath
  have hh := h (s.trans (p.trans s.symm))
  rw [Path.map_trans,Path.map_trans,← Path.map_symm] at hh
  simp only [basedPath_trans,basedPath_symm,map_mul,map_inv] at hh
  rw [← mul_assoc] at hh
  have he := mul_inv_eq_one.mp hh
  exact mul_left_cancel (show ρ (basedPath q (s.map f.continuous)) *
    ρ (basedPath q (p.map f.continuous)) = ρ (basedPath q (s.map f.continuous)) * 1 by simpa using he)

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport
variable {X G : Type*} [TopologicalSpace X] [Group G] {r : X} (q : ∀ y, Path r y)

theorem kills_annulus_loops (f : C(Annulus 2,X)) (y₀ : Annulus 2)
    (ρ : (FundamentalGroup X r)ᵐᵒᵖ →* G)
    (h : ρ (basedPath q ((annulusGenerator y₀).map f.continuous)) = 1)
    {y : Annulus 2} (p : Path y y) : ρ (basedPath q (p.map f.continuous)) = 1 := by
  apply kills_loops_of_root q f y₀ ρ _ p
  intro t
  obtain ⟨n,hn⟩ := annulus_loop_power y₀ t
  have he := congrArg (ρ.comp (basedHom q f y₀)) hn
  change ρ (basedHom q f y₀ (MulOpposite.op (asClass t))) = ρ (basedHom q f y₀ (_ ^ n)) at he
  rw [map_zpow,map_zpow] at he
  change ρ (basedPath q (t.map f.continuous)) = ρ (basedPath q ((annulusGenerator y₀).map f.continuous)) ^ n at he
  rw [h,one_zpow] at he
  exact he

end EilenbergGanea.CWCollar

namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y J G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r : X} (q : ∀ y, Path r y)

/-- A loop in a disjoint union stays in one actual component. -/
theorem kills_sigma_loops (f : C((Σ _ : J,Y),X)) (y₀ : Y)
    (ρ : (FundamentalGroup X r)ᵐᵒᵖ →* G)
    (hk : ∀ (j : J) (y : Y) (p : Path y y),
      ρ (basedPath q (p.map (f.comp (fiberInclusion j)).continuous)) = 1)
    {z : (Σ _ : J,Y)} (p : Path z z) : ρ (basedPath q (p.map f.continuous)) = 1 := by
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  have hi (t : I) : (p t).1 = z.1 := by
    have hc : Continuous (fun t => (p t).1) := (continuous_sigma (fun _ => continuous_const)).comp p.continuous
    have he : (p t).1 = (p 0).1 := (@inferInstance (PreconnectedSpace I)).constant hc
    exact he.trans (congrArg Sigma.fst p.source)
  let s := p.map (fiberProjection y₀ z.1).continuous
  have he := basedPath_congr q (s.map (f.comp (fiberInclusion z.1)).continuous)
    (p.map f.continuous) (fun t => by
      change f ((fiberInclusion z.1) ((fiberProjection y₀ z.1) (p t))) = f (p t)
      congr 1
      apply Sigma.ext
      · exact (hi t).symm
      · simp only [fiberInclusion,fiberProjection,ContinuousMap.coe_mk,hi t,ite_true]
        rfl)
  rw [← he]
  exact hk z.1 _ s

/-- A loop which becomes null after a map also has trivial based holonomy. -/
theorem map_basedPath_eq_one (f : C(X,Y)) {x : X} (p : Path x x)
    (hp : (p.map f.continuous).Homotopic (Path.refl (f x))) :
    (FundamentalGroup.map f r).op (basedPath q p) = 1 := by
  apply MulOpposite.unop_injective
  change asClass ((((q x).trans p).trans (q x).symm).map f.continuous) = Path.Homotopic.Quotient.refl (f r)
  rw [Path.map_trans,Path.map_trans,← Path.map_symm]
  simp only [asClass,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]
  have hh : Path.Homotopic.Quotient.mk (p.map f.continuous) = Path.Homotopic.Quotient.refl (f x) := Path.Homotopic.Quotient.eq.mpr hp
  rw [hh]
  simp only [Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_symm]

end EilenbergGanea.PathTransport

namespace EilenbergGanea.CWCollar.Attachment
open Set CubicalSingular PathTransport
variable {X J : Type*} [TopologicalSpace X] (a : Attachment X J 2)
variable {r : a.outer} (q : ∀ y, Path r y) (y₀ : Annulus 2)

def annulusMap (j : J) : C(Annulus 2,a.outer) :=
  capInclusion.comp ((a.annulusHomeomorph : C((Σ _ : J,Annulus 2),(a.outer ∩ a.inner : Set X))).comp (fiberInclusion j))

def annulusRelator (j : J) : (FundamentalGroup a.outer r)ᵐᵒᵖ :=
  basedPath q ((annulusGenerator y₀).map (a.annulusMap j).continuous)

theorem killsOverlap_of_relators {G : Type*} [Group G]
    (ρ : (FundamentalGroup a.outer r)ᵐᵒᵖ →* G)
    (h : ∀ j, ρ (a.annulusRelator q y₀ j) = 1) : KillsOverlap (V:=a.inner) q ρ := by
  intro z p
  let f : C((Σ _ : J,Annulus 2),a.outer) := capInclusion.comp (a.annulusHomeomorph : C((Σ _ : J,Annulus 2),(a.outer ∩ a.inner : Set X)))
  let t := p.map a.annulusHomeomorph.symm.continuous
  have hh := kills_sigma_loops q f y₀ ρ (fun j y s => kills_annulus_loops q (a.annulusMap j) y₀ ρ (h j) s) t
  have he := basedPath_congr q (t.map f.continuous) (p.map capInclusion.continuous) (fun s => by
    change (⟨(a.annulusHomeomorph (a.annulusHomeomorph.symm (p s))).val,_⟩ : a.outer) = _
    exact congrArg (fun z : (a.outer ∩ a.inner : Set X) => (⟨z.val,z.property.1⟩ : a.outer)) (a.annulusHomeomorph.apply_symm_apply (p s)))
  exact (congrArg ρ he).symm.trans hh

/-- The exact ordinary attachment kernel, with one genuine annular relator per
attached2-cell. The forward inclusion uses the finite-grid patching proof. -/
theorem annulus_normalClosure (hthin : ForestCover.ThinPaths a.inner) :
    ((FundamentalGroup.map (⟨Subtype.val,continuous_subtype_val⟩ : C(a.outer,X)) r).op).ker =
      Subgroup.normalClosure (Set.range (a.annulusRelator q y₀)) := by
  let f : C(a.outer,X) := ⟨Subtype.val,continuous_subtype_val⟩
  let N := Subgroup.normalClosure (Set.range (a.annulusRelator q y₀))
  let ρ := QuotientGroup.mk' N
  apply le_antisymm
  · intro w hw
    obtain ⟨p,hp⟩ := Quotient.exists_rep w.unop
    have hp' : MulOpposite.op (asClass p) = w := by
      exact (congrArg MulOpposite.op hp).trans (MulOpposite.op_unop w)
    have hn : (p.map f.continuous).Homotopic (Path.refl r.val) := by
      apply Path.Homotopic.Quotient.eq.mp
      change ((FundamentalGroup.map f r).op (MulOpposite.op (asClass p))).unop = (1 : FundamentalGroup X r.val)
      rw [hp']
      exact congrArg MulOpposite.unop hw
    have hk : KillsOverlap (V:=a.inner) q ρ := a.killsOverlap_of_relators q y₀ ρ (fun j =>
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j,rfl⟩))
    have he := kernel_killed q ρ a.outer_open a.inner_open a.outer_union_inner hk p hn
    let u : (FundamentalGroup a.outer r)ᵐᵒᵖ := MulOpposite.op (asClass (q r))
    have hbased : basedPath q p = u * w * u⁻¹ := by
      rw [← hp']
      rfl
    rw [hbased,map_mul,map_mul,map_inv] at he
    have hh := mul_inv_eq_one.mp he
    have hf : ρ w = 1 := mul_left_cancel (show ρ u * ρ w = ρ u * 1 by simpa using hh)
    exact (QuotientGroup.eq_one_iff _).mp hf
  · apply Subgroup.normalClosure_le_normal
    rintro w ⟨j,rfl⟩
    apply map_basedPath_eq_one q f
    let g : C(Annulus 2,a.inner) := ⟨fun z => ⟨(a.annulusHomeomorph ⟨j,z⟩).val,(a.annulusHomeomorph ⟨j,z⟩).property.2⟩,
      (continuous_subtype_val.comp (a.annulusHomeomorph.continuous.comp continuous_sigmaMk)).subtype_mk _⟩
    have h := (hthin _ _ ((annulusGenerator y₀).map g.continuous) (Path.refl (g y₀))).map
      (⟨Subtype.val,continuous_subtype_val⟩ : C(a.inner,X))
    exact h

end EilenbergGanea.CWCollar.Attachment

namespace EilenbergGanea.CubicalSingular
open Set
variable {J : Type*} {Y : J → Type*} [∀ j, TopologicalSpace (Y j)]

noncomputable def sigmaCenter [∀ j, ContractibleSpace (Y j)] (j : J) : Y j :=
  (id_nullhomotopic (Y j)).choose
noncomputable def sigmaContraction [∀ j, ContractibleSpace (Y j)] (j : J) :
    (ContinuousMap.id (Y j)).Homotopy (ContinuousMap.const (Y j) (sigmaCenter (Y:=Y) j)) :=
  (id_nullhomotopic (Y j)).choose_spec.some

noncomputable def sigmaCollapse [∀ j, ContractibleSpace (Y j)] : C((Σ j,Y j),(Σ j,Y j)) :=
  ⟨fun x => ⟨x.1,sigmaCenter (Y:=Y) x.1⟩,continuous_sigma (fun j => by
    change Continuous (fun _ : Y j => (⟨j,sigmaCenter (Y:=Y) j⟩ : Σ j,Y j))
    exact continuous_const)⟩

noncomputable def sigmaHomotopy [∀ j, ContractibleSpace (Y j)] :
    (ContinuousMap.id (Σ j,Y j)).Homotopy (sigmaCollapse (Y:=Y)) where
  toFun p := ⟨p.2.1,sigmaContraction (Y:=Y) p.2.1 (p.1,p.2.2)⟩
  continuous_toFun := by
    have hc : Continuous (fun p : Σ j, Y j × I =>
        (⟨p.1,sigmaContraction (Y:=Y) p.1 (p.2.2,p.2.1)⟩ : Σ j,Y j)) :=
      continuous_sigma (fun j => continuous_sigmaMk.comp ((sigmaContraction (Y:=Y) j).continuous.comp continuous_swap))
    exact hc.comp ((Homeomorph.sigmaProdDistrib (X:=Y) (Y:=I)).continuous.comp continuous_swap)
  map_zero_left x := by congr 1; exact (sigmaContraction (Y:=Y) x.1).apply_zero x.2
  map_one_left x := by
    change (⟨x.1,sigmaContraction (Y:=Y) x.1 (1,x.2)⟩ : Σ j,Y j) = ⟨x.1,sigmaCenter (Y:=Y) x.1⟩
    congr 1
    exact (sigmaContraction (Y:=Y) x.1).apply_one x.2

theorem push_sigmaCollapse_zero [∀ j, ContractibleSpace (Y j)] (c : N₁ (Σ j,Y j)) :
    pushN₁ (sigmaCollapse (Y:=Y)) c = 0 := by
  obtain ⟨c,rfl⟩ := (D₁ (Σ j,Y j)).mkQ_surjective c
  change (D₁ (Σ j,Y j)).mkQ (push₁ sigmaCollapse c) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (D₁ (Σ j,Y j)).add_mem hc hd
  | single σ m =>
    obtain ⟨j,g,hg,he⟩ := σ.continuous.exists_lift_sigma
    have hcomp : (sigmaCollapse (Y:=Y)).comp σ = constant₁ (⟨j,sigmaCenter (Y:=Y) j⟩ : Σ j,Y j) := by
      apply ContinuousMap.ext
      intro t
      change (⟨(σ t).1,sigmaCenter (Y:=Y) (σ t).1⟩ : Σ j,Y j) = ⟨j,sigmaCenter (Y:=Y) j⟩
      rw [congrFun he t]
      rfl
    rw [push₁_single,hcomp,← Finsupp.smul_single_one]
    exact (D₁ (Σ j,Y j)).smul_mem m (Submodule.subset_span ⟨_,rfl⟩)

/-- Disjoint unions of contractible components have zero integral cubical H1;
no finiteness of the component index is used. -/
theorem exact₁_sigma_contractible [∀ j, ContractibleSpace (Y j)]
    (z : N₁ (Σ j,Y j)) (hz : d₁ z = 0) : ∃ b : N₂ (Σ j,Y j), d₂ b = z := by
  refine ⟨-normalizedPrism (sigmaHomotopy (Y:=Y)) z,?_⟩
  rw [map_neg,normalizedPrism_boundary _ hz,push_sigmaCollapse_zero,pushN₁_id,zero_sub,neg_neg]

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exact₁_on_of_exact (U : Set X)
    (hU : ∀ z : N₁ U, d₁ z = 0 → ∃ b : N₂ U, d₂ b = z)
    {c : N₁ X} (hc : c ∈ L₁ U) (hz : d₁ c = 0) : ∃ b ∈ L₂ U, d₂ b = c := by
  rw [← range_pushN₁_inc] at hc
  obtain ⟨c,rfl⟩ := hc
  have hz' : d₁ c = 0 := by
    apply push₀_injective (inc U) Subtype.val_injective
    simpa only [d₁_push,map_zero] using hz
  obtain ⟨b,hb⟩ := hU c hz'
  refine ⟨pushN₂ (inc U) b,?_,?_⟩
  · rw [← range_pushN₂_inc]; exact ⟨b,rfl⟩
  · rw [d₂_push,hb]

theorem exact₁_homeomorph (e : X ≃ₜ Y)
    (hX : ∀ z : N₁ X, d₁ z = 0 → ∃ b : N₂ X, d₂ b = z)
    (z : N₁ Y) (hz : d₁ z = 0) : ∃ b : N₂ Y, d₂ b = z := by
  obtain ⟨b,hb⟩ := hX (pushN₁ (⟨e.symm,e.symm.continuous⟩ : C(Y,X)) z) (by rw [d₁_push,hz,map_zero])
  refine ⟨pushN₂ (⟨e,e.continuous⟩ : C(X,Y)) b,?_⟩
  rw [d₂_push,hb,← pushN₁_comp]
  have he : (⟨e,e.continuous⟩ : C(X,Y)).comp (⟨e.symm,e.symm.continuous⟩ : C(Y,X)) = ContinuousMap.id Y :=
    ContinuousMap.ext e.apply_symm_apply
  rw [he,pushN₁_id]

def subspaceHomologyMap (U : Set X) : HomologyOne U →ₗ[ℤ] Homology₁ U :=
  homologyMap (inc U) (by intro x _; exact x.property)

theorem subspaceHomologyMap_injective (U : Set X) : Function.Injective (subspaceHomologyMap U) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨z,rfl⟩ := (boundaries (univ : Set U)).mkQ_surjective q
  change (boundaries U).mkQ (cycleMap (inc U) _ z) = 0 at hq
  obtain ⟨b,hb,hdb⟩ := (Submodule.Quotient.mk_eq_zero (boundaries U)).mp hq
  rw [← range_pushN₂_inc] at hb
  obtain ⟨c,rfl⟩ := hb
  have hc : d₂ c = z.val := by
    apply pushN₁_injective (inc U) Subtype.val_injective
    rw [← d₂_push]
    exact hdb
  change (boundaries (univ : Set U)).mkQ z = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨c,by rw [L₂_univ]; trivial,hc⟩

theorem subspaceHomologyMap_surjective (U : Set X) : Function.Surjective (subspaceHomologyMap U) := by
  intro q
  obtain ⟨z,rfl⟩ := (boundaries U).mkQ_surjective q
  have hz := z.property.1
  rw [← range_pushN₁_inc] at hz
  obtain ⟨c,hc⟩ := hz
  have hdc : d₁ c = 0 := by
    apply push₀_injective (inc U) Subtype.val_injective
    rw [← d₁_push,hc,map_zero]
    exact z.property.2
  let c' : cyclesOn (univ : Set U) := ⟨c,by rw [L₁_univ]; trivial,hdc⟩
  refine ⟨(boundaries (univ : Set U)).mkQ c',?_⟩
  change (boundaries U).mkQ (cycleMap (inc U) _ c') = (boundaries U).mkQ z
  congr 1
  exact Subtype.ext hc

/-- Supported homology is the actual singular homology of the subspace. -/
def subspaceHomologyEquiv (U : Set X) : HomologyOne U ≃ₗ[ℤ] Homology₁ U :=
  LinearEquiv.ofBijective (subspaceHomologyMap U)
    ⟨subspaceHomologyMap_injective U,subspaceHomologyMap_surjective U⟩

end EilenbergGanea.CubicalSingular

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover CubicalSingular
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}

def openDiskHomeomorph (n : ℕ) : OpenDisk n ≃ₜ ball (0 : Fin n → ℝ) 1 where
  toFun z := ⟨z.val.val,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  invFun z := ⟨⟨z.val,ball_subset_closedBall z.property⟩,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance openDiskContractible (n : ℕ) : ContractibleSpace (OpenDisk n) := by
  let : ContractibleSpace (ball (0 : Fin n → ℝ) 1) := contractibleSpace_ball (by norm_num)
  exact (openDiskHomeomorph n).contractibleSpace

namespace Attachment
variable (a : Attachment X J n)

theorem inner_exact (z : N₁ a.inner) (hz : d₁ z = 0) : ∃ b : N₂ a.inner, d₂ b = z :=
  exact₁_homeomorph a.innerHomeomorph exact₁_sigma_contractible z hz

theorem inner_supported_exact {z : N₁ X} (hz : z ∈ L₁ a.inner) (hd : d₁ z = 0) :
    ∃ b ∈ L₂ a.inner, d₂ b = z := exact₁_on_of_exact a.inner a.inner_exact hz hd

def outerHomologyEquiv : HomologyOne a.outer ≃ₗ[ℤ] HomologyOne a.lower :=
  homologyOneEquiv a.retractMap a.sectionMap a.collarHomotopy.symm (by
    have he : a.retractMap.comp a.sectionMap = ContinuousMap.id a.lower :=
      ContinuousMap.ext a.retract_section
    rw [he]
    exact ContinuousMap.Homotopy.refl _)

/-- The top-cell collar comparison in a contractible ordinary attachment is
an actual integral H1 isomorphism, proved from singular subdivision. -/
def attachingHomologyEquiv [ContractibleSpace X] :
    HomologyOne (a.outer ∩ a.inner : Set X) ≃ₗ[ℤ] HomologyOne a.lower :=
  (subspaceHomologyEquiv (a.outer ∩ a.inner)).trans
    ((mayerVietoris_equiv a.outer a.inner a.outer_open a.inner_open a.outer_union_inner
      (fun _ hz hd => a.inner_supported_exact hz hd)).trans
      ((subspaceHomologyEquiv a.outer).symm.trans a.outerHomologyEquiv))

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set CubicalSingular PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp] theorem homologyOneMap_loop (f : C(X,Y)) {x : X} (p : Path x x) :
    homologyOneMap f (loopHomology p) = loopHomology (p.map f.continuous) := by
  change (boundaries univ).mkQ (cycleMap f _ (loopCycle p)) = (boundaries univ).mkQ (loopCycle _)
  congr 1
  apply Subtype.ext
  change pushN₁ f (gen₁ p.toContinuousMap) = gen₁ (p.map f.continuous).toContinuousMap
  rw [pushN₁_gen]
  rfl

namespace Attachment
variable {J : Type*} (a : Attachment X J 2)

def outerCapHomologyEquiv [ContractibleSpace X] :
    HomologyOne (a.outer ∩ a.inner : Set X) ≃ₗ[ℤ] HomologyOne a.outer :=
  (subspaceHomologyEquiv (a.outer ∩ a.inner)).trans
    ((mayerVietoris_equiv a.outer a.inner a.outer_open a.inner_open a.outer_union_inner
      (fun _ hz hd => a.inner_supported_exact hz hd)).trans (subspaceHomologyEquiv a.outer).symm)

theorem outerCapHomologyEquiv_apply [ContractibleSpace X] (c : HomologyOne (a.outer ∩ a.inner : Set X)) :
    a.outerCapHomologyEquiv c = homologyOneMap capInclusion c := by
  apply (subspaceHomologyEquiv a.outer).injective
  change (subspaceHomologyEquiv a.outer) ((subspaceHomologyEquiv a.outer).symm
    (homologyInclusion Set.inter_subset_left (subspaceHomologyEquiv (a.outer ∩ a.inner) c))) = _
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨z,rfl⟩ := (boundaries univ).mkQ_surjective c
  change (boundaries a.outer).mkQ (cycleInclusion Set.inter_subset_left (cycleMap (inc (a.outer ∩ a.inner)) _ z)) =
    (boundaries a.outer).mkQ (cycleMap (inc a.outer) _ (cycleMap capInclusion _ z))
  congr 1
  apply Subtype.ext
  change pushN₁ (inc (a.outer ∩ a.inner)) z.val = pushN₁ (inc a.outer) (pushN₁ capInclusion z.val)
  rw [← pushN₁_comp]
  rfl

def annularBasis [ContractibleSpace X] (y₀ : Annulus 2) :
    (J →₀ ℤ) ≃ₗ[ℤ] HomologyOne a.outer :=
  (sigmaHomologyBasis y₀ (annulusHomologyInt y₀)).trans
    ((homologyOneEquiv (a.annulusHomeomorph : C(_, _)) (a.annulusHomeomorph.symm : C(_, _))
      (by simpa using ContinuousMap.Homotopy.refl (ContinuousMap.id _))
      (by simpa using ContinuousMap.Homotopy.refl (ContinuousMap.id _))).trans a.outerCapHomologyEquiv)

/-- Each basis vector is precisely the singular class of its lifted annulus. -/
theorem annularBasis_single [ContractibleSpace X] (y₀ : Annulus 2) (j : J) :
    a.annularBasis y₀ (Finsupp.single j 1) = loopHomology ((annulusGenerator y₀).map (a.annulusMap j).continuous) := by
  change a.outerCapHomologyEquiv (homologyOneMap (a.annulusHomeomorph : C(_, _))
    (sigmaHomologyBasisMap (annulusHomologyInt y₀) (Finsupp.single j 1))) = _
  rw [outerCapHomologyEquiv_apply]
  simp only [sigmaHomologyBasisMap,Finsupp.linearCombination_single,one_smul]
  rw [← LinearMap.comp_apply,← homologyOneMap_comp,← LinearMap.comp_apply,← homologyOneMap_comp]
  rw [← annulusGenerator_homology,homologyOneMap_loop]
  rfl

end Attachment
end EilenbergGanea.CWCollar


namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X G H : Type*} [TopologicalSpace X] [Group G] [Group H]
variable {U : Set (Set X)} (l : Local (G:=G) U) (φ : G →* H)

def map : Local (G:=H) U where
  value := fun γ => φ (l.value γ)
  constant := fun x => by rw [l.constant,map_one]
  split := fun γ h => by rw [l.split γ h,map_mul]
  square := fun σ h => by rw [← map_mul,← map_mul,l.square σ h]

theorem map_transport (hU : ∀ V ∈ U, IsOpen V) (hc : ⋃₀ U = univ) (γ : Cube₁ X) :
    φ (l.transport hU hc γ) = (l.map φ).transport hU hc γ := by
  apply (l.map φ).transport_unique hU hc (fun γ => φ (l.transport hU hc γ))
  · intro γ; rw [l.transport_split hU hc,map_mul]
  · intro γ h; rw [l.transport_small hU hc h]; rfl

end EilenbergGanea.PathTransport.Local


namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X : Type*} [TopologicalSpace X] {r : X} (q : ∀ x, Path r x) (U V : Set X)
variable (hU : ThinPaths U) (hV : ThinPaths V)

theorem eval_rightLabel (x : X) (hx : x ∈ V) :
    evaluation q U V hU hV (rightLabel U V x) = potential q (inclusion V) ⟨x,hx⟩ * (gauge q U V x)⁻¹ := by
  by_cases hu : x ∈ U
  · rw [rightLabel_overlap U V ⟨x,hu,hx⟩]
    simp only [evaluation,FreeGroup.lift_apply_of,ZerothHomotopy.lift_mk,overlapValue,gauge,dite_eq_left hu]
  · have hnot : x ∉ U ∩ V := fun h => hu h.1
    simp only [rightLabel,dite_eq_right hnot,map_one,gauge,dite_eq_right hu,dite_eq_left hx,mul_inv_cancel]

def gauged (γ : Cube₁ X) : (FundamentalGroup X r)ᵐᵒᵖ :=
  gauge q U V (γ 0) * holonomy q γ * (gauge q U V (γ 1))⁻¹

theorem gauged_split (γ : Cube₁ X) :
    gauged q U V γ = gauged q U V (cut₁ γ false) * gauged q U V (cut₁ γ true) := by
  unfold gauged
  rw [holonomy_split q γ]
  simp only [cut₁,ContinuousMap.coe_comp,Function.comp_apply,half_false_zero,half_true_one,half_mid]
  group

theorem small_potential (W : Set X) (hW : ThinPaths W) (γ : Cube₁ X) (hγ : Set.range γ ⊆ W) :
    holonomy q γ = (potential q (inclusion W) ⟨γ 0,hγ ⟨0,rfl⟩⟩)⁻¹ *
      potential q (inclusion W) ⟨γ 1,hγ ⟨1,rfl⟩⟩ := by
  let p : Path (⟨γ 0,hγ ⟨0,rfl⟩⟩ : W) ⟨γ 1,hγ ⟨1,rfl⟩⟩ :=
    ⟨⟨fun t => ⟨γ t,hγ ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩,rfl,rfl⟩
  exact potential_path q hW (inclusion W) p

theorem gauged_small (γ : Cube₁ X) (hγ : γ ∈ CubicalMesh.small ({U,V} : Set (Set X))) :
    gauged q U V γ = evaluation q U V hU hV ((labels U V).value γ) := by
  rcases TwoPotential.small_either γ hγ with hγ | hγ
  · rw [(labels U V).value_left γ hγ]
    change gauged q U V γ = evaluation q U V hU hV (1⁻¹*1)
    simp only [inv_one,mul_one,map_one]
    unfold gauged
    rw [small_potential q U hU γ hγ]
    simp only [gauge,dite_eq_left (hγ ⟨0,rfl⟩),dite_eq_left (hγ ⟨1,rfl⟩)]
    group
  · rw [(labels U V).value_right γ hγ]
    change gauged q U V γ = evaluation q U V hU hV ((rightLabel U V (γ 0))⁻¹ * rightLabel U V (γ 1))
    rw [map_mul,map_inv,eval_rightLabel q U V hU hV _ (hγ ⟨0,rfl⟩),eval_rightLabel q U V hU hV _ (hγ ⟨1,rfl⟩)]
    unfold gauged
    rw [small_potential q V hV γ hγ]
    group

theorem eval_transport (hUo : IsOpen U) (hVo : IsOpen V) (hc : U ∪ V = univ) (γ : Cube₁ X) :
    evaluation q U V hU hV ((labels U V).transport hUo hVo hc γ) = gauged q U V γ := by
  rw [TwoPotential.transport,Local.map_transport]
  symm
  exact ((labels U V).system.map (evaluation q U V hU hV)).transport_unique _ _
    (gauged q U V) (gauged_split q U V) (gauged_small q U V hU hV) γ

theorem holonomy_loop_injective : Function.Injective (fun g : FundamentalGroup X r => based q g) := by
  intro g h he
  have he := congrArg MulOpposite.unop he
  let u : FundamentalGroup X r := asClass (q r)
  change u⁻¹ * (g * u) = u⁻¹ * (h * u) at he
  exact mul_right_cancel (mul_left_cancel he)

include q hU hV in
/-- A genuine two-open-set cover by spaces with simply connected components
has a free fundamental group. This includes graphs with arbitrary cell sets. -/
theorem isFree_fundamentalGroup (hUo : IsOpen U) (hVo : IsOpen V) (hc : U ∪ V = univ) :
    IsFreeGroup (FundamentalGroup X r) := by
  let f := (labels U V).system.fundamentalHom (TwoPotential.cover_open hUo hVo) (TwoPotential.cover_univ hc) r
  have hinj : Function.Injective f := by
    intro g h he
    obtain ⟨p,rfl⟩ := Quotient.exists_rep g
    obtain ⟨s,rfl⟩ := Quotient.exists_rep h
    have hv : (labels U V).transport hUo hVo hc p.toContinuousMap =
        (labels U V).transport hUo hVo hc s.toContinuousMap := MulOpposite.op_injective he
    have he' := congrArg (evaluation q U V hU hV) hv
    rw [eval_transport q U V hU hV hUo hVo hc,eval_transport q U V hU hV hUo hVo hc] at he'
    have hh : holonomy q p.toContinuousMap = holonomy q s.toContinuousMap := by
      unfold gauged at he'
      rw [show p.toContinuousMap 0 = r from p.source,show p.toContinuousMap 1 = r from p.target,
        show s.toContinuousMap 0 = r from s.source,show s.toContinuousMap 1 = r from s.target] at he'
      exact mul_left_cancel (mul_right_cancel he')
    apply holonomy_loop_injective q
    rw [holonomy_path,holonomy_path] at hh
    exact hh
  let : IsFreeGroup (FreeGroup (ZerothHomotopy (U ∩ V : Set X)))ᵐᵒᵖ :=
    IsFreeGroup.ofMulEquiv (MulEquiv.inv' _)
  exact IsFreeGroup.ofMulEquiv (MonoidHom.ofInjective hinj).symm

end EilenbergGanea.ForestCover


namespace EilenbergGanea.ForestCover
open CategoryTheory CubicalSingular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem thin_of_domination (f : C(X,Y)) (g : C(Y,X))
    (H : (g.comp f).Homotopy (ContinuousMap.id X)) (hY : ThinPaths Y) : ThinPaths X := by
  let F := FundamentalGroupoid.map f
  let G := FundamentalGroupoid.map g
  have ei : F ⋙ G ≅ 𝟭 (FundamentalGroupoid X) := by
    simpa only [F,G,← FundamentalGroupoid.map_comp,FundamentalGroupoid.map_id] using
      asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso H)
  have : F.Faithful := Functor.Faithful.of_comp_iso ei
  intro x y p q
  have he : F.map (⟦p⟧ : (FundamentalGroupoid.mk x) ⟶ FundamentalGroupoid.mk y) =
      F.map (⟦q⟧ : (FundamentalGroupoid.mk x) ⟶ FundamentalGroupoid.mk y) :=
    Quotient.sound (hY _ _ (p.map f.continuous) (q.map f.continuous))
  exact Quotient.exact (F.map_injective he)

theorem thin_discrete [DiscreteTopology X] : ThinPaths X := by
  intro x y p q
  have he : p = q := Path.ext (funext fun t => by
    have hp : p t = p 0 := (@inferInstance (PreconnectedSpace I)).constant p.continuous
    have hq : q t = q 0 := (@inferInstance (PreconnectedSpace I)).constant q.continuous
    exact hp.trans ((p.source.trans q.source.symm).trans hq.symm))
  rw [he]

theorem thin_homeomorph (e : X ≃ₜ Y) (hY : ThinPaths Y) : ThinPaths X :=
  thin_of_domination e e.symm (by
    have he : (e.symm : C(Y,X)).comp (e : C(X,Y)) = ContinuousMap.id X := ContinuousMap.ext e.left_inv
    rw [he]
    exact ContinuousMap.Homotopy.refl _) hY

end EilenbergGanea.ForestCover


namespace EilenbergGanea.ForestCover
open CubicalSingular CWCollar
variable {X J : Type*} [TopologicalSpace X] {Y : J → Type*} [∀ j, TopologicalSpace (Y j)]

theorem thin_sigma_contractible [∀ j, ContractibleSpace (Y j)] : ThinPaths (Σ j,Y j) := by
  let : TopologicalSpace J := ⊥
  let : DiscreteTopology J := ⟨rfl⟩
  let f : C((Σ j,Y j),J) := ⟨Sigma.fst,continuous_sigma (fun _ => continuous_const)⟩
  let g : C(J,(Σ j,Y j)) := ⟨fun j => ⟨j,sigmaCenter (Y:=Y) j⟩,continuous_of_discreteTopology⟩
  exact thin_of_domination f g (sigmaHomotopy (Y:=Y)).symm thin_discrete

theorem thin_outer {n : ℕ} (a : Attachment X J n) (hl : ThinPaths a.lower) : ThinPaths a.outer :=
  thin_of_domination a.retractMap a.sectionMap a.collarHomotopy.symm hl

theorem thin_inner {n : ℕ} (a : Attachment X J n) : ThinPaths a.inner :=
  thin_homeomorph a.innerHomeomorph.symm thin_sigma_contractible

include X J in
/-- Fundamental groups of arbitrary ordinary graph attachments are free. -/
theorem isFree_attachment (a : Attachment X J 1) [DiscreteTopology a.lower]
    {r : X} (q : ∀ x, Path r x) : IsFreeGroup (FundamentalGroup X r) :=
  isFree_fundamentalGroup q a.outer a.inner (thin_outer a thin_discrete) (thin_inner a)
    a.outer_open a.inner_open a.outer_union_inner

end EilenbergGanea.ForestCover


namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover CWCollar
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
abbrev Cell (n : ℕ) := RelCWComplex.cell C n

def characteristic {n : ℕ} (i : Cell C n) : C(Disk n,C) :=
  ⟨fun z => ⟨RelCWComplex.map n i z.val,
    RelCWComplex.closedCell_subset_complex n i ⟨z.val,z.property,rfl⟩⟩,
    (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩

abbrev CellDisks := Σ c : (Σ n, Cell C n), Disk c.1
def diskSum : CellDisks C → C := fun c => characteristic C c.1.2 c.2

omit [T2Space X] in
theorem diskSum_continuous : Continuous (diskSum C) :=
  continuous_sigma (fun c => (characteristic C c.2).continuous)

omit [T2Space X] in
theorem diskSum_surjective : Function.Surjective (diskSum C) := by
  intro x
  have hx : x.val ∈ ⋃ (n : ℕ) (i : Cell C n), RelCWComplex.closedCell n i := by
    rw [CWComplex.union]; exact x.property
  obtain ⟨n,i,z,hz,he⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using hx
  exact ⟨⟨⟨n,i⟩,⟨z,hz⟩⟩,Subtype.ext he⟩

theorem diskSum_quotient : IsQuotientMap (diskSum C) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨diskSum_surjective C,fun A => ⟨fun h => h.preimage (diskSum_continuous C),?_⟩⟩
  intro hA
  have hc : IsClosed ((Subtype.val : C → X) '' A) := by
    apply (CWComplex.closed C _ (by rintro _ ⟨x,_,rfl⟩; exact x.property)).mpr
    intro n i
    have hD : IsClosed (characteristic C i ⁻¹' A) :=
      hA.preimage (continuous_sigmaMk (i := (⟨n,i⟩ : Σ n,Cell C n)))
    have he : (fun z : Disk n => (characteristic C i z).val) '' (characteristic C i ⁻¹' A) =
        (Subtype.val '' A) ∩ RelCWComplex.closedCell n i := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨characteristic C i z,hz,rfl⟩,z.val,z.property,rfl⟩
      · rintro ⟨⟨y,hy,hxy⟩,z,hz,he⟩
        refine ⟨⟨z,hz⟩,?_,he⟩
        have h : characteristic C i ⟨z,hz⟩ = y := Subtype.ext (he.trans hxy.symm)
        simpa only [mem_preimage,h] using hy
    rw [← he]
    exact (hD.isCompact.image (continuous_subtype_val.comp (characteristic C i).continuous)).isClosed
  have hpre := hc.preimage (continuous_subtype_val : Continuous (Subtype.val : C → X))
  simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hpre

def lower (m : ℕ) : Set C := Subtype.val ⁻¹' (CWComplex.skeletonLT C m : Set X)

theorem characteristic_lower {k m : ℕ} (hk : k < m) (i : Cell C k) (z : Disk k) :
    characteristic C i z ∈ lower C m := by
  apply RelCWComplex.skeletonLT_mono (show (k:ℕ∞)+1 ≤ (m:ℕ∞) by exact_mod_cast Nat.succ_le_of_lt hk)
    (RelCWComplex.closedCell_subset_skeletonLT k i (show (characteristic C i z).val ∈ RelCWComplex.closedCell k i from ?_))
  exact ⟨z.val,z.property,rfl⟩

def topSum (m : ℕ) : lower C m ⊕ (Σ _ : Cell C m, Disk m) → C :=
  Sum.elim Subtype.val (fun c => characteristic C c.1 c.2)

theorem topSum_continuous (m : ℕ) : Continuous (topSum C m) :=
  continuous_subtype_val.sumElim (continuous_sigma (fun i => (characteristic C i).continuous))

theorem topSum_surjective (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell C k)) :
    Function.Surjective (topSum C m) := by
  intro x
  obtain ⟨⟨⟨k,i⟩,z⟩,rfl⟩ := diskSum_surjective C x
  by_cases hk : k < m
  · exact ⟨.inl ⟨characteristic C i z,characteristic_lower C hk i z⟩,rfl⟩
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact ⟨.inr ⟨i,z⟩,rfl⟩

theorem topSum_quotient (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell C k)) :
    IsQuotientMap (topSum C m) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨topSum_surjective C m hd,fun A => ⟨fun h => h.preimage (topSum_continuous C m),?_⟩⟩
  intro hA
  apply (diskSum_quotient C).isClosed_preimage.mp
  rw [isClosed_sigma_iff]
  rintro ⟨k,i⟩
  by_cases hk : k < m
  · let f : Disk k → lower C m ⊕ (Σ _ : Cell C m,Disk m) :=
      fun z => .inl ⟨characteristic C i z,characteristic_lower C hk i z⟩
    exact hA.preimage (continuous_inl.comp ((characteristic C i).continuous.subtype_mk (characteristic_lower C hk i)))
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact hA.preimage (continuous_inr.comp (continuous_sigmaMk (i := i)))

def attachment (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell C k)) : Attachment C (Cell C m) m where
  lower := lower C m
  closed_lower := (CWComplex.skeletonLT C m).closed'.preimage continuous_subtype_val
  chart := characteristic C
  boundary := by
    intro i z hz
    exact RelCWComplex.cellFrontier_subset_skeletonLT m i
      ⟨z.val,by simpa only [mem_sphere,dist_zero_right] using hz,rfl⟩
  interior := by
    intro i z hz hl
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeletonLT_openCell le_rfl) hl
      ⟨z.val,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
  disjoint := by
    intro i j z w hz hw he
    have he := congrArg Subtype.val he
    have hz' : z.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hz
    have hw' : w.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hw
    by_cases hij : i = j
    · subst j
      refine ⟨rfl,Subtype.ext ((RelCWComplex.map m i).injOn ?_ ?_ he)⟩
      · simpa only [RelCWComplex.source_eq] using hz'
      · simpa only [RelCWComplex.source_eq] using hw'
    · exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne
        (show (⟨m,i⟩ : Σ k,Cell C k) ≠ ⟨m,j⟩ by simpa using hij))
        ⟨z.val,hz',rfl⟩ ⟨w.val,hw',he.symm⟩)
  quotient := topSum_quotient C m hd

end EilenbergGanea.CWSubspace


namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- The ordinary zero-skeleton is discrete without any cardinality restriction. -/
theorem discrete_dim_zero (hd : ∀ k, 0 < k → IsEmpty (Cell C k)) : DiscreteTopology C := by
  apply discreteTopology_iff_forall_isOpen.mpr
  intro U
  apply (diskSum_quotient C).isOpen_preimage.mp
  rw [isOpen_sigma_iff]
  rintro ⟨n,i⟩
  have hn : n = 0 := by
    by_contra h
    have := hd n (Nat.pos_of_ne_zero h)
    exact isEmptyElim i
  subst n
  have : Subsingleton (Disk 0) := inferInstance
  exact isOpen_discrete _

end EilenbergGanea.CWSubspace

namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

def lowerHomeomorph (m : ℕ) : lower C m ≃ₜ (CWComplex.skeletonLT C m : Set X) where
  toFun z := ⟨z.val.val,z.property⟩
  invFun z := ⟨⟨z.val,(CWComplex.skeletonLT C m).subset_complex z.property⟩,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem discrete_lower_one : DiscreteTopology (lower C 1) := by
  let S := CWComplex.skeletonLT C (1 : ℕ)
  have hd (k : ℕ) (hk : 0 < k) : IsEmpty (Cell (S : Set X) k) := by
    refine ⟨fun i => ?_⟩
    have hki : (k : ℕ∞) < 1 := by
      have hi := i.property
      simpa only [S,CWComplex.skeletonLT_I,Set.mem_ofPred_eq,Nat.cast_one] using hi
    have hkn : k < 1 := by exact_mod_cast hki
    omega
  let : DiscreteTopology (CWComplex.skeletonLT C (1 : ℕ) : Set X) := by
    exact discrete_dim_zero (S : Set X) hd
  exact (lowerHomeomorph C 1).symm.discreteTopology

end EilenbergGanea.CWSubspace

namespace EilenbergGanea.ForestCover
open Set Topology CWSubspace
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- Arbitrary ordinary one-dimensional CW spaces have free fundamental groups. -/
theorem isFree_ordinary_graph (hd : ∀ k, 1 < k → IsEmpty (Cell C k))
    {r : C} (q : ∀ x, Path r x) : IsFreeGroup (FundamentalGroup C r) := by
  let : DiscreteTopology (CWSubspace.attachment C 1 hd).lower := discrete_lower_one C
  exact isFree_attachment (CWSubspace.attachment C 1 hd) q

end EilenbergGanea.ForestCover



end

end OAI
