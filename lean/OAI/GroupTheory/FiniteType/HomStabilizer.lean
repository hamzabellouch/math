import Mathlib
import OAI.GroupTheory.FiniteType.AscendingHNNInnerTwist

namespace OAI

noncomputable section
open scoped Pointwise
namespace HomStabilizer
variable {G X J : Type} [Group G]
                                                                                  
def conjugateTuple (ρ : G →* Equiv.Perm X) (x y : J → X) (q : G)
    (h : ∀ j, ρ q (x j) = y j) : fixedTuple ρ x ≃* fixedTuple ρ y where
  toFun g := ⟨q * g.val * q⁻¹, by
    intro j
    rw [← h j,map_mul,map_mul,map_inv]
    change ρ q (ρ g.val ((ρ q).symm (ρ q (x j)))) = ρ q (x j)
    rw [Equiv.symm_apply_apply,g.property j]⟩
  invFun g := ⟨q⁻¹ * g.val * q, by
    intro j
    rw [map_mul,map_mul,map_inv]
    change (ρ q).symm (ρ g.val (ρ q (x j))) = x j
    rw [h j,g.property j,←h j,Equiv.symm_apply_apply]⟩
  left_inv g := by apply Subtype.ext; change q⁻¹ * (q * g.val * q⁻¹) * q = g.val; group
  right_inv g := by apply Subtype.ext; change q * (q⁻¹ * g.val * q) * q⁻¹ = g.val; group
  map_mul' g g' := by
    apply Subtype.ext
    change q * (g.val * g'.val) * q⁻¹ = (q*g.val*q⁻¹)*(q*g'.val*q⁻¹)
    group

def enumeratedSubset [MulAction G X] (y : J → X) (s : Set X)
    (h : Set.range y=s) : fixedTuple (MulAction.toPermHom G X) y ≃* fixingSubgroup G s where
  toFun g := ⟨g.val, (mem_fixingSubgroup_iff G).mpr (by
    intro x hx
    obtain ⟨j,rfl⟩ := h.symm.subset hx
    exact g.property j)⟩
  invFun g := ⟨g.val, by
    intro j
    exact (mem_fixingSubgroup_iff G).mp g.property (y j) (h.subset ⟨j,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end HomStabilizer
namespace SimpleFInftyOvergroups

structure SplittingTorusModel (G : Type) [Group G] where
  U : Type
  P : Type
  [groupU : Group U]
  [groupP : Group P]
  [finitePresentation : Group.IsFinitelyPresented P]
  f : U →* U
  injective : Function.Injective f
  α : U →* P
  b : P →* U
  factorization : f = b.comp α
  splitting₂ : ListChains.IdempotentSplittings U (ZMod 2) f
  splitting₃ : ListChains.IdempotentSplittings U (ZMod 3) f
  identification : AscendingHNN.Torus f injective ≃* G
attribute [instance] SplittingTorusModel.groupU SplittingTorusModel.groupP
  SplittingTorusModel.finitePresentation

namespace SplittingTorusModel
variable {G H X : Type} [Group G] [Group H]
def relabel (M : SplittingTorusModel G) (e : G ≃* H) : SplittingTorusModel H :=
  { M with identification := M.identification.trans e }

theorem geometric (M : SplittingTorusModel G) : HasTypeFInfty G := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  subst f
  exact HasTypeFInfty.of_equiv e (ascending_hnn_geometric α b hf F₂ F₃)

theorem setwise_geometric [MulAction G X] (s : Set X) (hs : s.Finite)
    (M : SplittingTorusModel (fixingSubgroup G s)) :
    HasTypeFInfty (MulAction.stabilizer G s) := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  subst f
  exact setwise_stabilizer_of_ascending_torus α b hf F₂ F₃ s hs e
end SplittingTorusModel
end SimpleFInftyOvergroups

namespace StageGeometry
open StageConstruction
variable {R Y W : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y] [DecidableEq Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

include hTS hSe hTρ hpt he F₂ F₃ in

theorem finite_tuple_model [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (n : ℕ) (y : Fin n → LimitPoints φ S point) (hy : Function.Injective y) :
    Nonempty (SimpleFInftyOvergroups.SplittingTorusModel
      (HomStabilizer.fixedTuple
        (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) y)) := by
  have hs := sigma_injective φ e S T hTS point he hφ hpt
  let : Infinite (X R) := stagePoints_infinite φ e S T hTS point hφ hpt he
  let x : Fin n → X R := fun i => Infinite.natEmbedding (X R) i.val
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    exact (Infinite.natEmbedding (X R)).injective hij
  let z := sigma φ S point ∘ x
  have hz : Function.Injective z := hs.comp hx
  obtain ⟨a,ha⟩ := sigma_tuple_transitivity φ D e S T hTS hSe point hpt n z x hz hx
  obtain ⟨α,b,hb⟩ := factor φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs T hTρ
    e hTS hSe hz hpt
  let w : Fin n → LimitPoints φ S point := SequentialLimit.of (sigma φ S point) 0 ∘ z
  have hw : Function.Injective w := (SequentialLimit.of_injective _ hs 0).comp hz
  obtain ⟨q,hq⟩ := limit_tuple_transitivity φ D e S T hTS hSe ρ ι point hρS hpoint
    hφ hρ hι hpt n w y hw hy
  refine ⟨{
    U := base φ D S ρ ι point hρS hpoint hφ hρ hι z a
    P := Steinberg.Group (Fin 6) R
    f := endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha
    injective := endomorphism_injective φ D S ρ ι point hρS hpoint hφ hρ hι z a ha
    α := α
    b := b
    factorization := hb.symm
    splitting₂ := splittings φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs (ZMod 2) F₂
    splitting₃ := splittings φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs (ZMod 3) F₃
    identification := (TorusStabilizer.torusEquiv (trans φ D ρ ι)
      (transInjective φ D ρ ι hφ hρ hι) (shift φ S point)
      (compatible φ D S ρ ι point hρS hpoint) z a ha).trans
      (HomStabilizer.conjugateTuple
        (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) w y q hq) }⟩

include hTS hSe hTρ hpt he F₂ F₃ in

theorem finite_tuple_geometric [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (n : ℕ) (y : Fin n → LimitPoints φ S point) (hy : Function.Injective y) :
    SimpleFInftyOvergroups.HasTypeFInfty
      (HomStabilizer.fixedTuple
        (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) y) := by
  have hs := sigma_injective φ e S T hTS point he hφ hpt
  let : Infinite (X R) := stagePoints_infinite φ e S T hTS point hφ hpt he
  let x : Fin n → X R := fun i => Infinite.natEmbedding (X R) i.val
  have hx : Function.Injective x := by
    intro i j hij
    apply Fin.ext
    exact (Infinite.natEmbedding (X R)).injective hij
  let z := sigma φ S point ∘ x
  have hz : Function.Injective z := hs.comp hx
  obtain ⟨a,ha⟩ := sigma_tuple_transitivity φ D e S T hTS hSe point hpt n z x hz hx
  have hgeo := aligned_geometric φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs T hTρ
    e hTS hSe hz hpt F₂ F₃
  let w : Fin n → LimitPoints φ S point := SequentialLimit.of (sigma φ S point) 0 ∘ z
  have hw : Function.Injective w := (SequentialLimit.of_injective _ hs 0).comp hz
  obtain ⟨q,hq⟩ := limit_tuple_transitivity φ D e S T hTS hSe ρ ι point hρS hpoint
    hφ hρ hι hpt n w y hw hy
  exact SimpleFInftyOvergroups.HasTypeFInfty.of_equiv
    (HomStabilizer.conjugateTuple
      (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι) w y q hq) hgeo

abbrev limitAction : MulAction (LimitGroup φ D ρ ι hφ hρ hι) (LimitPoints φ S point) :=
  MulAction.compHom _ (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι)

include hTS hSe hTρ hpt he F₂ F₃ in
theorem finite_set_model [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (s : Set (LimitPoints φ S point)) (hs : s.Finite) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    Nonempty (SimpleFInftyOvergroups.SplittingTorusModel
      (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s)) := by
  classical
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  let := hs.fintype
  let E := Fintype.equivFin s
  let y : Fin (Fintype.card s) → LimitPoints φ S point := fun i => (E.symm i).val
  have hy : Function.Injective y := Subtype.val_injective.comp E.symm.injective
  have hyS : Set.range y = s := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (E.symm i).property
    · intro hx
      exact ⟨E ⟨x,hx⟩,congrArg Subtype.val (E.symm_apply_apply ⟨x,hx⟩)⟩
  obtain ⟨M⟩ := finite_tuple_model φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ (Fintype.card s) y hy
  exact ⟨M.relabel (HomStabilizer.enumeratedSubset y s hyS)⟩

include hTS hSe hTρ hpt he F₂ F₃ in

theorem finite_setwise_geometric [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (s : Set (LimitPoints φ S point)) (hs : s.Finite) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    SimpleFInftyOvergroups.HasTypeFInfty
      (MulAction.stabilizer (LimitGroup φ D ρ ι hφ hρ hι) s) := by
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  obtain ⟨M⟩ := finite_set_model φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ s hs
  exact M.setwise_geometric s hs

include hTS hSe hTρ hpt he F₂ F₃ in
theorem finite_pointwise_geometric [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)]
    (s : Set (LimitPoints φ S point)) (hs : s.Finite) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    SimpleFInftyOvergroups.HasTypeFInfty
      (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s) := by
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  obtain ⟨M⟩ := finite_set_model φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ s hs
  exact M.geometric

include hTS hSe hρS hTρ hpoint hpt he F₂ F₃ in
                                                                   
theorem limit_geometric [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)] :
    SimpleFInftyOvergroups.HasTypeFInfty (LimitGroup φ D ρ ι hφ hρ hι) := by
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  have h := finite_pointwise_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ ∅ Set.finite_empty
  rw [fixingSubgroup_empty] at h
  exact SimpleFInftyOvergroups.HasTypeFInfty.of_equiv Subgroup.topEquiv h

include hTS hSe hTρ hpt he F₂ F₃ in

theorem all_geometric_of_ring_data
    (A : Type) [Finite A] (π : SteinbergFinitePresentation.Coeff A →ₙ+* R)
    (hπ : Function.Surjective π) (rel : Set (SteinbergFinitePresentation.Coeff A))
    (hrel : rel.Finite)
    (hker : {r | π r=0}=(TwoSidedIdeal.span rel : Set (SteinbergFinitePresentation.Coeff A))) :
    letI := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
    SimpleFInftyOvergroups.HasTypeFInfty (LimitGroup φ D ρ ι hφ hρ hι) ∧
      ∀ s : Set (LimitPoints φ S point), s.Finite →
        SimpleFInftyOvergroups.HasTypeFInfty (fixingSubgroup (LimitGroup φ D ρ ι hφ hρ hι) s) ∧
        SimpleFInftyOvergroups.HasTypeFInfty (MulAction.stabilizer (LimitGroup φ D ρ ι hφ hρ hι) s) := by
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  let := SteinbergFinitePresentation.rank_six_finitelyPresented A π hπ rel hrel hker
  refine ⟨limit_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃,?_⟩
  intro s hs
  exact ⟨finite_pointwise_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ s hs,
    finite_setwise_geometric φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
      hφ hρ hι hpt he F₂ F₃ s hs⟩

end StageGeometry

end

end OAI
