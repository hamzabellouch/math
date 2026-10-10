import Mathlib
import OAI.GroupTheory.FiniteType.FiniteIndexProducts

namespace OAI

section
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrderChains
open OrderListChains
variable (P : Type*) [Preorder P]
lemma exactSubtype_of_exactSet {U : Set P} (u : U) {n : ℕ} (he : ExactSet P U n) :
    ExactIn U n := by
  intro c hc hn hd ha
  have hcU : c ∈ onSet U Set.univ := fun s hs => ⟨hc hs,Set.subset_univ _⟩
  have hi := map_onSet U (fun x : U => x.val) (V := U)
    (fun x _ => x.property) (fun _ _ _ _ hxy => hxy) hcU
  have hid : boundary P (mapChain U (fun x : U => x.val) c) = 0 := by
    rw [boundary_mapChain,hd,map_zero]
  have hia : augmentation P (mapChain U (fun x : U => x.val) c) = 0 := by
    rw [augmentation_mapChain,ha]
  obtain ⟨d,hdU,hdn,hdd⟩ := he _ hi (map_degree U _ hn) hid hia
  have hp := map_onSet P (project P U u) (V := Set.univ) (fun _ _ => Set.mem_univ _)
    (fun x hx y hy hxy => by
      change (project P U u x).val ≤ (project P U u y).val
      simpa only [project_val P u hx,project_val P u hy] using hxy) hdU
  refine ⟨mapChain P (project P U u) d,onSet_le_module U _ hp,map_degree P _ hdn,?_⟩
  rw [boundary_mapChain,hdd,mapChain_comp]
  have hf : project P U u ∘ (fun x : U => x.val) = id := funext (project_include P u)
  rw [hf,mapChain_id]
end OrderChains

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

theorem localGroup_regular_products [Nonempty S] (hρ : Function.Injective ρ)
    (ho : Oligomorphic ρ)
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
    (I : Type) (N : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (localGroup ρ) I) (N+1)) := by
  let h := 2*(2*2^(N+1+2)+1)
  let P := Sublevel (ρ := ρ) h
  have ht : 1 ≤ h := by dsimp [h]; omega
  let u : P := ⟨⟨trivial ρ⟩,by
    change rank ρ (trivial ρ) ≤ h
    simpa only [rank,trivial,Finset.card_singleton] using ht⟩
  let : Nonempty P := ⟨u⟩
  apply OrderBrown.vanishing (G := localGroup ρ) (P := P) N
  · intro i hi
    apply OrderChains.exactSubtype_of_exactSet (CutBasis ρ) u
    apply sublevel_exact i h
    dsimp [h]
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hi 2)
    omega
  · exact simplex_finite_orbits ho h
  · intro n s
    apply simplex_stabilizer_fg hρ _ h n s
    intro F
    let := hFP F
    exact ActionPresentation.fg_of_fp
  · exact simplex_stabilizer_products hρ hFP hz h

theorem localGroup_geometric_of_certificates [Nonempty S]
    (hρ : Function.Injective ρ) (ho : Oligomorphic ρ)
    [Group.IsFinitelyPresented A]
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1))) :
    SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ) := by
  let := localGroup_finitelyPresented hρ ho (fun F => by
    let := hFP F
    exact ActionPresentation.fg_of_fp)
  apply SimpleFInftyOvergroups.geometric_product_criterion
  intro I n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact localGroup_regular_products hρ ho hFP hz I j
end TwistedBrin.Basis.CutBasis

end
end

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SimpleFInftyOvergroups.SplittingTorusModel
variable {G : Type} [Group G]

theorem finitelyPresented (M : SplittingTorusModel G) : Group.IsFinitelyPresented G := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  let := AscendingHNN.finitelyPresented_of_factorization f hf α b hb
  exact Group.IsFinitelyPresented.equiv e

theorem products₂ (M : SplittingTorusModel G) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (n+2)) := by
  rcases M with @⟨U,P,gU,gP,hP,f,hf,α,b,hb,F₂,F₃,e⟩
  subst f
  let := ActionPresentation.fg_of_fp (G := P)
  have hz : IsZero (groupHomology (RegularProduct.rep (AscendingHNN.Torus (b.comp α) hf) I) (n+2)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => (AscendingHNN.regular_product_homology_vanishes α b hf F₂ F₃ I n x).trans
      (AscendingHNN.regular_product_homology_vanishes α b hf F₂ F₃ I n y).symm⟩
  exact hz.of_iso (RegularProductR.homologyRelabel e I (n+2)).symm

theorem products (M : SplittingTorusModel G) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (n+1)) := by
  let := M.finitelyPresented
  obtain ⟨P,hP⟩ := ProductFiniteResolution.finite_free_resolution_of_products G (by
    intro J m hm
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa only [Nat.add_comm 2] using M.products₂ J j)
  exact ProductCriterion.finite_free_products (I := I) P hP n
end SimpleFInftyOvergroups.SplittingTorusModel

end
end

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)

def globalHom : A →* localGroup ρ where
  toFun a := ⟨twist ρ a,by
    intro x
    refine ⟨Prefix.empty,Prefix.empty,a,⟨x,rfl⟩,?_⟩
    intro y
    rfl⟩
  map_one' := by
    apply Subtype.ext
    exact Equiv.ext (twist_one ρ)
  map_mul' a b := by
    apply Subtype.ext
    exact Equiv.ext (twist_mul ρ a b)

lemma globalHom_injective (hρ : Function.Injective ρ) : Function.Injective (globalHom ρ) := by
  intro a b he
  exact twist_injective ρ hρ (congrArg Subtype.val he)

lemma pointwise_eq_fixing (F : Finset S) :
    letI := MulAction.compHom S ρ
    pointwiseStabilizer ρ F = fixingSubgroup A (F : Set S) := by
  let := MulAction.compHom S ρ
  ext a
  exact (mem_fixingSubgroup_iff A).symm

lemma pointwise_empty : pointwiseStabilizer ρ ∅ = ⊤ := by
  ext a
  simp [pointwiseStabilizer]

lemma oligomorphic_of_highly_transitive [Infinite S]
    (ht : ∀ n (x y : Fin n → S), Function.Injective x → Function.Injective y →
      ∃ a : A, ∀ i, ρ a (x i) = y i) : Oligomorphic ρ := by
  classical
  intro n
  let y : Fin n → S := fun i => Infinite.natEmbedding S i.val
  have hy : Function.Injective y := (Infinite.natEmbedding S).injective.comp Fin.val_injective
  let E : Finset S := Finset.univ.image y
  refine ⟨{E},?_⟩
  intro F hF
  let e : F ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hF)
  let x : Fin n → S := fun i => (e.symm i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  obtain ⟨a,ha⟩ := ht n x y hx hy
  refine ⟨E,Finset.mem_singleton_self _,a,?_⟩
  ext s
  constructor
  · intro hs
    obtain ⟨t,ht,hst⟩ := Finset.mem_map.mp hs
    apply Finset.mem_image.mpr
    refine ⟨e ⟨t,ht⟩,Finset.mem_univ _,?_⟩
    rw [← ha]
    simpa [x] using hst
  · intro hs
    obtain ⟨i,hi,hsi⟩ := Finset.mem_image.mp hs
    exact Finset.mem_map.mpr ⟨x i,(e.symm i).property,(ha i).trans hsi⟩

theorem localGroup_geometric_of_torus_models [Nonempty S]
    (hρ : Function.Injective ρ) (ho : Oligomorphic ρ)
    (hm : ∀ F : Finset S, Nonempty
      (SimpleFInftyOvergroups.SplittingTorusModel (pointwiseStabilizer ρ F))) :
    SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ) := by
  have hf (F : Finset S) : Group.IsFinitelyPresented (pointwiseStabilizer ρ F) :=
    (hm F).some.finitelyPresented
  let := hf ∅
  let e : pointwiseStabilizer ρ ∅ ≃* A := (MulEquiv.subgroupCongr (pointwise_empty ρ)).trans Subgroup.topEquiv
  let : Group.IsFinitelyPresented A := Group.IsFinitelyPresented.equiv e
  exact Basis.CutBasis.localGroup_geometric_of_certificates hρ ho hf
    (fun F I n => (hm F).some.products I n)
end TwistedBrin

namespace StageGeometry
open StageConstruction
variable {R Y W G : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y]
  [DecidableEq Y] [Group G]
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
theorem localGroup_geometric_of_binary_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel) :
    SimpleFInftyOvergroups.HasTypeFInfty
      (TwistedBrin.localGroup (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι)) := by
  let σ := limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι
  let := limitAction φ D S ρ ι point hρS hpoint hφ hρ hι
  let := BinaryAlgebraPresentation.rank_six_of_binary_presentation A π hπ rel hrel hker
  let := limitPoints_infinite φ e S T hTS point hφ hpt he
  have hσ : Function.Injective σ :=
    limitRepresentation_injective φ D e S T hTS ρ ι point hρS hpoint hφ hρ hι hpt he
  have ho : TwistedBrin.Oligomorphic σ := TwistedBrin.oligomorphic_of_highly_transitive σ
    (fun n x y hx hy => limit_tuple_transitivity φ D e S T hTS hSe ρ ι point hρS hpoint
      hφ hρ hι hpt n x y hx hy)
  apply TwistedBrin.localGroup_geometric_of_torus_models σ hσ ho
  intro F
  obtain ⟨M⟩ := finite_set_model φ D e S T hTS hSe ρ ι point hρS hTρ hpoint
    hφ hρ hι hpt he F₂ F₃ (F : Set (LimitPoints φ S point)) F.finite_toSet
  exact ⟨M.relabel (MulEquiv.subgroupCongr (TwistedBrin.pointwise_eq_fixing σ F)).symm⟩

include hTS hSe hTρ hpt he F₂ F₃ in

theorem localGroup_overgroup_of_binary_ring_data
    (A : Type) [Finite A] (π : FreeAlgebra (ZMod 2) A →+* R)
    (hπ : Function.Surjective π) (rel : Set (FreeAlgebra (ZMod 2) A))
    (hrel : rel.Finite) (hker : TwoSidedIdeal.ker π=TwoSidedIdeal.span rel)
    (g : G →* Rˣ) (hg : Function.Injective g) :
    SimpleFInftyOvergroups.HasTypeFInfty
      (TwistedBrin.localGroup (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι)) ∧
    ∃ ν : G →* TwistedBrin.localGroup (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι),
      Function.Injective ν := by
  refine ⟨localGroup_geometric_of_binary_ring_data φ D e S T hTS hSe ρ ι point
    hρS hTρ hpoint hφ hρ hι hpt he F₂ F₃ A π hπ rel hrel hker,?_⟩
  let σ := limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι
  let j := (AscendingHNN.embed (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)).comp
    ((transitionUnits φ D).comp g)
  refine ⟨(TwistedBrin.globalHom σ).comp j,?_⟩
  apply (TwistedBrin.globalHom_injective σ
    (limitRepresentation_injective φ D e S T hTS ρ ι point hρS hpoint hφ hρ hι hpt he)).comp
  exact (AscendingHNN.embed_injective _ _).comp ((transitionUnits_injective φ D hφ).comp hg)
end StageGeometry

end
end

section

noncomputable section
open scoped commutatorElement

end
end

end OAI
