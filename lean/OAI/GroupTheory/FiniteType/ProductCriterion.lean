import Mathlib
import OAI.GroupTheory.FiniteType.SourceCorner

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCriterion
variable {k G I : Type} [CommRing k] [Group G]

def coordinates (C : Rep k G) : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants →ₗ[k] (I → C) :=
  LinearMap.pi (fun i => coordinate C i)

lemma coordinates_bijective_of_iso {C : Rep k G} {α : Type} [Finite α]
    (e : C ≅ Rep.free k G α) : Function.Bijective (coordinates (I := I) C) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)
  let E := F.mapIso e
  have hn (y : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants) :
      coordinates (Rep.free k G α) (E.hom y) = fun i => e.hom.hom (coordinates C y i) := by
    funext i
    exact coordinate_natural _ e.hom i y
  refine ⟨?_,?_⟩
  · intro x y h
    apply (ModuleCat.mono_iff_injective E.hom).mp inferInstance
    apply free_coordinates_injective α
    change coordinates (Rep.free k G α) (E.hom x) = coordinates (Rep.free k G α) (E.hom y)
    rw [hn,hn,h]
  · intro z
    obtain ⟨y,hy⟩ := free_coordinates_surjective (k := k) (G := G) (I := I) α
      (fun i => e.hom.hom (z i))
    refine ⟨E.inv y,?_⟩
    have hh := hn (E.inv y)
    have he : E.hom (E.inv y) = y := congrArg (fun f : F.obj (Rep.free k G α) ⟶ _ => f y)
      E.inv_hom_id
    rw [he] at hh
    funext i
    apply (Rep.mono_iff_injective e.hom).mp inferInstance
    exact (congrFun hh i).symm.trans (congrFun hy i)

theorem finite_free_products (P : ProjectiveResolution (Rep.trivial k G k))
    (hf : ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free k G α))
    (n : ℕ) : IsZero (groupHomology (RegularProductR.rep k G I) (n+1)) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)
  have hb (j : ℕ) : Function.Bijective (coordinates (I := I) (P.complex.X j)) := by
    obtain ⟨α,hα,⟨e⟩⟩ := hf j
    let := hα
    exact coordinates_bijective_of_iso e
  have he : (P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).ExactAt (n+1) := by
    rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hp := (HomologicalComplex.exactAt_iff' P.complex (n+2) (n+1) n
      (by simp) (by simp)).mp (P.complex_exactAt_succ n)
    have hp' := (ShortComplex.moduleCat_exact_iff _).mp
      (hp.map (forget₂ (Rep k G) (ModuleCat k)))
    have hz (i : I) : (P.complex.d (n+1) n).hom (coordinate (P.complex.X (n+1)) i x) = 0 := by
      rw [← coordinate_natural (P.complex.X n) (P.complex.d (n+1) n) i x]
      change coordinate (P.complex.X n) i
        ((P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).d (n+1) n x) = 0
      change (P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).d (n+1) n x = 0 at hx
      rw [hx]
      exact (coordinate (P.complex.X n) i).map_zero
    choose y hy using fun i => hp' (coordinate (P.complex.X (n+1)) i x) (hz i)
    obtain ⟨a,ha⟩ := (hb (n+2)).surjective y
    refine ⟨a,(hb (n+1)).injective ?_⟩
    funext i
    change coordinate (P.complex.X (n+1)) i
      (tensorMap (P.complex.X (n+1)) (P.complex.d (n+2) (n+1)) a) = _
    rw [coordinate_natural]
    exact (congrArg (P.complex.d (n+2) (n+1)).hom (congrFun ha i)).trans (hy i)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp he).of_iso
    (groupHomologyIso (RegularProductR.rep k G I) (n+1) P)
lemma tensorMap_surjective {C D : Rep k G} (f : C ⟶ D) (hf : Function.Surjective f.hom) :
    Function.Surjective (tensorMap (I := I) D f) := by
  intro x
  obtain ⟨a,rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  obtain ⟨b,rfl⟩ := LinearMap.lTensor_surjective (RegularProductR.Module k G I) hf a
  exact ⟨Representation.Coinvariants.mk _ b,rfl⟩

theorem coordinates_of_presentation {C : Rep k G} {α β : Type} [Finite α] [Finite β]
    (d : Rep.free k G β ⟶ Rep.free k G α) (f : Rep.free k G α ⟶ C) [Epi f]
    (w : d ≫ f = 0) (he : (ShortComplex.mk d f w).Exact) :
    Function.Bijective (coordinates (I := I) C) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)
  have hfs : Function.Surjective f.hom := (Rep.epi_iff_surjective f).mp inferInstance
  have hFt : Function.Surjective (F.map f) := tensorMap_surjective f hfs
  have hbase := (ShortComplex.moduleCat_exact_iff _).mp
    (he.map (forget₂ (Rep k G) (ModuleCat k)))
  refine ⟨?_,?_⟩
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨y,hy⟩ := hFt x
    have hcy (i : I) : f.hom (coordinate (Rep.free k G α) i y) = 0 := by
      rw [← coordinate_natural]
      change coordinate C i ((F.map f) y) = 0
      rw [hy]
      exact congrFun hx i
    choose z hz using fun i => hbase (coordinate (Rep.free k G α) i y) (hcy i)
    obtain ⟨a,ha⟩ := free_coordinates_surjective (k := k) (G := G) (I := I) β z
    have hd : (F.map d) a = y := by
      apply free_coordinates_injective α
      funext i
      change coordinate (Rep.free k G α) i (tensorMap _ d a) = _
      rw [coordinate_natural]
      exact (congrArg d.hom (congrFun ha i)).trans (hz i)
    rw [← hy,← hd]
    change ((F.map d ≫ F.map f) a) = 0
    rw [← Functor.map_comp,w,Functor.map_zero]
    rfl
  · intro z
    choose y hy using fun i => hfs (z i)
    obtain ⟨a,ha⟩ := free_coordinates_surjective (k := k) (G := G) (I := I) α y
    refine ⟨(F.map f) a,?_⟩
    funext i
    change coordinate C i (tensorMap _ f a) = _
    rw [coordinate_natural]
    exact (congrArg f.hom (congrFun ha i)).trans (hy i)

end ProductCriterion

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
namespace ProductBrown
attribute [-instance] AddCommGroup.toIntModule
variable {G I : Type} [Group G]
abbrev M := RegularProductR.rep ℤ G I

lemma tensorExact (S : ShortComplex (Rep.{0} ℤ G)) (he : S.Exact) :
    (S.map (tensorLeft (M (G := G) (I := I)))).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  have hh := (ShortComplex.moduleCat_exact_iff _).mp
    (he.map (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)))
  have hex : Function.Exact S.f.hom.toLinearMap S.g.hom.toLinearMap := by
    intro x
    constructor
    · exact hh x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f : S.X₁ ⟶ S.X₃ => f.hom y) S.zero
  exact fun x hx => (Module.Flat.lTensor_exact (RegularProductR.Module ℤ G I) hex x).mp hx

lemma H0exact (S : ShortComplex (Rep.{0} ℤ G)) (he : S.Exact)
    (hinj : Function.Injective (ProductCriterion.coordinates (I := I) S.X₃))
    (hbij : Function.Bijective (ProductCriterion.coordinates (I := I) S.X₂))
    (hsur : Function.Surjective (ProductCriterion.coordinates (I := I) S.X₁)) :
    ((S.map (tensorLeft (M (G := G) (I := I)))).map (groupHomology.functor ℤ G 0)).Exact := by
  have _ := hinj
  let F := (Rep.coinvariantsTensor ℤ G).obj (M (G := G) (I := I))
  have he' : (S.map F).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hbase := (ShortComplex.moduleCat_exact_iff _).mp
      (he.map (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)))
    have hc (i : I) : S.g.hom (ProductCriterion.coordinate S.X₂ i x) = 0 := by
      rw [← ProductCriterion.coordinate_natural]
      change ProductCriterion.coordinate S.X₃ i ((F.map S.g) x) = 0
      change (F.map S.g) x = 0 at hx
      rw [hx,map_zero]
    choose y hy using fun i => hbase (ProductCriterion.coordinate S.X₂ i x) (hc i)
    obtain ⟨a,ha⟩ := hsur y
    refine ⟨a,hbij.injective ?_⟩
    funext i
    change ProductCriterion.coordinate S.X₂ i (ProductCriterion.tensorMap _ S.f a) = _
    rw [ProductCriterion.coordinate_natural]
    exact (congrArg S.f.hom (congrFun ha i)).trans (hy i)
  let T := (S.map (tensorLeft (M (G := G) (I := I)))).map (groupHomology.functor ℤ G 0)
  let h : T ⟶ S.map F := {
    τ₁ := (groupHomology.H0Iso _).hom
    τ₂ := (groupHomology.H0Iso _).hom
    τ₃ := (groupHomology.H0Iso _).hom
    comm₁₂ := (groupHomology.map_id_comp_H0Iso_hom _).symm
    comm₂₃ := (groupHomology.map_id_comp_H0Iso_hom _).symm }
  let : Epi h.τ₁ := inferInstanceAs
    (Epi (groupHomology.H0Iso (M (G := G) (I := I) ⊗ S.X₁)).hom)
  let : IsIso h.τ₂ := inferInstanceAs
    (IsIso (groupHomology.H0Iso (M (G := G) (I := I) ⊗ S.X₂)).hom)
  let : Mono h.τ₃ := inferInstanceAs
    (Mono (groupHomology.H0Iso (M (G := G) (I := I) ⊗ S.X₃)).hom)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono h).mpr he'

theorem regularProductsOfComplex
    (C : ℕ → Rep ℤ G) (d : ∀ n, C (n+1) ⟶ C n)
    (w : ∀ n, d (n+1) ≫ d n = 0) (e : C 0 ≅ Rep.trivial ℤ G ℤ)
    (N : ℕ) [Epi (d 0)]
    (he : ∀ i ≤ N+1, (ShortComplex.mk (d (i+1)) (d i) (w i)).Exact)
    (hc : ∀ i ≤ N+3, 1 ≤ i → Function.Bijective (ProductCriterion.coordinates (I := I) (C i)))
    (ha : ∀ i ≤ N, ∀ n : ℕ,
      IsZero (groupHomology (M (G := G) (I := I) ⊗ C (i+1)) (n+1))) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (N+1)) := by
  let F := tensorLeft (M (G := G) (I := I))
  let D := fun i => F.obj (C i)
  let δ := fun i => F.map (d i)
  have w' (i : ℕ) : δ (i+1) ≫ δ i = 0 := by
    change F.map (d (i+1)) ≫ F.map (d i) = 0
    rw [← F.map_comp,w,Functor.map_zero]
  have hep : Epi (δ 0) := (Rep.epi_iff_surjective _).mpr
    (LinearMap.lTensor_surjective (RegularProductR.Module ℤ G I)
      ((Rep.epi_iff_surjective (d 0)).mp inferInstance))
  have hz := AcyclicChain.vanishing D δ w' N (fun i hi =>
    tensorExact (ShortComplex.mk _ _ (w i)) (he i (by omega)))
    (fun i hi => H0exact (ShortComplex.mk _ _ (w (i+1))) (he (i+1) (by omega))
      (hc (i+1) (by omega) (by omega)).injective (hc (i+2) (by omega) (by omega))
      (hc (i+3) (by omega) (by omega)).surjective) ha
  let E : D 0 ≅ M (G := G) (I := I) := F.mapIso e ≪≫ ρ_ _
  exact hz.of_iso (((groupHomology.functor ℤ G (N+1)).mapIso E).symm)
end ProductBrown

open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrbitCoefficients
variable {k G V W : Type} [CommRing k] [Group G] [MulAction G V] [MulAction G W]
variable (A : Rep k G)

local instance (V : Type) [MulAction G V] : CoeFun (FunctionalTree.diagonalRep (V := V) A) (fun _ => V → A) :=
  ⟨fun x => @DFunLike.coe (V →₀ A) V (fun _ => A) inferInstance x⟩

lemma diagonal_apply (g : G) (z : V →₀ A) (v : V) :
    ((FunctionalTree.diagonalRep (V := V) A).ρ g z : V →₀ A) v = A.ρ g (z (g⁻¹ • v)) := by
  classical
  change FunctionalTree.diagonalAction A g z v = _
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  | single x a =>
    rw [FunctionalTree.diagonalAction_single]
    by_cases h : g • x = v
    · have h' : x = g⁻¹ • v := by rw [← h,inv_smul_smul]
      simp [h']
    · have h' : x ≠ g⁻¹ • v := by intro h'; apply h; rw [h',smul_inv_smul]
      simp [h,h']

def diagonalMap (f : V → W) (hf : ∀ (g : G) (v : V), f (g • v) = g • f v) :
    FunctionalTree.diagonalRep (V := V) A ⟶ FunctionalTree.diagonalRep (V := W) A :=
  Rep.ofHom ⟨Finsupp.lmapDomain A k f,by
    intro g
    apply Finsupp.lhom_ext
    intro v a
    simp [hf]⟩

@[simp] lemma diagonalMap_single (f : V → W) (hf : ∀ (g : G) (v : V), f (g • v) = g • f v) (v : V) (a : A) :
    diagonalMap A f hf (Finsupp.single v a) = Finsupp.single (f v) a := by
  change Finsupp.mapDomain f (Finsupp.single v a) = _
  exact Finsupp.mapDomain_single

def diagonalIso (e : V ≃ W) (he : ∀ (g : G) (v : V), e (g • v) = g • e v) :
    FunctionalTree.diagonalRep (V := V) A ≅ FunctionalTree.diagonalRep (V := W) A := by
  have hi (g : G) (w : W) : e.symm (g • w) = g • e.symm w := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  exact {
    hom := diagonalMap A e he
    inv := diagonalMap A e.symm hi
    hom_inv_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Finsupp.lhom_ext
      intro v a
      change diagonalMap A e.symm hi (diagonalMap A e he (Finsupp.single v a)) = Finsupp.single v a
      simp only [diagonalMap_single,e.symm_apply_apply]
      rfl
    inv_hom_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Finsupp.lhom_ext
      intro v a
      change diagonalMap A e he (diagonalMap A e.symm hi (Finsupp.single v a)) = Finsupp.single v a
      simp only [diagonalMap_single,e.apply_symm_apply]
      rfl }

variable (V) in
abbrev Orbits := MulAction.orbitRel.Quotient G V
variable (j : Orbits (G := G) V)

def orbitInclusion : FunctionalTree.diagonalRep (V := j.orbit) A ⟶
    FunctionalTree.diagonalRep (V := V) A := diagonalMap A Subtype.val (fun _ _ => rfl)

def orbitProjection : FunctionalTree.diagonalRep (V := V) A ⟶
    FunctionalTree.diagonalRep (V := j.orbit) A :=
  Rep.ofHom ⟨Finsupp.lsubtypeDomain j.orbit,by
    intro g
    apply LinearMap.ext
    intro z
    apply Finsupp.ext
    intro v
    change ((FunctionalTree.diagonalRep (V := V) A).ρ g z : V →₀ A) v.val =
      ((FunctionalTree.diagonalRep (V := j.orbit) A).ρ g (Finsupp.subtypeDomain _ z) : j.orbit →₀ A) v
    rw [diagonal_apply,diagonal_apply]
    rfl⟩

lemma projection_apply (z : V →₀ A) (v : j.orbit) : (orbitProjection A j z : j.orbit →₀ A) v = z v := rfl

lemma inclusion_apply (z : j.orbit →₀ A) (v : V) :
    (orbitInclusion A j z : V →₀ A) v = if h : v ∈ j.orbit then z ⟨v,h⟩ else 0 := by
  classical
  by_cases h : v ∈ j.orbit
  · rw [dite_eq_left h]
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective z ⟨v,h⟩
  · rw [dite_eq_right h]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x,rfl⟩
    exact h x.property

lemma projection_inclusion : orbitInclusion A j ≫ orbitProjection A j = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  apply Finsupp.ext
  intro v
  change (orbitInclusion A j z : V →₀ A) v.val = (z : j.orbit →₀ A) v
  exact (inclusion_apply A j (z : j.orbit →₀ A) v.val).trans (dite_eq_left v.property)

lemma sum_projections [Fintype (Orbits (G := G) V)] :
    ∑ j : Orbits (G := G) V, orbitProjection A j ≫ orbitInclusion A j = 𝟙 _ := by
  classical
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  apply Finsupp.ext
  intro v
  simp only [Rep.sum_hom,Representation.IntertwiningMap.toLinearMap_sum,LinearMap.sum_apply]
  change (∑ j : Orbits (G := G) V, (orbitInclusion A j (orbitProjection A j z) : V →₀ A)) v = (z : V →₀ A) v
  refine (map_sum (Finsupp.lapply v : (V →₀ A) →ₗ[k] A)
    (fun j : Orbits (G := G) V => (orbitInclusion A j (orbitProjection A j z) : V →₀ A))
    Finset.univ).trans ?_
  let a : A := (z : V →₀ A) v
  change (∑ j, (orbitInclusion A j (orbitProjection A j z) : V →₀ A) v) = a
  trans ∑ j : Orbits (G := G) V, if v ∈ j.orbit then a else 0
  · apply Finset.sum_congr rfl
    intro j _
    refine (inclusion_apply A j (orbitProjection A j z) v).trans ?_
    by_cases hv : v ∈ j.orbit
    · simp only [dite_eq_left hv,ite_eq_left hv]
      exact projection_apply A j z ⟨v,hv⟩
    · simp only [dite_eq_right hv,ite_eq_right hv]
  have hm (j : Orbits (G := G) V) : v ∈ j.orbit ↔ (Quotient.mk'' v : Orbits (G := G) V) = j :=
    MulAction.orbitRel.Quotient.mem_orbit
  simp_rw [hm]
  simp

lemma orbitCoset_equivariant (g : G) (q : G ⧸ MulAction.stabilizer G j.out) :
    ((MulAction.orbitEquivQuotientStabilizer G j.out).symm (g • q)).val =
      g • ((MulAction.orbitEquivQuotientStabilizer G j.out).symm q).val :=
  MulAction.ofQuotientStabilizer_smul G j.out g q

def orbitCosetIso : CosetInduction.cosetRep (MulAction.stabilizer G j.out) A ≅
    FunctionalTree.diagonalRep (V := j.orbit) A := by
  let e0 := (MulAction.orbitEquivQuotientStabilizer G j.out).symm
  let e1 : MulAction.orbit G j.out ≃ j.orbit :=
    Set.equivOfEq (MulAction.orbitRel.Quotient.orbit_eq_orbit_out j Quotient.out_eq').symm
  exact diagonalIso A (e0.trans e1) (fun g q => Subtype.ext (orbitCoset_equivariant j g q))

theorem orbit_homology_zero (n : ℕ)
    (hz : IsZero (groupHomology (Rep.res (MulAction.stabilizer G j.out).subtype A) n)) :
    IsZero (groupHomology (FunctionalTree.diagonalRep (V := j.orbit) A) n) := by
  classical
  let S := MulAction.stabilizer G j.out
  let e := CosetInduction.indCosetIso S A ≪≫ orbitCosetIso A j
  exact hz.of_iso (((groupHomology.functor k G n).mapIso e).symm ≪≫ groupHomology.indIso S _ n)

theorem homology_zero [Finite (Orbits (G := G) V)] (n : ℕ)
    (hz : ∀ j : Orbits (G := G) V,
      IsZero (groupHomology (Rep.res (MulAction.stabilizer G j.out).subtype A) n)) :
    IsZero (groupHomology (FunctionalTree.diagonalRep (V := V) A) n) := by
  classical
  let := Fintype.ofFinite (Orbits (G := G) V)
  let F := groupHomology.functor k G n
  apply (IsZero.iff_id_eq_zero _).mpr
  have he := congrArg F.map (sum_projections (V := V) A)
  rw [Functor.map_sum,CategoryTheory.Functor.map_id] at he
  change 𝟙 (F.obj (FunctionalTree.diagonalRep (V := V) A)) = 0
  rw [← he]
  apply Finset.sum_eq_zero
  intro j _
  rw [CategoryTheory.Functor.map_comp]
  have hj : IsZero (F.obj (FunctionalTree.diagonalRep (V := j.orbit) A)) :=
    orbit_homology_zero A j n (hz j)
  exact (congrArg
    (fun f : F.obj (FunctionalTree.diagonalRep (V := V) A) ⟶
      F.obj (FunctionalTree.diagonalRep (V := j.orbit) A) => f ≫ F.map (orbitInclusion A j))
    (hj.eq_of_tgt (F.map (orbitProjection A j)) 0)).trans zero_comp
end OrbitCoefficients

end

end OAI
