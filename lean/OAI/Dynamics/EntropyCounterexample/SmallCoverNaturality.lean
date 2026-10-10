import OAI.Geometry.SingularHomology.SmallCoverMayerVietoris
import OAI.Geometry.SingularHomology.SingularCoverNaturality

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.SmallCoverMayerVietoris

open SingularSmallChains SingularCover

section SimplicialTransport

variable {K L : SSet}

theorem eqToHom_subcomplex_inclusion {A B : K.Subcomplex} (h : A = B) :
    eqToHom (congrArg SSet.Subcomplex.toSSet h) ≫ B.ι = A.ι := by
  subst B
  simp

theorem restrictedMap_eqToHom (f : K ⟶ L)
    {A B : K.Subcomplex} {A' B' : L.Subcomplex} (h : A = B) (h' : A' = B')
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    eqToHom (congrArg SSet.Subcomplex.toSSet h) ≫ restrictedMap f B B' hB =
      restrictedMap f A A' hA ≫ eqToHom (congrArg SSet.Subcomplex.toSSet h') := by
  subst B
  subst B'
  simp

end SimplicialTransport

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

abbrev singularMap (f : X → Y) (hf : Continuous f) : singularSet X ⟶ singularSet Y :=
  TopCat.toSSet.map (TopCat.ofHom (continuousMapOf f hf))

theorem inSubset_le_preimage (f : X → Y) (hf : Continuous f)
    (s : Set X) (t : Set Y) (h : Set.MapsTo f s t) :
    inSubset s ≤ (inSubset t).preimage (singularMap f hf) := by
  intro n σ hσ p
  exact h (hσ p)

theorem binary_le_preimage (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    small (binaryCover U V) ≤ (small (binaryCover U' V')).preimage (singularMap f hf) := by
  rw [small_binaryCover, small_binaryCover]
  exact preserves_union (singularMap f hf)
    (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)

def binaryMap (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    (small (binaryCover U V) : SSet) ⟶ small (binaryCover U' V') :=
  restrictedMap (singularMap f hf) _ _ (binary_le_preimage f hf U V U' V' hU hV)

@[reassoc] theorem binaryMap_inclusion (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    binaryMap f hf U V U' V' hU hV ≫ (small (binaryCover U' V')).ι =
      (small (binaryCover U V)).ι ≫ singularMap f hf := rfl

@[reassoc] theorem binaryHomologyMap_inclusion (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) n ≫
        HomologicalComplex.homologyMap (inclusion (binaryCover U' V')) n =
      HomologicalComplex.homologyMap (inclusion (binaryCover U V)) n ≫
        ModuleCat.ofHom (realHomologyMap n f hf) := by
  change SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) n ≫
      SSet.homologyMap (small (binaryCover U' V')).ι (ModuleCat.of ℝ ℝ) n =
    SSet.homologyMap (small (binaryCover U V)).ι (ModuleCat.of ℝ ℝ) n ≫
      SSet.homologyMap (singularMap f hf) (ModuleCat.of ℝ ℝ) n
  rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp, binaryMap_inclusion]

@[reassoc] theorem smallUnionHomologyIso_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    (smallUnionHomologyIso U V n).hom ≫
        SSet.homologyMap (restrictedMap (singularMap f hf)
          (inSubset U ⊔ inSubset V) (inSubset U' ⊔ inSubset V')
          (preserves_union (singularMap f hf)
            (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
          (ModuleCat.of ℝ ℝ) n =
      SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) n ≫
        (smallUnionHomologyIso U' V' n).hom := by
  have h := (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).congr_map
    (restrictedMap_eqToHom (singularMap f hf) (small_binaryCover U V)
      (small_binaryCover U' V') (binary_le_preimage f hf U V U' V' hU hV)
      (preserves_union (singularMap f hf)
        (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
  dsimp only [SSet.homologyFunctor] at h
  simpa only [Functor.map_comp, SSet.homologyFunctor_map, SSet.homologyFunctor_obj,
    SSet.homologyMap_comp, smallUnionHomologyIso, Functor.mapIso_hom, eqToIso.hom,
    binaryMap] using h

def intersectionMap (f : X → Y) (hf : Continuous f)
    (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') : C(↥(U ∩ V), ↥(U' ∩ V')) :=
  restrictMap f hf (U ∩ V) (U' ∩ V') (fun _ hx => ⟨hU hx.1, hV hx.2⟩)

theorem restrictedMap_inSubset (f : X → Y) (hf : Continuous f)
    (s : Set X) (t : Set Y) (h : Set.MapsTo f s t) :
    restrictedMap (singularMap f hf) (inSubset s) (inSubset t)
        (inSubset_le_preimage f hf s t h) = mapInSubset f hf s t h := rfl

@[reassoc] theorem subspaceHomologyIso_naturality
    (f : X → Y) (hf : Continuous f) (s : Set X) (t : Set Y)
    (h : Set.MapsTo f s t) (n : ℕ) :
    ModuleCat.ofHom (realHomologyMap n (restrictMap f hf s t h)
        (restrictMap f hf s t h).continuous) ≫ (subspaceHomologyIso t n).hom =
      (subspaceHomologyIso s n).hom ≫
        SSet.homologyMap (mapInSubset f hf s t h) (ModuleCat.of ℝ ℝ) n := by
  apply ModuleCat.hom_ext
  ext v
  exact subspaceHomologyIso_naturality_apply f hf s t h n v

@[reassoc] theorem intersectionHomologyIso_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    ModuleCat.ofHom (realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
        (intersectionMap f hf U V U' V' hU hV).continuous) ≫
        (intersectionHomologyIso U' V' n).hom =
      (intersectionHomologyIso U V n).hom ≫
        SSet.homologyMap (restrictedMap (singularMap f hf)
          (inSubset U ⊓ inSubset V) (inSubset U' ⊓ inSubset V')
          (preserves_inter (singularMap f hf)
            (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
          (ModuleCat.of ℝ ℝ) n := by
  let hI : Set.MapsTo f (U ∩ V) (U' ∩ V') := fun _ hx => ⟨hU hx.1, hV hx.2⟩
  have heq := (SSet.homologyFunctor (ModuleCat.of ℝ ℝ) n).congr_map
    (restrictedMap_eqToHom (singularMap f hf) (inSubset_inter U V)
      (inSubset_inter U' V') (inSubset_le_preimage f hf (U ∩ V) (U' ∩ V') hI)
      (preserves_inter (singularMap f hf)
        (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
  dsimp only [SSet.homologyFunctor] at heq
  simp only [SSet.homologyMap_comp] at heq
  change ModuleCat.ofHom (realHomologyMap n (restrictMap f hf (U ∩ V) (U' ∩ V') hI)
      (restrictMap f hf (U ∩ V) (U' ∩ V') hI).continuous) ≫
      ((subspaceHomologyIso (U' ∩ V') n).hom ≫
        SSet.homologyMap (eqToHom (congrArg SSet.Subcomplex.toSSet
          (inSubset_inter U' V'))) (ModuleCat.of ℝ ℝ) n) =
    ((subspaceHomologyIso (U ∩ V) n).hom ≫
      SSet.homologyMap (eqToHom (congrArg SSet.Subcomplex.toSSet
        (inSubset_inter U V))) (ModuleCat.of ℝ ℝ) n) ≫
      SSet.homologyMap (restrictedMap (singularMap f hf)
        (inSubset U ⊓ inSubset V) (inSubset U' ⊓ inSubset V')
        (preserves_inter (singularMap f hf)
          (inSubset_le_preimage f hf U U' hU) (inSubset_le_preimage f hf V V' hV)))
        (ModuleCat.of ℝ ℝ) n
  rw [← Category.assoc, subspaceHomologyIso_naturality f hf (U ∩ V) (U' ∩ V') hI n]
  rw [Category.assoc, ← restrictedMap_inSubset f hf (U ∩ V) (U' ∩ V') hI,
    ← heq, ← Category.assoc]

theorem transport_connecting_naturality {C : Type*} [Category C]
    {A A' B B' D D' E E' : C}
    (u : D ≅ A) (u' : D' ≅ A') (i : E ≅ B) (i' : E' ≅ B')
    (δ : A ⟶ B) (δ' : A' ⟶ B')
    (mA : A ⟶ A') (mB : B ⟶ B') (mD : D ⟶ D') (mE : E ⟶ E')
    (hu : u.hom ≫ mA = mD ≫ u'.hom)
    (hδ : δ ≫ mB = mA ≫ δ') (hi : mE ≫ i'.hom = i.hom ≫ mB) :
    mD ≫ (u'.hom ≫ δ' ≫ i'.inv) = (u.hom ≫ δ ≫ i.inv) ≫ mE := by
  apply (cancel_mono i'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hi]
  simp only [Iso.inv_hom_id_assoc]
  rw [hδ, ← Category.assoc, ← hu, Category.assoc]

@[reassoc] theorem connecting_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) :
    SSet.homologyMap (binaryMap f hf U V U' V' hU hV) (ModuleCat.of ℝ ℝ) (n + 1) ≫
        connecting U' V' n =
      connecting U V n ≫
        ModuleCat.ofHom (realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
          (intersectionMap f hf U V U' V' hU hV).continuous) := by
  let hA := inSubset_le_preimage f hf U U' hU
  let hB := inSubset_le_preimage f hf V V' hV
  let mI := SSet.homologyMap (restrictedMap (singularMap f hf)
    (inSubset U ⊓ inSubset V) (inSubset U' ⊓ inSubset V')
    (preserves_inter (singularMap f hf) hA hB)) (ModuleCat.of ℝ ℝ) n
  let mU := SSet.homologyMap (restrictedMap (singularMap f hf)
    (inSubset U ⊔ inSubset V) (inSubset U' ⊔ inSubset V')
    (preserves_union (singularMap f hf) hA hB)) (ModuleCat.of ℝ ℝ) (n + 1)
  have hδ : SimplicialMayerVietoris.connecting (inSubset U) (inSubset V) n ≫ mI =
      mU ≫ SimplicialMayerVietoris.connecting (inSubset U') (inSubset V') n :=
    union_connecting_naturality (singularMap f hf) hA hB n
  exact transport_connecting_naturality
    (smallUnionHomologyIso U V (n + 1)) (smallUnionHomologyIso U' V' (n + 1))
    (intersectionHomologyIso U V n) (intersectionHomologyIso U' V' n)
    (SimplicialMayerVietoris.connecting (inSubset U) (inSubset V) n)
    (SimplicialMayerVietoris.connecting (inSubset U') (inSubset V') n)
    mU mI _ _
    (smallUnionHomologyIso_naturality f hf U V U' V' hU hV (n + 1)) hδ
    (intersectionHomologyIso_naturality f hf U V U' V' hU hV n)

theorem descend_connecting_naturality {C : Type*} [Category C]
    {A A' B B' D D' : C}
    (s : D ⟶ A) [Epi s] (s' : D' ⟶ A')
    (δ : A ⟶ B) (δ' : A' ⟶ B') (d : D ⟶ B) (d' : D' ⟶ B')
    (f : A ⟶ A') (g : D ⟶ D') (h : B ⟶ B')
    (hs : s ≫ f = g ≫ s') (hd : s ≫ δ = d) (hd' : s' ≫ δ' = d')
    (hn : g ≫ d' = d ≫ h) : f ≫ δ' = δ ≫ h := by
  apply (cancel_epi s).1
  rw [← Category.assoc, hs, Category.assoc, hd', hn, ← hd, Category.assoc]

@[reassoc] theorem singularConnectingIsoOfQuasiIsoAt_naturality
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    [ContractibleSpace U] [ContractibleSpace V]
    [ContractibleSpace U'] [ContractibleSpace V']
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)]
    [QuasiIsoAt (inclusion (binaryCover U' V')) (n + 1)] :
    ModuleCat.ofHom (realHomologyMap (n + 1) f hf) ≫
        (singularConnectingIsoOfQuasiIsoAt U' V' n hn).hom =
      (singularConnectingIsoOfQuasiIsoAt U V n hn).hom ≫
        ModuleCat.ofHom (realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
          (intersectionMap f hf U V U' V' hU hV).continuous) := by
  exact descend_connecting_naturality
    (HomologicalComplex.homologyMap (inclusion (binaryCover U V)) (n + 1))
    (HomologicalComplex.homologyMap (inclusion (binaryCover U' V')) (n + 1))
    (singularConnectingIsoOfQuasiIsoAt U V n hn).hom
    (singularConnectingIsoOfQuasiIsoAt U' V' n hn).hom
    (connecting U V n) (connecting U' V' n) _ _ _
    (binaryHomologyMap_inclusion f hf U V U' V' hU hV (n + 1)).symm
    (inclusion_singularConnectingIsoOfQuasiIsoAt U V n hn)
    (inclusion_singularConnectingIsoOfQuasiIsoAt U' V' n hn)
    (connecting_naturality f hf U V U' V' hU hV n)

theorem singularConnectingIsoOfQuasiIsoAt_naturality_apply
    (f : X → Y) (hf : Continuous f) (U V : Set X) (U' V' : Set Y)
    [ContractibleSpace U] [ContractibleSpace V]
    [ContractibleSpace U'] [ContractibleSpace V']
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') (n : ℕ) (hn : n ≠ 0)
    [QuasiIsoAt (inclusion (binaryCover U V)) (n + 1)]
    [QuasiIsoAt (inclusion (binaryCover U' V')) (n + 1)]
    (v : RealSingularHomology (n + 1) X) :
    (singularConnectingIsoOfQuasiIsoAt U' V' n hn).hom (realHomologyMap (n + 1) f hf v) =
      realHomologyMap n (intersectionMap f hf U V U' V' hU hV)
        (intersectionMap f hf U V U' V' hU hV).continuous
        ((singularConnectingIsoOfQuasiIsoAt U V n hn).hom v) := by
  exact congrArg (fun k : RealSingularHomology (n + 1) X ⟶
      RealSingularHomology n ↥(U' ∩ V') => k v)
    (singularConnectingIsoOfQuasiIsoAt_naturality f hf U V U' V' hU hV n hn)

end Problem340.SmallCoverMayerVietoris

end

end OAI
