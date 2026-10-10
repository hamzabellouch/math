import Mathlib
import OAI.GroupTheory.PeriodicGroups.Homology.FiniteExtensions

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def quotientResolution (hN : LocallyFinite N) :
    ProjectiveResolution (Rep.trivial ℚ (G ⧸ N) ℚ) := by
  letI := preservesHomology N hN
  let P := (functor N).mapProjectiveResolution (Rep.barResolution ℚ G)
  exact
    { complex := P.complex
      projective := P.projective
      π := P.π ≫ (ChainComplex.single₀ _).map (trivialIso N).hom
      quasiIso := inferInstance }

def homologyIso (hN : LocallyFinite N) (A : Rep ℚ (G ⧸ N)) (n : ℕ) :
    groupHomology (Rep.res (QuotientGroup.mk' N) A) n ≅ groupHomology A n :=
  groupHomologyIso _ n (Rep.barResolution ℚ G) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex (quotientProjection N A) _).app
        (Rep.barResolution ℚ G).complex) ≪≫
    (groupHomologyIso A n (quotientResolution N hN)).symm

end RelativeCoinvariants
end

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open scoped TensorProduct

namespace BarMap
variable {G H : Type} [Group G] [Group H] (q : G →* H)

def component (n : ℕ) : Rep.free ℚ G (Fin n → G) ⟶
    Rep.res q (Rep.free ℚ H (Fin n → H)) :=
  Rep.freeLift ℚ G _ fun x => single (q ∘ x) (.single 1 1)

lemma component_single (n : ℕ) (x : Fin n → G) (g : G) (r : ℚ) :
    (component q n).hom (single x (.single g r)) = single (q ∘ x) (.single (q g) r) := by
  change Representation.freeLift ((Representation.free ℚ H (Fin n → H)).comp q)
    (fun x : Fin n → G => single (q ∘ x) (.single 1 (1 : ℚ)))
    (single x (.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free ℚ H (Fin n → H) (q g) (single (q ∘ x) (.single 1 1)) = _
  simp only [Representation.free_single_single, mul_one, smul_single, MonoidAlgebra.smul_single, smul_eq_mul]
def chain : Rep.barComplex ℚ G ⟶
    ((Rep.resFunctor q).mapHomologicalComplex _).obj (Rep.barComplex ℚ H) where
  f n := component q n
  comm' i j h := by
    change j + 1 = i at h
    subst i
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d, Rep.barComplex.d_def, Rep.barComplex.d_def]
    change component q (j+1) ≫ Rep.resMap q (Rep.barComplex.d ℚ H j) =
      Rep.barComplex.d ℚ G j ≫ component q j
    apply Rep.free_ext
    intro x
    change (Rep.barComplex.d ℚ H j).hom ((component q (j+1)).hom (single x (.single 1 1))) =
      (component q j).hom ((Rep.barComplex.d ℚ G j).hom (single x (.single 1 1)))
    simp only [← Representation.IntertwiningMap.toLinearMap_apply]
    have c (n : ℕ) (y : Fin n → G) (g : G) (r : ℚ) :
        (component q n).hom.toLinearMap (single y (.single g r)) =
          single (q ∘ y) (.single (q g) r) := component_single q n y g r
    have dG := Rep.barComplex.d_single (k := ℚ) j x
    have dH := Rep.barComplex.d_single (k := ℚ) j (q ∘ x)
    change (Rep.barComplex.d ℚ G j).hom.toLinearMap _ = _ at dG
    change (Rep.barComplex.d ℚ H j).hom.toLinearMap _ = _ at dH
    rw [c, map_one, dH, dG]
    simp only [map_add, map_sum, c, map_one]

    congr 1
    apply Finset.sum_congr rfl
    intro t _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b => map_mul q a b) t x).symm
lemma diagonal_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : ℚ) :
    (Rep.diagonalSuccIsoFree ℚ G m).inv.hom (single f (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  open MonoidalCategory in
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (leftRegularTensorTrivialIsoFree ℚ G (Fin m → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[ℚ] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [Action.tensorObj_V, tensor_V, tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := ℚ)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : ℚ) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℚ)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      congr 1
      exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g f)
lemma augmentation_single (x : Fin 0 → G) (g : G) (r : ℚ) :
    ((Rep.barResolution ℚ G).π.f 0).hom (single x (.single g r)) = r := by
  change (Rep.standardComplex.ε ℚ G).hom
    ((Rep.diagonalSuccIsoFree ℚ G 0).inv.hom (single x (.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

end BarMap
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open scoped TensorProduct
open MonoidalCategory

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

lemma inductionIso_one (B : Rep ℚ G) (b : B) :
    ((inductionIso N).hom.app B).hom (IndV.mk (QuotientGroup.mk' N) B.ρ 1 b) =
      Coinvariants.mk _ b := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (Rep.indResAdjunction ℚ (QuotientGroup.mk' N)) (adjunction N) B
  exact congrArg (fun f => f.hom b) h

lemma tensorSymmetry_mk {H : Type} [Group H] (A B : Rep ℚ H) (a : A) (b : B) :
    ((tensorSymmetry A).hom.app B) (coinvariantsTensorMk A B a b) =
      coinvariantsTensorMk B A b a := rfl

lemma tensorSymmetry_inv_mk {H : Type} [Group H] (A B : Rep ℚ H) (a : A) (b : B) :
    ((tensorSymmetry A).inv.app B) (coinvariantsTensorMk B A b a) =
      coinvariantsTensorMk A B a b := rfl

lemma tensor_map_mk {H : Type} [Group H] (A : Rep ℚ H) {B C : Rep ℚ H}
    (f : B ⟶ C) (a : A) (b : B) :
    (((coinvariantsTensor ℚ H).obj A).map f) (coinvariantsTensorMk A B a b) =
      coinvariantsTensorMk A C a (f.hom b) := rfl

lemma quotientProjection_mk (A : Rep ℚ (G ⧸ N)) (B : Rep ℚ G) (a : A) (b : B) :
    ((quotientProjection N A).hom.app B)
      (coinvariantsTensorMk (Rep.res (QuotientGroup.mk' N) A) B a b) =
      coinvariantsTensorMk A ((functor N).obj B) a (Coinvariants.mk _ b) := by
  change (((coinvariantsTensor ℚ (G ⧸ N)).obj A).map ((inductionIso N).hom.app B))
    (((tensorSymmetry A).inv.app (Rep.ind (QuotientGroup.mk' N) B))
      ((coinvariantsTensorIndInv (QuotientGroup.mk' N) B A)
        (((tensorSymmetry (Rep.res (QuotientGroup.mk' N) A)).hom.app B)
          (coinvariantsTensorMk (Rep.res (QuotientGroup.mk' N) A) B a b)))) = _
  rw [tensorSymmetry_mk]
  have h : coinvariantsTensorIndInv (QuotientGroup.mk' N) B A
      (coinvariantsTensorMk B (Rep.res (QuotientGroup.mk' N) A) b a) =
      coinvariantsTensorMk (Rep.ind (QuotientGroup.mk' N) B) A
        (IndV.mk (QuotientGroup.mk' N) B.ρ 1 b) a :=
    coinvariantsTensorIndInv_mk_tmul_indMk (QuotientGroup.mk' N) b a
  rw [h,tensorSymmetry_inv_mk]
  exact (tensor_map_mk A ((inductionIso N).hom.app B) a
    (IndV.mk (QuotientGroup.mk' N) B.ρ 1 b)).trans
    (congrArg (coinvariantsTensorMk A ((functor N).obj B) a) (inductionIso_one N B b))

def barComparisonComponent (n : ℕ) :
    (functor N).obj ((Rep.barComplex ℚ G).X n) ⟶ (Rep.barComplex ℚ (G ⧸ N)).X n :=
  (functor N).map ((BarMap.chain (QuotientGroup.mk' N)).f n) ≫
    counit N ((Rep.barComplex ℚ (G ⧸ N)).X n)

@[simp] lemma barComparisonComponent_mk (n : ℕ) (x : (Rep.barComplex ℚ G).X n) :
    (barComparisonComponent N n).hom (Coinvariants.mk _ x) =
      (BarMap.component (QuotientGroup.mk' N) n).hom x := rfl
def barComparison :
    ((functor N).mapHomologicalComplex _).obj (Rep.barComplex ℚ G) ⟶
      Rep.barComplex ℚ (G ⧸ N) where
  f n := barComparisonComponent N n
  comm' i j h := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Coinvariants.induction_on with | h x =>
    exact congrArg (fun f => f.hom x) ((BarMap.chain (QuotientGroup.mk' N)).comm i j)

lemma barComparison_π (hN : LocallyFinite N) :
    (barComparison N).f 0 ≫ (Rep.barResolution ℚ (G ⧸ N)).π.f 0 =
      (quotientResolution N hN).π.f 0 ≫ 𝟙 _ := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  induction x using Coinvariants.induction_on with | h x =>
  change ((Rep.barResolution ℚ (G ⧸ N)).π.f 0).hom
      ((BarMap.component (QuotientGroup.mk' N) 0).hom x) =
    ((Rep.barResolution ℚ G).π.f 0).hom x
  have h : BarMap.component (QuotientGroup.mk' N) 0 ≫
      Rep.resMap (QuotientGroup.mk' N) ((Rep.barResolution ℚ (G ⧸ N)).π.f 0) =
      (Rep.barResolution ℚ G).π.f 0 := by
    apply Rep.free_ext
    intro y
    change ((Rep.barResolution ℚ (G ⧸ N)).π.f 0).hom
      ((BarMap.component (QuotientGroup.mk' N) 0).hom (single y (.single 1 1))) = _
    rw [BarMap.component_single, BarMap.augmentation_single]
    exact (BarMap.augmentation_single y 1 1).symm
  exact congrArg (fun f => f.hom x) h

lemma barComparison_homology_isIso (hN : LocallyFinite N)
    (A : Rep ℚ (G ⧸ N)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((Rep.coinvariantsTensor ℚ (G ⧸ N)).obj A).mapHomologicalComplex _ |>.map
        (barComparison N)) n) := by
  let P := quotientResolution N hN
  let Q := Rep.barResolution ℚ (G ⧸ N)
  let F := (Rep.coinvariantsTensor ℚ (G ⧸ N)).obj A
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _) P Q
    (barComparison N) (barComparison_π N hN) F n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have he : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex _).map (barComparison N)) n =
      (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom := by
    rw [h]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  rw [he]
  exact inferInstanceAs (IsIso ((P.isoLeftDerivedObj F n).symm ≪≫
    Q.isoLeftDerivedObj F n).hom)

lemma chainsIso_single {H : Type} [Group H] [DecidableEq H] (A : Rep ℚ H) (n : ℕ)
    (x : Fin n → H) (a : A) :
    ((groupHomology.inhomogeneousChainsIso A).hom.f n) (single x a) =
      coinvariantsTensorMk A ((Rep.barComplex ℚ H).X n) a (single x (.single 1 1)) :=
  Rep.finsuppToCoinvariantsTensorFree_single x a

def projectionChain (A : Rep ℚ (G ⧸ N)) :
    (Rep.barComplex ℚ G).coinvariantsTensorObj (Rep.res (QuotientGroup.mk' N) A) ≅
      (((functor N).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex ℚ G)).coinvariantsTensorObj A :=
  (NatIso.mapHomologicalComplex (quotientProjection N A) (ComplexShape.down ℕ)).app (Rep.barComplex ℚ G)

def comparisonTensor (A : Rep ℚ (G ⧸ N)) :
    (((functor N).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex ℚ G)).coinvariantsTensorObj A ⟶
      (Rep.barComplex ℚ (G ⧸ N)).coinvariantsTensorObj A :=
  (((coinvariantsTensor ℚ (G ⧸ N)).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map (barComparison N)

lemma barComparison_free (n : ℕ) (x : Fin n → G) :
    (barComparisonComponent N n).hom (Coinvariants.mk _ (single x (.single 1 1))) =
      single (QuotientGroup.mk' N ∘ x) (.single 1 1) := by
  rw [barComparisonComponent_mk]
  exact (BarMap.component_single (QuotientGroup.mk' N) n x 1 1).trans (by rw [map_one])

lemma tensor_comparison_free (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((comparisonTensor N A).f n)
      (coinvariantsTensorMk A ((functor N).obj ((Rep.barComplex ℚ G).X n)) a
        (Coinvariants.mk _ (single x (.single 1 1)))) =
      coinvariantsTensorMk A ((Rep.barComplex ℚ (G ⧸ N)).X n) a
        (single (QuotientGroup.mk' N ∘ x) (.single 1 1)) := by
  change (((coinvariantsTensor ℚ (G ⧸ N)).obj A).map (barComparisonComponent N n)) _ = _
  erw [tensor_map_mk,barComparison_free]

lemma projection_single (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((projectionChain N A).hom.f n)
      (((groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom.f n) (single x a)) =
      coinvariantsTensorMk A ((functor N).obj ((Rep.barComplex ℚ G).X n)) a
        (Coinvariants.mk _ (single x (.single 1 1))) := by
  change ((quotientProjection N A).hom.app ((Rep.barComplex ℚ G).X n)) _ = _
  rw [chainsIso_single,quotientProjection_mk]

lemma tensor_comparison_chains (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((comparisonTensor N A).f n)
      (coinvariantsTensorMk A ((functor N).obj ((Rep.barComplex ℚ G).X n)) a
        (Coinvariants.mk _ (single x (.single 1 1)))) =
    ((groupHomology.inhomogeneousChainsIso A).hom.f n) (single (QuotientGroup.mk' N ∘ x) a) := by
  exact (tensor_comparison_free N A n x a).trans
    (chainsIso_single A n (QuotientGroup.mk' N ∘ x) a).symm

lemma comparison_single (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((comparisonTensor N A).f n) (((projectionChain N A).hom.f n)
      (((groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom.f n)
        (single x a))) =
      ((groupHomology.inhomogeneousChainsIso A).hom.f n) (single (QuotientGroup.mk' N ∘ x) a) := by
  exact (congrArg (fun z => ((comparisonTensor N A).f n) z)
    (projection_single N A n x a)).trans (tensor_comparison_chains N A n x a)

lemma quotient_chain_compare (A : Rep ℚ (G ⧸ N)) :
    groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 (Rep.res (QuotientGroup.mk' N) A)) ≫
      (groupHomology.inhomogeneousChainsIso A).hom =
    (groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom ≫
      (projectionChain N A).hom ≫
      comparisonTensor N A := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change ((groupHomology.inhomogeneousChainsIso A).hom.f n)
      ((groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 _)).f n (single x a)) =
    ((comparisonTensor N A).f n) (((projectionChain N A).hom.f n)
      (((groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom.f n)
        (single x a)))
  exact (congrArg (fun z => ((groupHomology.inhomogeneousChainsIso A).hom.f n) z)
    (groupHomology.chainsMap_f_single (QuotientGroup.mk' N) (𝟙 _) n x a)).trans
      (comparison_single N A n x a).symm

lemma quotient_map_isIso (hN : LocallyFinite N) (A : Rep ℚ (G ⧸ N)) (n : ℕ) :
    IsIso (groupHomology.map (QuotientGroup.mk' N) (𝟙 (Rep.res (QuotientGroup.mk' N) A)) n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  have h := congrArg F.map (quotient_chain_compare N A)
  simp only [CategoryTheory.Functor.map_comp] at h
  have : IsIso (F.map (comparisonTensor N A)) := barComparison_homology_isIso N hN A n
  have he : groupHomology.map (QuotientGroup.mk' N) (𝟙 (Rep.res (QuotientGroup.mk' N) A)) n =
      F.map (groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom ≫
        F.map (projectionChain N A).hom ≫
        F.map (comparisonTensor N A) ≫
        F.map (groupHomology.inhomogeneousChainsIso A).inv := by
    change F.map (groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 _)) = _
    calc
      _ = (F.map (groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 _)) ≫
          F.map (groupHomology.inhomogeneousChainsIso A).hom) ≫
          F.map (groupHomology.inhomogeneousChainsIso A).inv := by simp [←Functor.map_comp]
      _ = _ := by rw [h]; simp only [Category.assoc]

  rw [he]
  exact IsIso.comp_isIso'
    (F.mapIso (groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A))).isIso_hom
    (IsIso.comp_isIso' (F.mapIso (projectionChain N A)).isIso_hom
      (IsIso.comp_isIso' (barComparison_homology_isIso N hN A n)
        (F.mapIso (groupHomology.inhomogeneousChainsIso A)).isIso_inv))

end RelativeCoinvariants
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory Representation Rep
namespace RelativeCoinvariants
variable {G H : Type} [Group G] [Group H]

lemma equiv_map_isIso (e : G ≃* H) (A : Rep ℚ H) (n : ℕ) :
    IsIso (groupHomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n) := by
  let i := groupHomology.mapIso (A := Rep.res e.toMonoidHom A) (B := A) e
    (LinearEquiv.refl ℚ A) (fun g => by simp) n
  have he : groupHomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n = i.hom := by
    apply groupHomology.map_congr rfl
    rfl
  rw [he]
  infer_instance

lemma surjective_map_isIso (f : G →* H) (hf : Function.Surjective f)
    (hK : LocallyFinite f.ker) (A : Rep ℚ H) (n : ℕ) :
    IsIso (groupHomology.map f (𝟙 (Rep.res f A)) n) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let q := QuotientGroup.mk' f.ker
  have he : e.toMonoidHom.comp q = f := rfl
  have := quotient_map_isIso f.ker hK (Rep.res e.toMonoidHom A) n
  have := equiv_map_isIso e A n
  have h : groupHomology.map f (𝟙 (Rep.res f A)) n =
      groupHomology.map q (𝟙 (Rep.res q (Rep.res e.toMonoidHom A))) n ≫
        groupHomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n := by
    rw [←groupHomology.map_comp]
    apply groupHomology.map_congr he.symm
    rfl
  rw [h]
  exact IsIso.comp_isIso' (quotient_map_isIso f.ker hK (Rep.res e.toMonoidHom A) n)
    (equiv_map_isIso e A n)

end RelativeCoinvariants
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalHomology
noncomputable section
open CategoryTheory
variable {G H K : Type} [Group G] [Group H] [Group K]

abbrev map (f : G →* H) (n : ℕ) :
    groupHomology (Rep.trivial ℚ G ℚ) n ⟶ groupHomology (Rep.trivial ℚ H ℚ) n :=
  groupHomology.map (A := Rep.trivial ℚ G ℚ) (B := Rep.trivial ℚ H ℚ) f (𝟙 _) n

@[simp] lemma map_id (n : ℕ) : map (MonoidHom.id G) n = 𝟙 _ := groupHomology.map_id (A := Rep.trivial ℚ G ℚ) n

lemma map_comp (f : G →* H) (g : H →* K) (n : ℕ) :
    map (g.comp f) n = map f n ≫ map g n :=
  groupHomology.map_comp (A := Rep.trivial ℚ G ℚ) (B := Rep.trivial ℚ H ℚ) (C := Rep.trivial ℚ K ℚ)
    f g (𝟙 _) (𝟙 _) n

lemma equiv_isIso (e : G ≃* H) (n : ℕ) : IsIso (map e.toMonoidHom n) :=
  RelativeCoinvariants.equiv_map_isIso e (Rep.trivial ℚ H ℚ) n

lemma surjective_isIso (f : G →* H) (hf : Function.Surjective f)
    (hK : LocallyFinite f.ker) (n : ℕ) : IsIso (map f n) :=
  RelativeCoinvariants.surjective_map_isIso f hf hK (Rep.trivial ℚ H ℚ) n

end
end SourceBurnside.Stability.RationalHomology

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory
namespace VectorFactor
variable {U V W : Type} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

lemma exists_factor (f : U →ₗ[ℚ] V) (g : U →ₗ[ℚ] W) (h : f.ker ≤ g.ker) :
    ∃t : V →ₗ[ℚ] W, t.comp f = g := by
  let a : f.range →ₗ[ℚ] W := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨t,ht⟩ := a.exists_extend
  refine ⟨t,?_⟩
  ext u
  have he := LinearMap.congr_fun ht (f.rangeRestrict u)
  change t (f u) = _ at he
  change t (f u) = g u
  rw [he]
  change (f.ker.liftQ g h) (f.quotKerEquivRange.symm (f.rangeRestrict u)) = g u
  have hq : f.rangeRestrict u = f.quotKerEquivRange (Submodule.Quotient.mk u) := rfl
  rw [hq,LinearEquiv.symm_apply_apply]
  rfl
end VectorFactor
namespace RationalBar
variable (G : Type) [Group G]
abbrev T := Rep.trivial ℚ G ℚ
abbrev C1 := G →₀ ℚ
abbrev C2 := G × G →₀ ℚ
abbrev C3 := G × G × G →₀ ℚ
abbrev d2 : C2 G →ₗ[ℚ] C1 G := (groupHomology.d₂₁ (T G)).hom
abbrev d3 : C3 G →ₗ[ℚ] C2 G := (groupHomology.d₃₂ (T G)).hom
abbrev Z2 := groupHomology.cycles₂ (T G)
abbrev B2 := groupHomology.boundaries₂ (T G)
abbrev H2 := groupHomology (T G) 2
abbrev π : Z2 G →ₗ[ℚ] H2 G := (groupHomology.H2π (T G)).hom

def Cocycles : Submodule ℚ (C2 G →ₗ[ℚ] ℚ) :=
  LinearMap.ker (LinearMap.lcomp ℚ ℚ (d3 G))

variable {G}
lemma cocycle_iff (c : C2 G →ₗ[ℚ] ℚ) : c ∈ Cocycles G ↔ c.comp (d3 G)=0 := Iff.rfl
lemma cocycle_vanish (c : Cocycles G) (z : B2 G) : c.val z.val=0 := by
  obtain ⟨w,hw⟩ := z.property
  have h := LinearMap.congr_fun c.property w
  change c.val (d3 G w)=0 at h
  simpa only [hw] using h

lemma exists_evaluation (c : Cocycles G) :
    ∃e : H2 G →ₗ[ℚ] ℚ, e.comp (π G) = c.val.comp (Z2 G).subtype := by
  apply VectorFactor.exists_factor
  intro z hz
  have hb := (groupHomology.H2π_eq_zero_iff z).mp hz
  exact cocycle_vanish c ⟨z.val,hb⟩

def evaluation (c : Cocycles G) : H2 G →ₗ[ℚ] ℚ := (exists_evaluation c).choose
lemma evaluation_cycle (c : Cocycles G) (z : Z2 G) : evaluation c (π G z) = c.val z.val :=
  LinearMap.congr_fun (exists_evaluation c).choose_spec z

lemma cocycle_of_cycle_restriction (e : H2 G →ₗ[ℚ] ℚ) (c : C2 G →ₗ[ℚ] ℚ)
    (hc : c.comp (Z2 G).subtype = e.comp (π G)) : c ∈ Cocycles G := by
  rw [cocycle_iff]
  apply LinearMap.ext
  intro w
  let z : Z2 G := ⟨d3 G w,groupHomology.d₃₂_apply_mem_cycles₂ (A := T G) w⟩
  have hz : π G z=0 := (groupHomology.H2π_eq_zero_iff z).mpr ⟨w,rfl⟩
  have h := LinearMap.congr_fun hc z
  change c (d3 G w)=e (π G z) at h
  change c (d3 G w)=0
  simpa only [hz,map_zero] using h

lemma evaluation_surjective : Function.Surjective (evaluation (G := G)) := by
  intro e
  obtain ⟨c,hc⟩ := (e.comp (π G)).exists_extend
  refine ⟨⟨c,cocycle_of_cycle_restriction e c hc⟩,?_⟩
  apply LinearMap.ext
  intro h
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance h
  exact (evaluation_cycle _ z).trans (LinearMap.congr_fun hc z)

lemma evaluation_zero_iff (c : Cocycles G) : evaluation c=0 ↔
    ∃b : C1 G →ₗ[ℚ] ℚ, c.val=b.comp (d2 G) := by
  constructor
  · intro he
    obtain ⟨b,hb⟩ := VectorFactor.exists_factor (d2 G) c.val (by
      intro z hz
      have h := evaluation_cycle c ⟨z,hz⟩
      rw [he] at h
      exact h.symm)
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,hb⟩
    apply LinearMap.ext
    intro h
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance h
    rw [evaluation_cycle,hb]
    change b (d2 G z.val)=0
    rw [z.property,map_zero]

end RationalBar
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalBar
noncomputable section
open Classical CategoryTheory
variable {G H K : Type} [Group G] [Group H] [Group K]

lemma evaluation_ext (c d : Cocycles G) (h : ∀z : Z2 G,c.val z.val=d.val z.val) :
    evaluation c=evaluation d := by
  ext x
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
  rw [evaluation_cycle,evaluation_cycle,h]

def evaluationMap : Cocycles G →ₗ[ℚ] (H2 G →ₗ[ℚ] ℚ) where
  toFun := evaluation
  map_add' c d := by
    ext x
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
    change evaluation (c+d) (π G z)=evaluation c (π G z)+evaluation d (π G z)
    rw [evaluation_cycle,evaluation_cycle,evaluation_cycle]
    rfl
  map_smul' a c := by
    ext x
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
    change evaluation (a • c) (π G z)=a • evaluation c (π G z)
    rw [evaluation_cycle,evaluation_cycle]
    rfl

abbrev map2 (f : G →* H) : C2 G →ₗ[ℚ] C2 H :=
  (groupHomology.chainsMap₂ (A := T G) (B := T H) f (𝟙 (T G))).hom
abbrev map3 (f : G →* H) : C3 G →ₗ[ℚ] C3 H :=
  (groupHomology.chainsMap₃ (A := T G) (B := T H) f (𝟙 (T G))).hom

lemma map2_d3 (f : G →* H) : (map2 f).comp (d3 G) = (d3 H).comp (map3 f) := by
  exact (congrArg ModuleCat.Hom.hom (groupHomology.mapShortComplexH2 (A := T G) (B := T H) f (𝟙 (T G))).comm₁₂).symm

def pull (f : G →* H) : Cocycles H →ₗ[ℚ] Cocycles G where
  toFun c := ⟨c.val.comp (map2 f),by
    have hc : c.val.comp (d3 H)=0 := c.property
    rw [cocycle_iff,LinearMap.comp_assoc,map2_d3,←LinearMap.comp_assoc,hc]
    rfl⟩
  map_add' c d := by ext z; rfl
  map_smul' a c := by ext z; rfl

lemma evaluation_natural (f : G →* H) (c : Cocycles H) :
    evaluation (pull f c) = (evaluation c).comp (RationalHomology.map f 2).hom := by
  ext x
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
  rw [evaluation_cycle]
  have he := congrArg (fun u : ModuleCat.of ℚ (Z2 G) ⟶ H2 H => u z)
    (groupHomology.H2π_comp_map (A := T G) (B := T H) f (𝟙 (T G)))
  change RationalHomology.map f 2 (π G z) = π H (groupHomology.mapCycles₂ (B := T H) f (𝟙 (T G)) z) at he
  change c.val (map2 f z.val) = evaluation c (RationalHomology.map f 2 (π G z))
  rw [he,evaluation_cycle]
  rfl

lemma extend (f : G →* H) [IsIso (RationalHomology.map f 2)] (c : Cocycles G) :
    ∃d : Cocycles H, ∃b : C1 G →ₗ[ℚ] ℚ,
      c.val - (pull f d).val = b.comp (d2 G) := by
  let e : H2 H →ₗ[ℚ] ℚ := (evaluation c).comp (inv (RationalHomology.map f 2)).hom
  obtain ⟨d,hd⟩ := evaluation_surjective (G := H) e
  have hd' : evaluation (pull f d)=evaluation c := by
    rw [evaluation_natural,hd]
    ext x
    change evaluation c ((inv (RationalHomology.map f 2)) ((RationalHomology.map f 2) x)) = evaluation c x
    have he := congrArg (fun t : H2 G ⟶ H2 G => t x) (IsIso.hom_inv_id (RationalHomology.map f 2))
    change (inv (RationalHomology.map f 2)) ((RationalHomology.map f 2) x)=x at he
    rw [he]
  have hz : evaluation (c-pull f d)=0 := by
    change evaluationMap (c-pull f d)=0
    rw [map_sub]
    change evaluation c-evaluation (pull f d)=0
    rw [hd',sub_self]
  obtain ⟨b,hb⟩ := (evaluation_zero_iff _).mp hz
  exact ⟨d,b,hb⟩

lemma pull_coboundary_iff (f : G →* H) [IsIso (RationalHomology.map f 2)] (c : Cocycles H) :
    (∃b : C1 G →ₗ[ℚ] ℚ, (pull f c).val=b.comp (d2 G)) ↔
    (∃b : C1 H →ₗ[ℚ] ℚ, c.val=b.comp (d2 H)) := by
  rw [←evaluation_zero_iff,←evaluation_zero_iff,evaluation_natural]
  constructor
  · intro h
    ext x
    obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective (RationalHomology.map f 2)).mp inferInstance x
    exact LinearMap.congr_fun h y
  · intro h
    rw [h,LinearMap.zero_comp]

end

noncomputable section
open Classical CategoryTheory
variable {G H : Type} [Group G] [Group H]

def value (c : Cocycles G) (g h : G) : ℚ := c.val (Finsupp.single (g,h) 1)

lemma identity (c : Cocycles G) (g h k : G) :
    value c g h + value c (g*h) k = value c h k + value c g (h*k) := by
  have hc : c.val (d3 G (Finsupp.single (g,h,k) 1))=0 := LinearMap.congr_fun c.property _
  change c.val (groupHomology.d₃₂ (T G) (Finsupp.single (g,h,k) 1))=0 at hc
  rw [groupHomology.d₃₂_single] at hc
  change c.val (Finsupp.single (h,k) 1-Finsupp.single (g*h,k) 1+
    Finsupp.single (g,h*k) 1-Finsupp.single (g,h) 1)=0 at hc
  simp only [map_sub,map_add] at hc
  dsimp only [value]
  linarith

lemma value_one_left (c : Cocycles G) (g : G) : value c 1 g=value c 1 1 := by
  have h := identity c 1 1 g
  simp only [one_mul] at h
  linarith
lemma value_one_right (c : Cocycles G) (g : G) : value c g 1=value c 1 1 := by
  have h := identity c g 1 1
  simp only [mul_one] at h
  linarith
lemma value_inv (c : Cocycles G) (g : G) : value c g⁻¹ g=value c g g⁻¹ := by
  have h := identity c g g⁻¹ g
  simp only [mul_inv_cancel,inv_mul_cancel,value_one_left,value_one_right] at h
  linarith

def Extension (_c : Cocycles G) := ℚ × G

instance extensionGroup (c : Cocycles G) : Group (Extension c) where
  mul x y := (x.1+y.1+value c x.2 y.2,x.2*y.2)
  one := (-value c 1 1,1)
  inv x := (-value c 1 1-x.1-value c x.2 x.2⁻¹,x.2⁻¹)
  mul_assoc x y z := Prod.ext (by
    change x.1+y.1+value c x.2 y.2+z.1+value c (x.2*y.2) z.2 =
      x.1+(y.1+z.1+value c y.2 z.2)+value c x.2 (y.2*z.2)
    linarith [identity c x.2 y.2 z.2]) (mul_assoc _ _ _)
  one_mul x := Prod.ext (by
    change -value c 1 1+x.1+value c 1 x.2=x.1
    rw [value_one_left c x.2]; ring) (one_mul _)
  mul_one x := Prod.ext (by
    change x.1+-value c 1 1+value c x.2 1=x.1
    rw [value_one_right c x.2]; ring) (mul_one _)
  inv_mul_cancel x := Prod.ext (by
    change -value c 1 1-x.1-value c x.2 x.2⁻¹+x.1+value c x.2⁻¹ x.2=-value c 1 1
    rw [value_inv]; ring) (inv_mul_cancel _)

def inclusion (c : Cocycles G) : QGroup →* Extension c where
  toFun q := (q.toAdd-value c 1 1,1)
  map_one' := Prod.ext (by change 0-value c 1 1 = -value c 1 1; ring) rfl
  map_mul' q r := Prod.ext (by
    change q.toAdd+r.toAdd-value c 1 1 =
      (q.toAdd-value c 1 1)+(r.toAdd-value c 1 1)+value c 1 1
    ring) (one_mul 1).symm

def projection (c : Cocycles G) : Extension c →* G where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl

def extension (c : Cocycles G) : RationalExtension (Extension c) G where
  inl := inclusion c
  rightHom := projection c
  inl_injective := by
    intro q r h
    have he := congrArg Prod.fst h
    change q.toAdd-value c 1 1=r.toAdd-value c 1 1 at he
    change q.toAdd=r.toAdd
    linarith
  rightHom_surjective := fun g => ⟨(0,g),rfl⟩
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩; rfl
    · intro hx
      change x.2=1 at hx
      exact ⟨Multiplicative.ofAdd (x.1+value c 1 1),Prod.ext (by change x.1+value c 1 1-value c 1 1=x.1; ring) hx.symm⟩
  central := by
    rintro x ⟨q,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Prod.ext
    · change y.1+(q.toAdd-value c 1 1)+value c y.2 1 =
        q.toAdd-value c 1 1+y.1+value c 1 y.2
      rw [value_one_left c y.2,value_one_right c y.2]; ring
    · exact (mul_one _).trans (one_mul _).symm

lemma pull_value (f : G →* H) (c : Cocycles H) (g h : G) :
    value (pull f c) g h = value c (f g) (f h) := by
  change c.val (map2 f (Finsupp.single (g,h) 1)) = _
  simp [map2,groupHomology.chainsMap₂,value]
  rfl

lemma coboundary_value (b : C1 G →ₗ[ℚ] ℚ) (g h : G) :
    b (d2 G (Finsupp.single (g,h) 1)) = b (Finsupp.single g 1)+b (Finsupp.single h 1)-b (Finsupp.single (g*h) 1) := by
  change b (groupHomology.d₂₁ (T G) (Finsupp.single (g,h) 1)) = _
  rw [groupHomology.d₂₁_single]
  change b (Finsupp.single h 1-Finsupp.single (g*h) 1+Finsupp.single g 1)=_
  simp only [map_add,map_sub]
  ring

lemma relation_value (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) (g h : G) :
    value c g h = value d (f g) (f h) + b (Finsupp.single g 1)+b (Finsupp.single h 1)-b (Finsupp.single (g*h) 1) := by
  have he := LinearMap.congr_fun hb (Finsupp.single (g,h) 1)
  change value c g h-value (pull f d) g h=b (d2 G (Finsupp.single (g,h) 1)) at he
  rw [pull_value,coboundary_value] at he
  linarith

def morphism (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) : Extension c →* Extension d where
  toFun x := (x.1+b (Finsupp.single x.2 1),f x.2)
  map_one' := Prod.ext (by
    have he := relation_value f c d b hb 1 1
    simp only [map_one,one_mul] at he
    change -value c 1 1+b (Finsupp.single 1 1) = -value d 1 1
    linarith) (map_one f)
  map_mul' x y := Prod.ext (by
    have he := relation_value f c d b hb x.2 y.2
    change x.1+y.1+value c x.2 y.2+b (Finsupp.single (x.2*y.2) 1) =
      (x.1+b (Finsupp.single x.2 1))+(y.1+b (Finsupp.single y.2 1))+value d (f x.2) (f y.2)
    linarith) (map_mul f x.2 y.2)

lemma morphism_inclusion (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) (q : QGroup) :
    morphism f c d b hb (inclusion c q)=inclusion d q := by
  apply Prod.ext
  · have he := relation_value f c d b hb 1 1
    simp only [map_one,one_mul] at he
    change q.toAdd-value c 1 1+b (Finsupp.single 1 1)=q.toAdd-value d 1 1
    linarith
  · exact map_one f

lemma morphism_projection (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) (x : Extension c) :
    projection d (morphism f c d b hb x)=f (projection c x) := rfl

end
end SourceBurnside.Stability.RationalBar

namespace SourceBurnside.Stability
noncomputable section
open Classical
namespace RationalExtension
open RationalBar
variable {X G : Type} [Group X] [Group G] (S : RationalExtension X G)

def chosenSection : G → X := S.toGroupExtension.surjInvRightHom
@[simp] lemma projection_section (g : G) : S.rightHom (S.chosenSection g)=g :=
  S.toGroupExtension.surjInvRightHom.rightInverse_rightHom g

def factor (g h : G) : ℚ :=
  (S.kernelEquiv.symm ⟨S.chosenSection g*S.chosenSection h*(S.chosenSection (g*h))⁻¹,by
    simp only [MonoidHom.mem_ker,map_mul,map_inv,projection_section,mul_inv_cancel]⟩).toAdd

lemma factor_mul (g h : G) :
    S.inl (Multiplicative.ofAdd (S.factor g h))*S.chosenSection (g*h)=S.chosenSection g*S.chosenSection h := by
  have he := congrArg Subtype.val (S.kernelEquiv.apply_symm_apply
    ⟨S.chosenSection g*S.chosenSection h*(S.chosenSection (g*h))⁻¹,by
      simp only [MonoidHom.mem_ker,map_mul,map_inv,projection_section,mul_inv_cancel]⟩)
  change S.inl (Multiplicative.ofAdd (S.factor g h)) = _ at he
  rw [he,inv_mul_cancel_right]

lemma factor_identity (g h k : G) :
    S.factor g h+S.factor (g*h) k=S.factor h k+S.factor g (h*k) := by
  apply (Multiplicative.ofAdd).injective
  apply S.inl_injective
  apply mul_right_cancel (b := S.chosenSection (g*h*k))
  simp only [ofAdd_add,map_mul]
  rw [mul_assoc,S.factor_mul (g*h) k,←mul_assoc,S.factor_mul g h]
  rw [mul_assoc _ _ (S.chosenSection (g*h*k)),mul_assoc g h k,S.factor_mul g (h*k)]
  have hc := (S.inl_central (Multiplicative.ofAdd (S.factor h k))).comm (S.chosenSection g)
  calc
    S.chosenSection g*S.chosenSection h*S.chosenSection k = S.chosenSection g*(S.inl (Multiplicative.ofAdd (S.factor h k))*S.chosenSection (h*k)) := by rw [S.factor_mul,mul_assoc]
    _ = S.inl (Multiplicative.ofAdd (S.factor h k))*(S.chosenSection g*S.chosenSection (h*k)) := by rw [←mul_assoc,←hc.eq,mul_assoc]

lemma factor_one : S.inl (Multiplicative.ofAdd (S.factor 1 1))=S.chosenSection 1 := by
  apply mul_right_cancel (b := S.chosenSection 1)
  simpa only [one_mul] using S.factor_mul 1 1

def cochain : C2 G →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun p : G×G => S.factor p.1 p.2)
lemma cochain_single (g h : G) (a : ℚ) : S.cochain (Finsupp.single (g,h) a)=a*S.factor g h := by
  simp [cochain]

def cocycle : Cocycles G := ⟨S.cochain,by
  rw [cocycle_iff]
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro a
  obtain ⟨g,h,k⟩ := p
  change S.cochain (groupHomology.d₃₂ (T G) (Finsupp.single (g,h,k) a))=0
  rw [groupHomology.d₃₂_single]
  change S.cochain (Finsupp.single (h,k) a-Finsupp.single (g*h,k) a+
    Finsupp.single (g,h*k) a-Finsupp.single (g,h) a)=0
  simp only [map_add,map_sub,cochain_single]
  have he := S.factor_identity g h k
  linear_combination -a*he⟩

lemma cocycle_value (g h : G) : value S.cocycle g h=S.factor g h := by
  change S.cochain (Finsupp.single (g,h) 1)=_
  rw [cochain_single,one_mul]

def modelHom : Extension S.cocycle →* X where
  toFun x := S.inl (Multiplicative.ofAdd x.1)*S.chosenSection x.2
  map_one' := by
    change S.inl (Multiplicative.ofAdd (-value S.cocycle 1 1))*S.chosenSection 1=1
    rw [cocycle_value,ofAdd_neg,map_inv,factor_one,inv_mul_cancel]
  map_mul' x y := by
    change S.inl (Multiplicative.ofAdd (x.1+y.1+value S.cocycle x.2 y.2))*S.chosenSection (x.2*y.2)=
      (S.inl (Multiplicative.ofAdd x.1)*S.chosenSection x.2)*(S.inl (Multiplicative.ofAdd y.1)*S.chosenSection y.2)
    rw [cocycle_value]
    simp only [ofAdd_add,map_mul,mul_assoc]
    rw [S.factor_mul]
    have hc := (S.inl_central (Multiplicative.ofAdd y.1)).comm (S.chosenSection x.2)
    rw [←mul_assoc (S.inl (Multiplicative.ofAdd y.1)),hc.eq,mul_assoc]

lemma modelHom_inclusion (q : QGroup) : S.modelHom (inclusion S.cocycle q)=S.inl q := by
  change S.inl (Multiplicative.ofAdd (q.toAdd-value S.cocycle 1 1))*S.chosenSection 1=S.inl q
  rw [cocycle_value,sub_eq_add_neg,ofAdd_add,ofAdd_neg,map_mul,map_inv,factor_one]
  simp only [mul_assoc,inv_mul_cancel,mul_one,ofAdd_toAdd]
lemma modelHom_projection (x : Extension S.cocycle) : S.rightHom (S.modelHom x)=projection S.cocycle x := by
  change S.rightHom (S.inl (Multiplicative.ofAdd x.1)*S.chosenSection x.2)=x.2
  rw [map_mul,S.toGroupExtension.rightHom_inl,projection_section,one_mul]

def modelEquiv : (extension S.cocycle).toGroupExtension.Equiv S.toGroupExtension :=
  GroupExtension.Equiv.ofMonoidHom S.modelHom
    (by ext q; exact S.modelHom_inclusion q)
    (by ext x; exact S.modelHom_projection x)

end RationalExtension
end
end SourceBurnside.Stability

end OAI
