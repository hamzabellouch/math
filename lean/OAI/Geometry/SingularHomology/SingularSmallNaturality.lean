import OAI.Geometry.SingularHomology.SingularSmallChains

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularSmallChains

abbrev singularFunctor : TopCat ⥤ ChainComplex (ModuleCat ℝ) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)

abbrev singularDegree (n : ℕ) : TopCat ⥤ ModuleCat ℝ :=
  singularFunctor ⋙ HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n

variable {X : Type} [TopologicalSpace X]
variable {ι : Type*} (U : ι → Set X)

def memberInclusion (i : ι) : realSingularChainComplex (U i) ⟶ chains U :=
  SSet.chainComplexMap
    (subspaceMap (U i) ≫ SSet.Subcomplex.homOfLE
      (le_iSup (fun j => inSubset (U j)) i)) (ModuleCat.of ℝ ℝ)

@[reassoc] theorem memberInclusion_inclusion (i : ι) :
    memberInclusion U i ≫ inclusion U =
      realSingularChainMap (Subtype.val : U i → X) continuous_subtype_val := by
  change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ = _
  erw [← Functor.map_comp]
  rfl

private def simplexMember {n : ℕ} (σ : (small U : SSet) _⦋n⦌) : ι :=
  Classical.choose ((mem_small U σ.val).mp σ.property)

private theorem simplexMember_property {n : ℕ} (σ : (small U : SSet) _⦋n⦌) :
    ∀ p, TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ.val p ∈
      U (simplexMember U σ) := by
  exact fun p => Classical.choose_spec ((mem_small U σ.val).mp σ.property) ⟨p, rfl⟩

private def simplexInMember {n : ℕ} (σ : (small U : SSet) _⦋n⦌) :
    (singularSet (U (simplexMember U σ))) _⦋n⦌ :=
  (subspaceInverse (U (simplexMember U σ))).app _
    ⟨σ.val, simplexMember_property U σ⟩

private theorem simplexInMember_map {n : ℕ} (σ : (small U : SSet) _⦋n⦌) :
    (singularSet (U (simplexMember U σ))).ιChainComplex (simplexInMember U σ) ≫
      (memberInclusion U (simplexMember U σ)).f n =
        (small U : SSet).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ := by
  exact SSet.ι_chainComplexMap_f _ _
    (subspaceMap (U (simplexMember U σ)) ≫ SSet.Subcomplex.homOfLE
      (le_iSup (fun j => inSubset (U j)) (simplexMember U σ)))
    (ModuleCat.of ℝ ℝ) (simplexInMember U σ)

def restrict {n m : ℕ} (T : singularDegree n ⟶ singularDegree m) :
    (chains U).X n ⟶ (chains U).X m :=
  Sigma.desc fun σ =>
    (singularSet (U (simplexMember U σ))).ιChainComplex (simplexInMember U σ) ≫
      T.app (TopCat.of (U (simplexMember U σ))) ≫
        (memberInclusion U (simplexMember U σ)).f m

private theorem generator_restrict {n m : ℕ}
    (T : singularDegree n ⟶ singularDegree m) (σ : (small U : SSet) _⦋n⦌) :
    (small U : SSet).ιChainComplex σ ≫ restrict U T =
      (singularSet (U (simplexMember U σ))).ιChainComplex (simplexInMember U σ) ≫
        T.app (TopCat.of (U (simplexMember U σ))) ≫
          (memberInclusion U (simplexMember U σ)).f m := by
  exact Sigma.ι_comp_desc _ _

@[reassoc] theorem restrict_inclusion {n m : ℕ}
    (T : singularDegree n ⟶ singularDegree m) :
    restrict U T ≫ (inclusion U).f m =
      (inclusion U).f n ≫ T.app (TopCat.of X) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, generator_restrict]
  have hnat := T.naturality
    (TopCat.ofHom ⟨(Subtype.val : U (simplexMember U σ) → X), continuous_subtype_val⟩)
  change (realSingularChainMap
      (Subtype.val : U (simplexMember U σ) → X) continuous_subtype_val).f n ≫
        T.app (TopCat.of X) =
      T.app (TopCat.of (U (simplexMember U σ))) ≫
        (realSingularChainMap
          (Subtype.val : U (simplexMember U σ) → X) continuous_subtype_val).f m at hnat
  have hm (k : ℕ) := congrArg (fun f => f.f k)
    (memberInclusion_inclusion U (simplexMember U σ))
  simp only [HomologicalComplex.comp_f] at hm
  erw [Category.assoc, Category.assoc]
  erw [hm m, ← hnat, ← hm n]
  erw [← Category.assoc, ← Category.assoc, simplexInMember_map]
  exact Category.assoc _ _ _

@[simp] theorem restrict_id (n : ℕ) :
    restrict U (𝟙 (singularDegree n)) = 𝟙 ((chains U).X n) := by
  apply (cancel_mono ((inclusion U).f n)).1
  rw [restrict_inclusion]
  simp only [NatTrans.id_app, Category.id_comp]
  exact Category.comp_id _

@[simp] theorem restrict_zero (n m : ℕ) :
    restrict U (0 : singularDegree n ⟶ singularDegree m) = 0 := by
  apply (cancel_mono ((inclusion U).f m)).1
  rw [restrict_inclusion]
  simp

@[simp] theorem restrict_add {n m : ℕ}
    (S T : singularDegree n ⟶ singularDegree m) :
    restrict U (S + T) = restrict U S + restrict U T := by
  apply (cancel_mono ((inclusion U).f m)).1
  rw [restrict_inclusion, Preadditive.add_comp, restrict_inclusion, restrict_inclusion]
  simp

@[reassoc] theorem restrict_comp {n m k : ℕ}
    (S : singularDegree n ⟶ singularDegree m)
    (T : singularDegree m ⟶ singularDegree k) :
    restrict U (S ≫ T) = restrict U S ≫ restrict U T := by
  apply (cancel_mono ((inclusion U).f k)).1
  simp only [Category.assoc, restrict_inclusion, restrict_inclusion_assoc, NatTrans.comp_app]

def restrictChainMap (S : singularFunctor ⟶ singularFunctor) : chains U ⟶ chains U where
  f n := restrict U (Functor.whiskerRight S
    (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))
  comm' i j hij := by
    apply (cancel_mono ((inclusion U).f j)).1
    simp only [Category.assoc]
    rw [← (inclusion U).comm i j, restrict_inclusion_assoc, restrict_inclusion]
    change (inclusion U).f i ≫ (S.app (TopCat.of X)).f i ≫
      (realSingularChainComplex X).d i j =
      (chains U).d i j ≫ (inclusion U).f j ≫ (S.app (TopCat.of X)).f j
    rw [(S.app (TopCat.of X)).comm, ← Category.assoc, (inclusion U).comm]
    exact Category.assoc _ _ _

@[reassoc] theorem restrictChainMap_inclusion (S : singularFunctor ⟶ singularFunctor) :
    restrictChainMap U S ≫ inclusion U = inclusion U ≫ S.app (TopCat.of X) := by
  ext n : 1
  exact restrict_inclusion U (Functor.whiskerRight S
    (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))

@[simp] theorem restrictChainMap_id :
    restrictChainMap U (𝟙 singularFunctor) = 𝟙 (chains U) := by
  ext n : 1
  exact restrict_id U n

@[simp] theorem restrictChainMap_comp (S T : singularFunctor ⟶ singularFunctor) :
    restrictChainMap U (S ≫ T) = restrictChainMap U S ≫ restrictChainMap U T := by
  ext n : 1
  exact restrict_comp U
    (Functor.whiskerRight S (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))
    (Functor.whiskerRight T (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) n))

def HomotopyNatural {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y)) : Prop :=
  ∀ (i j : ℕ) {Y Z : TopCat} (f : Y ⟶ Z),
    (singularFunctor.map f).f i ≫ (H Z).hom i j =
      (H Y).hom i j ≫ (singularFunctor.map f).f j

def homotopyOperator {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y))
    (hH : HomotopyNatural H) (i j : ℕ) : singularDegree i ⟶ singularDegree j where
  app Y := (H Y).hom i j
  naturality {_ _} f := hH i j f

def restrictHomotopy {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y))
    (hH : HomotopyNatural H) :
    Homotopy (restrictChainMap U S) (restrictChainMap U T) where
  hom i j := restrict U (homotopyOperator H hH i j)
  zero i j hij := by
    apply (cancel_mono ((inclusion U).f j)).1
    rw [restrict_inclusion, zero_comp]
    change (inclusion U).f i ≫ (H (TopCat.of X)).hom i j = 0
    rw [(H (TopCat.of X)).zero i j hij, comp_zero]
  comm i := by
    apply (cancel_mono ((inclusion U).f i)).1
    simp only [Preadditive.add_comp]
    change restrict U (Functor.whiskerRight S
        (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) i)) ≫
        (inclusion U).f i = _
    rw [restrict_inclusion]
    change (inclusion U).f i ≫ (S.app (TopCat.of X)).f i = _
    rw [(H (TopCat.of X)).comm i]
    simp only [Preadditive.comp_add]
    congr 1
    · congr 1
      · change (inclusion U).f i ≫
            ((realSingularChainComplex X).d i ((ComplexShape.down ℕ).next i) ≫
              (H (TopCat.of X)).hom ((ComplexShape.down ℕ).next i) i) =
          ((chains U).d i ((ComplexShape.down ℕ).next i) ≫
            restrict U (homotopyOperator H hH ((ComplexShape.down ℕ).next i) i)) ≫
              (inclusion U).f i
        rw [Category.assoc, restrict_inclusion, ← Category.assoc, (inclusion U).comm]
        exact Category.assoc _ _ _
      · change (inclusion U).f i ≫
            ((H (TopCat.of X)).hom i ((ComplexShape.down ℕ).prev i) ≫
              (realSingularChainComplex X).d ((ComplexShape.down ℕ).prev i) i) =
          (restrict U (homotopyOperator H hH i ((ComplexShape.down ℕ).prev i)) ≫
            (chains U).d ((ComplexShape.down ℕ).prev i) i) ≫ (inclusion U).f i
        rw [Category.assoc, ← (inclusion U).comm, restrict_inclusion_assoc]
        rfl
    · exact (restrict_inclusion U (Functor.whiskerRight T
        (HomologicalComplex.eval (ModuleCat ℝ) (ComplexShape.down ℕ) i))).symm

@[reassoc] theorem restrictHomotopy_inclusion {S T : singularFunctor ⟶ singularFunctor}
    (H : ∀ Y : TopCat, Homotopy (S.app Y) (T.app Y))
    (hH : HomotopyNatural H) (i j : ℕ) :
    (restrictHomotopy U H hH).hom i j ≫ (inclusion U).f j =
      (inclusion U).f i ≫ (H (TopCat.of X)).hom i j :=
  restrict_inclusion U (homotopyOperator H hH i j)

end Problem340.SingularSmallChains

end

end OAI
