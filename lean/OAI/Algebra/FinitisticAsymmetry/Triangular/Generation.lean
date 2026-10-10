import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Triangular.Augmentation
import OAI.Algebra.FinitisticAsymmetry.Derived.UpperTruncation
import OAI.Algebra.FinitisticAsymmetry.Derived.ExactExtension
import OAI.Algebra.FinitisticAsymmetry.Derived.ModuleGeneration
import OAI.Algebra.FinitisticAsymmetry.Triangular.InjectiveResolution

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
namespace LittleFinitistic.CummingsConstruction
universe u w
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

lemma periodicOld_d (m n : ℕ) : (periodicOld χ i).d m n = 0 := by
  by_cases h : m = n+1
  · subst m
    simp [periodicOld]
    rfl
  · exact (periodicOld χ i).shape m n (by simpa [ComplexShape.down_Rel, eq_comm] using h)

def oldSingleι (n : ℕ) : (HomologicalComplex.single (ModuleCat (T χ)) (.down ℕ) n).obj
    (oldSimple χ i) ⟶ periodicOld χ i :=
  mkHomFromSingle (𝟙 _) (fun j hj => by simp [periodicOld_d]; exact Category.id_comp _)

def oldSingleπ (n : ℕ) : periodicOld χ i ⟶
    (HomologicalComplex.single (ModuleCat (T χ)) (.down ℕ) n).obj (oldSimple χ i) :=
  mkHomToSingle (𝟙 _) (fun j hj => by simp [periodicOld_d]; exact Category.comp_id _)

lemma oldSingleι_π (n : ℕ) : oldSingleι χ i n ≫ oldSingleπ χ i n = 𝟙 _ := by
  apply from_single_hom_ext
  simp [oldSingleι, oldSingleπ]
  erw [mkHomFromSingle_f, mkHomToSingle_f, Category.comp_id, Category.id_comp,
    Iso.hom_inv_id]

abbrev extendedInjective := (periodicInjective χ i).extend ComplexShape.embeddingDownNat
abbrev extendedRegular := (periodicRegular χ i).extend ComplexShape.embeddingDownNat
abbrev extendedOld := (periodicOld χ i).extend ComplexShape.embeddingDownNat

variable [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))]

def regularDerivedIso : DerivedCategory.Q.obj (extendedRegular χ i) ≅
    (DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (newSimple χ i) :=
  asIso (DerivedCategory.Q.map (extendMap (periodicAug χ i) ComplexShape.embeddingDownNat)) ≪≫
    DerivedCategory.Q.mapIso (extendSingleIso ComplexShape.embeddingDownNat (newSimple χ i) 0 0 rfl) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (T χ)) 0).app (newSimple χ i)).symm

def oldSingleDerivedIso (n : ℕ) :
    DerivedCategory.Q.obj (((HomologicalComplex.single (ModuleCat (T χ)) (.down ℕ) n).obj
      (oldSimple χ i)).extend ComplexShape.embeddingDownNat) ≅
    (DerivedCategory.singleFunctor (ModuleCat (T χ)) (-(n : ℤ))).obj (oldSimple χ i) :=
  DerivedCategory.Q.mapIso (extendSingleIso ComplexShape.embeddingDownNat (oldSimple χ i) n (-(n : ℤ)) rfl) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (T χ)) (-n)).app (oldSimple χ i)).symm

omit [HasDerivedCategory (ModuleCat (T χ))] in
lemma extended_shortExact :
    ((ShortComplex.mk (periodicι χ i) (periodicπ χ i) (periodicι_π χ i)).map
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat (T χ)))).ShortExact :=
  DerivedSupport.extend_shortExact _ _ (periodic_shortExact χ i)

variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} (T χ))))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]
  (hI : ∀ M : ModuleCat.{u} (T χ), Injective M →
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj M))

include hI

lemma extendedInjective_mem [DecidableEq ι] : P (DerivedCategory.Q.obj (extendedInjective χ i)) := by
  apply DerivedSupport.prop_of_boundedAbove_terms P _ 0
  · intro j hj
    exact CochainComplex.isZero_of_isStrictlyLE _ 0 j hj
  · intro j
    apply hI
    by_cases hj : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = j
    · obtain ⟨n, hn⟩ := hj
      exact Injective.of_iso ((periodicInjective χ i).extendXIso _ hn).symm
        (newInjective_injective χ i)
    · exact (isZero_extend_X _ _ j (fun n hn => hj ⟨n,hn⟩)).injective

lemma oldSimple_shifted_retract [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) (-2)).obj (oldSimple χ i)) := by
  let S := (ShortComplex.mk (periodicι χ i) (periodicπ χ i) (periodicι_π χ i)).map
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat (T χ)))
  let hS := extended_shortExact χ i
  let Δ := DerivedCategory.triangleOfSES hS
  have hΔ : Δ ∈ distTriang _ := DerivedCategory.triangleOfSES_distinguished hS
  let F := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat (T χ)) ⋙ DerivedCategory.Q
  let j := F.map (oldSingleι χ i 2)
  let p := F.map (oldSingleπ χ i 2)
  have hjp : j ≫ p = 𝟙 _ := by
    dsimp [j,p]
    rw [← F.map_comp, oldSingleι_π, F.map_id]
  have hzero : j ≫ Δ.mor₃ = 0 := by
    have hle : (DerivedCategory.TStructure.t (C := ModuleCat (T χ))).IsLE (F.obj _) (-2) :=
      DerivedCategory.TStructure.t.isLE_of_iso (oldSingleDerivedIso χ i 2).symm (-2)
    have hge : (DerivedCategory.TStructure.t (C := ModuleCat (T χ))).IsGE Δ.obj₁ 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso (regularDerivedIso χ i).symm 0
    have hges := DerivedCategory.TStructure.t.isGE_shift Δ.obj₁ 0 1 (-1) (by omega)
    exact DerivedCategory.TStructure.t.zero (j ≫ Δ.mor₃) (-2) (-1) (by omega)
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ Δ hΔ j hzero
  have hlp : l ≫ (Δ.mor₂ ≫ p) = 𝟙 _ := by erw [← Category.assoc, ← hl, hjp]
  apply P.prop_of_iso (oldSingleDerivedIso χ i 2)
  exact DerivedSupport.localizing_of_retract l (Δ.mor₂ ≫ p) hlp P
    (extendedInjective_mem χ i P hI)

lemma oldSimple_mem [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (oldSimple χ i)) := by
  apply P.prop_of_iso (((DerivedCategory.singleFunctors (ModuleCat (T χ))).shiftIso
    (-2) 0 (-2) (by omega)).app (oldSimple χ i))
  exact P.le_shift (-2) _ (oldSimple_shifted_retract χ i P hI)

lemma newRegular_mem [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (newRegular χ i)) := by
  exact DerivedSupport.prop_single_shortExact₁ P _ (newRegular_exact χ i)
    (hI _ (newInjective_injective χ i)) (oldSimple_mem χ i P hI)

lemma newSimple_mem [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (newSimple χ i)) := by
  apply P.prop_of_iso (regularDerivedIso χ i)
  apply DerivedSupport.prop_of_boundedAbove_terms P _ 0
  · intro j hj
    exact CochainComplex.isZero_of_isStrictlyLE _ 0 j hj
  · intro j
    by_cases hj : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = j
    · obtain ⟨n, hn⟩ := hj
      apply P.prop_of_iso ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).mapIso
        ((periodicRegular χ i).extendXIso _ hn).symm)
      exact newRegular_mem χ i P hI
    · apply P.prop_of_isZero
      apply (DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).map_isZero
      exact isZero_extend_X _ _ j (fun n hn => hj ⟨n,hn⟩)

omit hI [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))] in
lemma injectivesGenerate [Fintype ι] (hχ : Function.Surjective χ)
    (hnil : ∃ n : ℕ, (RingHom.ker χ.toRingHom)^n = ⊥) :
    InjectivesGenerate (T χ) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} (T χ))
  intro P hP hT hcop hI X
  let := hP
  let := hT
  let (I : Type u) := hcop I
  let : P.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u} ℕ ≃ ℕ))
  apply DerivedSupport.localizing_eq_top_of_all_modules P
  · intro M
    apply DerivedSupport.prop_all_of_product_augmentation P hcop
      (augmentation χ).toRingHom (augmentation_surjective χ hχ)
      (augmentation_ker_nilpotent χ hnil) _ M
    intro j
    cases j with
    | inl i => exact oldSimple_mem χ i P hI
    | inr i => exact newSimple_mem χ i P hI

end LittleFinitistic.CummingsConstruction

end

end OAI
