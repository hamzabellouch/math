import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace OAI

/-! # The successor shift of a nonnegative cochain complex -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {k : Type} [CommRing k]

def negativeCochainComplex (C : CochainComplex (ModuleCat k) ℕ) :
    CochainComplex (ModuleCat k) ℕ where
  X := C.X
  d i j := -C.d i j
  shape i j hij := by rw [C.shape i j hij, neg_zero]
  d_comp_d' i j l _ _ := by simp only [Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, C.d_comp_d]

def moduleNegIdentityIso (M : ModuleCat k) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

def negativeCochainShortComplexIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeCochainComplex C).sc i ≅ C.sc i :=
  ShortComplex.isoMk
    (S₁ := (negativeCochainComplex C).sc i) (S₂ := C.sc i)
    (moduleNegIdentityIso _) (Iso.refl _) (moduleNegIdentityIso _)
    (by change (-𝟙 _) ≫ C.d _ _ = (-C.d _ _) ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ C.d _ _ = (-C.d _ _) ≫ (-𝟙 _); simp)

def negativeCochainHomologyIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeCochainComplex C).homology i ≅ C.homology i :=
  ShortComplex.homologyMapIso (negativeCochainShortComplexIso C i)

def cochainSuccessorEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) where
  f n := n + 1
  injective_f := fun _ _ h => Nat.add_right_cancel h
  rel h := by simpa only [ComplexShape.up_Rel] using congrArg (fun n : ℕ => n + 1) h

def cochainSuccessor (C : CochainComplex (ModuleCat k) ℕ) :
    CochainComplex (ModuleCat k) ℕ :=
  (negativeCochainComplex C).extend cochainSuccessorEmbedding

def cochainSuccessorXIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).X (i + 1) ≅ C.X i :=
  (negativeCochainComplex C).extendXIso cochainSuccessorEmbedding rfl

def cochainSuccessorHomologyIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).homology (i + 1) ≅ C.homology i :=
  (negativeCochainComplex C).extendHomologyIso cochainSuccessorEmbedding rfl ≪≫
    negativeCochainHomologyIso C i

theorem cochainSuccessor_zero (C : CochainComplex (ModuleCat k) ℕ) :
    IsZero ((cochainSuccessor C).X 0) :=
  (negativeCochainComplex C).isZero_extend_X cochainSuccessorEmbedding 0 (by
    intro i
    simp [cochainSuccessorEmbedding])

theorem cochainSuccessor_homology_zero (C : CochainComplex (ModuleCat k) ℕ) :
    IsZero ((cochainSuccessor C).homology 0) :=
  (negativeCochainComplex C).extend_exactAt cochainSuccessorEmbedding 0 (by
    intro i
    simp [cochainSuccessorEmbedding]) |>.isZero_homology

theorem cochainSuccessor_d (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).d (i + 1) (i + 2) =
      (cochainSuccessorXIso C i).hom ≫ (-C.d i (i + 1)) ≫
        (cochainSuccessorXIso C (i + 1)).inv :=
  (negativeCochainComplex C).extend_d_eq cochainSuccessorEmbedding rfl rfl

def cochainSuccessorCyclesIso (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).cycles (i + 1) ≅ C.cycles i :=
  (negativeCochainComplex C).extendCyclesIso cochainSuccessorEmbedding rfl ≪≫
    ShortComplex.cyclesMapIso (negativeCochainShortComplexIso C i)

theorem cochainSuccessorCyclesIso_iCycles (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessorCyclesIso C i).hom ≫ C.iCycles i =
      (cochainSuccessor C).iCycles (i + 1) ≫ (cochainSuccessorXIso C i).hom := by
  have hn : ShortComplex.cyclesMap (negativeCochainShortComplexIso C i).hom ≫
      C.iCycles i = (negativeCochainComplex C).iCycles i := by
    exact (ShortComplex.cyclesMap_i (negativeCochainShortComplexIso C i).hom).trans
      (Category.comp_id _)
  exact (Category.assoc
    ((negativeCochainComplex C).extendCyclesIso cochainSuccessorEmbedding (j := i) rfl).hom
    (ShortComplex.cyclesMap (negativeCochainShortComplexIso C i).hom) (C.iCycles i)).trans
      ((congrArg
        (fun f => ((negativeCochainComplex C).extendCyclesIso
          cochainSuccessorEmbedding (j := i) rfl).hom ≫ f) hn).trans
        ((negativeCochainComplex C).extendCyclesIso_hom_iCycles
          cochainSuccessorEmbedding (j := i) rfl))

theorem cochainSuccessorHomologyIso_π (C : CochainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (cochainSuccessor C).homologyπ (i + 1) ≫ (cochainSuccessorHomologyIso C i).hom =
      (cochainSuccessorCyclesIso C i).hom ≫ C.homologyπ i := by
  have he := (negativeCochainComplex C).homologyπ_extendHomologyIso_hom
    cochainSuccessorEmbedding (j := i) rfl
  have hn := ShortComplex.homologyπ_naturality (negativeCochainShortComplexIso C i).hom
  exact (Category.assoc
    (((negativeCochainComplex C).extend cochainSuccessorEmbedding).homologyπ
      (cochainSuccessorEmbedding.f i))
    ((negativeCochainComplex C).extendHomologyIso cochainSuccessorEmbedding (j := i) rfl).hom
    (ShortComplex.homologyMap (negativeCochainShortComplexIso C i).hom)).symm.trans
    ((congrArg (fun f => f ≫ ShortComplex.homologyMap
      (negativeCochainShortComplexIso C i).hom) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
          (fun f => ((negativeCochainComplex C).extendCyclesIso
            cochainSuccessorEmbedding (j := i) rfl).hom ≫ f) hn).trans
          (Category.assoc _ _ _).symm)))

end PolycyclicRecognition

end

end OAI
