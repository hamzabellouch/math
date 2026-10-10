import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace OAI

/-! # The successor shift of a nonnegative chain complex -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {k : Type} [CommRing k]

def negativeChainComplex (C : ChainComplex (ModuleCat k) ℕ) :
    ChainComplex (ModuleCat k) ℕ where
  X := C.X
  d i j := -C.d i j
  shape i j hij := by rw [C.shape i j hij, neg_zero]
  d_comp_d' i j l _ _ := by simp only [Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, C.d_comp_d]

def chainModuleNegIdentityIso (M : ModuleCat k) : M ≅ M where
  hom := -𝟙 M
  inv := -𝟙 M
  hom_inv_id := by simp
  inv_hom_id := by simp

def negativeChainShortComplexIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeChainComplex C).sc i ≅ C.sc i :=
  ShortComplex.isoMk
    (S₁ := (negativeChainComplex C).sc i) (S₂ := C.sc i)
    (chainModuleNegIdentityIso _) (Iso.refl _) (chainModuleNegIdentityIso _)
    (by change (-𝟙 _) ≫ C.d _ _ = (-C.d _ _) ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ C.d _ _ = (-C.d _ _) ≫ (-𝟙 _); simp)

def negativeChainHomologyIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (negativeChainComplex C).homology i ≅ C.homology i :=
  ShortComplex.homologyMapIso (negativeChainShortComplexIso C i)

def chainSuccessorEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) where
  f n := n + 1
  injective_f := fun _ _ h => Nat.add_right_cancel h
  rel h := by simpa only [ComplexShape.down_Rel] using congrArg (fun n : ℕ => n + 1) h

def chainSuccessor (C : ChainComplex (ModuleCat k) ℕ) :
    ChainComplex (ModuleCat k) ℕ :=
  (negativeChainComplex C).extend chainSuccessorEmbedding

def chainSuccessorXIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).X (i + 1) ≅ C.X i :=
  (negativeChainComplex C).extendXIso chainSuccessorEmbedding rfl

def chainSuccessorHomologyIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).homology (i + 1) ≅ C.homology i :=
  (negativeChainComplex C).extendHomologyIso chainSuccessorEmbedding rfl ≪≫
    negativeChainHomologyIso C i

theorem chainSuccessor_zero (C : ChainComplex (ModuleCat k) ℕ) :
    IsZero ((chainSuccessor C).X 0) :=
  (negativeChainComplex C).isZero_extend_X chainSuccessorEmbedding 0 (by
    intro i
    simp [chainSuccessorEmbedding])

theorem chainSuccessor_homology_zero (C : ChainComplex (ModuleCat k) ℕ) :
    IsZero ((chainSuccessor C).homology 0) :=
  (negativeChainComplex C).extend_exactAt chainSuccessorEmbedding 0 (by
    intro i
    simp [chainSuccessorEmbedding]) |>.isZero_homology

theorem chainSuccessor_d (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).d (i + 2) (i + 1) =
      (chainSuccessorXIso C (i + 1)).hom ≫ (-C.d (i + 1) i) ≫
        (chainSuccessorXIso C i).inv :=
  (negativeChainComplex C).extend_d_eq chainSuccessorEmbedding rfl rfl

def chainSuccessorCyclesIso (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).cycles (i + 1) ≅ C.cycles i :=
  (negativeChainComplex C).extendCyclesIso chainSuccessorEmbedding rfl ≪≫
    ShortComplex.cyclesMapIso (negativeChainShortComplexIso C i)

theorem chainSuccessorCyclesIso_iCycles (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessorCyclesIso C i).hom ≫ C.iCycles i =
      (chainSuccessor C).iCycles (i + 1) ≫ (chainSuccessorXIso C i).hom := by
  change (_ ≫ ShortComplex.cyclesMap (negativeChainShortComplexIso C i).hom) ≫ _ = _
  erw [Category.assoc]
  have hn : ShortComplex.cyclesMap (negativeChainShortComplexIso C i).hom ≫
      C.iCycles i = (negativeChainComplex C).iCycles i := by
    exact (ShortComplex.cyclesMap_i (negativeChainShortComplexIso C i).hom).trans
      (Category.comp_id _)
  calc
    _ = ((negativeChainComplex C).extendCyclesIso chainSuccessorEmbedding rfl).hom ≫
        (negativeChainComplex C).iCycles i := congrArg _ hn
    _ = _ := (negativeChainComplex C).extendCyclesIso_hom_iCycles chainSuccessorEmbedding rfl

theorem chainSuccessorHomologyIso_π (C : ChainComplex (ModuleCat k) ℕ) (i : ℕ) :
    (chainSuccessor C).homologyπ (i + 1) ≫ (chainSuccessorHomologyIso C i).hom =
      (chainSuccessorCyclesIso C i).hom ≫ C.homologyπ i := by
  have he := (negativeChainComplex C).homologyπ_extendHomologyIso_hom
    chainSuccessorEmbedding (j := i) rfl
  have hn : (negativeChainComplex C).homologyπ i ≫
      ShortComplex.homologyMap (negativeChainShortComplexIso C i).hom =
      ShortComplex.cyclesMap (negativeChainShortComplexIso C i).hom ≫ C.homologyπ i :=
    ShortComplex.homologyπ_naturality (negativeChainShortComplexIso C i).hom
  change _ ≫ (_ ≫ ShortComplex.homologyMap (negativeChainShortComplexIso C i).hom) = _
  erw [← Category.assoc]
  exact (congrArg (fun f => f ≫ ShortComplex.homologyMap
    (negativeChainShortComplexIso C i).hom) he).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f =>
          ((negativeChainComplex C).extendCyclesIso chainSuccessorEmbedding rfl).hom ≫ f)
          hn).trans (Category.assoc _ _ _).symm))

end PolycyclicRecognition

end

end OAI
