import OAI.Geometry.SingularHomology.SingularCoverChains
import OAI.Geometry.SingularHomology.SingularSmallChains
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularCover

variable {X : Type} [TopologicalSpace X]

@[simp] theorem supported_eq_inSubset (U : Set X) :
    supported U = SingularSmallChains.inSubset U := rfl

variable {K L : SSet} (f : K ⟶ L)
variable {A B : K.Subcomplex} {A' B' : L.Subcomplex}

def restrictedMap (A : K.Subcomplex) (A' : L.Subcomplex)
    (h : A ≤ A'.preimage f) : (A : SSet) ⟶ (A' : SSet) :=
  SSet.Subcomplex.homOfLE h ≫ A'.fromPreimage f

@[reassoc (attr := simp)] theorem restrictedMap_ι
    (h : A ≤ A'.preimage f) :
    restrictedMap f A A' h ≫ A'.ι = A.ι ≫ f := rfl

theorem restrictedMap_inclusion
    {C : K.Subcomplex} {C' : L.Subcomplex}
    (hA : A ≤ A'.preimage f) (hC : C ≤ C'.preimage f)
    (hAC : A ≤ C) (hAC' : A' ≤ C') :
    restrictedMap f A A' hA ≫ SSet.Subcomplex.homOfLE hAC' =
      SSet.Subcomplex.homOfLE hAC ≫ restrictedMap f C C' hC := rfl

theorem preserves_inter (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    A ⊓ B ≤ (A' ⊓ B').preimage f := by
  intro n s hs
  exact ⟨hA n hs.1, hB n hs.2⟩

theorem preserves_union (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    A ⊔ B ≤ (A' ⊔ B').preimage f := by
  intro n s hs
  exact hs.elim (fun h => Or.inl (hA n h)) (fun h => Or.inr (hB n h))

theorem chainRestrictedMap_inclusion
    {C : K.Subcomplex} {C' : L.Subcomplex}
    (hA : A ≤ A'.preimage f) (hC : C ≤ C'.preimage f)
    (hAC : A ≤ C) (hAC' : A' ≤ C') :
    SSet.chainComplexMap (restrictedMap f A A' hA) (ModuleCat.of ℝ ℝ) ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE hAC') (ModuleCat.of ℝ ℝ) =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE hAC) (ModuleCat.of ℝ ℝ) ≫
        SSet.chainComplexMap (restrictedMap f C C' hC) (ModuleCat.of ℝ ℝ) := by
  have h := ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)).congr_map
    (restrictedMap_inclusion f hA hC hAC hAC')
  simpa only [Functor.map_comp] using h

def unionShortComplexMap
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) :
    unionShortComplex A B ⟶ unionShortComplex A' B' where
  τ₁ := SSet.chainComplexMap
    (restrictedMap f (A ⊓ B) (A' ⊓ B') (preserves_inter f hA hB)) (ModuleCat.of ℝ ℝ)
  τ₂ := biprod.map
    (SSet.chainComplexMap (restrictedMap f A A' hA) (ModuleCat.of ℝ ℝ))
    (SSet.chainComplexMap (restrictedMap f B B' hB) (ModuleCat.of ℝ ℝ))
  τ₃ := SSet.chainComplexMap
    (restrictedMap f (A ⊔ B) (A' ⊔ B') (preserves_union f hA hB)) (ModuleCat.of ℝ ℝ)
  comm₁₂ := by
    dsimp only [unionShortComplex, CommSq.shortComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact chainRestrictedMap_inclusion f (preserves_inter f hA hB) hA inf_le_left inf_le_left
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg
        (chainRestrictedMap_inclusion f (preserves_inter f hA hB) hB inf_le_right inf_le_right)
  comm₂₃ := by
    dsimp only [unionShortComplex, CommSq.shortComplex]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact chainRestrictedMap_inclusion f hA (preserves_union f hA hB) le_sup_left le_sup_left
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc]
      exact chainRestrictedMap_inclusion f hB (preserves_union f hA hB) le_sup_right le_sup_right

theorem union_connecting_naturality
    (hA : A ≤ A'.preimage f) (hB : B ≤ B'.preimage f) (n : ℕ) :
    (unionShortComplex_shortExact A B).δ (n + 1) n (by simp) ≫
        HomologicalComplex.homologyMap (unionShortComplexMap f hA hB).τ₁ n =
      HomologicalComplex.homologyMap (unionShortComplexMap f hA hB).τ₃ (n + 1) ≫
        (unionShortComplex_shortExact A' B').δ (n + 1) n (by simp) := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (unionShortComplexMap f hA hB)
    (unionShortComplex_shortExact A B) (unionShortComplex_shortExact A' B')
    (n + 1) n (by simp)

end Problem340.SingularCover

end

end OAI
