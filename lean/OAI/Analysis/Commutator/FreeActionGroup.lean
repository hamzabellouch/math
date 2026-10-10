import Mathlib
import OAI.Analysis.Commutator.FreeActionCovariance
import OAI.Analysis.Commutator.HilbertStrong

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable {G : Type*} [Monoid G] (α : G → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)

lemma action_one (h1 : ∀ i a, α 1 i a=a) :
    action t S (α 1) (hmem 1) (hτ 1) hfree hgen=LinearIsometry.id := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply ext_reduced t S hfree hgen
  intro w hw
  change action t S (α 1) (hmem 1) (hτ 1) hfree hgen
    (TracialGNS.algebraVector t.functional (word w))=TracialGNS.algebraVector t.functional (word w)
  simp only [TracialGNS.algebraVector_apply]
  rw [action_word t S _ _ _ hfree hgen w hw]
  congr 2
  simp only [word,List.map_map,Function.comp_def,letter_val,h1]

lemma action_mul (hmul : ∀ g h i a, α (g*h) i a=α g i (α h i a)) (g h : G) :
    action t S (α (g*h)) (hmem (g*h)) (hτ (g*h)) hfree hgen=
      (action t S (α g) (hmem g) (hτ g) hfree hgen).comp
        (action t S (α h) (hmem h) (hτ h) hfree hgen) := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply ext_reduced t S hfree hgen
  intro w hw
  change action t S (α (g*h)) (hmem (g*h)) (hτ (g*h)) hfree hgen
    (TracialGNS.algebraVector t.functional (word w))=
      action t S (α g) (hmem g) (hτ g) hfree hgen
        (action t S (α h) (hmem h) (hτ h) hfree hgen
          (TracialGNS.algebraVector t.functional (word w)))
  simp only [TracialGNS.algebraVector_apply]
  rw [action_word t S _ _ _ hfree hgen w hw,action_word t S _ _ _ hfree hgen w hw,
    action_word t S _ _ _ hfree hgen _ (reduced_map t S _ _ _ hw)]
  congr 2
  simp only [word,List.map_map,Function.comp_def,letter_val,letter_color,hmul]

end Kadison.FreeWordAction

namespace Kadison.TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma algebraVector_continuous (τ : A →ₚ[ℂ] ℂ) : Continuous (algebraVector τ) := by
  have he : (algebraVector τ : A → τ.GNS) = fun a => τ.gnsStarAlgHom a (vacuum τ) := by
    funext a
    exact (left_vacuum τ a).symm
  rw [he]
  exact (map_continuous τ.gnsStarAlgHom).clm_apply continuous_const

end Kadison.TracialGNS

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {X : Type*} [TopologicalSpace X] (α : X → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)
  (hc : ∀ i a, Continuous fun g => α g i a)

include hc

lemma letterIso_continuous (i : ι) (x : letterSpace t S i) :
    Continuous fun g => letterIso t S (α g) (hmem g) (hτ g) i x := by
  apply Continuous.subtype_mk
  apply (Completion.isUniformEmbedding_coe (preSpace t)).isEmbedding.continuous_iff.mpr
  exact (TracialGNS.algebraVector_continuous t.functional).comp (hc i (letterValue t S i x))

lemma tensorIso_continuous : ∀ is (x : tensor t S is),
    Continuous fun g => tensorIso t S (α g) (hmem g) (hτ g) is x
  | [], _ => continuous_const
  | i::is,x => StrongContinuity.tensor _ _ (letterIso_continuous t S α hmem hτ hc i)
      (tensorIso_continuous is) x

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_continuous (x : t.functional.GNS) :
    Continuous fun g => action t S (α g) (hmem g) (hτ g) hfree hgen x := by
  apply StrongContinuity.hilbertSum (wordInclusion t S hfree)
    (isHilbertSum_of_generation t S hfree hgen) _ _ x
  intro is y
  have he : (fun g => action t S (α g) (hmem g) (hτ g) hfree hgen
      (wordInclusion t S hfree is y)) = fun g => wordInclusion t S hfree is
        (completionIsometry (tensorIso t S (α g) (hmem g) (hτ g) is.val) y) := by
    funext g
    exact HilbertDiagonal.onSum_insert _ _ _ _ _ _
  rw [he]
  exact (wordInclusion t S hfree is).continuous.comp
    (StrongContinuity.completion _ (tensorIso_continuous t S α hmem hτ hc is.val) y)

end Kadison.FreeWordAction

end

end
end

end OAI
