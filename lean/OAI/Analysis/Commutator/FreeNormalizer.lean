import Mathlib
import OAI.Analysis.Commutator.ConjugationNormalizer
import OAI.Analysis.Commutator.FreeActualCovariance

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_conj_generator (u : unitary D) (k : ι) (a : A) (ha : a∈S k) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv
      (t.functional.gnsStarAlgHom a) =
    t.functional.gnsStarAlgHom (innerFamily f i u k a) := by
  ext x
  let W := innerRepresentation t ht f S i hS hfree hgen u
  change W (t.functional.gnsStarAlgHom a (W.symm x))=_
  have h := action_left_apply t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen k a ha (W.symm x)
  change W (t.functional.gnsStarAlgHom a (W.symm x))=
    t.functional.gnsStarAlgHom (innerFamily f i u k a) (W (W.symm x)) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

lemma innerRepresentation_conj_mem_generated (u : unitary D)
    {a : t.functional.GNS →L[ℂ] t.functional.GNS} (ha : a∈generatedOperators t S) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv a ∈ generatedOperators t S := by
  let α := (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv
  have hle : iSup S ≤ ((generatedOperators t S).comap α.toStarAlgHom).comap
      t.functional.gnsStarAlgHom := by
    refine iSup_le fun k => ?_
    intro b hb
    change α (t.functional.gnsStarAlgHom b) ∈ generatedOperators t S
    rw [innerRepresentation_conj_generator t ht f S i hS hfree hgen u k b hb]
    exact ⟨innerFamily f i u k b,(le_iSup S k) (innerFamily_mem f S i hS u k b hb),rfl⟩
  obtain ⟨b,hb,rfl⟩ := ha
  exact hle hb

lemma innerRepresentation_conj_mem_bicommutant (u : unitary D)
    {a : t.functional.GNS →L[ℂ] t.functional.GNS}
    (ha : a∈Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)) := by
  exact mem_bicommutant_of_maps_generators
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv.toMulEquiv
    (generatedOperators t S : Set _) (fun _ h =>
      innerRepresentation_conj_mem_generated t ht f S i hS hfree hgen u h) ha

lemma innerRepresentation_vacuum (u : unitary D) :
    innerRepresentation t ht f S i hS hfree hgen u (TracialGNS.vacuum t.functional)=
      TracialGNS.vacuum t.functional := by
  exact action_word t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen [] reduced_nil

end Kadison.FreeBlocks

end

end
end

end OAI
