import OAI.Analysis.KadisonKastler.DerivationExtensionFactor
import OAI.Analysis.KadisonKastler.CyclicSpatialDerivation

namespace OAI

/-! # The concrete generated algebra and its faithful maximal quotient

This constructs the one-implementer extension used in the unital case of
Sakai's argument. Its generation property is retained through the quotient.
No innerness or ideal membership of the implementer is assumed here.
-/

namespace KadisonKastler

noncomputable section

open CuntzPureness

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

def generatedExtensionAlgebra (φ : A →⋆ₐ[ℂ] B) (d : B) : StarSubalgebra ℂ B :=
  (StarAlgebra.adjoin ℂ (Set.range φ ∪ {d})).topologicalClosure

instance generatedExtension_complete (φ : A →⋆ₐ[ℂ] B) (d : B) :
    CompleteSpace (generatedExtensionAlgebra φ d) :=
  inferInstanceAs
    (CompleteSpace (StarAlgebra.adjoin ℂ (Set.range φ ∪ {d})).topologicalClosure)

instance generatedExtension_cstar (φ : A →⋆ₐ[ℂ] B) (d : B) :
    CStarAlgebra (generatedExtensionAlgebra φ d) := {}

theorem generatedExtensionAlgebra_source (φ : A →⋆ₐ[ℂ] B) (d : B) (a : A) :
    φ a ∈ generatedExtensionAlgebra φ d :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩))

theorem generatedExtensionAlgebra_element (φ : A →⋆ₐ[ℂ] B) (d : B) :
    d ∈ generatedExtensionAlgebra φ d :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_singleton d)))

def generatedExtensionEmbedding (φ : A →⋆ₐ[ℂ] B) (d : B) :
    A →⋆ₐ[ℂ] generatedExtensionAlgebra φ d :=
  φ.codRestrict _ (generatedExtensionAlgebra_source φ d)

def generatedExtensionElement (φ : A →⋆ₐ[ℂ] B) (d : B) :
    generatedExtensionAlgebra φ d := ⟨d, generatedExtensionAlgebra_element φ d⟩

theorem generatedExtension_normGenerated (φ : A →⋆ₐ[ℂ] B) (d : B) :
    NormGeneratedExtension (generatedExtensionEmbedding φ d) (generatedExtensionElement φ d) := by
  intro C hC hsource hd
  let S := generatedExtensionAlgebra φ d
  let E : StarSubalgebra ℂ B := C.map S.subtype
  have hEclosed : IsClosed (E : Set B) :=
    (StarSubalgebra.isClosed_topologicalClosure _).isClosedMap_subtype_val _ hC
  have hSE : S ≤ E := by
    apply StarSubalgebra.topologicalClosure_minimal _ hEclosed
    apply StarAlgebra.adjoin_le
    rintro x (⟨a, rfl⟩ | hx)
    · exact ⟨generatedExtensionEmbedding φ d a, hsource a, rfl⟩
    · have hx' : x = d := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨generatedExtensionElement φ d, hd, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hSE x.property
  have hxy : y = x := Subtype.ext he
  rwa [← hxy]

theorem NormGeneratedExtension.map_surjective
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hgen : NormGeneratedExtension φ d)
    {C : Type*} [CStarAlgebra C] (ψ : B →⋆ₐ[ℂ] C)
    (hψ : Function.Surjective ψ) : NormGeneratedExtension (ψ.comp φ) (ψ d) := by
  intro E hE hsource hd
  have hc : Continuous ψ :=
    (ψ.toLinearMap.mkContinuous 1 (fun x => by
      change ‖ψ x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le ψ x)).continuous
  have htop : E.comap ψ = ⊤ :=
    hgen (E.comap ψ) (hE.preimage hc) hsource hd
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hψ y
  change x ∈ E.comap ψ
  rw [htop]
  trivial

theorem exists_generated_derivation_extension
    [Nontrivial A] (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ (B : Type u) (_ : CStarAlgebra B) (_ : Nontrivial B)
      (φ : A →⋆ₐ[ℂ] B) (d : B),
      Function.Injective φ ∧ IsSelfAdjoint d ∧
      (∀ a, φ (D a) = d * φ a - φ a * d) ∧
      NormGeneratedExtension φ d ∧
      (∀ (C : Type u) [CStarAlgebra C] [Nontrivial C]
        (ψ : B →⋆ₐ[ℂ] C), Function.Injective ψ) := by
  obtain ⟨H, _, _, _, _, π, hπ, _, T, hT, hTD⟩ :=
    exists_simple_spatial_derivation hA D hD hstar
  let S := generatedExtensionAlgebra π T
  let φ := generatedExtensionEmbedding π T
  let d := generatedExtensionElement π T
  let : CompleteSpace S := inferInstanceAs
    (CompleteSpace (StarAlgebra.adjoin ℂ (Set.range π ∪ {T})).topologicalClosure)
  let : CStarAlgebra S := inferInstance
  let : Nontrivial S := inferInstance
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  have hd : ∀ a, φ (D a) = d * φ a - φ a * d := fun a => Subtype.ext (hTD a)
  have hdsa : IsSelfAdjoint d := Subtype.ext hT.star_eq
  obtain ⟨J, hJ, hmax⟩ := exists_maximal_proper_closedStarIdeal (B := S)
  let : Nontrivial J.Quotient := closedStarIdeal_quotient_nontrivial J hJ
  let ψ := J.quotientStarHom
  refine ⟨J.Quotient, inferInstance, inferInstance, ψ.comp φ, ψ d,
    simple_quotient_composition_injective hA φ J hJ, hdsa.map ψ, ?_, ?_, ?_⟩
  · intro a
    change ψ (φ (D a)) = ψ d * ψ (φ a) - ψ (φ a) * ψ d
    rw [hd, map_sub, map_mul, map_mul]
  · exact NormGeneratedExtension.map_surjective φ d (generatedExtension_normGenerated π T) ψ
      J.quotientMap_surjective
  · intro C _ _ χ
    exact maximal_closedStarIdeal_quotient_injective J hmax χ

end

end KadisonKastler

end OAI
