import Mathlib
import OAI.Analysis.WeakInfiniteness.UniversalMapping

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A]

lemma algebraWord_append (x : A) (w z : List Bool) :
    algebraWord x (w ++ z) = algebraWord x w * algebraWord x z := by
  induction w with
  | nil => simp [algebraWord]
  | cons i w ih => simp [algebraWord, ih, mul_assoc]

def wordMonoid (x : A) : Submonoid A where
  carrier := Set.range (algebraWord x)
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro _ _ ⟨w,rfl⟩ ⟨z,rfl⟩
    exact ⟨w++z, algebraWord_append x w z⟩

lemma adjoin_le_wordSpan (x : A) :
    (StarAlgebra.adjoin ℂ {x}).toSubalgebra.toSubmodule ≤
      Submodule.span ℂ (Set.range (algebraWord x)) := by
  rw [StarAlgebra.adjoin_eq_span]
  apply Submodule.span_mono
  change Submonoid.closure ({x} ∪ star {x}) ≤ wordMonoid x
  apply Submonoid.closure_le.mpr
  intro y hy
  have hy' : y = x ∨ star y = x := by simpa using hy
  rcases hy' with rfl | he
  · exact ⟨[true], by simp [algebraWord]⟩
  · exact ⟨[false], by simp [algebraWord, ← he]⟩

lemma exists_polynomial_of_mem_adjoin (x y : A) (hy : y ∈ StarAlgebra.adjoin ℂ {x}) :
    ∃ c : List Bool →₀ ℂ, algebraPolynomial x c = y :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (adjoin_le_wordSpan x hy)

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma universal_graph_bound (v : B) (hv : ‖v‖ ≤ 1)
    (z : UniversalContraction × B)
    (hz : z ∈ closedStarSpan {(universalContractionGenerator, v)}) :
    ‖z.2‖ ≤ ‖z.1‖ := by
  change z ∈ {z : UniversalContraction × B | ‖z.2‖ ≤ ‖z.1‖}
  apply closure_minimal (s := (StarAlgebra.adjoin ℂ {(universalContractionGenerator, v)} : Set _)) ?_ ?_ hz
  · intro z hz
    obtain ⟨c, rfl⟩ := exists_polynomial_of_mem_adjoin _ _ hz
    change ‖(StarAlgHom.snd ℂ UniversalContraction B) (algebraPolynomial _ c)‖ ≤
      ‖(StarAlgHom.fst ℂ UniversalContraction B) (algebraPolynomial _ c)‖
    rw [map_algebraPolynomial, map_algebraPolynomial]
    exact norm_algebraPolynomial_le_universal v hv c
  · exact isClosed_le (continuous_norm.comp continuous_snd) (continuous_norm.comp continuous_fst)

def universalGraph (v : B) : StarSubalgebra ℂ (UniversalContraction × B) :=
  closedStarSpan {(universalContractionGenerator, v)}

instance universalGraphCStar (v : B) : CStarAlgebra (universalGraph v) := closedStarSpanCStar _

def universalGraphFirst (v : B) : universalGraph v →⋆ₐ[ℂ] UniversalContraction :=
  (StarAlgHom.fst ℂ UniversalContraction B).comp (universalGraph v).subtype

lemma universalGraphFirst_isometry (v : B) (hv : ‖v‖ ≤ 1) :
    Isometry (universalGraphFirst v) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  change ‖z.val.1‖ = ‖z.val‖
  rw [Prod.norm_def, max_eq_left (universal_graph_bound v hv z.val z.property)]

lemma universalGraphFirst_surjective (v : B) (hv : ‖v‖ ≤ 1) :
    Function.Surjective (universalGraphFirst v) := by
  let : CompleteSpace (universalGraph v) := (closedStarSpan_closed _).completeSpace_coe
  let φ := universalGraphFirst v
  let S := φ.range.map universalContractionSubalgebra.subtype
  have hS : IsClosed (S : Set ContractionAmbient) := by
    have hi : Isometry (universalContractionSubalgebra.subtype.comp φ) :=
      (isometry_subtype_coe).comp (universalGraphFirst_isometry v hv)
    have he : (S : Set ContractionAmbient) = Set.range (universalContractionSubalgebra.subtype.comp φ) := by
      ext x
      simp only [S]
      change (∃ y, (∃ z, φ z = y) ∧ _ = x) ↔ ∃ z, _ = x
      constructor
      · rintro ⟨y, ⟨z,rfl⟩, rfl⟩; exact ⟨z,rfl⟩
      · rintro ⟨z,rfl⟩; exact ⟨φ z, ⟨z,rfl⟩, rfl⟩
    rw [he]
    exact hi.isClosedEmbedding.isClosed_range
  have hgen : universalOperator ∈ S := by
    refine ⟨universalContractionGenerator, ?_, rfl⟩
    exact ⟨⟨(universalContractionGenerator, v), subset_closedStarSpan _ (Set.mem_singleton _)⟩,rfl⟩
  have hs : universalContractionSubalgebra ≤ S :=
    closedStarSpan_le {universalOperator} S hS (Set.singleton_subset_iff.mpr hgen)
  intro x
  obtain ⟨y,hy,hey⟩ := hs x.property
  obtain ⟨z,hz⟩ := hy
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun y : UniversalContraction => y.val) hz).trans hey

def universalContractionMap (v : B) (hv : ‖v‖ ≤ 1) : UniversalContraction →⋆ₐ[ℂ] B :=
  ((StarAlgHom.snd ℂ UniversalContraction B).comp (universalGraph v).subtype).comp
    (StarAlgEquiv.ofBijective (universalGraphFirst v)
      ⟨(universalGraphFirst_isometry v hv).injective, universalGraphFirst_surjective v hv⟩).symm.toStarAlgHom

@[simp] lemma universalContractionMap_generator (v : B) (hv : ‖v‖ ≤ 1) :
    universalContractionMap v hv universalContractionGenerator = v := by
  let z : universalGraph v :=
    ⟨(universalContractionGenerator, v), subset_closedStarSpan _ (Set.mem_singleton _)⟩
  let e := StarAlgEquiv.ofBijective (universalGraphFirst v)
    ⟨(universalGraphFirst_isometry v hv).injective, universalGraphFirst_surjective v hv⟩
  have he : e z = universalContractionGenerator := rfl
  change (e.symm universalContractionGenerator).val.2 = v
  rw [← he, StarAlgEquiv.symm_apply_apply]

@[simp] lemma universalContractionMap_polynomial (v : B) (hv : ‖v‖ ≤ 1)
    (c : List Bool →₀ ℂ) :
    universalContractionMap v hv (algebraPolynomial universalContractionGenerator c) =
      algebraPolynomial v c := by
  rw [map_algebraPolynomial, universalContractionMap_generator]

end WeakPureInfiniteness
end

end OAI
