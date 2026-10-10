import OAI.Analysis.Quantum.DimensionTen.GaloisCertificate
import OAI.Analysis.Quantum.DimensionTen.LowBasis

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

abbrev K := fQ.SplittingField
instance : NumberField K := NumberField.of_module_finite ℚ K
instance : IsSplittingField ℚ K fQ := IsSplittingField.splittingField fQ
instance : IsGalois ℚ K := IsGalois.of_separable_splitting_field (p := fQ) F_irreducible.separable

lemma F_map_K : F.map (algebraMap ℤ K) = fQ.map (algebraMap ℚ K) := by
  change F.map (algebraMap ℤ K) = (F.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K)
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K]
lemma F_separable_K : (F.map (algebraMap ℤ K)).Separable := by
  rw [F_map_K]; exact F_irreducible.separable.map
lemma F_splits_K : (F.map (algebraMap ℤ K)).Splits := by
  rw [F_map_K]; exact SplittingField.splits fQ
lemma roots_card_K : Fintype.card (F.rootSet K) = 20 :=
  (roots_card_int F F_monic F_separable_K F_splits_K).trans F_degree

lemma aroot_iff_root {R : Type*} [Field R] [Algebra ℚ R] (x : R) :
    x ∈ fQ.aroots R ↔ x ∈ F.rootSet R := by
  let : CharZero R := Algebra.charZero_of_charZero ℚ R
  rw [mem_aroots, mem_rootSet]
  have h : aeval x fQ = aeval x F := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ R, aeval_def]
  constructor
  · intro hx; exact ⟨F_monic.ne_zero, h ▸ hx.2⟩
  · intro hx; exact ⟨F_irreducible.ne_zero, h.symm ▸ hx.2⟩

def embeddingRootEquiv {R : Type*} [Field R] [Algebra ℚ R] :
    (L →ₐ[ℚ] R) ≃ F.rootSet R :=
  (AdjoinRoot.equiv R ℚ fQ F_irreducible.ne_zero).trans
    (Equiv.subtypeEquivRight aroot_iff_root)

lemma embeddingRootEquiv_apply {R : Type*} [Field R] [Algebra ℚ R] (σ : L →ₐ[ℚ] R) :
    (embeddingRootEquiv σ : R) = σ (AdjoinRoot.root fQ) := rfl

lemma embeddings_card_K : Fintype.card (L →ₐ[ℚ] K) = 20 :=
  (Fintype.card_congr (embeddingRootEquiv (R := K))).trans roots_card_K

def embeddingsK : Fin 20 ≃ (L →ₐ[ℚ] K) :=
  (Fintype.equivFinOfCardEq embeddings_card_K).symm

def complexEmbedding : K →ₐ[ℚ] ℂ := IsAlgClosed.lift

lemma finrank_L : Module.finrank ℚ L = 20 := by
  simpa using Module.finrank_eq_card_basis basis

lemma embeddings_card_complex : Fintype.card (L →ₐ[ℚ] ℂ) = 20 :=
  (AlgHom.card ℚ L ℂ).trans finrank_L

lemma complex_embeddings_bijective :
    Function.Bijective (fun i : Fin 20 => complexEmbedding.comp (embeddingsK i)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simpa using embeddings_card_complex.symm⟩
  intro i j hij
  apply embeddingsK.injective
  apply DFunLike.ext
  intro a
  exact complexEmbedding.injective (congrArg (fun σ : L →ₐ[ℚ] ℂ => σ a) hij)

def embeddingsC : Fin 20 ≃ (L →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective _ complex_embeddings_bijective

lemma galois_permute (π : Equiv.Perm (Fin 20)) :
    ∃ σ : Gal(K/ℚ), ∀ i, σ.toAlgHom.comp (embeddingsK i) = embeddingsK (π i) := by
  classical
  let e := embeddingsK.trans (embeddingRootEquiv (R := K))
  let p : Equiv.Perm (F.rootSet K) := (e.symm.trans π).trans e
  obtain ⟨σ, hσ⟩ := root_action_full_symmetric F F_monic F_separable_K F_splits_K
    roots_card_K F_reduction_41 F_reduction_131 F_reduction_139 p
  refine ⟨σ, fun i => ?_⟩
  apply (embeddingRootEquiv (R := K)).injective
  apply Subtype.ext
  have hi := congrArg (fun q : Equiv.Perm (F.rootSet K) => (q (e i) : K)) hσ
  change σ (e i : K) = (e (π (e.symm (e i))) : K) at hi
  rw [e.symm_apply_apply] at hi
  exact hi

end DimensionTen.Border

end
end

end OAI
