import OAI.Probability.SignedSweeps.MarkedPairFibers
import OAI.Probability.SignedSweeps.CoefficientPositivity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

def fiberBlock (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) (z w : Z) : E →ₗ[ℂ] E :=
  fiberEvaluation z ∘ₗ A ∘ₗ (fiberInsertion w).toLinearMap

lemma fiberBlock_positive (A : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E)
    (hA : A.IsPositive) (z : Z) : (fiberBlock A z z).IsPositive := by
  rw [fiberBlock, ← fiberInsertion_adjoint]
  exact hA.adjoint_conj _

lemma fiber_resolution :
    (∑ z : Z, (fiberInsertion (E:=E) z).toLinearMap ∘ₗ fiberEvaluation z) = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro w
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, fiberInsertion_apply,
    Module.End.one_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

lemma fiberBlock_mul (A B : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) (z w : Z) :
    fiberBlock (A * B) z w = ∑ t : Z, fiberBlock A z t * fiberBlock B t w := by
  calc
    _ = fiberEvaluation z ∘ₗ A ∘ₗ (1 : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E) ∘ₗ B ∘ₗ
        (fiberInsertion w).toLinearMap := rfl
    _ = _ := by
      rw [← fiber_resolution]
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, fiberBlock,
        Module.End.mul_apply]

lemma fiberBlock_diagonal_mul {H K : Type*} (col : Z → H) (row : Z → K)
    (hinj : Function.Injective (fun z => (col z, row z)))
    (A B : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E)
    (hA : ∀ z w, col z ≠ col w → fiberBlock A z w = 0)
    (hB : ∀ z w, row z ≠ row w → fiberBlock B z w = 0) (z : Z) :
    fiberBlock (A * B) z z = fiberBlock A z z * fiberBlock B z z := by
  rw [fiberBlock_mul, Finset.sum_eq_single z]
  · intro w _ hw
    by_cases hc : col z = col w
    · have hr : row w ≠ row z := fun hr => hw (hinj (Prod.ext hc.symm hr))
      rw [hB w z hr, mul_zero]
    · rw [hA z w hc, zero_mul]
  · simp

lemma trace_fiber_product {H K : Type*} (col : Z → H) (row : Z → K)
    (hinj : Function.Injective (fun z => (col z, row z)))
    (P : Z → E →ₗ[ℂ] E) (A B : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E)
    (hA : ∀ z w, col z ≠ col w → fiberBlock A z w = 0)
    (hB : ∀ z w, row z ≠ row w → fiberBlock B z w = 0) :
    LinearMap.trace ℂ (HilbertFibers Z E) (fiberDiagonal P * A * B) =
      ∑ z, LinearMap.trace ℂ E (P z * fiberBlock A z z * fiberBlock B z z) := by
  rw [mul_assoc, trace_fiberDiagonal_mul]
  apply Finset.sum_congr rfl
  intro z _
  change LinearMap.trace ℂ E (P z * fiberBlock (A*B) z z) = _
  rw [fiberBlock_diagonal_mul col row hinj A B hA hB, mul_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedWord_fiberBlock {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (z w : MarkedAssignment l n) :
    fiberBlock (markedWordRepresentation h C g) z w =
      if z = moveMarks g w then signedWordRepresentation p C (markedSpinTransport h g w) else 0 := by
  apply LinearMap.ext
  intro x
  change fiberEvaluation z (markedWordRepresentation h C g (fiberInsertion w x)) = _
  rw [markedWordRepresentation_insertion]
  change (fiberInsertion (moveMarks g w) _).ofLp z = _
  rw [fiberInsertion_apply]
  split_ifs <;> rfl

lemma coefficient_fiberBlock {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ) (z w : MarkedAssignment l n) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z w =
      ∑ g : SymmetricGroup n, f g • fiberBlock (markedWordRepresentation h C g) z w := by
  apply LinearMap.ext
  intro x
  simp only [fiberBlock, coefficientAction, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]

lemma marked_fiberBlock_viaEmbedding {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (z : MarkedAssignment l n) (g : SymmetricGroup p) :
    fiberBlock (markedWordRepresentation h C (g.viaEmbedding (markedInjection h z))) z z =
      signedWordRepresentation p C g := by
  rw [markedWord_fiberBlock, moveMarks_viaEmbedding, ite_eq_left rfl, markedSpinTransport_viaEmbedding]

theorem marked_coefficient_compression {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ) (z : MarkedAssignment l n) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z z =
      coefficientAction (signedWordRepresentation p C) (fun g => f (g.viaEmbedding (markedInjection h z))) := by
  rw [coefficient_fiberBlock, coefficientAction]
  let i := Equiv.Perm.viaEmbeddingHom (markedInjection h z)
  have hi : Function.Injective i := viaEmbeddingHom_injective (markedInjection h z)
  calc
    _ = ∑ g ∈ Finset.image i Finset.univ,
        f g • fiberBlock (markedWordRepresentation h C g) z z := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro g _ hg
      have hz : z ≠ moveMarks g z := by
        intro hz
        apply hg
        exact Finset.mem_image.mpr ⟨markedSpinTransport h g z, Finset.mem_univ _,
          markedSpinTransport_viaEmbedding_of_fixed h g z hz.symm⟩
      rw [markedWord_fiberBlock, ite_eq_right hz, smul_zero]
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ he => hi he)]
      apply Finset.sum_congr rfl
      intro g _
      simp only [i, Equiv.Perm.viaEmbeddingHom_apply]
      rw [marked_fiberBlock_viaEmbedding]

def markedRoutes {l n : ℕ} {J : Type*} (route : Fin n → J)
    (z : MarkedAssignment l n) : Fin l → J := route ∘ z

lemma markedRoutes_preserved {l n : ℕ} {J : Type*} (route : Fin n → J)
    (g : SymmetricGroup n) (hg : g ∈ fiberSubgroup route) (z : MarkedAssignment l n) :
    markedRoutes route (moveMarks g z) = markedRoutes route z := by
  funext a
  exact hg (z a)

lemma marked_coefficient_support {p l n : ℕ} {C J : Type*} [Fintype C]
    (h : p+l=n) (route : Fin n → J) (f : SymmetricGroup n → ℂ)
    (hf : ∀ g, g ∉ fiberSubgroup route → f g = 0)
    (z w : MarkedAssignment l n) (hzw : markedRoutes route z ≠ markedRoutes route w) :
    fiberBlock (coefficientAction (markedWordRepresentation h C) f) z w = 0 := by
  rw [coefficient_fiberBlock]
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : g ∈ fiberSubgroup route
  · have hz : z ≠ moveMarks g w := by
      rintro rfl
      exact hzw (markedRoutes_preserved route g hg w)
    rw [markedWord_fiberBlock, ite_eq_right hz, smul_zero]
  · rw [hf g hg, zero_smul]

lemma marked_routes_injective {l n : ℕ} {A B : Type*} (e : Fin n ≃ A × B) :
    Function.Injective (fun z : MarkedAssignment l n =>
      (markedRoutes (fun x => (e x).2) z, markedRoutes (fun x => (e x).1) z)) := by
  intro z w h
  apply Function.Embedding.ext
  intro a
  apply e.injective
  exact Prod.ext (congrFun (congrArg Prod.snd h) a) (congrFun (congrArg Prod.fst h) a)

theorem marked_positive_product_trace_split {u v p l n : ℕ} {A B C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (e : Fin n ≃ A × B) (f k : SymmetricGroup n → ℂ)
    (hf : ∀ g, g ∉ fiberSubgroup (fun x => (e x).2) → f g = 0)
    (hk : ∀ g, g ∉ fiberSubgroup (fun x => (e x).1) → k g = 0) :
    LinearMap.trace ℂ (MarkedWordSpace p l n C)
      (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
        coefficientAction (markedWordRepresentation h C) k) =
      ∑ z : MarkedAssignment l n, LinearMap.trace ℂ (WordSpace p (C ⊕ C))
        (pairTypeProjection hu a b C *
          coefficientAction (signedWordRepresentation p C) (fun g => f (g.viaEmbedding (markedInjection h z))) *
          coefficientAction (signedWordRepresentation p C) (fun g => k (g.viaEmbedding (markedInjection h z)))) := by
  change LinearMap.trace ℂ _ (fiberDiagonal _ * _ * _) = _
  rw [trace_fiber_product (markedRoutes (fun x => (e x).2)) (markedRoutes (fun x => (e x).1))
    (marked_routes_injective e) _ _ _ (marked_coefficient_support h _ f hf)
      (marked_coefficient_support h _ k hk)]
  simp only [marked_coefficient_compression]

lemma marked_coefficient_compression_positive {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) (z : MarkedAssignment l n) :
    (coefficientAction (signedWordRepresentation p C)
      (fun g => f (g.viaEmbedding (markedInjection h z)))).IsPositive := by
  rw [← marked_coefficient_compression h f z]
  apply fiberBlock_positive
  exact unitary_coefficientAction_positive _ (markedWordRepresentation_norm h) f hf

end SignedSweeps
end

end OAI
