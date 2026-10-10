import OAI.Probability.SignedSweeps.PairConstituents
import OAI.Probability.SignedSweeps.InjectionRestriction
import OAI.Probability.SignedSweeps.MarkedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedSpinTransport_viaEmbedding_of_fixed {p l n : ℕ} (h : p+l=n)
    (g : SymmetricGroup n) (z : MarkedAssignment l n) (hg : moveMarks g z = z) :
    (markedSpinTransport h g z).viaEmbedding (markedInjection h z) = g := by
  apply Equiv.ext
  intro i
  obtain ⟨i,rfl⟩ := (markedAllSites h z).surjective i
  cases i with
  | inl i =>
    rw [markedAllSites_left, Equiv.Perm.viaEmbedding_apply]
    simpa only [hg] using markedSpinTransport_sites h g z i
  | inr a =>
    rw [markedAllSites_right, Equiv.Perm.viaEmbedding_apply_of_notMem]
    · exact (congrArg (fun w : MarkedAssignment l n => w a) hg).symm
    · rintro ⟨i,hi⟩
      exact markedInjection_avoids h z i ⟨a,hi.symm⟩

def markedPairEmbeddingHom {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    SymmetricGroup u × SymmetricGroup v →* SymmetricGroup n :=
  (Equiv.Perm.viaEmbeddingHom (markedInjection h z)).comp
    (pairEmbeddingHom (allocationEquiv hu S))

lemma pairEmbeddingHom_injective {u v p : ℕ} (e : Fin u ⊕ Fin v ≃ Fin p) :
    Function.Injective (pairEmbeddingHom e) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  have he' : a.sumCongr b = c.sumCongr d := e.permCongr.injective he
  apply Prod.ext
  · apply Equiv.ext
    intro i
    exact Sum.inl_injective (congrArg (fun t : Equiv.Perm (Fin u ⊕ Fin v) => t (Sum.inl i)) he')
  · apply Equiv.ext
    intro i
    exact Sum.inr_injective (congrArg (fun t : Equiv.Perm (Fin u ⊕ Fin v) => t (Sum.inr i)) he')

lemma markedPairEmbeddingHom_injective {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    Function.Injective (markedPairEmbeddingHom hu h z S) :=
  (viaEmbeddingHom_injective (markedInjection h z)).comp
    (pairEmbeddingHom_injective (allocationEquiv hu S))

lemma markedPair_range_of_preserves {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) (g : SymmetricGroup n)
    (hz : moveMarks g z = z)
    (hS : ∀ i ∈ S.1, markedSpinTransport h g z i ∈ S.1) :
    g ∈ Set.range (markedPairEmbeddingHom hu h z S) := by
  let t := markedSpinTransport h g z
  let e := allocationEquiv hu S
  obtain ⟨a,b,hab⟩ := allocation_factorEquiv hu S (e.trans t)
    (fun i => hS _ (allocationEquiv_left_mem hu S i))
  have ht : t = e.permCongr (a.sumCongr b) := by
    apply Equiv.ext
    intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    have hi := Equiv.congr_fun hab i
    change t (e i) = _ at hi
    simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.trans_apply] using hi
  refine ⟨(a,b),?_⟩
  change (e.permCongr (a.sumCongr b)).viaEmbedding (markedInjection h z) = g
  rw [← ht]
  exact markedSpinTransport_viaEmbedding_of_fixed h g z hz

def markedPairInsertion {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (_h : p+l=n) (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    (WordSpace u C ⊗[ℂ] WordSpace v C) →ₗᵢ[ℂ] MarkedWordSpace p l n C :=
  (fiberInsertion z).comp (pairWordEmbedding (allocationEquiv hu S))

lemma inner_fiberInsertion {Z E : Type*} [Fintype Z] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (z w : Z) (x y : E) :
    inner ℂ (fiberInsertion z x) (fiberInsertion w y) = if z = w then inner ℂ x y else 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single z]
  · simp only [fiberInsertion_apply, ite_true]
    split_ifs
    · rfl
    · simp only [inner_zero_right]
  · intro k _ hk
    simp only [fiberInsertion_apply, ite_eq_right hk, inner_zero_left]
  · simp

lemma pairWord_inner_signed_off {u v p : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (S : EvenAllocation u p) (g : SymmetricGroup p)
    (hg : ¬ ∀ i ∈ S.1, g i ∈ S.1)
    (x y : WordSpace u C ⊗[ℂ] WordSpace v C) :
    inner ℂ (pairWordEmbedding (allocationEquiv hu S) x)
      (signedWordRepresentation p C g (pairWordEmbedding (allocationEquiv hu S) y)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : wordEvenSites w = S.1
  · have hw' : wordEvenSites (w ∘ g) ≠ S.1 := by
      intro hw'
      apply hg
      intro i hi
      have he : i ∈ wordEvenSites (w ∘ g) := by rwa [hw']
      rw [wordEvenSites_comp_mem, hw] at he
      exact he
    simp only [signedWordRepresentation_apply, pairWordEmbedding_off hu S y _ hw',
      mul_zero, inner_zero_right]
  · rw [pairWordEmbedding_off hu S x w hw, inner_zero_left]

theorem markedPairInsertion_off {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (g : SymmetricGroup n) (hg : g ∉ Set.range (markedPairEmbeddingHom hu h z S))
    (x y : WordSpace u C ⊗[ℂ] WordSpace v C) :
    inner ℂ (markedPairInsertion hu h z S x)
      (markedWordRepresentation h C g (markedPairInsertion hu h z S y)) = 0 := by
  change inner ℂ (fiberInsertion z (pairWordEmbedding _ x))
    (markedWordRepresentation h C g (fiberInsertion z (pairWordEmbedding _ y))) = 0
  rw [markedWordRepresentation_insertion, inner_fiberInsertion]
  split_ifs with hz
  · apply pairWord_inner_signed_off
    exact fun hS => hg (markedPair_range_of_preserves hu h z S g hz.symm hS)
  · rfl

end SignedSweeps
end

end OAI
