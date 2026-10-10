import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesMass

namespace OAI

noncomputable section
namespace Ostmann.Construction
open CanonicalOccurrenceTransport
open scoped BigOperators

def pairedInternalOrigin (seed : List SourceSlot) (l : ℕ) :
    Internal seed l ⊕ Internal seed l → ℕ :=
  Sum.elim (fun i => (internalSource seed i).origin) (fun i => (internalSource seed i).origin)

abbrev PairedInternalSourceDraws (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :=
  ∀ i : Internal seed l ⊕ Internal seed l,(sources (pairedInternalOrigin seed l i)).Sample

instance pairedInternalSourceDrawsFintype (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :
    Fintype (PairedInternalSourceDraws sources seed l) := by
  classical
  exact inferInstanceAs (Fintype (∀ i : Internal seed l ⊕ Internal seed l,
    (sources (pairedInternalOrigin seed l i)).Sample))

def pairedInternalSourcePrior (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :
    FinitePrior (PairedInternalSourceDraws sources seed l) := by
  classical
  exact dependentProductPrior (fun i => (sources (pairedInternalOrigin seed l i)).law)

def pairedInternalDrawsEquiv (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ) :
    PairedInternalSourceDraws sources seed l ≃
      InternalSourceDraws sources seed l × InternalSourceDraws sources seed l where
  toFun z := ⟨fun i => z (.inl i),fun i => z (.inr i)⟩
  invFun z := fun | .inl i => z.1 i | .inr i => z.2 i
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := rfl

@[simp] theorem pairedInternalSourcePrior_mass (sources : SourceFamily) (seed : List SourceSlot)
    (l : ℕ) (z : PairedInternalSourceDraws sources seed l) :
    (pairedInternalSourcePrior sources seed l).mass z =
      (internalSourcePrior sources seed l).mass (fun i => z (.inl i))*
      (internalSourcePrior sources seed l).mass (fun i => z (.inr i)) := by
  classical
  simp only [pairedInternalSourcePrior,internalSourcePrior,dependentProductPrior,
    Fintype.prod_sum_type,pairedInternalOrigin,Sum.elim_inl,Sum.elim_inr]

theorem sum_pairedInternalSourcePrior (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ)
    (G : InternalSourceDraws sources seed l → InternalSourceDraws sources seed l → ℂ) :
    (∑ z : PairedInternalSourceDraws sources seed l,
      ((pairedInternalSourcePrior sources seed l).mass z:ℂ)*
        G (fun i => z (.inl i)) (fun i => z (.inr i))) =
      ∑ x : InternalSourceDraws sources seed l,∑ y : InternalSourceDraws sources seed l,
        ((internalSourcePrior sources seed l).mass x:ℂ)*
          ((internalSourcePrior sources seed l).mass y:ℂ)*G x y := by
  classical
  have hh := Fintype.sum_equiv (pairedInternalDrawsEquiv sources seed l)
    (fun z => ((pairedInternalSourcePrior sources seed l).mass z:ℂ)*
      G (fun i => z (.inl i)) (fun i => z (.inr i)))
    (fun z => ((internalSourcePrior sources seed l).mass z.1:ℂ)*
      ((internalSourcePrior sources seed l).mass z.2:ℂ)*G z.1 z.2)
    (fun z => by rw [pairedInternalSourcePrior_mass,Complex.ofReal_mul]; rfl)
  simpa only [Fintype.sum_prod_type] using hh

theorem sum_pair_choicesMass_eq_source_prior (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (F : HistoryChoices sources seed V l → HistoryChoices sources seed V l → ℂ) :
    (∑ c : HistoryChoices sources seed V l,∑ d : HistoryChoices sources seed V l,
      (choicesMass sources seed V l c:ℂ)*(choicesMass sources seed V l d:ℂ)*F c d) =
      ∑ f : FrequencyChoices V l,∑ g : FrequencyChoices V l,
        ∑ z : PairedInternalSourceDraws sources seed l,
          ((pairedInternalSourcePrior sources seed l).mass z:ℂ)*
            F (assembleHistoryChoices sources seed V l f (fun i => z (.inl i)))
              (assembleHistoryChoices sources seed V l g (fun i => z (.inr i))) := by
  classical
  calc
    _ = ∑ f : FrequencyChoices V l,∑ x : InternalSourceDraws sources seed l,
        ∑ g : FrequencyChoices V l,∑ y : InternalSourceDraws sources seed l,
          ((internalSourcePrior sources seed l).mass x:ℂ)*
            ((internalSourcePrior sources seed l).mass y:ℂ)*
              F (assembleHistoryChoices sources seed V l f x)
                (assembleHistoryChoices sources seed V l g y) := by
      rw [sum_historyChoices_eq]
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro x _
      rw [sum_historyChoices_eq]
      simp only [choicesMass_assemble]
    _ = ∑ f : FrequencyChoices V l,∑ g : FrequencyChoices V l,
        ∑ x : InternalSourceDraws sources seed l,∑ y : InternalSourceDraws sources seed l,
          ((internalSourcePrior sources seed l).mass x:ℂ)*
            ((internalSourcePrior sources seed l).mass y:ℂ)*
              F (assembleHistoryChoices sources seed V l f x)
                (assembleHistoryChoices sources seed V l g y) := by
      apply Finset.sum_congr rfl
      intro f _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro g _
      exact (sum_pairedInternalSourcePrior sources seed l
        (fun x y => F (assembleHistoryChoices sources seed V l f x)
          (assembleHistoryChoices sources seed V l g y))).symm

end Ostmann.Construction

end

end OAI
