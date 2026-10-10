import OAI.Combinatorics.ContingencyTables.Transport.ContextWeightedEnumeration
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPrefixEnergies
import OAI.Combinatorics.ContingencyTables.Transport.FiniteChoiceFibres

namespace OAI

/-! # Literal finite choice fibres equal the transport child sums -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily
open FirstPaperContextTransport FirstPaperPhysicalMarginal ExcessContextProfiles SmallGraphProfiles
open FiniteExposureVariance
open IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def rawChoice (small : I → J → Bool) (U : ℕ) (x : Cells small → Fin (U+1)) :
    SmallProfile small := fun p => if p.2 then U-(x p.1).val else (x p.1).val

def earlierChoices (small : I → J → Bool) (s : I×J) (U : ℕ)
    (x : Cells small → Fin (U+1)) : Earlier small s → Fin (U+1) := fun a => x a.val

omit [Fintype I] [Fintype J] in
lemma earlierChoices_eq_iff (small : I → J → Bool) (s : I×J) (U : ℕ)
    (x : Cells small → Fin (U+1)) (τ : Earlier small s → Fin (U+1)) :
    earlierChoices small s U x=τ ↔ ∀ a : Earlier small s,x a.val=τ a :=
  funext_iff

def ChoiceContext (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1)) :=
  {x : Cells small → Fin (U+1) // earlierChoices small s U x=τ ∧ x ⟨s,hs⟩=k}

noncomputable instance choiceContextFintype (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ) (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1)) :
    Fintype (ChoiceContext small s hs U τ k) := by unfold ChoiceContext; infer_instance

noncomputable def choiceContextEquiv (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (U : ℕ) (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1)) :
    (Later small s → Fin (U+1)) ≃ ChoiceContext small s hs U τ k where
  toFun y := ⟨splitChoices small s hs U τ k y,funext (splitChoices_prefix small s hs U τ k y),
    splitChoices_special small s hs U τ k y⟩
  invFun x := fun a => x.val a.val
  left_inv y := by funext a; exact splitChoices_later small s hs U τ k y a
  right_inv x := by
    apply Subtype.ext
    funext a
    obtain ⟨v,rfl⟩ := (cellSplitEquiv small s hs).surjective a
    rcases v with p|(_|t)
    · exact (splitChoices_prefix small s hs U τ k _ p).trans (congrFun x.property.1 p).symm
    · exact (splitChoices_special small s hs U τ k _).trans x.property.2.symm
    · exact splitChoices_later small s hs U τ k _ t

lemma choice_fibre_sum (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (U : ℕ) (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    (F : (Cells small → Fin (U+1)) → ℝ) :
    (∑ x,fibreWeight (fibreWeight F (earlierChoices small s U) τ) (fun x => x ⟨s,hs⟩) k x)=
      ∑ x : ChoiceContext small s hs U τ k,F x.val := by
  exact double_fibre_sum F (earlierChoices small s U) (fun x => x ⟨s,hs⟩) τ k

omit [Fintype I] [Fintype J] in
lemma prefixChoices_extension (small : I → J → Bool) (s : I×J) (U : ℕ)
    (τ : Earlier small s → Fin (U+1)) :
    prefixChoices small s (prefixExtension small s U τ) U (prefixExtension_bounded small s U τ)=τ := by
  funext a
  apply Fin.ext
  exact prefixExtension_at small s U τ a

/-- The child mass and every child moment are the actual finite fibre
sums of balanced physical choices, retaining all large completions. -/
theorem eliminate_context_eq_choice_fibre (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (τ : Earlier small s → Fin (U+1)) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) (F : SmallProfile small → ℝ) :
    eliminate (widths (fun _ : Fin n => U))
      (fun p => F (assemble small s hs (prefixExtension small s U τ) U e p)) (childProfile U k.val)=
      ∑ x,fibreWeight (fibreWeight (fun x => F (rawChoice small U x))
        (earlierChoices small s U) τ) (fun x => x ⟨s,hs⟩) k x := by
  rw [eliminate_context_eq_weighted_sum small B s hs _ U hB
    (prefixExtension_bounded small s U τ),choice_fibre_sum]
  have he := Fintype.sum_equiv
    (balancedContextEquiv small B s hs (prefixExtension small s U τ) U hB
      (prefixExtension_bounded small s U τ) k)
    (fun y => F (rawChoice small U (splitChoices small s hs U τ k y)))
    (fun z => F (naturalProfile z.val)) (fun y => by
      change F (rawChoice small U (splitChoices small s hs U τ k y))=
        F (rawChoice small U (splitChoices small s hs U
          (prefixChoices small s (prefixExtension small s U τ) U (prefixExtension_bounded small s U τ)) k y))
      rw [prefixChoices_extension])
  have hc := Fintype.sum_equiv (choiceContextEquiv small s hs U τ k)
    (fun y => F (rawChoice small U (splitChoices small s hs U τ k y)))
    (fun x => F (rawChoice small U x.val)) (fun _ => rfl)
  exact he.symm.trans hc

end ContingencyTables.SmallContextEnumeration

end OAI
