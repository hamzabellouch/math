import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsHistory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentatives
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPair

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationRepresentativePatterns
open Construction Construction.CanonicalOccurrenceTransport HistoryPairRows HistoryPairRepresentatives
open CompensationEqualityPatterns Characters.RationalHistory HistorySymbolicEncoding
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

def pairedInternalEquiv (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) :
    Internal seed l ⊕ Internal seed l ≃ Occurrences h k :=
  Equiv.sumCongr (internalEquiv seed h hh) (internalEquiv seed k hk)

@[simp] theorem pairedInternalEquiv_level (seed : List SourceSlot) {l : ℕ} (h k : History l)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k) (i : Internal seed l ⊕ Internal seed l) :
    level h k (pairedInternalEquiv seed h k hh hk i) = pairedHistoryType seed l i := by
  cases i <;> simp only [pairedInternalEquiv,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    level,pairedHistoryType,Sum.elim_inl,Sum.elim_inr,internalEquiv_level]

def natBlockDraw {ι κ : Type*} [Fintype ι] [DecidableEq ι] {τ : ι → ℕ}
    (p : Pattern τ) (b : BlockDraw p κ) (v : κ → ℕ) (hv : Function.Injective v) : BlockDraw p ℕ := by
  refine ⟨fun q => v (b.val q), ?_⟩
  intro q r he
  apply b.property
  apply Prod.ext
  · exact congrArg (fun x : ℕ × ℕ => x.1) he
  · exact hv (congrArg (fun x : ℕ × ℕ => x.2) he)

variable (seed : List SourceSlot) {l : ℕ} (h k : History l)
  (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
  (p : Pattern (pairedHistoryType seed l)) (b : BlockDraw p ℕ)
  (hv : ∀ i, (slot h k (pairedInternalEquiv seed h k hh hk i)).value = expand p b i)

def representativeLabel (i : Internal seed l ⊕ Internal seed l) : Representative h k :=
  HistoryPairRepresentatives.label h k (pairedInternalEquiv seed h k hh hk i)

theorem representativeLabel_surjective : Function.Surjective (representativeLabel seed h k hh hk) :=
  (HistoryPairRepresentatives.label_surjective h k).comp (pairedInternalEquiv seed h k hh hk).surjective

include hv

theorem representativeLabel_eq_iff (i j : Internal seed l ⊕ Internal seed l) :
    representativeLabel seed h k hh hk i = representativeLabel seed h k hh hk j ↔
      CompensationEqualityPatterns.label p i = CompensationEqualityPatterns.label p j := by
  rw [representativeLabel,representativeLabel,HistoryPairRepresentatives.label_eq_iff,
    pairedInternalEquiv_level,pairedInternalEquiv_level,hv i,hv j]
  constructor
  · rintro ⟨ht,hb⟩
    apply b.property
    exact Prod.ext ht hb
  · intro he
    exact ⟨congrArg (blockType p) he,congrArg b.val he⟩

def representativeBlockEquiv : Representative h k ≃ Block p :=
  sameFibersEquiv (representativeLabel seed h k hh hk) (CompensationEqualityPatterns.label p)
    (representativeLabel_surjective seed h k hh hk) (CompensationEqualityPatterns.label_surjective p)
    (representativeLabel_eq_iff seed h k hh hk p b hv)

@[simp] theorem representativeBlockEquiv_label (i : Internal seed l ⊕ Internal seed l) :
    representativeBlockEquiv seed h k hh hk p b hv (representativeLabel seed h k hh hk i) =
      CompensationEqualityPatterns.label p i :=
  sameFibersEquiv_apply _ _ _ _ _ i

theorem representativeBlockEquiv_prime (r : Representative h k) :
    prime h k r = b.val (representativeBlockEquiv seed h k hh hk p b hv r) := by
  obtain ⟨i,rfl⟩ := representativeLabel_surjective seed h k hh hk r
  rw [representativeBlockEquiv_label]
  exact hv i

def representativeFiberEquiv (r : Representative h k) : HistoryPairRepresentatives.Fiber h k r ≃
    CompensationEqualityPatterns.Fiber p (representativeBlockEquiv seed h k hh hk p b hv r) where
  toFun i := ⟨(pairedInternalEquiv seed h k hh hk).symm i.val, by
    rw [← representativeBlockEquiv_label seed h k hh hk p b hv]
    apply congrArg (representativeBlockEquiv seed h k hh hk p b hv)
    simpa only [representativeLabel,Equiv.apply_symm_apply] using i.property⟩
  invFun i := ⟨pairedInternalEquiv seed h k hh hk i.val, by
    apply (representativeBlockEquiv seed h k hh hk p b hv).injective
    exact (representativeBlockEquiv_label seed h k hh hk p b hv i.val).trans i.property⟩
  left_inv i := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _
  right_inv i := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _

theorem representativeBlockEquiv_multiplicity (r : Representative h k) :
    Fintype.card (HistoryPairRepresentatives.Fiber h k r) =
      multiplicity p (representativeBlockEquiv seed h k hh hk p b hv r) :=
  Fintype.card_congr (representativeFiberEquiv seed h k hh hk p b hv r)

theorem representative_product_eq_blocks {M : Type*} [CommMonoid M] (f : ℕ → M) :
    (∏ r : Representative h k, f (prime h k r)) = ∏ q : Block p, f (b.val q) := by
  conv_lhs => arg 2; ext r; rw [representativeBlockEquiv_prime seed h k hh hk p b hv r]
  exact (representativeBlockEquiv seed h k hh hk p b hv).prod_comp (fun q => f (b.val q))

end Ostmann.Arithmetic.HistoryCompensationRepresentativePatterns

end

end OAI
