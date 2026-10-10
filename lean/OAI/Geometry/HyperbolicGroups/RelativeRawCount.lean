import Mathlib
import OAI.Geometry.HyperbolicGroups.ActualRawCount
import OAI.Geometry.HyperbolicGroups.RelativeTriangleTransport
import OAI.Geometry.HyperbolicGroups.RelativeContact
import OAI.Geometry.HyperbolicGroups.RelativePayment
import OAI.Geometry.HyperbolicGroups.RelativeFaceSide

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev DecorationSideIndex := Σ k : Square n w ⊕ Six n d,
  KindFace n w d ell hell word c hc f P select (.inr (.inr k)) × Fin ((frozenBoundary n w d).size (.inr k))

def decorationRawDart (p : DecorationSideIndex n w d ell hell word c hc f P select) : P.Dart :=
  frozenFaceDart n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2

lemma decorationRawDart_injective : Function.Injective
    (decorationRawDart n w d ell hell word c hc f P select hm) := by
  rintro ⟨k,F,j⟩ ⟨k',F',j'⟩ hh
  obtain ⟨o,ho⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr k) F j
  obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr k') F' j'
  have he := congrArg P.index hh
  change P.index (frozenFaceDart n w d ell hell word c hc f P select hm (.inr k) F j) =
    P.index (frozenFaceDart n w d ell hell word c hc f P select hm (.inr k') F' j') at he
  rw [ho,ho'] at he
  have hk : k = k' := Sum.inr.inj (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj he)))
  subst k'
  exact Sigma.ext rfl (heq_of_eq (frozenFaceDart_injective n w d ell hell word c hc f P select hm (.inr k) hh))

lemma decorationRawDart_raw (p : DecorationSideIndex n w d ell hell word c hc f P select) :
    rawDart n w d ell hell word c hc f P (decorationRawDart n w d ell hell word c hc f P select hm p) := by
  obtain ⟨o,ho⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2
  unfold rawDart decorationRawDart
  rw [ho]
  rcases p with ⟨k,F,j⟩
  rcases k with k | k
  · change Fin 4 at j
    fin_cases j <;> cases o <;> rfl
  · cases o <;> rfl

abbrev RawAccountIndex := AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕
  (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕
    DecorationSideIndex n w d ell hell word c hc f P select)

def accountDart : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad → P.Dart :=
  Sum.elim (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad)
    (Sum.elim (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad)
      (decorationRawDart n w d ell hell word c hc f P select hm))

lemma accountDart_injective (hb : P.NoBigon) : Function.Injective
    (accountDart n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q hh
  have hi := congrArg P.index hh
  rcases p with p | (p | p) <;> rcases q with q | (q | q)
  all_goals dsimp only [accountDart,Sum.elim,decorationRawDart] at hh hi
  · exact congrArg Sum.inl (paymentRawDart_injective n w d ell hell word c hc f P select hs hb hm hred hrad hh)
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad q
    change P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    obtain ⟨o,hg⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr q.1) q.2.1 q.2.2
    change P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad q
    obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
    change P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · exact congrArg (Sum.inr ∘ Sum.inl) (triangleRawDart_injective n w d ell hell word c hc f P select hs hm hred hrad hh)
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
    obtain ⟨o',hk⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr q.1) q.2.1 q.2.2
    change P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [hg,hk] at hi
    have he := congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj hi))
    cases he
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad q
    obtain ⟨o,hg⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2
    change P.index (frozenFaceDart _ _ _ _ _ _ _ _ _ _ _ _ _ p.2.1 p.2.2) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad q
    obtain ⟨o',hk⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2
    change P.index (frozenFaceDart _ _ _ _ _ _ _ _ _ _ _ _ _ p.2.1 p.2.2) = _ at hi
    rw [hg,hk] at hi
    have he := congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj hi))
    cases he
  · exact congrArg (Sum.inr ∘ Sum.inr) (decorationRawDart_injective n w d ell hell word c hc f P select hm hh)

lemma accountDart_selected (p : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    selectedDart n w d ell hell word c hc f P select (accountDart n w d ell hell word c hc f P select hs hm hred hrad p) := by
  rcases p with p | (p | p)
  · exact payment_selected n w d ell hell word c hc f P select hs hm hred hrad p
  · change select (P.faceClass (P.pairing.face _)) = true
    rw [P.faceClass_apply]
    exact triangle_selected n w d ell hell word c hc f P select hs hm hred hrad p
  · exact frozenFaceDart_selected n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2

lemma accountDart_raw (hb : P.NoBigon)
    (p : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    rawDart n w d ell hell word c hc f P (accountDart n w d ell hell word c hc f P select hs hm hred hrad p) := by
  rcases p with p | (p | p)
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    change isLetter n w ((target n w d ell hell word c hc f).label (P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p))) = true
    rw [ha]
    cases ho : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p <;> rfl
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
    change isLetter n w ((target n w d ell hell word c hc f).label (P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p))) = true
    rw [hg]
    cases o <;> rfl
  · exact decorationRawDart_raw n w d ell hell word c hc f P select hm p

lemma actual_raw_account_le (hb : P.NoBigon) :
    Fintype.card (RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad) ≤
      Fintype.card (ActualRawSide n w d ell hell word c hc f P select) := by
  let g : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad → ActualRawSide n w d ell hell word c hc f P select :=
    fun p => ⟨accountDart n w d ell hell word c hc f P select hs hm hred hrad p,
      accountDart_raw n w d ell hell word c hc f P select hs hm hred hrad hb p,
      accountDart_selected n w d ell hell word c hc f P select hs hm hred hrad p⟩
  exact Fintype.card_le_of_injective g (fun _ _ hh =>
    accountDart_injective n w d ell hell word c hc f P select hs hm hred hrad hb (congrArg Subtype.val hh))

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
