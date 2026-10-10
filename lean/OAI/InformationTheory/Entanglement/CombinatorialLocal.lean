import OAI.InformationTheory.Entanglement.CombinatorialOrder
import OAI.InformationTheory.Entanglement.ParityObstruction

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace FiniteConstruction
open ChannelCompletion

def trivial (a : Outcome) : Mat Four := if a=(1,1) then 1 else 0
def localProjection (S : Eight) (q : Question) (a : Outcome) : Mat Four :=
  match contextAt S q with
  | some t => h t a
  | none => trivial a
lemma localProjection_six (S : Eight) (hS : OrthogonalEight S) (t : Fin 6) (a : Outcome) :
    localProjection S (six S t) a=h t a := by
  simp only [localProjection,contextAt_six S hS]
lemma localProjection_hermitian (S : Eight) (q : Question) (a : Outcome) :
    (localProjection S q a).IsHermitian := by
  unfold localProjection
  cases contextAt S q with
  | none => unfold trivial; split_ifs <;> simp
  | some t => exact h_hermitian t a
lemma localProjection_real (S : Eight) (q : Question) (a : Outcome) (i j : Four) :
    star (localProjection S q a i j)=localProjection S q a i j := by
  unfold localProjection
  cases contextAt S q with
  | none => unfold trivial; split_ifs <;> simp [Matrix.one_apply]
  | some t => exact h_real t a i j
lemma localProjection_idempotent (S : Eight) (q : Question) (a : Outcome) :
    localProjection S q a*localProjection S q a=localProjection S q a := by
  unfold localProjection
  cases contextAt S q with
  | none => unfold trivial; split_ifs <;> simp
  | some t => exact h_idempotent t a
lemma localProjection_orthogonal (S : Eight) (q : Question) (a b : Outcome) (hab : a ≠ b) :
    localProjection S q a*localProjection S q b=0 := by
  unfold localProjection
  cases contextAt S q with
  | none => unfold trivial; split_ifs <;> simp_all
  | some t => exact h_orthogonal t a b hab
lemma localProjection_complete (S : Eight) (q : Question) :
    ∑ a, localProjection S q a=1 := by
  unfold localProjection
  cases contextAt S q with
  | none => simp [trivial]
  | some t => exact h_complete t
lemma localProjection_commute_same (S : Eight) (q : Question) (a b : Outcome) :
    localProjection S q a*localProjection S q b=
      localProjection S q b*localProjection S q a := by
  by_cases he : a=b
  · subst b; rfl
  · rw [localProjection_orthogonal S q a b he,localProjection_orthogonal S q b a (Ne.symm he)]
lemma both_contexts_orthogonal (S : Eight) (q r : Question) (t v : Fin 6)
    (hq : contextAt S q=some t) (hr : contextAt S r=some v) (hqr : q ≠ r) :
    ProjectionCriterion.correlation u q r=0 := by
  obtain ⟨hS,ht⟩ := contextAt_some S q t hq
  obtain ⟨_,hv⟩ := contextAt_some S r v hr
  apply hS q (ht ▸ six_mem S t) r (hv ▸ six_mem S v) hqr
lemma localProjection_commute (S : Eight) (q r : Question) (a b : Outcome)
    (hc : ProjectionCriterion.correlation u q r ≠ 0) :
    localProjection S q a*localProjection S r b=
      localProjection S r b*localProjection S q a := by
  by_cases hqr : q=r
  · subst r; exact localProjection_commute_same S q a b
  unfold localProjection
  cases hq : contextAt S q with
  | none => unfold trivial; split_ifs <;> simp
  | some t =>
    cases hr : contextAt S r with
    | none => unfold trivial; split_ifs <;> simp
    | some v => exact (hc (both_contexts_orthogonal S q r t v hq hr hqr)).elim
end FiniteConstruction

end

end OAI
