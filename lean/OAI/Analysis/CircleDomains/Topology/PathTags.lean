import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! The ambient tagged-path code space and its compact residual-time sections.
An active slot contains a nonempty finite label tuple, its circle levels,
and the two ends of its open time interval. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev TagParameters (n : ℕ) :=
  (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle) × PathTime × PathTime

abbrev TagData := Σ n : ℕ, TagParameters n

def TagSlot := Unit ⊕ TagData

instance : TopologicalSpace TagSlot := inferInstanceAs (TopologicalSpace (Unit ⊕ TagData))

instance : SecondCountableTopology TagSlot :=
  inferInstanceAs (SecondCountableTopology (Unit ⊕ TagData))

instance : MeasurableSpace TagSlot := borel TagSlot

instance : BorelSpace TagSlot := ⟨rfl⟩

def tagLeft : TagSlot → PathTime :=
  Sum.elim (fun _ => ⊤) (fun t => t.2.2.2.1)

def tagRight : TagSlot → PathTime :=
  Sum.elim (fun _ => ⊥) (fun t => t.2.2.2.2)

theorem continuous_tagLeft : Continuous tagLeft :=
  continuous_const.sumElim (continuous_sigma fun _ => continuous_snd.snd.fst)

theorem continuous_tagRight : Continuous tagRight :=
  continuous_const.sumElim (continuous_sigma fun _ => continuous_snd.snd.snd)

abbrev TaggedPath (X : Type*) [TopologicalSpace X] :=
  C(PathTime, X) × (ℕ → TagSlot)

def residualTimeGraph {X : Type*} [TopologicalSpace X] (B : Set X) :
    Set (TaggedPath X × PathTime) :=
  {q | q.1.1 q.2 ∈ B ∧ ∀ k,
    q.2 ≤ tagLeft (q.1.2 k) ∨ tagRight (q.1.2 k) ≤ q.2}

theorem isClosed_residualTimeGraph {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsClosed B) : IsClosed (residualTimeGraph B) := by
  apply IsClosed.inter
  · exact hB.preimage (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))
  · change IsClosed {q : TaggedPath X × PathTime | ∀ k,
      q.2 ≤ tagLeft (q.1.2 k) ∨ tagRight (q.1.2 k) ≤ q.2}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro k
    exact (isClosed_le (continuous_subtype_val.comp continuous_snd)
      (continuous_subtype_val.comp (continuous_tagLeft.comp
        ((continuous_apply k).comp continuous_fst.snd)))).union
      (isClosed_le (continuous_subtype_val.comp (continuous_tagRight.comp
        ((continuous_apply k).comp continuous_fst.snd)))
        (continuous_subtype_val.comp continuous_snd))

def residualTimes {X : Type*} [TopologicalSpace X] (B : Set X) (Γ : TaggedPath X) :
    Set PathTime := {t | (Γ, t) ∈ residualTimeGraph B}

theorem isCompact_residualTimes {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsClosed B) (Γ : TaggedPath X) : IsCompact (residualTimes B Γ) :=
  ((isClosed_residualTimeGraph hB).preimage (continuous_const.prodMk continuous_id)).isCompact

theorem residualTimes_eq {X : Type*} [TopologicalSpace X] (B : Set X) (Γ : TaggedPath X) :
    residualTimes B Γ = Γ.1 ⁻¹' B \ ⋃ k, Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
  ext t
  simp only [residualTimes, residualTimeGraph, mem_ofPred_eq, mem_sdiff,
    mem_preimage, mem_iUnion, mem_Ioo, not_exists, not_and_or, not_lt]

end CircleDomainRigidity

end

end OAI
