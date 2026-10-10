import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StoredForms

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

theorem finish_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (fuel : ℕ) (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ))
    (hfuel : (F\s.opened).card≤fuel) :
    let r := finish distance F v lam fuel s
    CountedTrace (PlainOpening loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
    (F\r.1.opened).card+r.2.length=(F\s.opened).card ∧
    s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
    r.1.phase=s.phase ∧ PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real := by
  induction fuel generalizing s with
  | zero =>
    simp only [finish,List.length_nil,Nat.add_zero]
    refine ⟨.nil _,trivial,Finset.Subset.refl _,Finset.subset_union_left,trivial,?_⟩
    intro i hi hin
    have hh : i∈F\s.opened := Finset.mem_sdiff.mpr ⟨hi,hin⟩
    have hh' := Finset.card_pos.mpr ⟨i,hh⟩
    omega
  | succ fuel ih =>
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i)) with
    | none =>
      simp only [finish,he,List.length_nil,Nat.add_zero]
      exact ⟨.nil _,trivial,Finset.Subset.refl _,Finset.subset_union_left,trivial,
        first_none_maximal loc distance hd F v lam s hv hv1 hz he⟩
    | some e =>
      have hop := first_plain loc distance hd F v lam s _ e hv hv1 hz he
      have hdrop : (F\(update distance v s e).opened).card+1=(F\s.opened).card := hop.remaining_drop
      have hs := first_some distance F s.opened v s.phase lam _ e he
      obtain ⟨htrace,hcount,hlo,hhi,hphase,hmax⟩ :=
        ih (update distance v s e) hz (by omega)
      simp only [finish,he,List.length_cons]
      refine ⟨.cons hop htrace,by omega,?_,?_,hphase,hmax⟩
      · exact (Finset.subset_insert _ _).trans hlo
      · apply hhi.trans
        exact Finset.union_subset (Finset.insert_subset (Finset.mem_union_right _ hs.1)
          Finset.subset_union_left) Finset.subset_union_right

theorem complete_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ)) :
    let r := finish distance F v lam F.card s
    CountedTrace (PlainOpening loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
    r.2.length≤F.card ∧ (F\r.1.opened).card+r.2.length=(F\s.opened).card ∧
    s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
    r.1.phase=s.phase ∧ PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real := by
  have hf := Finset.card_le_card (Finset.sdiff_subset : F\s.opened⊆F)
  obtain ⟨ht,hc,hlo,hhi,hz',hm⟩ := finish_spec loc distance hd F v lam hv hv1 F.card s hz hf
  exact ⟨ht,by omega,hc,hlo,hhi,hz',hm⟩

end MetricKMedianRecovery.RationalPhase

namespace MetricKMedianRecovery.OrdinaryProducer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive OrdinaryStep (loc : D → X) (F : Finset X) (v lam : ℝ) :
    ExecutionState D X → ExecutionState D X → Prop
  | opening {s e : ExecutionState D X} (h : PlainOpening loc F v lam s e) : OrdinaryStep loc F v lam s e
  | advance (s : ExecutionState D X) (h : PhaseMaximal loc F v lam s) :
      OrdinaryStep loc F v lam s (phaseUpdate loc (1-3*v) (1+v^2) s)

namespace OrdinaryStep
variable {loc : D → X} {F : Finset X} {v lam : ℝ} {s e : ExecutionState D X}
lemma atomic (h : OrdinaryStep loc F v lam s e) : AtomicStep loc F v lam 0 s e := by
  cases h with
  | opening h => exact h.atomic
  | advance h => exact AtomicStep.update _ h
lemma opened_in (h : OrdinaryStep loc F v lam s e) (hs : s.opened ⊆ F) : e.opened ⊆ F := by
  cases h with
  | opening h => exact h.opened_in hs
  | advance => exact hs
end OrdinaryStep

end MetricKMedianRecovery.OrdinaryProducer

end OAI
