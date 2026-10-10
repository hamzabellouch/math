import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeCharts
import OAI.Probability.Ballisticity.Stationary.EpisodeAdapted
import OAI.Probability.Ballisticity.Estimates.StageClassification
import OAI.Probability.Ballisticity.Stationary.EpisodeGlobalRetention

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience
theorem episode_log_bound_local {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hr : StageRadiusOrder r fexp b sfloor) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (hf : 0 ≤ fexp) (hb : 0 ≤ b) (hsfloor : 0 < sfloor)
    (ω : Environment d) (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s)
    (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hκ : ∀ y u, κ ≤ (ω y).1 u)
    (hk : 0 < k) (hbκ : -Real.log κ ≤ b) :
    0 ≤ Real.log (crossingQuenched (realPosition (step e)) 0 t ω).toReal -
      Real.log (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω).toReal ∧
    Real.log (crossingQuenched (realPosition (step e)) 0 t ω).toReal -
      Real.log (crossingQuenched (realPosition (step e)) 0
        (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height ω).toReal ≤
      (BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)+
      2*b*(episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) := by
  let T := (episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height
  have hpos (h : ℕ) : crossingQuenched (realPosition (step e)) 0 h ω ≠ 0 :=
    ne_of_gt ((ENNReal.pow_pos (ENNReal.coe_pos.mpr hκ0) h).trans_le
      (coordinate_survival_lower e ω κ (fun y => hκ y e) h))
  have hfinite (h : ℕ) := crossingQuenched_ne_top (realPosition (step e)) 0 h ω
  have hl := episode_log_algebra (hfinite t) (hfinite T) (hpos t) (hpos T) κ hκ0 b k
    (BoundedInjection.injectionMultiplier (r sfloor)*k+1)
    (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω) hk
    (episode_survival_lower_local e f hef r fexp g χ b sfloor hr hR N t hf hb hsfloor ω hH κ hκ1 hκ)
  constructor
  · have hm := crossingQuenched_antitone (realPosition (step e)) 0 ω
      (a:= (t:ℝ)) (b:= (T:ℝ)) (by exact_mod_cast (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N t ω).le)
    exact sub_nonneg.mpr (Real.log_le_log (ENNReal.toReal_pos (hpos T) (hfinite T))
      (ENNReal.toReal_mono (hfinite t) hm))
  · have hj : 0 ≤ (episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω : ℝ) := by positivity
    dsimp only [T] at hl
    push_cast at hl ⊢
    nlinarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

noncomputable def failsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) (ω : Environment d) : Prop :=
  stageTestMass e f c.height (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
    c.layerProfile (episodeStageH χ b c.scale) j ω < ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))

lemma measurableSet_failsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      {ω | c.failsAt fexp g χ b j ω} := by
  have hm := measurableSet_lt
    (stageTestMass_adapted e f c.height (r (c.scale*Real.exp (-fexp*b)))
      (r (c.scale*Real.exp (g*b))) c.layerProfile c.measurable_layerProfile
      (episodeStageH χ b c.scale) j)
    (measurable_const (a:=ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))))
  convert hm using 1 <;> first | rfl | (rw [Nat.cast_add]; rfl)

lemma failsAt_eq (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) (ω : Environment d) :
    c.failsAt fexp g χ b (c.stop fexp g χ b N ω) ω ↔
      episodeStageFails e f r fexp g χ b N (c.state ω) ω := Iff.rfl

noncomputable def countedNext (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow failed : Bool) : EpisodeChart (k:=k) e f r :=
  { c.next hef fexp g χ b sfloor N j grow with
    event := (c.next hef fexp g χ b sfloor N j grow).event ∩
      {ω | c.failsAt fexp g χ b j ω ↔ failed=true}
    measurable_event := (c.measurable_nextEvent fexp g χ b sfloor N j grow).inter (by
      cases failed
      · simpa only [Bool.false_eq_true,iff_false,Set.compl_ofPred] using (c.measurableSet_failsAt fexp g χ b j).compl
      · simpa only [iff_true] using c.measurableSet_failsAt fexp g χ b j) }

noncomputable def countedBranch (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) : Option (ℕ×Bool×Bool) → EpisodeChart (k:=k) e f r
  | none => c.frozen sfloor N
  | some (j,grow,failed) => c.countedNext hef fexp g χ b sfloor N j grow failed

lemma countedBranch_covers (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (hω : ω∈c.event) :
    ∃ l, ω∈(c.countedBranch hef fexp g χ b sfloor N l).event := by
  obtain ⟨l,hl⟩ := c.branch_covers hef fexp g χ b sfloor N ω hω
  cases l with
  | none => exact ⟨none,hl⟩
  | some l =>
    by_cases hf : c.failsAt fexp g χ b l.1 ω
    · exact ⟨some (l.1,l.2,true),hl,by simpa only [Set.mem_ofPred_eq,iff_true] using hf⟩
    · exact ⟨some (l.1,l.2,false),hl,by simpa only [Set.mem_ofPred_eq,Bool.false_eq_true,iff_false] using hf⟩

lemma countedBranch_state (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l : Option (ℕ×Bool×Bool))
    (hω : ω∈(c.countedBranch hef fexp g χ b sfloor N l).event) :
    ω∈c.event ∧ (c.countedBranch hef fexp g χ b sfloor N l).state ω =
      if EpisodeReady e f r sfloor N (c.state ω)
      then episodeStageNext e f hef r fexp g χ b N (c.state ω) ω else c.state ω := by
  cases l with
  | none => exact c.branch_state hef fexp g χ b sfloor N ω none hω
  | some l => exact c.branch_state hef fexp g χ b sfloor N ω (some (l.1,l.2.1)) hω.1

lemma countedBranch_record (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l : Option (ℕ×Bool×Bool))
    (hω : ω∈(c.countedBranch hef fexp g χ b sfloor N l).event) :
    (if EpisodeReady e f r sfloor N (c.state ω) then 1 else 0 : ℕ) = (if l.isSome then 1 else 0) ∧
    (if EpisodeReady e f r sfloor N (c.state ω) ∧ episodeStageFails e f r fexp g χ b N (c.state ω) ω
      then 1 else 0 : ℕ) = (if (l.map (fun z => z.2.2)).getD false then 1 else 0) := by
  cases l with
  | none =>
    have hn : ¬EpisodeReady e f r sfloor N (c.state ω) := hω.2
    simp only [hn,false_and,ite_false,Option.isSome_none,Option.map_none,Option.getD_none,Bool.false_eq_true,and_self]
  | some l =>
    have hr : EpisodeReady e f r sfloor N (c.state ω) := ⟨hω.1.2.1,hω.1.2.2.1⟩
    have hfail : episodeStageFails e f r fexp g χ b N (c.state ω) ω ↔ l.2.2=true := by
      rw [←c.failsAt_eq fexp g χ b N ω,hω.1.2.2.2.1]
      exact hω.2
    simp only [hr,true_and,ite_true,Option.isSome_some,Option.map_some,Option.getD_some,hfail]

lemma countedBranch_unique (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l m : Option (ℕ×Bool×Bool))
    (hl : ω∈(c.countedBranch hef fexp g χ b sfloor N l).event)
    (hm : ω∈(c.countedBranch hef fexp g χ b sfloor N m).event) : l=m := by
  cases l with
  | none =>
    cases m with
    | none => rfl
    | some m => exact False.elim (hl.2 ⟨hm.1.2.1,hm.1.2.2.1⟩)
  | some l =>
    cases m with
    | none => exact False.elim (hm.2 ⟨hl.1.2.1,hl.1.2.2.1⟩)
    | some m =>
      have hp := c.branch_unique hef fexp g χ b sfloor N ω (some (l.1,l.2.1)) (some (m.1,m.2.1)) hl.1 hm.1
      have hj : l.1=m.1 := congrArg (fun z : ℕ×Bool => z.1) (Option.some.inj hp)
      have hg : l.2.1=m.2.1 := congrArg (fun z : ℕ×Bool => z.2) (Option.some.inj hp)
      have hh := hl.2
      rw [hj] at hh
      have hb : (l.2.2=true) ↔ (m.2.2=true) := hh.symm.trans hm.2
      have hf : l.2.2=m.2.2 := by
        cases h₁ : l.2.2 <;> cases h₂ : m.2.2 <;> simp_all only [Bool.false_eq_true,iff_false,
          iff_true,not_true_eq_false,iff_self]
      exact congrArg some (Prod.ext hj (Prod.ext hg hf))

end EpisodeChart
end DirectionalTransience

end

end OAI
