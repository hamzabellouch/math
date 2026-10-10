import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.GrowthProcess
import OAI.Probability.CriticalPercolation.Gluing.StoredPrediction

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

def actual (n : ℕ) (ω : Set E) : GrowthState := P.rule.state n (P.rule.codeOf n ω)

lemma actual_succ (n : ℕ) (ω : Set E) :
    P.actual (n+1) ω=(P.actual n ω).advance n
      (if ω∈P.accepted n (P.actual n ω) then true else false) := rfl

lemma actual_good_mono (ω : Set E) : Monotone (fun n => ((P.actual n ω).good : Set Site)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [P.actual_succ]
  exact GrowthState.good_mono _ _ _

lemma actual_root (n : ℕ) (ω : Set E) : (0,0)∈(P.actual n ω).good :=
  P.state_valid n (P.rule.codeOf n ω) |>.1

def allGood (ω : Set E) : Set Site := ⋃ n, ((P.actual n ω).good : Set Site)

lemma allGood_root (ω : Set E) : (0,0)∈P.allGood ω := Set.mem_iUnion.mpr ⟨0,P.actual_root 0 ω⟩

lemma allGood_quadrant (ω : Set E) {v : Site} (hv : v∈P.allGood ω) : quadrant v := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
  exact P.state_valid n (P.rule.codeOf n ω) |>.2.1 v hn |>.1

lemma actual_good_birth (n : ℕ) (ω : Set E) {v : Site} (hv : v∈(P.actual n ω).good) :
    v=(0,0) ∨ ∃ k, v=slotSite k ∧ v∈(P.actual (k+1) ω).good := by
  induction n with
  | zero => exact Or.inl (by simpa [actual,DecisionRule.state,rule,GrowthState.initial] using hv)
  | succ n ih =>
    have hvo := hv
    rw [P.actual_succ] at hv
    change v∈(if (incoming n (P.actual n ω).good).isSome ∧
      (if ω∈P.accepted n (P.actual n ω) then true else false)=true
      then insert (slotSite n) (P.actual n ω).good else (P.actual n ω).good) at hv
    by_cases ha : (incoming n (P.actual n ω).good).isSome ∧
      (if ω∈P.accepted n (P.actual n ω) then true else false)=true
    · rw [ite_eq_left ha] at hv
      rcases Finset.mem_insert.mp hv with hv|hv
      · exact Or.inr ⟨n,hv,hvo⟩
      · exact ih hv
    · rw [ite_eq_right ha] at hv
      exact ih hv

lemma good_parent_present (ω : Set E) {e : Edge} (hp : source e∈P.allGood ω) :
    source e∈(P.actual (gridSlot (target e)) ω).good := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hp
  have hq := (P.state_valid n (P.rule.codeOf n ω)).2.1 _ hn |>.1
  have hlt := parent_slot_lt e hq
  rcases P.actual_good_birth n ω hn with he|⟨k,he,hg⟩
  · rw [he]
    exact P.actual_root _ _
  · have hsk : gridSlot (source e)=k := by rw [he,gridSlot_slotSite]
    exact P.actual_good_mono ω (show k+1 ≤ gridSlot (target e) by omega) hg

lemma missing_child_fails (ω : Set E) (z : Site) (hz : z∉P.allGood ω)
    (hc : ∃ y∈P.allGood ω, z=y+(1,0) ∨ z=y+(0,1)) :
    ω∈P.rule.failure (gridSlot z) := by
  obtain ⟨y,hy,hz'⟩ := hc
  let e : Edge := (y,if z=y+(1,0) then true else false)
  have he : target e=z := by
    by_cases hh : z=y+(1,0)
    · simp [e,target,hh]
    · rcases hz' with hz'|hz'
      · exact (hh hz').elim
      · simp [e,target,hz']
  have hp : source e∈P.allGood ω := hy
  have hyp := P.good_parent_present ω hp
  rw [he] at hyp
  have hqz := target_quadrant e (P.allGood_quadrant ω hp)
  rw [he] at hqz
  have hs : slotSite (gridSlot z)=z := slotSite_gridSlot z hqz
  have hex : ∃ f, incoming (gridSlot z) (P.actual (gridSlot z) ω).good=some f := by
    apply incoming_exists
    refine ⟨y,hyp,?_⟩
    rwa [hs]
  obtain ⟨f,hf⟩ := hex
  apply (P.rule.failure_on_cell (gridSlot z) (P.rule.codeOf_mem _ ω)).mpr
  constructor
  · change (incoming (gridSlot z) (P.actual (gridSlot z) ω).good).isSome
    simp [hf]
  · change ω∉P.accepted (gridSlot z) (P.actual (gridSlot z) ω)
    intro ha
    apply hz
    apply Set.mem_iUnion.mpr
    refine ⟨gridSlot z+1,?_⟩
    rw [P.actual_succ]
    change z∈(if (incoming (gridSlot z) (P.actual (gridSlot z) ω).good).isSome ∧
      (if ω∈P.accepted (gridSlot z) (P.actual (gridSlot z) ω) then true else false)=true
      then insert (slotSite (gridSlot z)) (P.actual (gridSlot z) ω).good else (P.actual (gridSlot z) ω).good)
    simp [hf,ha,hs]

lemma allGood_reached (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) {ω : Set E} (hB : ω∈P.rootEvent)
    {v : Site} (hv : v∈P.allGood ω) : ω∈P.graph.seedHitEvent P.seed (P.mark v) := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
  have hs := P.stable_on_cell hh hhj hsep hroot n (P.rule.codeOf n ω) ω (P.rule.codeOf_mem n ω) hB
  have hr := hs.1 v hn
  exact P.graph.seedHitEvent_upper _ _ (Set.inter_subset_left) hr

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
