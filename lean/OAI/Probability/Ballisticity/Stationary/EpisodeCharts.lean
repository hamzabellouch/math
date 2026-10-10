import Mathlib
import OAI.Probability.Ballisticity.Stationary.OperationalEpisode

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma EpisodeState.ext_raw {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    {p q : EpisodeState (k:=k) e f r} (hh : p.height=q.height) (hs : p.scale=q.scale)
    (hm : p.profile.val=q.profile.val) : p=q := by
  cases p with | mk hp sp pp =>
    cases q with | mk hq sq pq =>
      dsimp only at hh hs hm
      subst hq
      subst sq
      have he : pp=pq := Subtype.ext hm
      subst pq
      rfl

structure EpisodeChart {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ) where
  height : ℕ
  scale : ℝ
  profile : Environment d → BudgetProfile (k:=k) e f height (r scale)
  measurable_profile : @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) height)) _ profile
  event : Set (Environment d)
  measurable_event : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) height)] event

namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

noncomputable def state (c : EpisodeChart (k:=k) e f r) (ω : Environment d) : EpisodeState (k:=k) e f r :=
  ⟨c.height,c.scale,c.profile ω⟩

noncomputable def layerProfile (c : EpisodeChart (k:=k) e f r) : Environment d → LayerTupleProfile (k:=k) e c.height :=
  fun ω => (c.profile ω).toLayerProfile

lemma measurable_layerProfile (c : EpisodeChart (k:=k) e f r) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) c.height)) _ c.layerProfile :=
  (measurable_subtype_coe.comp c.measurable_profile).subtype_mk

noncomputable def stop (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) : Environment d → ℕ :=
  stageStop e f c.height (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
    ((k:ℝ)*b) c.layerProfile (episodeStageH χ b c.scale) (N-c.height)

noncomputable def growsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) (ω : Environment d) : Prop :=
  j=episodeStageH χ b c.scale ∧ ENNReal.ofReal (Real.exp (-((k:ℝ)*b))) ≤
    stageTestMass e f c.height (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
      c.layerProfile (episodeStageH χ b c.scale) j ω

lemma measurableSet_growsAt (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (j : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      {ω | c.growsAt fexp g χ b j ω} := by
  have hm := (MeasurableSet.const (j=episodeStageH χ b c.scale)).inter
    (measurableSet_le (f:=fun _ : Environment d => ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) measurable_const
      (stageTestMass_adapted e f c.height (r (c.scale*Real.exp (-fexp*b)))
        (r (c.scale*Real.exp (g*b))) c.layerProfile c.measurable_layerProfile
        (episodeStageH χ b c.scale) j))
  convert hm using 1 <;> first | rfl | (rw [Nat.cast_add]; rfl)

lemma stop_eq (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) (ω : Environment d) :
    c.stop fexp g χ b N ω=episodeStageLength e f r fexp g χ b N (c.state ω) ω := rfl

lemma growsAt_eq (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ) (ω : Environment d) :
    c.growsAt fexp g χ b (c.stop fexp g χ b N ω) ω ↔
      episodeStageGrows e f r fexp g χ b N (c.state ω) ω := by
  simp only [growsAt,episodeStageGrows,neg_mul]
  rfl

noncomputable def nextScale (c : EpisodeChart (k:=k) e f r) (fexp g b : ℝ) (grow : Bool) : ℝ :=
  if grow then c.scale*Real.exp (g*b) else c.scale*Real.exp (-fexp*b)

noncomputable def nextProfile (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g b : ℝ) (j : ℕ) (grow : Bool) (ω : Environment d) :
    BudgetProfile (k:=k) e f ((c.height+j:ℕ):ℝ) (r (c.nextScale fexp g b grow)) := by
  let p := seedSeparatedProfile e f hef c.height (r (c.nextScale fexp g b grow)) j (c.layerProfile ω) ω
  refine ⟨p.val,p.property.1,?_⟩
  simpa only [Nat.cast_add] using p.property.2

lemma measurable_nextProfile (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g b : ℝ) (j : ℕ) (grow : Bool) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))) _
      (c.nextProfile hef fexp g b j grow) := by
  apply Measurable.subtype_mk
  have hm := measurable_subtype_coe.comp
    (seedSeparatedProfile_measurable e f hef c.height (r (c.nextScale fexp g b grow)) j
      c.layerProfile c.measurable_layerProfile)
  convert hm using 1 <;> first | rfl | rw [Nat.cast_add]

noncomputable def nextEvent (c : EpisodeChart (k:=k) e f r)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) : Set (Environment d) :=
  {ω | ω∈c.event ∧ c.height<N ∧ sfloor ≤ c.scale ∧ c.stop fexp g χ b N ω=j ∧
    (c.growsAt fexp g χ b j ω ↔ grow=true)}

lemma measurable_nextEvent (c : EpisodeChart (k:=k) e f r)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      (c.nextEvent fexp g χ b sfloor N j grow) := by
  have hle : rowSigma (BelowHeight (realPosition (step e)) (c.height:ℝ)) ≤
      rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ)) :=
    rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < ((c.height+j:ℕ):ℝ)
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right c.height j))
  have hstop := stageStop_event e f c.height (r (c.scale*Real.exp (-fexp*b)))
    (r (c.scale*Real.exp (g*b))) ((k:ℝ)*b) c.layerProfile c.measurable_layerProfile
    (episodeStageH χ b c.scale) (N-c.height) j
  have hg := c.measurableSet_growsAt fexp g χ b j
  have hlast : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))]
      {ω | c.growsAt fexp g χ b j ω ↔ grow=true} := by
    cases grow
    · simpa only [Bool.false_eq_true,iff_false,Set.compl_ofPred,Nat.cast_add] using hg.compl
    · simpa only [iff_true,Nat.cast_add] using hg
  have hc := hle _ c.measurable_event
  have hcast : ((c.height+j:ℕ):ℝ) = (c.height:ℝ)+(j:ℝ) := Nat.cast_add _ _
  rw [hcast] at hc hlast
  rw [hcast]
  exact hc.inter
    ((MeasurableSet.const (c.height<N)).inter ((MeasurableSet.const (sfloor ≤ c.scale)).inter
      (hstop.inter hlast)))

noncomputable def next (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) : EpisodeChart (k:=k) e f r where
  height := c.height+j
  scale := c.nextScale fexp g b grow
  profile := c.nextProfile hef fexp g b j grow
  measurable_profile := c.measurable_nextProfile hef fexp g b j grow
  event := c.nextEvent fexp g χ b sfloor N j grow
  measurable_event := c.measurable_nextEvent fexp g χ b sfloor N j grow

end EpisodeChart
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStageNext_profile {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    (episodeStageNext e f hef r fexp g χ b N q ω).profile.val =
      (seedSeparatedProfile e f hef q.height (r (episodeStageScale e f r fexp g χ b N q ω))
        (episodeStageLength e f r fexp g χ b N q ω) q.profile.toLayerProfile ω).val := by
  change (seedSeparatedProfile e f hef q.height
    (stageRetainedGap e f q.height (r (q.scale*Real.exp (-fexp*b)))
      (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
      (episodeStageH χ b q.scale) (N-q.height) ω) _ _ ω).val = _
  rw [episodeStageGap]
  rfl

namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma next_state (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N j : ℕ) (grow : Bool) (ω : Environment d)
    (hω : ω∈(c.next hef fexp g χ b sfloor N j grow).event) :
    (c.next hef fexp g χ b sfloor N j grow).state ω =
      episodeStageNext e f hef r fexp g χ b N (c.state ω) ω := by
  have hj : c.stop fexp g χ b N ω=j := hω.2.2.2.1
  have hg : episodeStageGrows e f r fexp g χ b N (c.state ω) ω ↔ grow=true := by
    rw [←c.growsAt_eq fexp g χ b N ω,hj]
    exact hω.2.2.2.2
  have hscale : c.nextScale fexp g b grow=episodeStageScale e f r fexp g χ b N (c.state ω) ω := by
    cases grow with
    | false =>
      have hn : ¬episodeStageGrows e f r fexp g χ b N (c.state ω) ω := by
        intro hh
        exact Bool.false_ne_true (hg.mp hh)
      simp only [nextScale,Bool.false_eq_true,ite_false,episodeStageScale,ite_eq_right hn]
      rfl
    | true =>
      have hp : episodeStageGrows e f r fexp g χ b N (c.state ω) ω := hg.mpr rfl
      simp only [nextScale,ite_true,episodeStageScale,ite_eq_left hp]
      rfl
  apply EpisodeState.ext_raw
  · change c.height+j=c.height+episodeStageLength e f r fexp g χ b N (c.state ω) ω
    rw [←c.stop_eq,hj]
  · exact hscale
  · rw [episodeStageNext_profile,←c.stop_eq,hj]
    change (seedSeparatedProfile e f hef c.height (r (c.nextScale fexp g b grow)) j (c.layerProfile ω) ω).val=_
    rw [hscale]
    rfl

noncomputable def frozen (c : EpisodeChart (k:=k) e f r) (sfloor : ℝ) (N : ℕ) : EpisodeChart (k:=k) e f r where
  height := c.height
  scale := c.scale
  profile := c.profile
  measurable_profile := c.measurable_profile
  event := c.event ∩ {_ω | ¬(c.height<N ∧ sfloor ≤ c.scale)}
  measurable_event := c.measurable_event.inter (MeasurableSet.const _)

noncomputable def branch (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) : Option (ℕ×Bool) → EpisodeChart (k:=k) e f r
  | none => c.frozen sfloor N
  | some (j,grow) => c.next hef fexp g χ b sfloor N j grow

lemma branch_covers (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (hω : ω∈c.event) :
    ∃ l, ω∈(c.branch hef fexp g χ b sfloor N l).event := by
  by_cases hr : c.height<N ∧ sfloor ≤ c.scale
  · let j := c.stop fexp g χ b N ω
    by_cases hg : c.growsAt fexp g χ b j ω
    · exact ⟨some (j,true),hω,hr.1,hr.2,rfl,by simpa only [iff_true] using hg⟩
    · exact ⟨some (j,false),hω,hr.1,hr.2,rfl,by simpa only [Bool.false_eq_true,iff_false] using hg⟩
  · exact ⟨none,hω,hr⟩

lemma branch_state (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (ω : Environment d) (l : Option (ℕ×Bool))
    (hω : ω∈(c.branch hef fexp g χ b sfloor N l).event) :
    ω∈c.event ∧ (c.branch hef fexp g χ b sfloor N l).state ω =
      if EpisodeReady e f r sfloor N (c.state ω)
      then episodeStageNext e f hef r fexp g χ b N (c.state ω) ω else c.state ω := by
  cases l with
  | none =>
    refine ⟨hω.1,?_⟩
    rw [ite_eq_right (show ¬EpisodeReady e f r sfloor N (c.state ω) from hω.2)]
    rfl
  | some l =>
    have hr : EpisodeReady e f r sfloor N (c.state ω) := ⟨hω.2.1,hω.2.2.1⟩
    exact ⟨hω.1,by rw [ite_eq_left hr]; exact c.next_state hef fexp g χ b sfloor N l.1 l.2 ω hω⟩

end EpisodeChart

structure EpisodeAtlas {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    (q : Environment d → EpisodeState (k:=k) e f r) where
  Label : Type
  countable : Countable Label
  chart : Label → EpisodeChart (k:=k) e f r
  cover : ∀ ω, ∃ l, ω∈(chart l).event
  correct : ∀ l ω, ω∈(chart l).event → q ω=(chart l).state ω

namespace EpisodeAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r}

noncomputable def advance (A : EpisodeAtlas q) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) :
    EpisodeAtlas (fun ω => if EpisodeReady e f r sfloor N (q ω)
      then episodeStageNext e f hef r fexp g χ b N (q ω) ω else q ω) := by
  let := A.countable
  refine ⟨A.Label×Option (ℕ×Bool),inferInstance,
    fun l => (A.chart l.1).branch hef fexp g χ b sfloor N l.2,?_,?_⟩
  · intro ω
    obtain ⟨l,hl⟩ := A.cover ω
    obtain ⟨j,hj⟩ := (A.chart l).branch_covers hef fexp g χ b sfloor N ω hl
    exact ⟨(l,j),hj⟩
  · intro l ω hω
    obtain ⟨hl,hnext⟩ := (A.chart l.1).branch_state hef fexp g χ b sfloor N ω l.2 hω
    rw [A.correct l.1 ω hl]
    exact hnext.symm

noncomputable def run (A : EpisodeAtlas q) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) (n : ℕ) :
    EpisodeAtlas (fun ω => episodeRun e f hef r fexp g χ b sfloor N (q ω) ω n) := by
  induction n with
  | zero => exact A
  | succ n ih => exact ih.advance hef fexp g χ b sfloor N

lemma height_event (A : EpisodeAtlas q) (m : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)] {ω | (q ω).height=m} := by
  let := A.countable
  have he : {ω | (q ω).height=m} = ⋃ l : {l : A.Label // (A.chart l).height=m}, (A.chart l.val).event := by
    ext ω
    change (q ω).height=m ↔ _
    constructor
    · intro hω
      obtain ⟨l,hl⟩ := A.cover ω
      have hh : (A.chart l).height=m := by rw [A.correct l ω hl] at hω; exact hω
      exact Set.mem_iUnion.mpr ⟨⟨l,hh⟩,hl⟩
    · intro hω
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hω
      rw [A.correct l.val ω hl]
      exact l.property
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event
  rwa [l.property] at hm

lemma profile_event (A : EpisodeAtlas q) (m : ℕ) (U : Set (Measure (Fin k → Lattice d)))
    (hU : MeasurableSet U) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      ({ω | (q ω).profile.val∈U} ∩ {ω | (q ω).height=m}) := by
  let := A.countable
  have he : {ω | (q ω).profile.val∈U} ∩ {ω | (q ω).height=m} =
      ⋃ l : {l : A.Label // (A.chart l).height=m},
        (A.chart l.val).event ∩ {ω | ((A.chart l.val).profile ω).val∈U} := by
    ext ω
    change ((q ω).profile.val∈U ∧ (q ω).height=m) ↔ _
    constructor
    · rintro ⟨hUω,hmω⟩
      obtain ⟨l,hl⟩ := A.cover ω
      have hh : (A.chart l).height=m := by rw [A.correct l ω hl] at hmω; exact hmω
      exact Set.mem_iUnion.mpr ⟨⟨l,hh⟩,hl,by rw [A.correct l ω hl] at hUω; exact hUω⟩
    · intro hω
      obtain ⟨l,hl,hV⟩ := Set.mem_iUnion.mp hω
      rw [A.correct l.val ω hl]
      exact ⟨hV,l.property⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event.inter
    ((measurable_subtype_coe.comp (A.chart l.val).measurable_profile) hU)
  have hle : rowSigma (BelowHeight (realPosition (step e)) ((A.chart l.val).height:ℝ)) ≤
      rowSigma (BelowHeight (realPosition (step e)) (m:ℝ)) := by rw [l.property]
  exact hle _ hm

end EpisodeAtlas
end DirectionalTransience

end

end OAI
