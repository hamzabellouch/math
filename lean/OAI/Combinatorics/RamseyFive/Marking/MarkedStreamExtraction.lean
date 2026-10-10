import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.StageState
import OAI.Combinatorics.RamseyFive.Marking.TwoScanContext
import OAI.Combinatorics.RamseyFive.Entropy.ConditionPullback

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
local instance streamClassFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance streamClassPointDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance streamClassDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

def markedContext (ctx : Ω→κ) (x : Ω→Fin n→FlagPair K V) (a : Ω) :=
  (ctx a,markingMessage (x a))

def markedPositions (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (ctx : Ω→κ) (x : Ω→Fin n→FlagPair K V) (a : SlotClass) (z : Ω) :=
  classPositions (unspecified (markingMessage (x z)))
    (markedCode hdim width hw (markedContext ctx x z)) a

def markedEvent (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (l : ℕ) : SlotClass→Finset (κ×UnionTranscript (Fin n) (FlagPair K V)) :=
  selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw)

def classStream (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) :
    SelectedStream (Ω:=Ω) (β:=FlagPair K V) N l admissible :=
  (S.restrict _ hE).extract hl (markedPositions hdim width hw ctx S.tuple a)

omit [Finite K] in
lemma markedContext_law (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) :
    first (withMessage (pair S.law ctx S.tuple) markingMessage)=
      map S.law (markedContext ctx S.tuple) := by
  rw [withMessage_pair,first_pair]
  rfl

lemma actual_marked_class (hdim : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible) (ctx : Ω→κ)
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z))
    (width : ℝ) (hw : 0≤width) (l : ℕ)
    (hsize : 39*(l:ℝ)+expensiveBound K V≤n) :
    ∃ a : SlotClass,(1:ℝ)/39≤eventMass S.law
      (eventPreimage (markedContext ctx S.tuple) (markedEvent hdim width hw l a)) := by
  have hpcons : ∀ c x,0<pair S.law ctx S.tuple (c,x)→TupleConsistent x := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hcons z hz
  obtain ⟨a,ha⟩:=marking_fixed_class hdim (pair S.law ctx S.tuple) hpcons width hw l hsize
  refine ⟨a,?_⟩
  rw [markedContext_law,eventMass_map_preimage] at ha
  exact ha

lemma classStream_density (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hm : (1:ℝ)/39≤eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) :
    (classStream hdim width hw S ctx hl a hE).density≤39*S.density := by
  change S.density/eventMass S.law _≤39*S.density
  apply (div_le_iff₀ hE).mpr
  have h:=mul_le_mul_of_nonneg_left hm S.density_nonneg
  nlinarith

lemma classStream_joint (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) :
    ∃ hE',pair (classStream hdim width hw S ctx hl a hE).law (markedContext ctx S.tuple)
      (classStream hdim width hw S ctx hl a hE).tuple=
        markedClassLaw hdim (pair S.law ctx S.tuple) hl width hw a hE' := by
  have hE' : 0<eventMass (first (withMessage (pair S.law ctx S.tuple) markingMessage))
      (markedEvent hdim width hw l a) := by
    rwa [markedContext_law,eventMass_map_preimage]
  refine ⟨hE',?_⟩
  change pair (conditionOn S.law _ hE) (markedContext ctx S.tuple)
    (fun z=>retainedTuple hl (S.tuple z) (markedPositions hdim width hw ctx S.tuple a z)) = _
  unfold markedClassLaw
  simp only [withMessage_pair]
  rw [←conditionContext_pair,selected_pair]
  · rfl
  · rw [eventMass_map_preimage]
    exact hE

lemma classStream_consistent (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hinc : ∀ z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀ z,0<(classStream hdim width hw S ctx hl a hE).law z→
      TupleIncident ((classStream hdim width hw S ctx hl a hE).tuple z) ∧
      TupleConsistent ((classStream hdim width hw S ctx hl a hE).tuple z) := by
  intro z hz
  have h:=conditionOn_positive S.law _ hE z hz
  constructor
  · intro i
    exact hinc z h.2 _
  · intro i j hij
    exact hcons z h.2 _ _ ((retainedIndices hl _).strictMono hij)

def classDomain (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V)) (i : Fin l) :=
  markingDomain c.2 (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c i)

attribute [local irreducible] unspecified classPositions

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma marked_indices_properties (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (c : κ×UnionTranscript (Fin n) (FlagPair K V))
    (hc : c∈markedEvent hdim width hw l a) (i : Fin l) :
    selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c i∈unspecified c.2 ∧
    markedCode hdim width hw c
      (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a c i)=a := by
  have hc' : c∈selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a := by
    simpa only [markedEvent] using hc
  exact selectedClassIndices_properties hl (fun c=>unspecified c.2)
    (markedCode hdim width hw) a c hc' i

lemma markedSelected_decodes (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (f : Fin n→FlagPair K V) (ctx : κ)
    (hinc : TupleIncident f) (hcons : TupleConsistent f)
    (hc : (ctx,markingMessage f)∈markedEvent hdim width hw l a) (i : Fin l) :
    let j:=selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a (ctx,markingMessage f) i
    f j∈markingDomain (markingMessage f) j := by
  apply marking_decodes hdim f hinc hcons
  exact (marked_indices_properties hdim width hw hl a (ctx,markingMessage f) hc i).1

lemma markedSelected_valid (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (f : Fin n→FlagPair K V) (ctx : κ)
    (hinc : TupleIncident f) (hcons : TupleConsistent f)
    (hc : (ctx,markingMessage f)∈markedEvent hdim width hw l a) (i : Fin l) :
    classValid width (markingMessage f)
      (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a (ctx,markingMessage f) i) a := by
  have hi:=(marked_indices_properties hdim width hw hl a (ctx,markingMessage f) hc i).2
  have hd:=markedSelected_decodes hdim width hw hl a f ctx hinc hcons hc i
  have hv:=markingClass_valid hdim width hw (markingMessage f) _ ⟨_,hd⟩
  simp only [markedCode] at hi
  rw [hi] at hv
  exact hv

lemma classStream_tuple (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) (z : Ω) (i : Fin l) :
    (classStream hdim width hw S ctx hl a hE).tuple z i=
      S.tuple z (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a
        (markedContext ctx S.tuple z) i) := rfl

lemma classStream_event (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) (z : Ω)
    (hz : 0<(classStream hdim width hw S ctx hl a hE).law z) :
    markedContext ctx S.tuple z∈markedEvent hdim width hw l a ∧ 0<S.law z := by
  obtain ⟨he,hp⟩:=conditionOn_positive S.law _ hE z hz
  exact ⟨(mem_eventPreimage _ _ _).mp he,hp⟩

lemma classStream_contains (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hinc : ∀ z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀ z,0<(classStream hdim width hw S ctx hl a hE).law z→∀ i,
      (classStream hdim width hw S ctx hl a hE).tuple z i∈
        classDomain hdim width hw hl a (markedContext ctx S.tuple z) i := by
  intro z hz i
  obtain ⟨hc,hp⟩:=classStream_event hdim width hw S ctx hl a hE z hz
  rw [classStream_tuple]
  exact markedSelected_decodes hdim width hw hl a (S.tuple z) (ctx z) (hinc z hp) (hcons z hp) hc i

lemma classStream_valid (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hinc : ∀ z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀ z,0<(classStream hdim width hw S ctx hl a hE).law z→∀ i,
      classValid width (markingMessage (S.tuple z))
        (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a
          (markedContext ctx S.tuple z) i) a := by
  intro z hz i
  obtain ⟨hc,hp⟩:=classStream_event hdim width hw S ctx hl a hE z hz
  exact markedSelected_valid hdim width hw hl a (S.tuple z) (ctx z) (hinc z hp) (hcons z hp) hc i
end
end SharpRamseyFive.Marking

end OAI
