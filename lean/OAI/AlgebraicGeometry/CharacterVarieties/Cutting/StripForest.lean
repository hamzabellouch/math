import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.Grafting

namespace OAI

/-!
# Finite trails of secondary corners in a realized band.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical

/-- The child-seam graph of a half-band: internal seams have distinct ends and
strictly increasing layer. This will be constructed from the literal whole-
port gallery below, not requested as a lower-diagram hypothesis. -/
structure LayeredTrail (N E : Type) where
  bound : ℕ
  level : N → Fin (bound+1)
  source : E ↪ N
  target : E ↪ N
  increasing : ∀ e,level (source e)<level (target e)

namespace LayeredTrail
variable {N E : Type} (T : LayeredTrail N E)

noncomputable def root (x : N) : N :=
  if h : ∃ e,T.target e=x then root (T.source h.choose) else x
termination_by (T.level x).val
decreasing_by
  have hlt := T.increasing h.choose
  rw [h.choose_spec] at hlt
  exact hlt

noncomputable def run (x : N) : List N :=
  if h : ∃ e,T.source e=x then x::run (T.target h.choose) else [x]
termination_by T.bound-(T.level x).val
decreasing_by
  have hlt := T.increasing h.choose
  rw [h.choose_spec] at hlt
  have hbd := (T.level (T.target h.choose)).isLt
  change (T.level x).val<(T.level (T.target h.choose)).val at hlt
  omega

lemma root_of_source (x : N) (h : ¬∃ e,T.target e=x) : T.root x=x := by
  rw [root,dite_eq_right h]
lemma root_of_edge (e : E) : T.root (T.target e)=T.root (T.source e) := by
  rw [root,dite_eq_left ⟨e,rfl⟩]
  congr 2
  exact T.target.injective (Classical.choose_spec (show ∃ d,T.target d=T.target e from ⟨e,rfl⟩))
lemma run_of_sink (x : N) (h : ¬∃ e,T.source e=x) : T.run x=[x] := by
  rw [run,dite_eq_right h]
lemma run_of_edge (e : E) : T.run (T.source e)=T.source e::T.run (T.target e) := by
  rw [run,dite_eq_left ⟨e,rfl⟩]
  congr 3
  exact T.source.injective (Classical.choose_spec (show ∃ d,T.source d=T.source e from ⟨e,rfl⟩))

lemma root_external (x : N) : ¬∃ e,T.target e=T.root x := by
  induction h : (T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.target e=x
    · obtain ⟨e,rfl⟩ := he
      rw [T.root_of_edge]
      apply ih (T.level (T.source e)).val
      · have hh := T.increasing e
        change (T.level (T.source e)).val<(T.level (T.target e)).val at hh
        omega
      · rfl
    · rw [T.root_of_source x he]
      exact he

lemma mem_run_self (x : N) : x∈T.run x := by
  rw [run]
  split_ifs <;> simp

lemma root_eq_of_mem_run {x y : N} (hy : y∈T.run x) : T.root y=T.root x := by
  induction h : T.bound-(T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.source e=x
    · obtain ⟨e,rfl⟩ := he
      rw [T.run_of_edge,List.mem_cons] at hy
      rcases hy with rfl|hy
      · rfl
      · refine (ih (T.bound-(T.level (T.target e)).val) ?_ hy rfl).trans (T.root_of_edge e)
        have hh := T.increasing e
        have hb := (T.level (T.target e)).isLt
        change (T.level (T.source e)).val<(T.level (T.target e)).val at hh
        omega
    · rw [T.run_of_sink x he,List.mem_singleton] at hy
      subst y
      rfl

/-- Every actual corner node belongs to the run of an exposed end. -/
lemma mem_run_root (x : N) : x∈T.run (T.root x) := by
  induction h : (T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.target e=x
    · obtain ⟨e,rfl⟩ := he
      have hm : T.source e∈T.run (T.root (T.source e)) := ih (T.level (T.source e)).val
        (by have hh := T.increasing e; change (T.level (T.source e)).val<(T.level (T.target e)).val at hh; omega)
        _ rfl
      rw [T.root_of_edge]
      -- Any outgoing successor of a node in a run belongs to the same run.
      suffices hs : ∀ z,T.source e∈T.run z → T.target e∈T.run z from hs _ hm
      intro z hz
      induction k : T.bound-(T.level z).val using Nat.strong_induction_on generalizing z with
      | h m ihz =>
        by_cases hf : ∃ d,T.source d=z
        · obtain ⟨d,rfl⟩ := hf
          rw [T.run_of_edge,List.mem_cons] at hz ⊢
          rcases hz with hz|hz
          · have hed := T.source.injective hz
            subst d
            exact Or.inr (T.mem_run_self _)
          · exact Or.inr (ihz (T.bound-(T.level (T.target d)).val)
              (by have hh := T.increasing d; have hb := (T.level (T.target d)).isLt
                  change (T.level (T.source d)).val<(T.level (T.target d)).val at hh; omega)
              _ hz rfl)
        · rw [T.run_of_sink z hf,List.mem_singleton] at hz
          exact (hf ⟨e,hz⟩).elim
    · rw [T.root_of_source x he]
      exact T.mem_run_self x

lemma external_run_cover (x : N) : ∃ s, (¬∃ e,T.target e=s) ∧ x∈T.run s :=
  ⟨T.root x,T.root_external x,T.mem_run_root x⟩

lemma external_run_unique {s t x : N} (hs : ¬∃ e,T.target e=s) (ht : ¬∃ e,T.target e=t)
    (hxs : x∈T.run s) (hxt : x∈T.run t) : s=t := by
  have hh := (T.root_eq_of_mem_run hxs).symm.trans (T.root_eq_of_mem_run hxt)
  rwa [T.root_of_source s hs,T.root_of_source t ht] at hh

lemma run_level {x y : N} (hy : y∈T.run x) : T.level x≤T.level y := by
  induction h : T.bound-(T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.source e=x
    · obtain ⟨e,rfl⟩ := he
      rw [T.run_of_edge,List.mem_cons] at hy
      rcases hy with rfl|hy
      · rfl
      · have hh := T.increasing e
        have ht := ih (T.bound-(T.level (T.target e)).val)
          (by have hb := (T.level (T.target e)).isLt
              change (T.level (T.source e)).val<(T.level (T.target e)).val at hh; omega)
          hy rfl
        exact le_trans (le_of_lt (T.increasing e)) ht
    · rw [T.run_of_sink x he,List.mem_singleton] at hy
      subst y
      exact le_rfl

lemma run_nodup (x : N) : (T.run x).Nodup := by
  induction h : T.bound-(T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.source e=x
    · obtain ⟨e,rfl⟩ := he
      rw [T.run_of_edge,List.nodup_cons]
      constructor
      · intro hm
        exact (not_le_of_gt (T.increasing e)) (T.run_level hm)
      · apply ih (T.bound-(T.level (T.target e)).val)
        · have hh := T.increasing e
          have hb := (T.level (T.target e)).isLt
          change (T.level (T.source e)).val<(T.level (T.target e)).val at hh
          omega
        · rfl
    · rw [T.run_of_sink x he]
      simp

end LayeredTrail
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.LayeredTrail
open scoped Classical
variable {N E : Type} (T : LayeredTrail N E)

/-- Both endpoints of each literal strip run are exposed. -/
def reverse : LayeredTrail N E where
  bound := T.bound
  level x := (T.level x).rev
  source := T.target
  target := T.source
  increasing e := by simpa only [Fin.rev_lt_rev] using T.increasing e

noncomputable def tip (x : N) := T.reverse.root x

lemma tip_external (x : N) : ¬∃ e,T.source e=T.tip x := T.reverse.root_external x
lemma tip_of_sink (x : N) (h : ¬∃ e,T.source e=x) : T.tip x=x := T.reverse.root_of_source x h
lemma tip_of_edge (e : E) : T.tip (T.source e)=T.tip (T.target e) := T.reverse.root_of_edge e

lemma tip_mem_run (x : N) : T.tip x∈T.run x := by
  induction h : T.bound-(T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.source e=x
    · obtain ⟨e,rfl⟩ := he
      rw [T.tip_of_edge,T.run_of_edge,List.mem_cons]
      right
      apply ih (T.bound-(T.level (T.target e)).val)
      · have hh := T.increasing e
        have hb := (T.level (T.target e)).isLt
        change (T.level (T.source e)).val<(T.level (T.target e)).val at hh
        omega
      · rfl
    · rw [T.tip_of_sink x he]
      exact T.mem_run_self x

lemma tip_eq_of_mem_run {x y : N} (hy : y∈T.run x) : T.tip y=T.tip x := by
  induction h : T.bound-(T.level x).val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,T.source e=x
    · obtain ⟨e,rfl⟩ := he
      rw [T.run_of_edge,List.mem_cons] at hy
      rcases hy with rfl|hy
      · rfl
      · refine (ih (T.bound-(T.level (T.target e)).val) ?_ hy rfl).trans (T.tip_of_edge e).symm
        have hh := T.increasing e
        have hb := (T.level (T.target e)).isLt
        change (T.level (T.source e)).val<(T.level (T.target e)).val at hh
        omega
    · rw [T.run_of_sink x he,List.mem_singleton] at hy
      subst y
      rfl

lemma tip_root (x : N) : T.tip (T.root x)=T.tip x := (T.tip_eq_of_mem_run (T.mem_run_root x)).symm
lemma root_tip (x : N) : T.root (T.tip x)=T.root x := T.root_eq_of_mem_run (T.tip_mem_run x)

/-- The open-end matching is produced, bijective, and retains every corner of
every path. There are no concealed circular lower strips. -/
noncomputable def endsEquiv : {x : N // ¬∃ e,T.target e=x} ≃ {x : N // ¬∃ e,T.source e=x} where
  toFun x := ⟨T.tip x.val,T.tip_external x.val⟩
  invFun y := ⟨T.root y.val,T.root_external y.val⟩
  left_inv x := Subtype.ext ((T.root_tip x.val).trans (T.root_of_source x.val x.property))
  right_inv y := Subtype.ext ((T.tip_root y.val).trans (T.tip_of_sink y.val y.property))

end IntegralCharacterVarieties.OccurrenceIncidence.LayeredTrail
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
namespace Kind

/-- One oriented SECONDARY corner of an actual allowed vertex. Removing the
principal parent corner is essential: this is the graph of the lower strips. -/
def SecondaryNode (k : Kind) :=
  {z : (p : k.table.Port) × Option (k.table.Child p) //
    k.table.endpoint z.1≠z.2.isNone ∧ z≠⟨k.output,none⟩}

def inputNode (k : Kind) (c : k.table.Child k.input) : k.SecondaryNode :=
  ⟨⟨k.input,some c⟩,by simp [Kind.input_endpoint],by
    intro h; have hh := congrArg (fun z : (p : k.table.Port) × Option (k.table.Child p) => z.2.isNone) h
    exact Bool.noConfusion hh⟩

def outputNode (k : Kind) (c : k.table.Child k.output) : k.SecondaryNode :=
  ⟨k.table.mate ⟨k.output,some c⟩,by
    have hh := k.table.orientation ⟨k.output,some c⟩
    have hn : k.table.endpoint k.output=(some c).isNone := k.output_endpoint
    exact fun he => (hh.mp he) hn,by
    intro h
    have hh := congrArg k.table.mate h
    rw [k.table.involutive] at hh
    have hi := k.table.involutive ⟨k.input,none⟩
    rw [Kind.principal_corner] at hi
    rw [hi] at hh
    have hx := congrArg (fun z : (p : k.table.Port) × Option (k.table.Child p) => z.2.isNone) hh
    exact Bool.noConfusion hx⟩

lemma inputNode_injective (k : Kind) : Function.Injective k.inputNode := by
  intro c d h
  have hh := congrArg Subtype.val h
  simpa only [inputNode,Sigma.mk.inj_iff,heq_eq_eq,true_and,Option.some.injEq] using hh
lemma outputNode_injective (k : Kind) : Function.Injective k.outputNode := by
  intro c d h
  have hh := congrArg k.table.mate (congrArg Subtype.val h)
  change k.table.mate (k.table.mate ⟨k.output,some c⟩)=k.table.mate (k.table.mate ⟨k.output,some d⟩) at hh
  rw [k.table.involutive,k.table.involutive] at hh
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and,Option.some.injEq] using hh

lemma node_not_output (k : Kind) (z : k.SecondaryNode) : z.val.1≠k.output := by
  rcases z with ⟨⟨p,c⟩,hn,hp⟩
  intro h
  change p=k.output at h
  subst p
  cases c with
  | none => exact hp rfl
  | some c => exact hn k.output_endpoint

lemma node_mate_not_input (k : Kind) (z : k.SecondaryNode) : (k.table.mate z.val).1≠k.input := by
  have hpos := (k.table.orientation z.val).mpr z.property.1
  intro h
  have hb : (k.table.mate z.val).2.isNone=true :=
    hpos.symm.trans ((congrArg k.table.endpoint h).trans k.input_endpoint)
  have hnone : (k.table.mate z.val).2=none := Option.isNone_iff_eq_none.mp hb
  have he : k.table.mate z.val=⟨k.input,none⟩ := by
    cases hm : k.table.mate z.val with
    | mk p c =>
      have hc : c=none := Option.isNone_iff_eq_none.mp
        ((congrArg (fun z : (p : k.table.Port) × Option (k.table.Child p) => z.2.isNone) hm).symm.trans hb)
      have hp : p=k.input := (congrArg Sigma.fst hm).symm.trans h
      subst p
      subst c
      rfl
  have he' := congrArg k.table.mate he
  rw [k.table.involutive,k.principal_corner] at he'
  exact z.property.2 he'

end Kind
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)

abbrev StripNode := (v : Fin (B.length+1)) × (B.kind v).SecondaryNode
abbrev StripEdge := (j : Fin B.length) × Fin ((B.kind j.castSucc).arity (B.kind j.castSucc).output)

noncomputable def stripSource (e : B.StripEdge) : B.StripNode :=
  ⟨e.1.castSucc,(B.kind e.1.castSucc).outputNode
    (((B.kind e.1.castSucc).childEnumeration (B.kind e.1.castSucc).output).symm e.2)⟩
noncomputable def stripTarget (e : B.StripEdge) : B.StripNode :=
  ⟨e.1.succ,(B.kind e.1.succ).inputNode
    (((B.kind e.1.succ).childEnumeration (B.kind e.1.succ).input).symm
      (finCongr (B.arity_match e.1) e.2))⟩

lemma stripSource_injective : Function.Injective B.stripSource := by
  rintro ⟨j,i⟩ ⟨k,t⟩ h
  have hjk : j.castSucc=k.castSucc := congrArg Sigma.fst h
  have hjk' := Fin.castSucc_injective _ hjk
  subst k
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have he := (B.kind j.castSucc).outputNode_injective hc
  have ht := ((B.kind j.castSucc).childEnumeration (B.kind j.castSucc).output).symm.injective he
  exact congrArg (Sigma.mk j) ht

lemma stripTarget_injective : Function.Injective B.stripTarget := by
  rintro ⟨j,i⟩ ⟨k,t⟩ h
  have hjk : j.succ=k.succ := congrArg Sigma.fst h
  have hjk' := Fin.succ_injective _ hjk
  subst k
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have he := (B.kind j.succ).inputNode_injective hc
  have ht := ((B.kind j.succ).childEnumeration (B.kind j.succ).input).symm.injective he
  have hi := (finCongr (B.arity_match j)).injective ht
  exact congrArg (Sigma.mk j) hi

/-- Produced from all and only the actual internally sewn child-port
occurrences. In particular no transverse branch is treated as internal. -/
noncomputable def stripForest : LayeredTrail B.StripNode B.StripEdge where
  bound := B.length
  level := Sigma.fst
  source := ⟨B.stripSource,B.stripSource_injective⟩
  target := ⟨B.stripTarget,B.stripTarget_injective⟩
  increasing e := by change e.1.val<e.1.val+1; omega

def stripColor (x : B.StripNode) : F := (B.decoration x.1).color x.2.val

lemma stripColor_edge (e : B.StripEdge) : B.stripColor (B.stripSource e)=B.stripColor (B.stripTarget e) := by
  change (B.decoration e.1.castSucc).color ((B.kind e.1.castSucc).table.mate
    ⟨(B.kind e.1.castSucc).output,some (((B.kind e.1.castSucc).childEnumeration
      (B.kind e.1.castSucc).output).symm e.2)⟩)=_
  rw [(B.decoration e.1.castSucc).corner]
  exact B.color_match e.1 (some e.2)

lemma stripColor_root (x : B.StripNode) : B.stripColor (B.stripForest.root x)=B.stripColor x := by
  induction h : x.1.val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,B.stripTarget e=x
    · obtain ⟨e,rfl⟩ := he
      change B.stripColor (B.stripForest.root (B.stripForest.target e))=_
      rw [B.stripForest.root_of_edge]
      exact (ih e.1.val (by change e.1.val+1=n at h; omega) _ rfl).trans (B.stripColor_edge e)
    · rw [B.stripForest.root_of_source x he]

/-- Every local lower corner is on one and only one actual finite no-repeat
strip run, with its original label constant along the entire run. -/
theorem strip_runs_cover (x : B.StripNode) :
    ∃ s,(¬∃ e,B.stripTarget e=s) ∧ x∈B.stripForest.run s ∧
      (B.stripForest.run s).Nodup ∧ B.stripColor s=B.stripColor x :=
  ⟨B.stripForest.root x,B.stripForest.root_external x,B.stripForest.mem_run_root x,
    B.stripForest.run_nodup _,B.stripColor_root x⟩

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.Kind
open scoped Classical
variable (k : Kind)
lemma node_at_input (z : k.SecondaryNode) (h : z.val.1=k.input) :
    ∃ c,z=k.inputNode c := by
  rcases z with ⟨⟨p,c⟩,hn,hp⟩
  change p=k.input at h
  subst p
  cases c with
  | none => exact (hn k.input_endpoint).elim
  | some c => exact ⟨c,rfl⟩

lemma node_at_output (z : k.SecondaryNode) (h : (k.table.mate z.val).1=k.output) :
    ∃ c,z=k.outputNode c := by
  have hpos := (k.table.orientation z.val).mpr z.property.1
  cases hm : k.table.mate z.val with
  | mk p c =>
    have hp : p=k.output := (congrArg Sigma.fst hm).symm.trans h
    subst p
    have hb : c.isNone=false := by
      exact ((congrArg (fun a : (p : k.table.Port) × Option (k.table.Child p) => a.2.isNone) hm).symm.trans
        (hpos.symm.trans ((congrArg k.table.endpoint h).trans k.output_endpoint)))
    cases c with
    | none => exact Bool.noConfusion hb
    | some c =>
      refine ⟨c,Subtype.ext ?_⟩
      exact (k.table.involutive z.val).symm.trans (congrArg k.table.mate hm)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.Kind

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma input_predecessor (j : Fin B.length) (c : (B.kind j.succ).table.Child (B.kind j.succ).input) :
    ∃ e,B.stripTarget e=⟨j.succ,(B.kind j.succ).inputNode c⟩ := by
  refine ⟨⟨j,(finCongr (B.arity_match j)).symm (((B.kind j.succ).childEnumeration (B.kind j.succ).input) c)⟩,?_⟩
  simp only [stripTarget,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

lemma output_successor (j : Fin B.length) (c : (B.kind j.castSucc).table.Child (B.kind j.castSucc).output) :
    ∃ e,B.stripSource e=⟨j.castSucc,(B.kind j.castSucc).outputNode c⟩ := by
  refine ⟨⟨j,((B.kind j.castSucc).childEnumeration (B.kind j.castSucc).output) c⟩,?_⟩
  simp only [stripSource,Equiv.symm_apply_apply]

/-- An incoming strip end is either at the first short end or on an actual
transverse port. It cannot terminate invisibly inside a running seam. -/
lemma root_exposed (x : B.StripNode) (he : ¬∃ e,B.stripTarget e=x) :
    x.2.val.1≠(B.kind x.1).output ∧
      (x.2.val.1≠(B.kind x.1).input ∨ x.1=0) := by
  refine ⟨(B.kind x.1).node_not_output x.2,?_⟩
  rcases x with ⟨v,z⟩
  cases v using Fin.cases with
  | zero => exact Or.inr rfl
  | succ j =>
    left
    intro hp
    obtain ⟨c,rfl⟩ := (B.kind j.succ).node_at_input z hp
    exact he (B.input_predecessor j c)

/-- The outgoing end of a strip is similarly at the final short end or on a
transverse port, including every split and merge branch. -/
lemma tip_exposed (x : B.StripNode) (he : ¬∃ e,B.stripSource e=x) :
    ((B.kind x.1).table.mate x.2.val).1≠(B.kind x.1).input ∧
      (((B.kind x.1).table.mate x.2.val).1≠(B.kind x.1).output ∨ x.1=Fin.last B.length) := by
  refine ⟨(B.kind x.1).node_mate_not_input x.2,?_⟩
  rcases x with ⟨v,z⟩
  cases v using Fin.lastCases with
  | last => exact Or.inr rfl
  | cast j =>
    left
    intro hp
    obtain ⟨c,rfl⟩ := (B.kind j.castSucc).node_at_output z hp
    exact he (B.output_successor j c)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
noncomputable def inputStrip (c : (B.kind 0).table.Child (B.kind 0).input) : B.StripNode :=
  ⟨0,(B.kind 0).inputNode c⟩
noncomputable def outputStrip (c : (B.kind (Fin.last B.length)).table.Child (B.kind (Fin.last B.length)).output) : B.StripNode :=
  ⟨Fin.last B.length,(B.kind (Fin.last B.length)).outputNode c⟩
lemma inputStrip_external (c) : ¬∃ e,B.stripTarget e=B.inputStrip c := by
  rintro ⟨e,he⟩
  have h := congrArg (fun x : B.StripNode => x.1.val) he
  change e.1.val+1=0 at h
  omega
lemma outputStrip_external (c) : ¬∃ e,B.stripSource e=B.outputStrip c := by
  rintro ⟨e,he⟩
  have h := congrArg (fun x : B.StripNode => x.1.val) he
  change e.1.val=B.length at h
  exact (Nat.ne_of_lt e.1.isLt) h
lemma inputStrip_color (c) : B.stripColor (B.inputStrip c)∈a := by
  apply Eq.mp (congrArg (fun l => B.stripColor (B.inputStrip c)∈l) B.input_children)
  change (B.decoration 0).color ⟨(B.kind 0).input,some c⟩ ∈ _
  rw [←(B.decoration 0).portColor_child]
  exact List.mem_ofFn.mpr ⟨((B.kind 0).childEnumeration (B.kind 0).input) c,rfl⟩
lemma outputStrip_color (c) : B.stripColor (B.outputStrip c)∈b := by
  apply Eq.mp (congrArg (fun l => B.stripColor (B.outputStrip c)∈l) B.output_children)
  change (B.decoration (Fin.last B.length)).color ((B.kind (Fin.last B.length)).table.mate
    ⟨(B.kind (Fin.last B.length)).output,some c⟩) ∈ _
  rw [(B.decoration (Fin.last B.length)).corner,←(B.decoration (Fin.last B.length)).portColor_child]
  exact List.mem_ofFn.mpr ⟨((B.kind (Fin.last B.length)).childEnumeration (B.kind (Fin.last B.length)).output) c,rfl⟩

/-- Run colors rather than rank sums rule out a strip joining the two short
ends. This is false after forgetting occurrence labels, so proved first on the
named band, before attachment to possibly repeated old facets. -/
lemma no_short_to_short (h : List.Disjoint a b) (c) (d) :
    B.stripForest.root (B.outputStrip d)≠B.inputStrip c := by
  intro he
  have hc := B.stripColor_root (B.outputStrip d)
  rw [he] at hc
  exact List.disjoint_left.mp h (B.inputStrip_color c) (hc ▸ B.outputStrip_color d)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

namespace IntegralCharacterVarieties.TwoFlagBand.RankShape
open scoped Classical
open OccurrenceIncidence.VertexTable
variable {n m r : ℕ} (d : RankShape n m r)
lemma atomic_short_disjoint : List.Disjoint
    ((List.ofFn (Secondary.row : Fin n → Secondary n m)).map some)
    ((List.ofFn (Secondary.col : Fin m → Secondary n m)).map some) := by
  simp only [List.disjoint_left,List.mem_map,List.mem_ofFn]
  rintro x ⟨y,⟨i,rfl⟩,rfl⟩ ⟨z,⟨j,rfl⟩,he⟩
  cases he
lemma atomic_no_short_to_short (c) (e) :
    d.atomicBand.stripForest.root (d.atomicBand.outputStrip e)≠d.atomicBand.inputStrip c :=
  d.atomicBand.no_short_to_short (atomic_short_disjoint (n:=n) (m:=m)) c e
end IntegralCharacterVarieties.TwoFlagBand.RankShape

end OAI
