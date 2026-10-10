import OAI.Computability.TypeSystem.Relational

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
/-- The exact three-copy observations at the special carrier. -/
structure ObservationCode (S : Type u) where
  relational : RelationalCode S
  inner : DoubleCode S
  outer : DoubleCode S
namespace ObservationCode
variable (O : ObservationCode S)
def rename (ρ : Nat → Nat) : ObservationCode S :=
  ⟨O.relational.rename ρ,O.inner.rename ρ,O.outer.rename ρ⟩
def subst (σ : Nat → Expr S) : ObservationCode S :=
  ⟨O.relational.subst σ,O.inner.subst σ,O.outer.subst σ⟩
def copies : ThreeCopyCode S := ⟨O.relational.logical,O.relational.probe.raw,O.inner,O.outer⟩
def carrier := O.copies.carrier O.relational.probe.carrier
def tagged (L : LogicCode S) (t : Fin 3) (x : Expr S) :=
  O.copies.tagged L t O.relational.probe.carrier x
def bitInner (L : LogicCode S) (y : Expr S) := O.copies.bitInner L O.relational.probe.carrier y
def bitOuter (L : LogicCode S) (y : Expr S) := O.copies.bitOuter L O.relational.probe.carrier y
def observe (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) :=
  O.copies.observe L O.relational.probe.carrier y (O.relational.probeFor L KY KP i)
def observeBody (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) :=
  (O.rename Nat.succ).observe (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (.var 0) (y.rename Nat.succ)
def compareBody (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  (L.rename Nat.succ).iff (O.observeBody L KY KP y) (O.observeBody L KY KP z)
def compare (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  KP.all (O.relational.channel.predicateType O.relational.probe.carrier) (O.compareBody L KY KP y z)
def ae (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  L.conj (L.iff (O.bitInner L y) (O.bitInner L z))
    (L.conj (L.iff (O.bitOuter L y) (O.bitOuter L z)) (O.compare L KY KP y z))

theorem rename_comp (ρ τ : Nat → Nat) : (O.rename τ).rename ρ = O.rename (ρ ∘ τ) := by
  cases O; simp only [rename,RelationalCode.rename_comp,DoubleCode.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (O.rename ρ).subst σ = O.subst (σ ∘ ρ) := by
  cases O; simp only [rename,subst,RelationalCode.subst_rename,DoubleCode.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (O.subst σ).rename ρ = O.subst (fun i => (σ i).rename ρ) := by
  cases O; simp only [rename,subst,RelationalCode.rename_subst,DoubleCode.rename_subst]
theorem instantiate_raise (a : Expr S) : (O.rename Nat.succ).subst (Expr.single a) = O := by
  cases O; simp only [rename,subst,RelationalCode.instantiate_raise,DoubleCode.instantiate_raise]
theorem copies_rename (ρ : Nat → Nat) : O.copies.rename ρ = (O.rename ρ).copies := rfl
theorem copies_subst (σ : Nat → Expr S) : O.copies.subst σ = (O.subst σ).copies := rfl
theorem carrier_rename (ρ : Nat → Nat) :
    (O.carrier ).rename ρ = (O.rename ρ).carrier  := by
  simp only [carrier,ThreeCopyCode.carrier_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem carrier_subst (σ : Nat → Expr S) :
    (O.carrier ).subst σ = (O.subst σ).carrier  := by
  simp only [carrier,ThreeCopyCode.carrier_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem tagged_rename (L : LogicCode S) (t : Fin 3) (x : Expr S) (ρ : Nat → Nat) :
    (O.tagged L t x).rename ρ = (O.rename ρ).tagged (L.rename ρ) t (x.rename ρ) := by
  simp only [tagged,ThreeCopyCode.tagged_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (x : Expr S) (σ : Nat → Expr S) :
    (O.tagged L t x).subst σ = (O.subst σ).tagged (L.subst σ) t (x.subst σ) := by
  simp only [tagged,ThreeCopyCode.tagged_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitInner_rename (L : LogicCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.bitInner L y).rename ρ = (O.rename ρ).bitInner (L.rename ρ) (y.rename ρ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem bitInner_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitInner L y).subst σ = (O.subst σ).bitInner (L.subst σ) (y.subst σ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitOuter_rename (L : LogicCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.bitOuter L y).rename ρ = (O.rename ρ).bitOuter (L.rename ρ) (y.rename ρ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem bitOuter_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitOuter L y).subst σ = (O.subst σ).bitOuter (L.subst σ) (y.subst σ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observe_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (ρ : Nat → Nat) :
    (O.observe L KY KP i y).rename ρ = (O.rename ρ).observe (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (y.rename ρ) := by
  simp only [observe,ThreeCopyCode.observe_rename,copies_rename,ProbeCode.carrier_rename,RelationalCode.probeFor_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem observe_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (σ : Nat → Expr S) :
    (O.observe L KY KP i y).subst σ = (O.subst σ).observe (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (y.subst σ) := by
  simp only [observe,ThreeCopyCode.observe_subst,copies_subst,ProbeCode.carrier_subst,RelationalCode.probeFor_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observeBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.observeBody L KY KP y).rename (Expr.liftRen ρ) = (O.rename ρ).observeBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) := by
  simp only [observeBody,observe_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem observeBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.observeBody L KY KP y).subst (Expr.liftSub σ) = (O.subst σ).observeBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) := by
  simp only [observeBody,observe_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem compareBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.compareBody L KY KP y z).rename (Expr.liftRen ρ) = (O.rename ρ).compareBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compareBody,LogicCode.iff_rename,observeBody_rename,LogicCode.rename_comp]
  try rfl
theorem compareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compareBody L KY KP y z).subst (Expr.liftSub σ) = (O.subst σ).compareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,observeBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  try rfl
theorem compare_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.compare L KY KP y z).rename ρ = (O.rename ρ).compare (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compare,QuantifierCode.all_rename,RelationalCode.p_type_rename,compareBody_rename]
  try rfl
theorem compare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compare L KY KP y z).subst σ = (O.subst σ).compare (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst,compareBody_subst]
  try rfl
theorem ae_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.ae L KY KP y z).rename ρ = (O.rename ρ).ae (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [ae,LogicCode.conj_rename,LogicCode.iff_rename,bitInner_rename,bitOuter_rename,compare_rename]
  try rfl
theorem ae_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.ae L KY KP y z).subst σ = (O.subst σ).ae (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [ae,LogicCode.conj_subst,LogicCode.iff_subst,bitInner_subst,bitOuter_subst,compare_subst]
  try rfl
theorem observeBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (y i : Expr S) :
    (O.observeBody L KY KP y).instantiate i = O.observe L KY KP i y := by
  simp only [observeBody,Expr.instantiate,observe_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem compareBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (y z i : Expr S) :
    (O.compareBody L KY KP y z).instantiate i = L.iff (O.observe L KY KP i y) (O.observe L KY KP i z) := by
  change ((L.rename Nat.succ).iff (O.observeBody L KY KP y) (O.observeBody L KY KP z)).subst (Expr.single i) = _
  rw [LogicCode.iff_subst,LogicCode.instantiate_raise]
  change L.iff ((O.observeBody L KY KP y).instantiate i) ((O.observeBody L KY KP z).instantiate i) = _
  rw [observeBody_instantiate,observeBody_instantiate]
end ObservationCode
end

section
universe u v
variable {S : Type u} {P : Specification S} {α : Type v}
namespace LogicCode
variable (L : LogicCode S)
/-- Right-associated finite disjunction used by the source query object. -/
def choices (xs : List α) (mark property : α → Expr S) : Expr S :=
  xs.foldr (fun t Q => L.disj (L.conj (mark t) (property t)) Q) L.bottom

theorem choices_nil (mark property : α → Expr S) : L.choices [] mark property = L.bottom := rfl
theorem choices_cons (t : α) (ts : List α) (mark property : α → Expr S) :
    L.choices (t::ts) mark property = L.disj (L.conj (mark t) (property t)) (L.choices ts mark property) := rfl

theorem choices_rename (xs : List α) (mark property : α → Expr S) (ρ : Nat → Nat) :
    (L.choices xs mark property).rename ρ =
      (L.rename ρ).choices xs (fun t => (mark t).rename ρ) (fun t => (property t).rename ρ) := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp only [choices_cons,disj_rename,conj_rename,ih]

theorem choices_subst (xs : List α) (mark property : α → Expr S) (σ : Nat → Expr S) :
    (L.choices xs mark property).subst σ =
      (L.subst σ).choices xs (fun t => (mark t).subst σ) (fun t => (property t).subst σ) := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp only [choices_cons,disj_subst,conj_subst,ih]
end LogicCode
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {mark property : α → Expr S}

theorem choices_formula (xs : List α) (hm : ∀ t ∈ xs, L.Formula (mark t))
    (hp : ∀ t ∈ xs, L.Formula (property t)) : L.Formula (L.code.choices xs mark property) := by
  induction xs with
  | nil => exact L.bottom_formula
  | cons t ts ih =>
    exact L.disj_formula (L.conj_formula (hm t (by simp)) (hp t (by simp)))
      (ih (fun s hs => hm s (by simp [hs])) (fun s hs => hp s (by simp [hs])))

theorem choices_false (xs : List α) (hm : ∀ t ∈ xs, L.Formula (mark t))
    (hp : ∀ t ∈ xs, L.Formula (property t))
    (hn : ∀ t ∈ xs, Proves P Γ γ (L.neg (mark t))) :
    Equivalent P Γ γ (L.code.choices xs mark property) L.bottom := by
  induction xs with
  | nil =>
    obtain ⟨s,hs⟩ := L.bottom_formula.sorted L
    exact .refl hs
  | cons t ts ih =>
    have ht := hm t (by simp)
    have hpt := hp t (by simp)
    have hnt := hn t (by simp)
    have hc := L.choices_formula ts (fun s hs => hm s (by simp [hs])) (fun s hs => hp s (by simp [hs]))
    have hi := ih (fun s hs => hm s (by simp [hs])) (fun s hs => hp s (by simp [hs]))
      (fun s hs => hn s (by simp [hs]))
    apply L.equivalent_of_iff (L.choices_formula (t::ts) hm hp) L.bottom_formula
    change Proves P Γ γ (L.iff (L.disj (L.conj (mark t) (property t)) (L.code.choices ts mark property)) L.bottom)
    pts_pl L using [hnt,hi]

theorem choices_select [DecidableEq α] (xs : List α) (q : α) (hq : q ∈ xs)
    (hnd : xs.Nodup) (hm : ∀ t ∈ xs, L.Formula (mark t))
    (hp : ∀ t ∈ xs, L.Formula (property t))
    (hn : ∀ t ∈ xs, Proves P Γ γ (L.code.sign (decide (q = t)) (mark t))) :
    Equivalent P Γ γ (L.code.choices xs mark property) (property q) := by
  induction xs with
  | nil => simp at hq
  | cons t ts ih =>
    have ht := hm t (by simp)
    have hpt := hp t (by simp)
    have hmt : ∀ s ∈ ts, L.Formula (mark s) := fun s hs => hm s (by simp [hs])
    have hps : ∀ s ∈ ts, L.Formula (property s) := fun s hs => hp s (by simp [hs])
    have hc := L.choices_formula ts hmt hps
    have hnt := hn t (by simp)
    by_cases he : q = t
    · subst q
      have hi := L.choices_false ts hmt hps (fun s hs => by
        have hne : t ≠ s := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hs)
        simpa only [hne,decide_false,LogicCode.sign,Bool.false_eq_true,ite_false,LogicSetup.code_neg] using hn s (by simp [hs]))
      simp only [decide_true,LogicCode.sign,ite_true] at hnt
      apply L.equivalent_of_iff (L.choices_formula (t::ts) hm hp) hpt
      change Proves P Γ γ (L.iff (L.disj (L.conj (mark t) (property t)) (L.code.choices ts mark property)) (property t))
      pts_pl L using [hnt,hi]
    · have hqt : q ∈ ts := (List.mem_cons.mp hq).resolve_left he
      have hi := ih hqt (List.nodup_cons.mp hnd).2 hmt hps (fun s hs => hn s (by simp [hs]))
      have hqp := hp q hq
      simp only [he,decide_false,LogicCode.sign,Bool.false_eq_true,ite_false] at hnt
      apply L.equivalent_of_iff (L.choices_formula (t::ts) hm hp) hqp
      change Proves P Γ γ (L.iff (L.disj (L.conj (mark t) (property t)) (L.code.choices ts mark property)) (property q))
      pts_pl L using [hnt,hi]

namespace Family
variable {L} {T : Expr S} {ms ps : α → Expr S}
theorem choices (xs : List α) (hm : ∀ t ∈ xs, L.Family T (ms t))
    (hp : ∀ t ∈ xs, L.Family T (ps t)) :
    L.Family T ((L.code.rename Nat.succ).choices xs ms ps) := by
  intro Δ δ e a ha ma
  simp only [LogicCode.choices_rename,Expr.instantiate,LogicCode.choices_subst]
  have he : ((L.code.rename Nat.succ).rename (Expr.liftRen e.names)).subst (Expr.single a) = (L.rename e).code := by
    rw [LogicCode.rename_comp]
    have hn : Expr.liftRen e.names ∘ Nat.succ = Nat.succ ∘ e.names := by funext n; rfl
    rw [hn,← LogicCode.rename_comp,LogicCode.instantiate_raise,LogicSetup.code_rename]
  rw [he]
  exact (L.rename e).choices_formula xs (fun t ht => hm t ht Δ δ e a ha ma)
    (fun t ht => hp t ht Δ δ e a ha ma)
end Family
end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace DoubleCode
variable (R : DoubleCode S)
/-- The source's seven structural branches; evaluation tag 7 is excluded. -/
def realizationBody (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) :=
  (L.rename Nat.succ).choices (List.finRange 7)
    (fun t => R.markBody L t.castSucc T c) (fun t => (Q t).compose (R.decodeMap U L T))
def realization (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) :=
  R.second.build (R.bpType T) (R.realizationBody U L T c Q)

theorem realizationBody_instantiate (U : DataWrapper S true) (L : LogicCode S)
    (T c bp : Expr S) (Q : Fin 7 → Expr S) :
    (R.realizationBody U L T c Q).instantiate bp = L.choices (List.finRange 7)
      (fun t => R.mark L t.castSucc T c bp) (fun t => (Q t).instantiate (R.decode U L T bp)) := by
  change ((L.rename Nat.succ).choices _ _ _).subst (Expr.single bp) = _
  rw [LogicCode.choices_subst,LogicCode.instantiate_raise]
  congr 1
  · funext t; exact R.markBody_instantiate _ _ _ _ _
  · funext t
    change ((Q t).compose (R.decodeMap U L T)).instantiate bp = _
    rw [Expr.compose_instantiate,decodeMap_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
    {T c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    {Q : Fin 7 → Expr S} (hQ : ∀ t, L.Family (U.apply T) (Q t))
include h hU hT mT hc mc hs hr hQ

theorem realizationBody_family : L.Family (R.bpType T) (R.realizationBody U L.code T c Q) :=
  .choices _ (fun t _ => h.markBody_family hT mT t.castSucc hc mc)
    (fun t _ => (hQ t).compose (h.decodeMap_typed hU hT mT hs hr) hr)

theorem realization_typed :
    HasType P Γ (R.realization U L.code T c Q) (R.paramType T) ∧
      WellModed γ (R.realization U L.code T c Q) .data :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).1 _
    (h.realizationBody_family hU hT mT hc mc hs hr hQ)

theorem realization_evaluation {bp : Expr S}
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data) :
    Equivalent P Γ γ (R.second.observe (R.bpType T) (R.realization U L.code T c Q) bp)
      (L.code.choices (List.finRange 7) (fun t => R.mark L.code t.castSucc T c bp)
        (fun t => (Q t).instantiate (R.decode U L.code T bp))) := by
  have he := h.second.cancellation (h.bp_sorted hT) (h.bp_mode mT)
    (h.realizationBody_family hU hT mT hc mc hs hr hQ) ⟨hb,mb⟩
  simpa only [DataWrapper.cancelFormula,ite_true,realization,realizationBody_instantiate] using he

theorem realization_query_decoded (t : Fin 7) {p : Expr S}
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Equivalent P Γ γ (R.query U L.code t.castSucc T (R.realization U L.code T c Q) p)
      ((Q t).instantiate (R.decode U L.code T (R.encode U L.code t.castSucc T p))) := by
  have hb := h.encode_typed hU hT mT t.castSucc hp mp
  have hd := h.decode_typed hU hT mT hb.1 hb.2 hs
  have he := h.realization_evaluation hU hT mT hc mc hs hr hQ hb.1 hb.2
  have hm : ∀ u, L.Formula (R.mark L.code (u : Fin 7).castSucc T c (R.encode U L.code t.castSucc T p)) := by
    intro u
    simpa only [markBody_instantiate] using (h.markBody_family hT mT u.castSucc hc mc).instantiate hb.1 hb.2
  have hprop := fun u => (hQ u).instantiate hd.1 hd.2
  have hsel := L.choices_select (List.finRange 7) t (by simp) (by decide)
    (fun u _ => hm u) (fun u _ => hprop u) (fun u _ => by
      have hm := h.encode_mark hU hT mT t.castSucc u.castSucc hp mp hc mc
      have heq : (t.castSucc == u.castSucc) = decide (t = u) := by
        by_cases ht : t = u
        · simp [ht]
        · have hn : t.castSucc ≠ u.castSucc := fun h => ht (Fin.castSucc_inj.mp h)
          simp [ht, hn]
      simpa only [heq] using hm)
  have ho := h.realization_typed hU hT mT hc mc hs hr hQ
  have f₀ := (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ ho.1 ho.2 hb
  have f₁ := L.choices_formula (List.finRange 7) (fun u _ => hm u) (fun u _ => hprop u)
  obtain ⟨a,ha⟩ := f₀.sorted L
  obtain ⟨b,hb⟩ := f₁.sorted L
  obtain ⟨d,hd⟩ := (hprop t).sorted L
  exact he.trans hsel ha hb hd

theorem realization_not_dummy :
    Proves P Γ γ (L.neg (R.isDummy L.code T (R.realization U L.code T c Q))) := by
  have hb := h.bpBottom_typed hT mT
  have hd := h.decode_typed hU hT mT hb.1 hb.2 hs
  have he := h.realization_evaluation hU hT mT hc mc hs hr hQ hb.1 hb.2
  have hm : ∀ u, L.Formula (R.mark L.code (u : Fin 7).castSucc T c (R.bpBottom L.code T)) := by
    intro u
    simpa only [markBody_instantiate] using (h.markBody_family hT mT u.castSucc hc mc).instantiate hb.1 hb.2
  have hprop := fun u => (hQ u).instantiate hd.1 hd.2
  have hfalse := L.choices_false (List.finRange 7) (fun u _ => hm u) (fun u _ => hprop u)
    (fun u _ => h.bottom_mark hT mT u.castSucc hc mc)
  have ho := h.realization_typed hU hT mT hc mc hs hr hQ
  have f₀ := (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ ho.1 ho.2 hb
  have f₁ := L.choices_formula (List.finRange 7) (fun u _ => hm u) (fun u _ => hprop u)
  obtain ⟨a,ha⟩ := f₀.sorted L
  obtain ⟨b,hb⟩ := f₁.sorted L
  obtain ⟨d,hd⟩ := L.bottom_formula.sorted L
  exact L.equivalent_bottom_neg f₀ (he.trans hfalse ha hb hd)
end Formed
end DoubleCode
end

section
universe u
structure SpecializedCode (S : Type u) where
  observation : ObservationCode S
  type : Expr S
namespace SpecializedCode
variable {S : Type u} (B : SpecializedCode S)
def rename (ρ : Nat → Nat) : SpecializedCode S := ⟨B.observation.rename ρ,B.type.rename ρ⟩
def subst (σ : Nat → Expr S) : SpecializedCode S := ⟨B.observation.subst σ,B.type.subst σ⟩
theorem rename_comp (ρ τ : Nat → Nat) : (B.rename ρ).rename τ = B.rename (τ ∘ ρ) := by
  simp only [rename,ObservationCode.rename_comp,Expr.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) : (B.rename ρ).subst σ = B.subst (σ ∘ ρ) := by
  simp only [rename,subst,ObservationCode.subst_rename,Expr.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) : (B.subst σ).rename ρ = B.subst (fun n => (σ n).rename ρ) := by
  simp only [rename,subst,ObservationCode.rename_subst,Expr.rename_subst]
theorem instantiate_raise (a : Expr S) : (B.rename Nat.succ).subst (Expr.single a) = B := by
  simp only [rename,subst,ObservationCode.instantiate_raise,Expr.subst_lift_single]
def relational := B.observation.relational
def baseType := B.relational.baseType B.type
def xType := B.relational.channel.logicalType B.relational.probe.carrier
def yType := B.observation.carrier
def predType := B.relational.channel.predicateType B.baseType
def xPredType := B.relational.channel.predicateType B.relational.probe.carrier
def ev (v y : Expr S) := B.relational.channel.eval B.baseType v y
def gStep (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :=
  L.imp (B.observation.ae L KY KP y z) (L.iff (B.ev v y) (B.ev v z))
def gAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  (B.rename Nat.succ).gStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (y.rename Nat.succ) (.var 0)
def gAt (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  KY.all B.yType (B.gAtBody L KY KP v y)
def gBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).gAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def propertyG (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  KY.all B.yType (B.gBody L KY KP v)
def cStep (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) :=
  L.iff (B.ev v w) (B.observation.ae L KY KP w (B.observation.tagged L t x))
def cAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  (B.rename Nat.succ).cStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (x.rename Nat.succ) (.var 0)
def cAt (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  KY.all B.yType (B.cAtBody L KY KP t v x)
def cBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  (B.rename Nat.succ).cAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (.var 0)
def propertyC (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  L.ex KY B.xType (B.cBody L KY KP t v)
def eStep (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) :=
  L.iff (B.ev v w) (L.disj (B.observation.ae L KY KP w (B.observation.tagged L 0 x)) (B.observation.ae L KY KP w (B.observation.tagged L t x)))
def eAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  (B.rename Nat.succ).eStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (x.rename Nat.succ) (.var 0)
def eAt (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :=
  KY.all B.yType (B.eAtBody L KY KP t v x)
def eBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  (B.rename Nat.succ).eAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (.var 0)
def propertyE (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) :=
  L.ex KY B.xType (B.eBody L KY KP t v)
def rPredStep (L : LogicCode S) (_KY _KP : QuantifierCode S) (v x : Expr S) :=
  B.ev v (B.observation.tagged L 1 x)
def rPredBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).rPredStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def rPred (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.rPredBody L KY KP v)
def rStep (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :=
  L.imp (B.relational.valid L KY KP x) (L.imp (B.ev v (B.observation.tagged L 2 x)) (B.relational.le L KY KP (B.rPred L KY KP v) x))
def rBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).rStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def rAll (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  KY.all B.xType (B.rBody L KY KP v)
def propertyR (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  L.imp (B.relational.extensional L KY KP (B.rPred L KY KP v)) (B.rAll L KY KP v)
theorem baseType_rename (ρ : Nat → Nat) : (B.baseType ).rename ρ = (B.rename ρ).baseType  := by
  simp only [baseType,RelationalCode.baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem baseType_subst (σ : Nat → Expr S) : (B.baseType ).subst σ = (B.subst σ).baseType  := by
  simp only [baseType,RelationalCode.baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem xType_rename (ρ : Nat → Nat) : (B.xType ).rename ρ = (B.rename ρ).xType  := by
  simp only [xType,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem xType_subst (σ : Nat → Expr S) : (B.xType ).subst σ = (B.subst σ).xType  := by
  simp only [xType,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem yType_rename (ρ : Nat → Nat) : (B.yType ).rename ρ = (B.rename ρ).yType  := by
  simp only [yType,ObservationCode.carrier_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem yType_subst (σ : Nat → Expr S) : (B.yType ).subst σ = (B.subst σ).yType  := by
  simp only [yType,ObservationCode.carrier_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem predType_rename (ρ : Nat → Nat) : (B.predType ).rename ρ = (B.rename ρ).predType  := by
  simp only [predType,ChannelCode.predicateType_rename,baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem predType_subst (σ : Nat → Expr S) : (B.predType ).subst σ = (B.subst σ).predType  := by
  simp only [predType,ChannelCode.predicateType_subst,baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem xPredType_rename (ρ : Nat → Nat) : (B.xPredType ).rename ρ = (B.rename ρ).xPredType  := by
  simp only [xPredType,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem xPredType_subst (σ : Nat → Expr S) : (B.xPredType ).subst σ = (B.subst σ).xPredType  := by
  simp only [xPredType,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem ev_rename (v y : Expr S) (ρ : Nat → Nat) : (B.ev v y).rename ρ = (B.rename ρ).ev (v.rename ρ) (y.rename ρ) := by
  simp only [ev,ChannelCode.eval_rename,baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem ev_subst (v y : Expr S) (σ : Nat → Expr S) : (B.ev v y).subst σ = (B.subst σ).ev (v.subst σ) (y.subst σ) := by
  simp only [ev,ChannelCode.eval_subst,baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem gStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (ρ : Nat → Nat) :
    (B.gStep L KY KP v y z).rename ρ = (B.rename ρ).gStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [gStep,LogicCode.imp_rename,LogicCode.iff_rename,ObservationCode.ae_rename,ev_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem gStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (σ : Nat → Expr S) :
    (B.gStep L KY KP v y z).subst σ = (B.subst σ).gStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [gStep,LogicCode.imp_subst,LogicCode.iff_subst,ObservationCode.ae_subst,ev_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.gAtBody L KY KP v y).rename (Expr.liftRen ρ) = (B.rename ρ).gAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [gAtBody,gStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem gAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAtBody L KY KP v y).subst (Expr.liftSub σ) = (B.subst σ).gAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAtBody,gStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem gAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :
    (B.gAtBody L KY KP v y).instantiate z = B.gStep L KY KP v y z := by
  simp only [gAtBody,Expr.instantiate,gStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem gAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.gAt L KY KP v y).rename ρ = (B.rename ρ).gAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [gAt,QuantifierCode.all_rename,yType_rename,gAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem gAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAt L KY KP v y).subst σ = (B.subst σ).gAt (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAt,QuantifierCode.all_subst,yType_subst,gAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.gBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).gBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [gBody,gAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem gBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.gBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).gBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [gBody,gAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem gBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :
    (B.gBody L KY KP v).instantiate y = B.gAt L KY KP v y := by
  simp only [gBody,Expr.instantiate,gAt_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem propertyG_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyG L KY KP v).rename ρ = (B.rename ρ).propertyG (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [propertyG,QuantifierCode.all_rename,yType_rename,gBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyG_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyG L KY KP v).subst σ = (B.subst σ).propertyG (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyG,QuantifierCode.all_subst,yType_subst,gBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (ρ : Nat → Nat) :
    (B.cStep L KY KP t v x w).rename ρ = (B.rename ρ).cStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) (w.rename ρ) := by
  simp only [cStep,LogicCode.iff_rename,ev_rename,ObservationCode.ae_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem cStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.cStep L KY KP t v x w).subst σ = (B.subst σ).cStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [cStep,LogicCode.iff_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.cAtBody L KY KP t v x).rename (Expr.liftRen ρ) = (B.rename ρ).cAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [cAtBody,cStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem cAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).cAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAtBody,cStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem cAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) :
    (B.cAtBody L KY KP t v x).instantiate w = B.cStep L KY KP t v x w := by
  simp only [cAtBody,Expr.instantiate,cStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem cAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.cAt L KY KP t v x).rename ρ = (B.rename ρ).cAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [cAt,QuantifierCode.all_rename,yType_rename,cAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem cAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAt L KY KP t v x).subst σ = (B.subst σ).cAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAt,QuantifierCode.all_subst,yType_subst,cAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.cBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).cBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [cBody,cAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem cBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.cBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).cBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [cBody,cAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem cBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :
    (B.cBody L KY KP t v).instantiate x = B.cAt L KY KP t v x := by
  simp only [cBody,Expr.instantiate,cAt_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem propertyC_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyC L KY KP t v).rename ρ = (B.rename ρ).propertyC (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [propertyC,LogicCode.ex_rename,xType_rename,cBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyC_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyC L KY KP t v).subst σ = (B.subst σ).propertyC (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyC,LogicCode.ex_subst,xType_subst,cBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (ρ : Nat → Nat) :
    (B.eStep L KY KP t v x w).rename ρ = (B.rename ρ).eStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) (w.rename ρ) := by
  simp only [eStep,LogicCode.iff_rename,LogicCode.disj_rename,ev_rename,ObservationCode.ae_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem eStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.eStep L KY KP t v x w).subst σ = (B.subst σ).eStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [eStep,LogicCode.iff_subst,LogicCode.disj_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.eAtBody L KY KP t v x).rename (Expr.liftRen ρ) = (B.rename ρ).eAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [eAtBody,eStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem eAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).eAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAtBody,eStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem eAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) :
    (B.eAtBody L KY KP t v x).instantiate w = B.eStep L KY KP t v x w := by
  simp only [eAtBody,Expr.instantiate,eStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem eAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.eAt L KY KP t v x).rename ρ = (B.rename ρ).eAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [eAt,QuantifierCode.all_rename,yType_rename,eAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem eAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAt L KY KP t v x).subst σ = (B.subst σ).eAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAt,QuantifierCode.all_subst,yType_subst,eAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.eBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).eBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [eBody,eAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem eBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.eBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).eBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [eBody,eAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem eBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) :
    (B.eBody L KY KP t v).instantiate x = B.eAt L KY KP t v x := by
  simp only [eBody,Expr.instantiate,eAt_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem propertyE_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyE L KY KP t v).rename ρ = (B.rename ρ).propertyE (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [propertyE,LogicCode.ex_rename,xType_rename,eBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyE_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyE L KY KP t v).subst σ = (B.subst σ).propertyE (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyE,LogicCode.ex_subst,xType_subst,eBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.rPredStep L KY KP v x).rename ρ = (B.rename ρ).rPredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [rPredStep,ev_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rPredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rPredStep L KY KP v x).subst σ = (B.subst σ).rPredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rPredStep,ev_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rPredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).rPredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rPredBody,rPredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem rPredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rPredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPredBody,rPredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rPredBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.rPredBody L KY KP v).instantiate x = B.rPredStep L KY KP v x := by
  simp only [rPredBody,Expr.instantiate,rPredStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem rPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rPred L KY KP v).rename ρ = (B.rename ρ).rPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rPred,ChannelCode.pred_rename,ProbeCode.carrier_rename,rPredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem rPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPred L KY KP v).subst σ = (B.subst σ).rPred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPred,ChannelCode.pred_subst,ProbeCode.carrier_subst,rPredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem rStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.rStep L KY KP v x).rename ρ = (B.rename ρ).rStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [rStep,LogicCode.imp_rename,RelationalCode.valid_rename,ev_rename,ObservationCode.tagged_rename,RelationalCode.le_rename,rPred_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rStep L KY KP v x).subst σ = (B.subst σ).rStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rStep,LogicCode.imp_subst,RelationalCode.valid_subst,ev_subst,ObservationCode.tagged_subst,RelationalCode.le_subst,rPred_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).rBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rBody,rStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem rBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rBody,rStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.rBody L KY KP v).instantiate x = B.rStep L KY KP v x := by
  simp only [rBody,Expr.instantiate,rStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem rAll_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rAll L KY KP v).rename ρ = (B.rename ρ).rAll (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rAll,QuantifierCode.all_rename,xType_rename,rBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rAll_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rAll L KY KP v).subst σ = (B.subst σ).rAll (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rAll,QuantifierCode.all_subst,xType_subst,rBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem propertyR_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyR L KY KP v).rename ρ = (B.rename ρ).propertyR (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [propertyR,LogicCode.imp_rename,RelationalCode.extensional_rename,rPred_rename,rAll_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyR_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyR L KY KP v).subst σ = (B.subst σ).propertyR (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyR,LogicCode.imp_subst,RelationalCode.extensional_subst,rPred_subst,rAll_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ObservationCode
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (O : ObservationCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
structure Formed : Prop where
  relational : O.relational.Formed L I J k p n g j h
  inner : O.inner.Formed L p k p
  outer : O.outer.Formed L p k j
namespace Formed
variable {O L I J k p n g j h} (H : O.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (O.rename e.names).Formed (L.rename e) I J k p n g j h :=
  ⟨H.relational.rename e,H.inner.rename e,H.outer.rename e⟩
theorem copies_formed : O.copies.Formed L k j p k p k j :=
  ⟨H.relational.channel.logical,H.relational.probe.raw,H.inner,H.outer⟩
theorem carrier_sorted : SortedAt P Γ O.carrier j :=
  H.outer.sorted (H.inner.sorted (H.relational.probe.raw.sorted H.relational.probe.carrier_sorted))
theorem carrier_mode : WellModed γ O.carrier .data :=
  H.outer.mode (H.inner.mode (H.relational.probe.raw.mode H.relational.probe.carrier_mode))
theorem tagged_typed {x : Expr S} (t : Fin 3)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data) :
    HasType P Γ (O.tagged L.code t x) O.carrier ∧ WellModed γ (O.tagged L.code t x) .data :=
  H.copies_formed.tagged_typed H.relational.probe.carrier_sorted H.relational.probe.carrier_mode t hx mx
theorem bitInner_formula {y : Expr S} (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data) :
    L.Formula (O.bitInner L.code y) :=
  H.copies_formed.bitInner_formula H.relational.probe.carrier_sorted H.relational.probe.carrier_mode hy my
theorem bitOuter_formula {y : Expr S} (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data) :
    L.Formula (O.bitOuter L.code y) :=
  H.copies_formed.bitOuter_formula H.relational.probe.carrier_sorted H.relational.probe.carrier_mode hy my
theorem observe_formula {i y : Expr S}
    (hi : HasType P Γ i (O.relational.channel.predicateType O.relational.probe.carrier)) (mi : WellModed γ i .data)
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data) :
    L.Formula (O.observe L.code KY.code KP.code i y) := by
  have hp := H.relational.probeFor_typed KY KP hi mi
  exact H.copies_formed.observe_formula H.relational.probe.carrier_sorted H.relational.probe.carrier_mode hy my hp.1 hp.2
theorem observeBody_family {y : Expr S} (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data) :
    L.Family (O.relational.channel.predicateType O.relational.probe.carrier) (O.observeBody L.code KY.code KP.code y) := by
  intro Δ δ e i hi mi
  rw [observeBody_rename,observeBody_instantiate]
  exact (H.rename e).observe_formula (KY.rename e) (KP.rename e)
    (by simpa only [RelationalCode.p_type_rename,ObservationCode.rename] using hi) mi
    (by simpa only [carrier_rename] using e.typing hy) (e.moded my)
theorem compareBody_family {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data) :
    L.Family (O.relational.channel.predicateType O.relational.probe.carrier) (O.compareBody L.code KY.code KP.code y z) :=
  (H.observeBody_family KY KP hy my).code_iff (H.observeBody_family KY KP hz mz)
theorem compare_formula {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data) :
    L.Formula (O.compare L.code KY.code KP.code y z) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted)
    (H.relational.channel.predicate_mode H.relational.probe.carrier_mode)
    (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted s hs) (H.compareBody_family KY KP hy my hz mz)
theorem ae_formula {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data) :
    L.Formula (O.ae L.code KY.code KP.code y z) :=
  L.conj_formula (L.iff_formula (H.bitInner_formula hy my) (H.bitInner_formula hz mz))
    (L.conj_formula (L.iff_formula (H.bitOuter_formula hy my) (H.bitOuter_formula hz mz))
      (H.compare_formula KY KP hy my hz mz))

/-- The source's canonical O_i(x^t) evaluation is the genuine le(i,x). -/
theorem tagged_observe {i x : Expr S} (t : Fin 3)
    (hi : HasType P Γ i (O.relational.channel.predicateType O.relational.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (O.observe L.code KY.code KP.code i (O.tagged L.code t x))
      (O.relational.le L.code KY.code KP.code i x) := by
  have hp := H.relational.probeFor_typed KY KP hi mi
  exact H.copies_formed.tagged_observe H.relational.probe.carrier_sorted H.relational.probe.carrier_mode t hx mx hp.1 hp.2
end Formed
end ObservationCode

namespace ObservationCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {O : ObservationCode S}
    (H : O.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem compare_intro {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) i,
      HasType P Δ i ((O.rename e.names).relational.channel.predicateType (O.rename e.names).relational.probe.carrier) →
      WellModed δ i .data → Equivalent P Δ δ
        ((O.rename e.names).observe (L.rename e).code (KY.rename e).code (KP.rename e).code i (y.rename e.names))
        ((O.rename e.names).observe (L.rename e).code (KY.rename e).code (KP.rename e).code i (z.rename e.names))) :
    Proves P Γ γ (O.compare L.code KY.code KP.code y z) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted)
    (H.relational.channel.predicate_mode H.relational.probe.carrier_mode)
    (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted s hs) (H.compareBody_family KY KP hy my hz mz)
  intro Δ δ e i hi mi
  rw [compareBody_rename,compareBody_instantiate]
  have hi' : HasType P Δ i ((O.rename e.names).relational.channel.predicateType (O.rename e.names).relational.probe.carrier) := by
    simpa only [RelationalCode.p_type_rename,ObservationCode.rename] using hi
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).observe_formula (KY.rename e) (KP.rename e) hi' mi (by simpa only [carrier_rename] using e.typing hy) (e.moded my))
    ((H.rename e).observe_formula (KY.rename e) (KP.rename e) hi' mi (by simpa only [carrier_rename] using e.typing hz) (e.moded mz))
    (hh Δ δ e i hi' mi)

theorem compare_elim {y z i : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (hi : HasType P Γ i (O.relational.channel.predicateType O.relational.probe.carrier)) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (O.compare L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (O.observe L.code KY.code KP.code i y) (O.observe L.code KY.code KP.code i z) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have hh := L.all_elim_family KP (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted)
    (H.relational.channel.predicate_mode H.relational.probe.carrier_mode)
    (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted s hs) (H.compareBody_family KY KP hy my hz mz) hi mi he
  rw [compareBody_instantiate,LogicSetup.code_iff] at hh
  exact L.equivalent_of_iff (H.observe_formula KY KP hi mi hy my) (H.observe_formula KY KP hi mi hz mz) hh

theorem ae_intro {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (hi : Equivalent P Γ γ (O.bitInner L.code y) (O.bitInner L.code z))
    (ho : Equivalent P Γ γ (O.bitOuter L.code y) (O.bitOuter L.code z))
    (hc : Proves P Γ γ (O.compare L.code KY.code KP.code y z)) :
    Proves P Γ γ (O.ae L.code KY.code KP.code y z) :=
  L.conj_intro (L.iff_formula (H.bitInner_formula hy my) (H.bitInner_formula hz mz))
    (L.conj_formula (L.iff_formula (H.bitOuter_formula hy my) (H.bitOuter_formula hz mz))
      (H.compare_formula KY KP hy my hz mz))
    (L.iff_of_equivalent (H.bitInner_formula hy my) (H.bitInner_formula hz mz) hi)
    (L.conj_intro (L.iff_formula (H.bitOuter_formula hy my) (H.bitOuter_formula hz mz))
      (H.compare_formula KY KP hy my hz mz)
      (L.iff_of_equivalent (H.bitOuter_formula hy my) (H.bitOuter_formula hz mz) ho) hc)

theorem ae_elim {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (O.ae L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (O.bitInner L.code y) (O.bitInner L.code z) ∧
    Equivalent P Γ γ (O.bitOuter L.code y) (O.bitOuter L.code z) ∧
    Proves P Γ γ (O.compare L.code KY.code KP.code y z) := by
  have fi := L.iff_formula (H.bitInner_formula hy my) (H.bitInner_formula hz mz)
  have fo := L.iff_formula (H.bitOuter_formula hy my) (H.bitOuter_formula hz mz)
  have fc := H.compare_formula KY KP hy my hz mz
  have hi := L.conj_left fi (L.conj_formula fo fc) he
  have hr := L.conj_right fi (L.conj_formula fo fc) he
  exact ⟨L.equivalent_of_iff (H.bitInner_formula hy my) (H.bitInner_formula hz mz) hi,
    L.equivalent_of_iff (H.bitOuter_formula hy my) (H.bitOuter_formula hz mz) (L.conj_left fo fc hr),
    L.conj_right fo fc hr⟩
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {O : ObservationCode S}
    (H : O.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem carrier_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {y : Expr S}
    (hy : HasType P Γ y O.carrier) : HasType P Δ (y.rename e.names) (O.rename e.names).carrier := by
  simpa only [carrier_rename] using e.typing hy

omit H in
theorem compare_proof_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {y z : Expr S}
    (he : Proves P Γ γ (O.compare L.code KY.code KP.code y z)) :
    Proves P Δ δ ((O.rename e.names).compare (L.rename e).code (KY.rename e).code (KP.rename e).code
      (y.rename e.names) (z.rename e.names)) := by
  simpa only [compare_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using he.rename e

theorem compare_refl {y : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    : Proves P Γ γ (O.compare L.code KY.code KP.code y y) := by
  apply H.compare_intro KY KP hy my hy my
  intro Δ δ e i hi mi
  have fy := (H.rename e).observe_formula (KY.rename e) (KP.rename e) hi mi (carrier_typed_rename (O := O) e hy) (e.moded my)
  exact fy.equivalent_refl

theorem compare_symm {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (e0 : Proves P Γ γ (O.compare L.code KY.code KP.code y z))
    : Proves P Γ γ (O.compare L.code KY.code KP.code z y) := by
  apply H.compare_intro KY KP hz mz hy my
  intro Δ δ e i hi mi
  have fy := (H.rename e).observe_formula (KY.rename e) (KP.rename e) hi mi (carrier_typed_rename (O := O) e hy) (e.moded my)
  have fz := (H.rename e).observe_formula (KY.rename e) (KP.rename e) hi mi (carrier_typed_rename (O := O) e hz) (e.moded mz)
  have d0 := (H.rename e).compare_elim (KY.rename e) (KP.rename e)
    (carrier_typed_rename (O := O) e hy) (e.moded my) (carrier_typed_rename (O := O) e hz) (e.moded mz) hi mi
    (compare_proof_rename (O := O) KY KP e e0)
  exact d0.symm

theorem compare_trans {y z w : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (hw : HasType P Γ w O.carrier) (mw : WellModed γ w .data)
    (e0 : Proves P Γ γ (O.compare L.code KY.code KP.code y z))
    (e1 : Proves P Γ γ (O.compare L.code KY.code KP.code z w))
    : Proves P Γ γ (O.compare L.code KY.code KP.code y w) := by
  apply H.compare_intro KY KP hy my hw mw
  intro Δ δ e i hi mi
  have fy := (H.rename e).observe_formula (KY.rename e) (KP.rename e) hi mi (carrier_typed_rename (O := O) e hy) (e.moded my)
  have fz := (H.rename e).observe_formula (KY.rename e) (KP.rename e) hi mi (carrier_typed_rename (O := O) e hz) (e.moded mz)
  have fw := (H.rename e).observe_formula (KY.rename e) (KP.rename e) hi mi (carrier_typed_rename (O := O) e hw) (e.moded mw)
  have d0 := (H.rename e).compare_elim (KY.rename e) (KP.rename e)
    (carrier_typed_rename (O := O) e hy) (e.moded my) (carrier_typed_rename (O := O) e hz) (e.moded mz) hi mi
    (compare_proof_rename (O := O) KY KP e e0)
  have d1 := (H.rename e).compare_elim (KY.rename e) (KP.rename e)
    (carrier_typed_rename (O := O) e hz) (e.moded mz) (carrier_typed_rename (O := O) e hw) (e.moded mw) hi mi
    (compare_proof_rename (O := O) KY KP e e1)
  exact fy.equivalent_trans fz fw d0 d1

theorem ae_refl {y : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    : Proves P Γ γ (O.ae L.code KY.code KP.code y y) := by
  apply H.ae_intro KY KP hy my hy my
  · exact (H.bitInner_formula hy my).equivalent_refl
  · exact (H.bitOuter_formula hy my).equivalent_refl
  · exact H.compare_refl KY KP hy my 

theorem ae_symm {y z : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (e0 : Proves P Γ γ (O.ae L.code KY.code KP.code y z))
    : Proves P Γ γ (O.ae L.code KY.code KP.code z y) := by
  obtain ⟨i0,o0,c0⟩ := H.ae_elim KY KP hy my hz mz e0
  apply H.ae_intro KY KP hz mz hy my
  · exact i0.symm
  · exact o0.symm
  · exact H.compare_symm KY KP hy my hz mz c0

theorem ae_trans {y z w : Expr S}
    (hy : HasType P Γ y O.carrier) (my : WellModed γ y .data)
    (hz : HasType P Γ z O.carrier) (mz : WellModed γ z .data)
    (hw : HasType P Γ w O.carrier) (mw : WellModed γ w .data)
    (e0 : Proves P Γ γ (O.ae L.code KY.code KP.code y z))
    (e1 : Proves P Γ γ (O.ae L.code KY.code KP.code z w))
    : Proves P Γ γ (O.ae L.code KY.code KP.code y w) := by
  obtain ⟨i0,o0,c0⟩ := H.ae_elim KY KP hy my hz mz e0
  obtain ⟨i1,o1,c1⟩ := H.ae_elim KY KP hz mz hw mw e1
  apply H.ae_intro KY KP hy my hw mw
  · exact (H.bitInner_formula hy my).equivalent_trans (H.bitInner_formula hz mz) (H.bitInner_formula hw mw) i0 i1
  · exact (H.bitOuter_formula hy my).equivalent_trans (H.bitOuter_formula hz mz) (H.bitOuter_formula hw mw) o0 o1
  · exact H.compare_trans KY KP hy my hz mz hw mw c0 c1
end ObservationCode.Formed
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} (L : LogicSetup P Γ γ C) {A A' B B' : Expr S}

theorem iff_equivalent (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.iff A B) (L.iff A' B') := by
  apply L.equivalent_of_iff (L.iff_formula hA hB) (L.iff_formula hA' hB')
  pts_pl L using [eA,eB]

theorem imp_equivalent (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.imp A B) (L.imp A' B') := by
  apply L.equivalent_of_iff (L.imp_formula hA hB) (L.imp_formula hA' hB')
  pts_pl L using [eA,eB]

theorem conj_equivalent (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.conj A B) (L.conj A' B') := by
  apply L.equivalent_of_iff (L.conj_formula hA hB) (L.conj_formula hA' hB')
  pts_pl L using [eA,eB]

theorem disj_congr (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.disj A B) (L.disj A' B') := by
  apply L.equivalent_of_iff (L.disj_formula hA hB) (L.disj_formula hA' hB')
  pts_pl L using [eA,eB]

theorem signed_agree (b : Bool) (hA : L.Formula A) (hB : L.Formula B)
    (ha : Proves P Γ γ (L.code.sign b A)) (hb : Proves P Γ γ (L.code.sign b B)) :
    Equivalent P Γ γ A B := by
  apply L.equivalent_of_iff hA hB
  cases b
  · change Proves P Γ γ (L.neg A) at ha
    change Proves P Γ γ (L.neg B) at hb
    pts_pl L using [ha,hb]
  · change Proves P Γ γ A at ha
    change Proves P Γ γ B at hb
    pts_pl L using [ha,hb]
theorem signed_disagree (b c : Bool) (hbc : b ≠ c) (hA : L.Formula A) (hB : L.Formula B)
    (ha : Proves P Γ γ (L.code.sign b A)) (hb : Proves P Γ γ (L.code.sign c B)) :
    Proves P Γ γ (L.neg (L.iff A B)) := by
  cases b <;> cases c <;> try contradiction
  · change Proves P Γ γ (L.neg A) at ha
    change Proves P Γ γ B at hb
    pts_pl L using [ha,hb]
  · change Proves P Γ γ A at ha
    change Proves P Γ γ (L.neg B) at hb
    pts_pl L using [ha,hb]
theorem agreed_bits {D : Expr S} (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B') (hD : L.Formula D)
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.conj (L.iff A A') (L.conj (L.iff B B') D)) D := by
  apply L.equivalent_of_iff (L.conj_formula (L.iff_formula hA hA') (L.conj_formula (L.iff_formula hB hB') hD)) hD
  pts_pl L using [eA,eB]
theorem different_bits_left {D : Expr S} (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B') (hD : L.Formula D)
    (hn : Proves P Γ γ (L.neg (L.iff A A'))) :
    Proves P Γ γ (L.neg (L.conj (L.iff A A') (L.conj (L.iff B B') D))) := by
  pts_pl L using [hn]
theorem different_bits_right {D : Expr S} (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B') (hD : L.Formula D)
    (hn : Proves P Γ γ (L.neg (L.iff B B'))) :
    Proves P Γ γ (L.neg (L.conj (L.iff A A') (L.conj (L.iff B B') D))) := by
  pts_pl L using [hn]
end PureTypeSystem.Labelled.LogicSetup

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace ObservationCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {O : ObservationCode S}
    (H : O.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem tagged_bitInner {x : Expr S} (t : Fin 3)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data) :
    Proves P Γ γ (L.code.sign (t == 1) (O.bitInner L.code (O.tagged L.code t x))) :=
  H.copies_formed.tagged_bitInner H.relational.probe.carrier_sorted H.relational.probe.carrier_mode t hx mx

theorem tagged_bitOuter {x : Expr S} (t : Fin 3)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data) :
    Proves P Γ γ (L.code.sign (t == 2) (O.bitOuter L.code (O.tagged L.code t x))) :=
  H.copies_formed.tagged_bitOuter H.relational.probe.carrier_sorted H.relational.probe.carrier_mode t hx mx

theorem compare_tagged {x z : Expr S} (t u : Fin 3)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data)
    (hz : HasType P Γ z (O.relational.channel.logicalType O.relational.probe.carrier)) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (O.compare L.code KY.code KP.code (O.tagged L.code t x) (O.tagged L.code u z))
      (O.relational.xCompare L.code KY.code KP.code x z) := by
  have ht := H.tagged_typed t hx mx
  have hu := H.tagged_typed u hz mz
  apply L.all_equivalent_future KP (H.relational.channel.predicate_sorted H.relational.probe.carrier_sorted)
    (H.relational.channel.predicate_mode H.relational.probe.carrier_mode)
    (H.compareBody_family KY KP ht.1 ht.2 hu.1 hu.2) (H.relational.xCompareBody_family KY KP hx mx hz mz)
  intro Δ δ e i hi mi
  rw [compareBody_rename,compareBody_instantiate,RelationalCode.xCompareBody_rename,RelationalCode.xCompareBody_instantiate,
    tagged_rename,tagged_rename]
  have hi' : HasType P Δ i ((O.rename e.names).relational.channel.predicateType (O.rename e.names).relational.probe.carrier) := by
    simpa only [RelationalCode.p_type_rename,ObservationCode.rename] using hi
  have hx' : HasType P Δ (x.rename e.names) ((O.rename e.names).relational.channel.logicalType (O.rename e.names).relational.probe.carrier) := by
    simpa only [ObservationCode.rename] using RelationalCode.Formed.x_typed_rename (R := O.relational) e hx
  have hz' : HasType P Δ (z.rename e.names) ((O.rename e.names).relational.channel.logicalType (O.rename e.names).relational.probe.carrier) := by
    simpa only [ObservationCode.rename] using RelationalCode.Formed.x_typed_rename (R := O.relational) e hz
  have ht' := (H.rename e).tagged_typed t hx' (e.moded mx)
  have hu' := (H.rename e).tagged_typed u hz' (e.moded mz)
  exact (L.rename e).iff_equivalent
    ((H.rename e).observe_formula (KY.rename e) (KP.rename e) hi' mi ht'.1 ht'.2)
    ((H.rename e).relational.le_formula (KY.rename e) (KP.rename e) hi' mi hx' (e.moded mx))
    ((H.rename e).observe_formula (KY.rename e) (KP.rename e) hi' mi hu'.1 hu'.2)
    ((H.rename e).relational.le_formula (KY.rename e) (KP.rename e) hi' mi hz' (e.moded mz))
    ((H.rename e).tagged_observe (KY.rename e) (KP.rename e) t hi' mi hx' (e.moded mx))
    ((H.rename e).tagged_observe (KY.rename e) (KP.rename e) u hi' mi hz' (e.moded mz))

theorem ae_tagged_same {x z : Expr S} (t : Fin 3)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data)
    (hz : HasType P Γ z (O.relational.channel.logicalType O.relational.probe.carrier)) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (O.ae L.code KY.code KP.code (O.tagged L.code t x) (O.tagged L.code t z))
      (O.relational.xCompare L.code KY.code KP.code x z) := by
  have ht := H.tagged_typed t hx mx
  have hu := H.tagged_typed t hz mz
  have fi := H.bitInner_formula ht.1 ht.2
  have fi' := H.bitInner_formula hu.1 hu.2
  have fo := H.bitOuter_formula ht.1 ht.2
  have fo' := H.bitOuter_formula hu.1 hu.2
  have fc := H.compare_formula KY KP ht.1 ht.2 hu.1 hu.2
  have fr := H.relational.xCompare_formula KY KP hx mx hz mz
  have ei := L.signed_agree (t == 1) fi fi' (H.tagged_bitInner t hx mx) (H.tagged_bitInner t hz mz)
  have eo := L.signed_agree (t == 2) fo fo' (H.tagged_bitOuter t hx mx) (H.tagged_bitOuter t hz mz)
  have ec := H.compare_tagged KY KP t t hx mx hz mz
  have eb := L.agreed_bits fi fi' fo fo' fc ei eo
  exact (H.ae_formula KY KP ht.1 ht.2 hu.1 hu.2).equivalent_trans fc fr eb ec
theorem ae_tagged_distinct {x z : Expr S} (t u : Fin 3) (htu : t ≠ u)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data)
    (hz : HasType P Γ z (O.relational.channel.logicalType O.relational.probe.carrier)) (mz : WellModed γ z .data) :
    Proves P Γ γ (L.neg (O.ae L.code KY.code KP.code (O.tagged L.code t x) (O.tagged L.code u z))) := by
  have ht := H.tagged_typed t hx mx
  have hu := H.tagged_typed u hz mz
  have fi := H.bitInner_formula ht.1 ht.2
  have fi' := H.bitInner_formula hu.1 hu.2
  have fo := H.bitOuter_formula ht.1 ht.2
  have fo' := H.bitOuter_formula hu.1 hu.2
  have fc := H.compare_formula KY KP ht.1 ht.2 hu.1 hu.2
  have hd : (t == 1) ≠ (u == 1) ∨ (t == 2) ≠ (u == 2) := by
    fin_cases t <;> fin_cases u <;> simp_all
  change Proves P Γ γ (L.neg (L.conj (L.iff _ _) (L.conj (L.iff _ _) _)))
  rcases hd with hd | hd
  · have hn := L.signed_disagree (t == 1) (u == 1) hd fi fi' (H.tagged_bitInner t hx mx) (H.tagged_bitInner u hz mz)
    exact L.different_bits_left fi fi' fo fo' fc hn
  · have hn := L.signed_disagree (t == 2) (u == 2) hd fo fo' (H.tagged_bitOuter t hx mx) (H.tagged_bitOuter u hz mz)
    exact L.different_bits_right fi fi' fo fo' fc hn
end ObservationCode.Formed

namespace SpecializedCode

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (B : SpecializedCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
structure Formed : Prop where
  observation : B.observation.Formed L I J k p n g j h
  type_sorted : HasType P Γ B.type (.sort B.relational.probe.seed)
  type_mode : WellModed γ B.type .data
  shape : B.yType = B.relational.channel.logicalType B.baseType
  outer_second_shape : B.observation.outer.second = B.relational.logical
  outer_first_shape : B.observation.outer.first.apply (B.observation.copies.middleType B.relational.probe.carrier) = B.baseType
namespace Formed
variable {B L I J k p n g j h} (H : B.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (B.rename e.names).Formed (L.rename e) I J k p n g j h := by
  refine ⟨H.observation.rename e,e.typing H.type_sorted,e.moded H.type_mode,?_,?_,?_⟩
  · have hh := congrArg (Expr.rename e.names) H.shape
    simpa only [yType_rename,ChannelCode.logicalType_rename,baseType_rename,SpecializedCode.rename,
      relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hh
  · exact congrArg (DataWrapper.rename e.names) H.outer_second_shape
  · have hh := congrArg (Expr.rename e.names) H.outer_first_shape
    simpa only [DataWrapper.apply_rename,ThreeCopyCode.middleType_rename,ProbeCode.carrier_rename,
      baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,ObservationCode.copies,
      RelationalCode.rename,DoubleCode.rename,ThreeCopyCode.rename,ProbeCode.rename] using hh

theorem relational_formed : B.relational.Formed L I J k p n g j h := H.observation.relational

theorem base_sorted : SortedAt P Γ B.baseType k := H.relational_formed.base_sorted H.type_sorted
theorem base_mode : WellModed γ B.baseType .data := H.relational_formed.base_mode H.type_mode
theorem y_sorted : SortedAt P Γ B.yType j := H.observation.carrier_sorted
theorem y_mode : WellModed γ B.yType .data := H.observation.carrier_mode
theorem x_sorted : SortedAt P Γ B.xType j := H.relational_formed.channel.logical_sorted H.relational_formed.probe.carrier_sorted
theorem x_mode : WellModed γ B.xType .data := H.relational_formed.channel.logical_mode H.relational_formed.probe.carrier_mode
theorem pred_sorted : SortedAt P Γ B.predType h := H.relational_formed.channel.predicate_sorted H.base_sorted
theorem pred_mode : WellModed γ B.predType .data := H.relational_formed.channel.predicate_mode H.base_mode

theorem ev_formula {v y : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) : L.Formula (B.ev v y) := by
  exact H.relational_formed.channel.eval_formula H.base_sorted H.base_mode hv mv (H.shape ▸ hy) my

theorem tagged_typed {x : Expr S} (t : Fin 3) (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    HasType P Γ (B.observation.tagged L.code t x) B.yType ∧ WellModed γ (B.observation.tagged L.code t x) .data :=
  H.observation.tagged_typed t hx mx
theorem gStep_formula {v y z : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    : L.Formula (B.gStep L.code KY.code KP.code v y z) := 
  L.imp_formula (H.observation.ae_formula KY KP hy my hz mz) (L.iff_formula (H.ev_formula hv mv hy my) (H.ev_formula hv mv hz mz))

theorem gAtBody_family {v y : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    : L.Family B.yType (B.gAtBody L.code KY.code KP.code v y) := by
  intro Δ δ e z hz mz
  rw [gAtBody_rename,gAtBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hy' : HasType P Δ (y.rename e.names) (B.rename e.names).yType := by
    simpa only [yType_rename] using e.typing hy
  have hz' : HasType P Δ z (B.rename e.names).yType := by
    simpa only [yType_rename] using hz
  exact (H.rename e).gStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' (e.moded my) hz' mz

theorem gAt_formula {v y : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    : L.Formula (B.gAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.gAtBody_family KY KP hv mv hy my)

theorem gBody_family {v : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Family B.yType (B.gBody L.code KY.code KP.code v) := by
  intro Δ δ e y hy my
  rw [gBody_rename,gBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    simpa only [yType_rename] using hy
  exact (H.rename e).gAt_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' my

theorem propertyG_formula {v : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Formula (B.propertyG L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.gBody_family KY KP hv mv)

theorem cStep_formula {v x w : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    : L.Formula (B.cStep L.code KY.code KP.code t v x w) := by
  have ht := H.tagged_typed t hx mx
  exact L.iff_formula (H.ev_formula hv mv hw mw) (H.observation.ae_formula KY KP hw mw ht.1 ht.2)

theorem cAtBody_family {v x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Family B.yType (B.cAtBody L.code KY.code KP.code t v x) := by
  intro Δ δ e w hw mw
  rw [cAtBody_rename,cAtBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hx' : HasType P Δ (x.rename e.names) (B.rename e.names).xType := by
    simpa only [xType_rename] using e.typing hx
  have hw' : HasType P Δ w (B.rename e.names).yType := by
    simpa only [yType_rename] using hw
  exact (H.rename e).cStep_formula (KY.rename e) (KP.rename e) t hv' (e.moded mv) hx' (e.moded mx) hw' mw

theorem cAt_formula {v x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.cAt L.code KY.code KP.code t v x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.cAtBody_family KY KP t hv mv hx mx)

theorem cBody_family {v : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Family B.xType (B.cBody L.code KY.code KP.code t v) := by
  intro Δ δ e x hx mx
  rw [cBody_rename,cBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).cAt_formula (KY.rename e) (KP.rename e) t hv' (e.moded mv) hx' mx

theorem propertyC_formula {v : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Formula (B.propertyC L.code KY.code KP.code t v) := by
  exact L.ex_formula KY H.x_sorted H.x_mode (H.cBody_family KY KP t hv mv)

theorem eStep_formula {v x w : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    : L.Formula (B.eStep L.code KY.code KP.code t v x w) := by
  have ht := H.tagged_typed t hx mx
  have h0 := H.tagged_typed 0 hx mx
  exact L.iff_formula (H.ev_formula hv mv hw mw) (L.disj_formula (H.observation.ae_formula KY KP hw mw h0.1 h0.2) (H.observation.ae_formula KY KP hw mw ht.1 ht.2))

theorem eAtBody_family {v x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Family B.yType (B.eAtBody L.code KY.code KP.code t v x) := by
  intro Δ δ e w hw mw
  rw [eAtBody_rename,eAtBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hx' : HasType P Δ (x.rename e.names) (B.rename e.names).xType := by
    simpa only [xType_rename] using e.typing hx
  have hw' : HasType P Δ w (B.rename e.names).yType := by
    simpa only [yType_rename] using hw
  exact (H.rename e).eStep_formula (KY.rename e) (KP.rename e) t hv' (e.moded mv) hx' (e.moded mx) hw' mw

theorem eAt_formula {v x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.eAt L.code KY.code KP.code t v x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.eAtBody_family KY KP t hv mv hx mx)

theorem eBody_family {v : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Family B.xType (B.eBody L.code KY.code KP.code t v) := by
  intro Δ δ e x hx mx
  rw [eBody_rename,eBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).eAt_formula (KY.rename e) (KP.rename e) t hv' (e.moded mv) hx' mx

theorem propertyE_formula {v : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Formula (B.propertyE L.code KY.code KP.code t v) := by
  exact L.ex_formula KY H.x_sorted H.x_mode (H.eBody_family KY KP t hv mv)

theorem rPredStep_formula {v x : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.rPredStep L.code KY.code KP.code v x) := by
  have ht := H.tagged_typed 1 hx mx
  exact H.ev_formula hv mv ht.1 ht.2

theorem rPredBody_family {v : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Family B.xType (B.rPredBody L.code KY.code KP.code v) := by
  intro Δ δ e x hx mx
  rw [rPredBody_rename,rPredBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).rPredStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' mx

theorem rPred_typed {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    HasType P Γ (B.rPred L.code KY.code KP.code v) B.xPredType ∧ WellModed γ (B.rPred L.code KY.code KP.code v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.rPredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs)

theorem rStep_formula {v x : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.rStep L.code KY.code KP.code v x) := by
  have ht := H.tagged_typed 2 hx mx
  have hi := H.rPred_typed KY KP hv mv
  exact L.imp_formula (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.ev_formula hv mv ht.1 ht.2) (H.relational_formed.le_formula KY KP hi.1 hi.2 hx mx))

theorem rBody_family {v : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Family B.xType (B.rBody L.code KY.code KP.code v) := by
  intro Δ δ e x hx mx
  rw [rBody_rename,rBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
    simpa only [predType_rename] using e.typing hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).rStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' mx

theorem rAll_formula {v : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Formula (B.rAll L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.rBody_family KY KP hv mv)

theorem propertyR_formula {v : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    : L.Formula (B.propertyR L.code KY.code KP.code v) := by
  have hi := H.rPred_typed KY KP hv mv
  exact L.imp_formula (H.relational_formed.extensional_formula KY KP hi.1 hi.2) (H.rAll_formula KY KP hv mv)

end Formed
end

variable (B : SpecializedCode S)
/-- The seven source structural tags G,C0,Cl,Cr,El,Er,R, in that order. -/
def property (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :=
  match t.val with
  | 0 => B.propertyG L KY KP v
  | 1 => B.propertyC L KY KP 0 v
  | 2 => B.propertyC L KY KP 1 v
  | 3 => B.propertyC L KY KP 2 v
  | 4 => B.propertyE L KY KP 1 v
  | 5 => B.propertyE L KY KP 2 v
  | _ => B.propertyR L KY KP v

def propertyBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) :=
  (B.rename Nat.succ).property (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (.var 0)

theorem property_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.property L KY KP t v).rename ρ = (B.rename ρ).property (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  fin_cases t <;> simp only [property,propertyG_rename,propertyC_rename,propertyE_rename,propertyR_rename]
theorem property_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.property L KY KP t v).subst σ = (B.subst σ).property (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  fin_cases t <;> simp only [property,propertyG_subst,propertyC_subst,propertyE_subst,propertyR_subst]
theorem propertyBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (ρ : Nat → Nat) :
    (B.propertyBody L KY KP t).rename (Expr.liftRen ρ) =
      (B.rename ρ).propertyBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t := by
  simp only [propertyBody,property_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem propertyBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :
    (B.propertyBody L KY KP t).instantiate v = B.property L KY KP t v := by
  simp only [propertyBody,Expr.instantiate,property_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst,Expr.single]

/-- This is m0 itself, with no recursive occurrence in its seven properties. -/
def parameter (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.probe.doubled.realization B.relational.predicate L (B.relational.probe.rawType B.type)
    (B.relational.rawTop L B.type) (B.propertyBody L KY KP)

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem property_formula (t : Fin 7) {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    L.Formula (B.property L.code KY.code KP.code t v) := by
  fin_cases t
  · exact H.propertyG_formula KY KP hv mv
  · exact H.propertyC_formula KY KP 0 hv mv
  · exact H.propertyC_formula KY KP 1 hv mv
  · exact H.propertyC_formula KY KP 2 hv mv
  · exact H.propertyE_formula KY KP 1 hv mv
  · exact H.propertyE_formula KY KP 2 hv mv
  · exact H.propertyR_formula KY KP hv mv

theorem propertyBody_family (t : Fin 7) : L.Family B.predType (B.propertyBody L.code KY.code KP.code t) := by
  intro Δ δ e v hv mv
  rw [propertyBody_rename,propertyBody_instantiate]
  exact (H.rename e).property_formula (KY.rename e) (KP.rename e) t (by simpa only [predType_rename] using hv) mv

theorem parameter_typed : HasType P Γ (B.parameter L.code KY.code KP.code) (B.relational.probe.paramType B.type) ∧
    WellModed γ (B.parameter L.code KY.code KP.code) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.relational_formed.probe.mainTriple.product.1
  have hc := H.relational_formed.rawTop_typed H.type_sorted H.type_mode
  exact H.relational_formed.probe.doubled_formed.realization_typed H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    hc.1 hc.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)
    (H.relational_formed.probe.doubled_formed.bp_sorted (H.relational_formed.probe.raw_sorted H.type_sorted) r hr)
    (H.propertyBody_family KY KP)

theorem parameter_not_dummy : Proves P Γ γ (L.neg (B.relational.probe.doubled.isDummy L.code
    (B.relational.probe.rawType B.type) (B.parameter L.code KY.code KP.code))) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.relational_formed.probe.mainTriple.product.1
  have hc := H.relational_formed.rawTop_typed H.type_sorted H.type_mode
  exact H.relational_formed.probe.doubled_formed.realization_not_dummy H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    hc.1 hc.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)
    (H.relational_formed.probe.doubled_formed.bp_sorted (H.relational_formed.probe.raw_sorted H.type_sorted) r hr)
    (H.propertyBody_family KY KP)

theorem parameter_query_decoded (t : Fin 7) {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ
      (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
        (B.parameter L.code KY.code KP.code) v)
      (B.property L.code KY.code KP.code t
        (B.relational.probe.doubled.decode B.relational.predicate L.code (B.relational.probe.rawType B.type)
          (B.relational.probe.doubled.encode B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type) v))) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.relational_formed.probe.mainTriple.product.1
  have hc := H.relational_formed.rawTop_typed H.type_sorted H.type_mode
  have he := H.relational_formed.probe.doubled_formed.realization_query_decoded H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    hc.1 hc.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)
    (H.relational_formed.probe.doubled_formed.bp_sorted (H.relational_formed.probe.raw_sorted H.type_sorted) r hr)
    (H.propertyBody_family KY KP) t hv mv
  simpa only [propertyBody_instantiate,parameter,RelationalCode.channel] using he
end Formed
end SpecializedCode
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} (L : LogicSetup P Γ γ C) {A B D : Expr S}
/-- The source's guarded comparison builder, with a genuine proof binder. -/
theorem guarded_equivalent_future (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ), Proves P Δ δ (A.rename e.names) →
      Equivalent P Δ δ (B.rename e.names) (D.rename e.names)) :
    Equivalent P Γ γ (L.imp A B) (L.imp A D) := by
  have hp : Proves P Γ γ (L.imp A (L.iff B D)) := by
    apply L.imp_intro_future hA (L.iff_formula hB hD)
    intro Δ δ e ha
    rw [L.iff_rename]
    exact (L.rename e).iff_of_equivalent (hB.rename e) (hD.rename e) (hh Δ δ e ha)
  apply L.equivalent_of_iff (L.imp_formula hA hB) (L.imp_formula hA hD)
  pts_pl L using [hp]
end PureTypeSystem.Labelled.LogicSetup

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem v_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.predType) : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
  simpa only [predType_rename] using e.typing hv
omit H in
theorem y_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.yType) : HasType P Δ (v.rename e.names) (B.rename e.names).yType := by
  simpa only [yType_rename] using e.typing hv
omit H in
theorem x_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.xType) : HasType P Δ (v.rename e.names) (B.rename e.names).xType := by
  simpa only [xType_rename] using e.typing hv
omit H in
theorem comparison_rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (e : Embedding P Γ γ Δ δ) {v c : Expr S}
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Proves P Δ δ ((B.rename e.names).relational.channel.predCompare (L.rename e).code (KY.rename e).code
      (B.rename e.names).baseType (v.rename e.names) (c.rename e.names)) := by
  simpa only [ChannelCode.predCompare_rename,baseType_rename,LogicSetup.code_rename,QuantifierRoute.code_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,
    ChannelCode.rename,ProbeCode.rename] using he.rename e

theorem ev_compare {v c y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.ev v y) (B.ev c y) :=
  H.relational_formed.channel.predCompare_elim H.base_sorted H.base_mode KY hv mv hc mc (H.shape ▸ hy) my he

theorem gStep_respect {v c y z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.gStep L.code KY.code KP.code v y z) (B.gStep L.code KY.code KP.code c y z) := by
  have ey := H.ev_compare KY hv mv hc mc hy my he
  have ez := H.ev_compare KY hv mv hc mc hz mz he
  have fy := H.ev_formula hv mv hy my
  have fz := H.ev_formula hv mv hz mz
  have fc := H.ev_formula hc mc hy my
  have fd := H.ev_formula hc mc hz mz
  have fa := H.observation.ae_formula KY KP hy my hz mz
  apply L.equivalent_of_iff (H.gStep_formula KY KP hv mv hy my hz mz) (H.gStep_formula KY KP hc mc hy my hz mz)
  change Proves P Γ γ (L.iff (L.imp _ (L.iff _ _)) (L.imp _ (L.iff _ _)))
  pts_pl L using [ey,ez]

theorem cStep_respect {v c x w : Expr S} (t : Fin 3)
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.cStep L.code KY.code KP.code t v x w) (B.cStep L.code KY.code KP.code t c x w) := by
  have ew := H.ev_compare KY hv mv hc mc hw mw he
  have fv := H.ev_formula hv mv hw mw
  have fc := H.ev_formula hc mc hw mw
  have ht := H.tagged_typed t hx mx
  have ft := H.observation.ae_formula KY KP hw mw ht.1 ht.2
  apply L.equivalent_of_iff (H.cStep_formula KY KP t hv mv hx mx hw mw) (H.cStep_formula KY KP t hc mc hx mx hw mw)
  change Proves P Γ γ (L.iff (L.iff _ _) (L.iff _ _))
  pts_pl L using [ew]

theorem eStep_respect {v c x w : Expr S} (t : Fin 3)
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.eStep L.code KY.code KP.code t v x w) (B.eStep L.code KY.code KP.code t c x w) := by
  have ew := H.ev_compare KY hv mv hc mc hw mw he
  have fv := H.ev_formula hv mv hw mw
  have fc := H.ev_formula hc mc hw mw
  have ht := H.tagged_typed t hx mx
  have ft := H.observation.ae_formula KY KP hw mw ht.1 ht.2
  have h0 := H.tagged_typed 0 hx mx
  have f0 := H.observation.ae_formula KY KP hw mw h0.1 h0.2
  have fa := L.disj_formula f0 ft
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact L.iff_equivalent fv fc fa fa ew (Equivalent.refl (fa.1 s hs))

theorem gAt_respect {v c y : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.gAt L.code KY.code KP.code v y) (B.gAt L.code KY.code KP.code c y) := by
  apply L.all_equivalent_future KY H.y_sorted H.y_mode (H.gAtBody_family KY KP hv mv hy my)
    (H.gAtBody_family KY KP hc mc hy my)
  intro Δ δ e w hw mw
  rw [gAtBody_rename,gAtBody_rename,gAtBody_instantiate,gAtBody_instantiate]
  exact (H.rename e).gStep_respect (KY.rename e) (KP.rename e) 
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (y_typed_rename (B := B) e hy) (e.moded my) (by simpa only [yType_rename] using hw) mw
    (comparison_rename (B := B) KY e he)

theorem propertyG_respect {v c : Expr S} 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.propertyG L.code KY.code KP.code v) (B.propertyG L.code KY.code KP.code c) := by
  apply L.all_equivalent_future KY H.y_sorted H.y_mode (H.gBody_family KY KP hv mv)
    (H.gBody_family KY KP hc mc)
  intro Δ δ e y hy my
  rw [gBody_rename,gBody_rename,gBody_instantiate,gBody_instantiate]
  exact (H.rename e).gAt_respect (KY.rename e) (KP.rename e) 
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (by simpa only [yType_rename] using hy) my (comparison_rename (B := B) KY e he)

theorem cAt_respect {v c x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.cAt L.code KY.code KP.code t v x) (B.cAt L.code KY.code KP.code t c x) := by
  apply L.all_equivalent_future KY H.y_sorted H.y_mode (H.cAtBody_family KY KP t hv mv hx mx)
    (H.cAtBody_family KY KP t hc mc hx mx)
  intro Δ δ e w hw mw
  rw [cAtBody_rename,cAtBody_rename,cAtBody_instantiate,cAtBody_instantiate]
  exact (H.rename e).cStep_respect (KY.rename e) (KP.rename e) t 
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (x_typed_rename (B := B) e hx) (e.moded mx) (by simpa only [yType_rename] using hw) mw
    (comparison_rename (B := B) KY e he)

theorem propertyC_respect {v c : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.propertyC L.code KY.code KP.code t v) (B.propertyC L.code KY.code KP.code t c) := by
  apply L.ex_equivalent_future KY H.x_sorted H.x_mode (H.cBody_family KY KP t hv mv)
    (H.cBody_family KY KP t hc mc)
  intro Δ δ e x hx mx
  rw [cBody_rename,cBody_rename,cBody_instantiate,cBody_instantiate]
  exact (H.rename e).cAt_respect (KY.rename e) (KP.rename e) t 
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (by simpa only [xType_rename] using hx) mx (comparison_rename (B := B) KY e he)

theorem eAt_respect {v c x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.eAt L.code KY.code KP.code t v x) (B.eAt L.code KY.code KP.code t c x) := by
  apply L.all_equivalent_future KY H.y_sorted H.y_mode (H.eAtBody_family KY KP t hv mv hx mx)
    (H.eAtBody_family KY KP t hc mc hx mx)
  intro Δ δ e w hw mw
  rw [eAtBody_rename,eAtBody_rename,eAtBody_instantiate,eAtBody_instantiate]
  exact (H.rename e).eStep_respect (KY.rename e) (KP.rename e) t 
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (x_typed_rename (B := B) e hx) (e.moded mx) (by simpa only [yType_rename] using hw) mw
    (comparison_rename (B := B) KY e he)

theorem propertyE_respect {v c : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.propertyE L.code KY.code KP.code t v) (B.propertyE L.code KY.code KP.code t c) := by
  apply L.ex_equivalent_future KY H.x_sorted H.x_mode (H.eBody_family KY KP t hv mv)
    (H.eBody_family KY KP t hc mc)
  intro Δ δ e x hx mx
  rw [eBody_rename,eBody_rename,eBody_instantiate,eBody_instantiate]
  exact (H.rename e).eAt_respect (KY.rename e) (KP.rename e) t 
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (by simpa only [xType_rename] using hx) mx (comparison_rename (B := B) KY e he)
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem relational_rename (ρ : Nat → Nat) : (B.relational.rename ρ) = (B.rename ρ).relational := rfl
theorem observation_rename (ρ : Nat → Nat) : (B.observation.rename ρ) = (B.rename ρ).observation := rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem rPred_evaluation {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.rPred L.code KY.code KP.code v) x)
      (B.rPredStep L.code KY.code KP.code v (B.relational.channel.round B.relational.probe.carrier x)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.rPredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs) hx mx
  simpa only [rPredBody_instantiate,rPred] using he

theorem rPred_compare_at {v c x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.rPred L.code KY.code KP.code v) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.rPred L.code KY.code KP.code c) x) := by
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have tx := H.tagged_typed 1 rx.1 rx.2
  have e1 := H.rPred_evaluation KY KP hv mv hx mx
  have e2 := H.rPred_evaluation KY KP hc mc hx mx
  have ec := H.ev_compare KY hv mv hc mc tx.1 tx.2 he
  have iv := H.rPred_typed KY KP hv mv
  have ic := H.rPred_typed KY KP hc mc
  have fv := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx
  have fc := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode ic.1 ic.2 hx mx
  have fwv := H.ev_formula hv mv tx.1 tx.2
  have fwc := H.ev_formula hc mc tx.1 tx.2
  change Equivalent P Γ γ _ (B.ev v _) at e1
  change Equivalent P Γ γ _ (B.ev c _) at e2
  apply L.equivalent_of_iff fv fc
  pts_pl L using [e1,e2,ec]

theorem rPred_respect {v c : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier
      (B.rPred L.code KY.code KP.code v) (B.rPred L.code KY.code KP.code c)) := by
  have iv := H.rPred_typed KY KP hv mv
  have ic := H.rPred_typed KY KP hc mc
  apply H.relational_formed.channel.predCompare_intro H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY iv.1 iv.2 ic.1 ic.2
  intro Δ δ e x hx mx
  simp only [rPred_rename]
  simpa only [LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using (H.rename e).rPred_compare_at (KY.rename e) (KP.rename e)
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (by simpa only [ProbeCode.carrier_rename,xType,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hx) mx (comparison_rename (B := B) KY e he)

theorem rConsequence_respect {v c x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Equivalent P Γ γ
      (L.imp (B.ev v (B.observation.tagged L.code 2 x)) (B.relational.le L.code KY.code KP.code (B.rPred L.code KY.code KP.code v) x))
      (L.imp (B.ev c (B.observation.tagged L.code 2 x)) (B.relational.le L.code KY.code KP.code (B.rPred L.code KY.code KP.code c) x)) := by
  have iv := H.rPred_typed KY KP hv mv
  have ic := H.rPred_typed KY KP hc mc
  have tx := H.tagged_typed 2 hx mx
  have evc := H.ev_compare KY hv mv hc mc tx.1 tx.2 he
  have el := H.relational_formed.valid_elim KY KP hx mx iv.1 iv.2 ic.1 ic.2 hu (H.rPred_respect KY KP hv mv hc mc he)
  exact L.imp_equivalent (H.ev_formula hv mv tx.1 tx.2) (H.ev_formula hc mc tx.1 tx.2)
    (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx) (H.relational_formed.le_formula KY KP ic.1 ic.2 hx mx) evc el

theorem rStep_respect {v c x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.rStep L.code KY.code KP.code v x) (B.rStep L.code KY.code KP.code c x) := by
  have iv := H.rPred_typed KY KP hv mv
  have ic := H.rPred_typed KY KP hc mc
  have tx := H.tagged_typed 2 hx mx
  apply L.guarded_equivalent_future (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.ev_formula hv mv tx.1 tx.2) (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx))
    (L.imp_formula (H.ev_formula hc mc tx.1 tx.2) (H.relational_formed.le_formula KY KP ic.1 ic.2 hx mx))
  intro Δ δ e hu
  have hu' : Proves P Δ δ ((B.rename e.names).relational.valid (L.rename e).code (KY.rename e).code (KP.rename e).code (x.rename e.names)) := by
    simpa only [RelationalCode.valid_rename,relational_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using hu
  simpa only [LogicSetup.imp_rename,ev_rename,ObservationCode.tagged_rename,RelationalCode.le_rename,
    rPred_rename,relational_rename,observation_rename,LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename] using
    (H.rename e).rConsequence_respect (KY.rename e) (KP.rename e)
      (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
      (x_typed_rename (B := B) e hx) (e.moded mx) (comparison_rename (B := B) KY e he) hu'

theorem rAll_respect {v c : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.rAll L.code KY.code KP.code v) (B.rAll L.code KY.code KP.code c) := by
  apply L.all_equivalent_future KY H.x_sorted H.x_mode (H.rBody_family KY KP hv mv)
    (H.rBody_family KY KP hc mc)
  intro Δ δ e x hx mx
  rw [rBody_rename,rBody_rename,rBody_instantiate,rBody_instantiate]
  exact (H.rename e).rStep_respect (KY.rename e) (KP.rename e)
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (by simpa only [xType_rename] using hx) mx (comparison_rename (B := B) KY e he)

theorem propertyR_respect {v c : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.propertyR L.code KY.code KP.code v) (B.propertyR L.code KY.code KP.code c) := by
  have iv := H.rPred_typed KY KP hv mv
  have ic := H.rPred_typed KY KP hc mc
  have ex := H.relational_formed.extensional_respect KY KP iv.1 iv.2 ic.1 ic.2 (H.rPred_respect KY KP hv mv hc mc he)
  exact L.imp_equivalent (H.relational_formed.extensional_formula KY KP iv.1 iv.2)
    (H.relational_formed.extensional_formula KY KP ic.1 ic.2) (H.rAll_formula KY KP hv mv) (H.rAll_formula KY KP hc mc)
    ex (H.rAll_respect KY KP hv mv hc mc he)
end Formed

def decoded (L : LogicCode S) (t : Fin 7) (v : Expr S) :=
  B.relational.probe.doubled.decode B.relational.predicate L (B.relational.probe.rawType B.type)
    (B.relational.probe.doubled.encode B.relational.predicate L t.castSucc (B.relational.probe.rawType B.type) v)
theorem decoded_rename (L : LogicCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.decoded L t v).rename ρ = (B.rename ρ).decoded (L.rename ρ) t (v.rename ρ) := by
  simp only [decoded,DoubleCode.decode_rename,DoubleCode.encode_rename,ProbeCode.rawType_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename]
  rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem property_respect (t : Fin 7) {v c : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (B.property L.code KY.code KP.code t v) (B.property L.code KY.code KP.code t c) := by
  fin_cases t
  · exact H.propertyG_respect KY KP hv mv hc mc he
  · exact H.propertyC_respect KY KP 0 hv mv hc mc he
  · exact H.propertyC_respect KY KP 1 hv mv hc mc he
  · exact H.propertyC_respect KY KP 2 hv mv hc mc he
  · exact H.propertyE_respect KY KP 1 hv mv hc mc he
  · exact H.propertyE_respect KY KP 2 hv mv hc mc he
  · exact H.propertyR_respect KY KP hv mv hc mc he

theorem decoded_typed (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    HasType P Γ (B.decoded L.code t v) B.predType ∧ WellModed γ (B.decoded L.code t v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have ht := H.relational_formed.probe.raw_sorted H.type_sorted
  have mT := H.relational_formed.probe.raw_mode H.type_mode
  have he := H.relational_formed.probe.doubled_formed.encode_typed H.relational_formed.channel.predicate ht mT t.castSucc hv mv
  exact H.relational_formed.probe.doubled_formed.decode_typed H.relational_formed.channel.predicate ht mT he.1 he.2 (ht s hs)

theorem decoded_at (t : Fin 7) {v y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.ev (B.decoded L.code t v) y) (B.ev v y) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have hy' := H.relational_formed.channel.toRaw_typed H.base_sorted H.base_mode (H.shape ▸ hy) my
  exact H.relational_formed.probe.doubled_formed.decode_encode H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    t.castSucc hv mv hy'.1 hy'.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem decoded_compare (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType (B.decoded L.code t v) v) := by
  have hd := H.decoded_typed t hv mv
  apply H.relational_formed.channel.predCompare_intro H.base_sorted H.base_mode KY hd.1 hd.2 hv mv
  intro Δ δ e y hy my
  simp only [decoded_rename]
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    rw [(H.rename e).shape]
    simpa only [baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,
      RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hy
  simpa only [ev,baseType_rename,LogicSetup.code_rename,SpecializedCode.rename,relational,ObservationCode.rename,
    RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).decoded_at t (v_typed_rename (B := B) e hv) (e.moded mv) hy' my

theorem parameter_query_formula (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    L.Formula (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
      (B.parameter L.code KY.code KP.code) v) := by
  have hm := H.parameter_typed KY KP
  exact H.relational_formed.probe.doubled_formed.query_formula H.relational_formed.channel.predicate t.castSucc
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode) hm.1 hm.2 hv mv

/-- Exact source q_t(P), from actual cancellation and the proved respect law. -/
theorem parameter_query (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ
      (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
        (B.parameter L.code KY.code KP.code) v)
      (B.property L.code KY.code KP.code t v) := by
  have hd := H.decoded_typed t hv mv
  have he := H.parameter_query_decoded KY KP t hv mv
  have hr := H.property_respect KY KP t hd.1 hd.2 hv mv (H.decoded_compare KY t hv mv)
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact he.trans hr ((H.parameter_query_formula KY KP t hv mv).1 s hs)
    ((H.property_formula KY KP t hd.1 hd.2).1 s hs) ((H.property_formula KY KP t hv mv).1 s hs)
end Formed
end SpecializedCode
end

universe u
variable {S : Type u}
namespace DoubleCode
variable (R : DoubleCode S)
theorem realizationBody_rename (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (ρ : Nat → Nat) :
    (R.realizationBody U L T c Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).realizationBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (c.rename ρ) (fun t => (Q t).rename (Expr.liftRen ρ)) := by
  simp only [realizationBody,LogicCode.choices_rename,LogicCode.rename_comp,Expr.compose_rename,markBody_rename,decodeMap_rename]
  rfl
theorem realizationBody_subst (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (σ : Nat → Expr S) :
    (R.realizationBody U L T c Q).subst (Expr.liftSub σ) =
      (R.subst σ).realizationBody (U.subst σ) (L.subst σ) (T.subst σ) (c.subst σ) (fun t => (Q t).subst (Expr.liftSub σ)) := by
  simp only [realizationBody,LogicCode.choices_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.compose_subst,markBody_subst,decodeMap_subst]
  rfl
theorem realization_rename (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (ρ : Nat → Nat) :
    (R.realization U L T c Q).rename ρ =
      (R.rename ρ).realization (U.rename ρ) (L.rename ρ) (T.rename ρ) (c.rename ρ) (fun t => (Q t).rename (Expr.liftRen ρ)) := by
  simp only [realization,DataWrapper.build_rename,bpType_rename,realizationBody_rename,rename_second,
    DataWrapper.argRen,ite_true]
theorem realization_subst (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (σ : Nat → Expr S) :
    (R.realization U L T c Q).subst σ =
      (R.subst σ).realization (U.subst σ) (L.subst σ) (T.subst σ) (c.subst σ) (fun t => (Q t).subst (Expr.liftSub σ)) := by
  simp only [realization,DataWrapper.build_subst,bpType_subst,realizationBody_subst,subst_second,
    DataWrapper.argSub,ite_true]
end DoubleCode
namespace SpecializedCode
variable (B : SpecializedCode S)
theorem propertyBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (σ : Nat → Expr S) :
    (B.propertyBody L KY KP t).subst (Expr.liftSub σ) =
      (B.subst σ).propertyBody (L.subst σ) (KY.subst σ) (KP.subst σ) t := by
  simp only [propertyBody,property_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl
theorem parameter_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.parameter L KY KP).rename ρ = (B.rename ρ).parameter (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [parameter,DoubleCode.realization_rename,ProbeCode.rawType_rename,RelationalCode.rawTop_rename,propertyBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename,ProbeCode.doubled,DoubleCode.rename]
theorem parameter_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.parameter L KY KP).subst σ = (B.subst σ).parameter (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [parameter,DoubleCode.realization_subst,ProbeCode.rawType_subst,RelationalCode.rawTop_subst,propertyBody_subst,
    SpecializedCode.subst,relational,ObservationCode.subst,RelationalCode.subst,ProbeCode.subst,ProbeCode.doubled,DoubleCode.subst]
end SpecializedCode
end PureTypeSystem.Labelled

end OAI
