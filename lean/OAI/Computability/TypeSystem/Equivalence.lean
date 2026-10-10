import OAI.Computability.TypeSystem.Specialization

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode
variable (B : SpecializedCode S)
def query (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :=
  B.relational.probe.doubled.query B.relational.predicate L t.castSucc (B.relational.probe.rawType B.type)
    (B.parameter L KY KP) v
def predCompare (L : LogicCode S) (KY : QuantifierCode S) (v w : Expr S) :=
  B.relational.channel.predCompare L KY B.baseType v w
def qrStep (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v w : Expr S) :=
  L.imp (B.predCompare L KY v w) (L.iff (B.query L KY KP t v) (B.query L KY KP t w))
def qrAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :=
  (B.rename Nat.succ).qrStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (v.rename Nat.succ) (.var 0)
def qrAt (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :=
  KP.all B.predType (B.qrAtBody L KY KP t v)
def qrBody (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) :=
  (B.rename Nat.succ).qrAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) t (.var 0)
def queryRespect (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) :=
  KP.all B.predType (B.qrBody L KY KP t)
theorem query_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.query L KY KP t v).rename (ρ) = (B.rename ρ).query (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [query,DoubleCode.query_rename,ProbeCode.rawType_rename,parameter_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename,ProbeCode.doubled,DoubleCode.rename]
  try rfl
theorem query_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.query L KY KP t v).subst (σ) = (B.subst σ).query (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [query,DoubleCode.query_subst,ProbeCode.rawType_subst,parameter_subst,SpecializedCode.subst,relational,ObservationCode.subst,RelationalCode.subst,ProbeCode.subst,ProbeCode.doubled,DoubleCode.subst]
  try rfl
theorem predCompare_rename (L : LogicCode S) (KY : QuantifierCode S) (v w : Expr S) (ρ : Nat → Nat) :
    (B.predCompare L KY v w).rename (ρ) = (B.rename ρ).predCompare (L.rename ρ) (KY.rename ρ) (v.rename ρ) (w.rename ρ) := by
  simp only [predCompare,ChannelCode.predCompare_rename,baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]
  try rfl
theorem predCompare_subst (L : LogicCode S) (KY : QuantifierCode S) (v w : Expr S) (σ : Nat → Expr S) :
    (B.predCompare L KY v w).subst (σ) = (B.subst σ).predCompare (L.subst σ) (KY.subst σ) (v.subst σ) (w.subst σ) := by
  simp only [predCompare,ChannelCode.predCompare_subst,baseType_subst,SpecializedCode.subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst,ChannelCode.subst,ProbeCode.subst]
  try rfl
theorem qrStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v w : Expr S) (ρ : Nat → Nat) :
    (B.qrStep L KY KP t v w).rename (ρ) = (B.rename ρ).qrStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (w.rename ρ) := by
  simp only [qrStep,LogicCode.imp_rename,LogicCode.iff_rename,predCompare_rename,query_rename]
theorem qrStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v w : Expr S) (σ : Nat → Expr S) :
    (B.qrStep L KY KP t v w).subst (σ) = (B.subst σ).qrStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (w.subst σ) := by
  simp only [qrStep,LogicCode.imp_subst,LogicCode.iff_subst,predCompare_subst,query_subst]
theorem qrAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.qrAtBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).qrAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [qrAtBody,qrStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem qrAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.qrAtBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).qrAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [qrAtBody,qrStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem qrAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.qrAt L KY KP t v).rename (ρ) = (B.rename ρ).qrAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [qrAt,QuantifierCode.all_rename,predType_rename,qrAtBody_rename]
theorem qrAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.qrAt L KY KP t v).subst (σ) = (B.subst σ).qrAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [qrAt,QuantifierCode.all_subst,predType_subst,qrAtBody_subst]
theorem qrBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (ρ : Nat → Nat) :
    (B.qrBody L KY KP t).rename (Expr.liftRen ρ) = (B.rename ρ).qrBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t := by
  simp only [qrBody,qrAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem qrBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (σ : Nat → Expr S) :
    (B.qrBody L KY KP t).subst (Expr.liftSub σ) = (B.subst σ).qrBody (L.subst σ) (KY.subst σ) (KP.subst σ) t := by
  simp only [qrBody,qrAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem queryRespect_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (ρ : Nat → Nat) :
    (B.queryRespect L KY KP t).rename (ρ) = (B.rename ρ).queryRespect (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t := by
  simp only [queryRespect,QuantifierCode.all_rename,predType_rename,qrBody_rename]
theorem queryRespect_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (σ : Nat → Expr S) :
    (B.queryRespect L KY KP t).subst (σ) = (B.subst σ).queryRespect (L.subst σ) (KY.subst σ) (KP.subst σ) t := by
  simp only [queryRespect,QuantifierCode.all_subst,predType_subst,qrBody_subst]
theorem qrAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v w : Expr S) :
    (B.qrAtBody L KY KP t v).instantiate w = B.qrStep L KY KP t v w := by
  simp only [qrAtBody,Expr.instantiate,qrStep_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem qrBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :
    (B.qrBody L KY KP t).instantiate v = B.qrAt L KY KP t v := by
  simp only [qrBody,Expr.instantiate,qrAt_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst,Expr.single]
def admissible (L : LogicCode S) (KY KP : QuantifierCode S) :=
  L.conj (L.neg (B.relational.probe.doubled.isDummy L (B.relational.probe.rawType B.type) (B.parameter L KY KP)))
    (L.conj (B.queryRespect L KY KP 0) (L.conj (B.queryRespect L KY KP 1) (L.conj (B.queryRespect L KY KP 2) (L.conj (B.queryRespect L KY KP 3) (L.conj (B.queryRespect L KY KP 4) (L.conj (B.queryRespect L KY KP 5) (B.queryRespect L KY KP 6)))))))

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem predCompare_formula {v w : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hw : HasType P Γ w B.predType) (mw : WellModed γ w .data) :
    L.Formula (B.predCompare L.code KY.code v w) :=
  H.relational_formed.channel.predCompare_formula H.base_sorted H.base_mode KY hv mv hw mw

theorem qrStep_formula (t : Fin 7) {v w : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hw : HasType P Γ w B.predType) (mw : WellModed γ w .data) :
    L.Formula (B.qrStep L.code KY.code KP.code t v w) :=
  L.imp_formula (H.predCompare_formula KY hv mv hw mw)
    (L.iff_formula (H.parameter_query_formula KY KP t hv mv) (H.parameter_query_formula KY KP t hw mw))

theorem qrAtBody_family (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    L.Family B.predType (B.qrAtBody L.code KY.code KP.code t v) := by
  intro Δ δ e w hw mw
  rw [qrAtBody_rename,qrAtBody_instantiate]
  exact (H.rename e).qrStep_formula (KY.rename e) (KP.rename e) t (v_typed_rename (B := B) e hv) (e.moded mv)
    (by simpa only [predType_rename] using hw) mw

theorem qrAt_formula (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) : L.Formula (B.qrAt L.code KY.code KP.code t v) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP H.pred_sorted H.pred_mode (H.pred_sorted s hs) (H.qrAtBody_family KY KP t hv mv)

theorem qrBody_family (t : Fin 7) : L.Family B.predType (B.qrBody L.code KY.code KP.code t) := by
  intro Δ δ e v hv mv
  rw [qrBody_rename,qrBody_instantiate]
  exact (H.rename e).qrAt_formula (KY.rename e) (KP.rename e) t (by simpa only [predType_rename] using hv) mv

theorem queryRespect_formula (t : Fin 7) : L.Formula (B.queryRespect L.code KY.code KP.code t) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP H.pred_sorted H.pred_mode (H.pred_sorted s hs) (H.qrBody_family KY KP t)

theorem query_equivalent (t : Fin 7) {v w : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hw : HasType P Γ w B.predType) (mw : WellModed γ w .data)
    (he : Proves P Γ γ (B.predCompare L.code KY.code v w)) :
    Equivalent P Γ γ (B.query L.code KY.code KP.code t v) (B.query L.code KY.code KP.code t w) := by
  have h1 := H.parameter_query KY KP t hv mv
  have h2 := H.property_respect KY KP t hv mv hw mw he
  have h3 := H.parameter_query KY KP t hw mw
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact (h1.trans h2 ((H.parameter_query_formula KY KP t hv mv).1 s hs)
    ((H.property_formula KY KP t hv mv).1 s hs) ((H.property_formula KY KP t hw mw).1 s hs)).trans h3.symm
    ((H.parameter_query_formula KY KP t hv mv).1 s hs) ((H.property_formula KY KP t hw mw).1 s hs)
    ((H.parameter_query_formula KY KP t hw mw).1 s hs)

theorem qrStep_proves (t : Fin 7) {v w : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hw : HasType P Γ w B.predType) (mw : WellModed γ w .data) : Proves P Γ γ (B.qrStep L.code KY.code KP.code t v w) := by
  apply L.imp_intro_future (H.predCompare_formula KY hv mv hw mw)
    (L.iff_formula (H.parameter_query_formula KY KP t hv mv) (H.parameter_query_formula KY KP t hw mw))
  intro Δ δ e he
  simp only [predCompare_rename] at he
  change Proves P Δ δ ((L.iff (B.query L.code KY.code KP.code t v) (B.query L.code KY.code KP.code t w)).rename e.names)
  simp only [LogicSetup.iff_rename,query_rename]
  have hv' := v_typed_rename (B := B) e hv
  have hw' := v_typed_rename (B := B) e hw
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).parameter_query_formula (KY.rename e) (KP.rename e) t hv' (e.moded mv))
    ((H.rename e).parameter_query_formula (KY.rename e) (KP.rename e) t hw' (e.moded mw))
    ((H.rename e).query_equivalent (KY.rename e) (KP.rename e) t hv' (e.moded mv) hw' (e.moded mw) he)

theorem qrAt_proves (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) : Proves P Γ γ (B.qrAt L.code KY.code KP.code t v) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP H.pred_sorted H.pred_mode (H.pred_sorted s hs) (H.qrAtBody_family KY KP t hv mv)
  intro Δ δ e w hw mw
  rw [qrAtBody_rename,qrAtBody_instantiate]
  exact (H.rename e).qrStep_proves (KY.rename e) (KP.rename e) t (v_typed_rename (B := B) e hv) (e.moded mv)
    (by simpa only [predType_rename] using hw) mw

theorem queryRespect_proves (t : Fin 7) : Proves P Γ γ (B.queryRespect L.code KY.code KP.code t) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP H.pred_sorted H.pred_mode (H.pred_sorted s hs) (H.qrBody_family KY KP t)
  intro Δ δ e v hv mv
  rw [qrBody_rename,qrBody_instantiate]
  exact (H.rename e).qrAt_proves (KY.rename e) (KP.rename e) t (by simpa only [predType_rename] using hv) mv

theorem not_dummy_formula : L.Formula (L.neg (B.relational.probe.doubled.isDummy L.code
    (B.relational.probe.rawType B.type) (B.parameter L.code KY.code KP.code))) := by
  have hm := H.parameter_typed KY KP
  exact L.neg_formula (H.relational_formed.probe.doubled_formed.isDummy_formula
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode) hm.1 hm.2)

theorem admissible_formula : L.Formula (B.admissible L.code KY.code KP.code) := by
  have f := H.queryRespect_formula KY KP
  exact L.conj_formula (H.not_dummy_formula KY KP)
    (L.conj_formula (f 0) (L.conj_formula (f 1) (L.conj_formula (f 2) (L.conj_formula (f 3) (L.conj_formula (f 4) (L.conj_formula (f 5) (f 6)))))))

theorem admissible_proves : Proves P Γ γ (B.admissible L.code KY.code KP.code) := by
  have f := H.queryRespect_formula KY KP
  have q := H.queryRespect_proves KY KP
  have f6 := f 6
  have q6 := q 6
  have f5 := L.conj_formula (f 5) f6
  have q5 := L.conj_intro (f 5) f6 (q 5) q6
  have f4 := L.conj_formula (f 4) f5
  have q4 := L.conj_intro (f 4) f5 (q 4) q5
  have f3 := L.conj_formula (f 3) f4
  have q3 := L.conj_intro (f 3) f4 (q 3) q4
  have f2 := L.conj_formula (f 2) f3
  have q2 := L.conj_intro (f 2) f3 (q 2) q3
  have f1 := L.conj_formula (f 1) f2
  have q1 := L.conj_intro (f 1) f2 (q 1) q2
  have f0 := L.conj_formula (f 0) f1
  have q0 := L.conj_intro (f 0) f1 (q 0) q1
  exact L.conj_intro (H.not_dummy_formula KY KP) f0 (H.parameter_not_dummy KY KP) q0
end Formed
end SpecializedCode

namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {A A' B B' : Expr S}
theorem recover_equivalent (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.code.cond A B (L.neg B)) (L.code.cond A' B' (L.neg B')) := by
  apply L.equivalent_of_iff (L.cond_formula hA hB (L.neg_formula hB))
    (L.cond_formula hA' hB' (L.neg_formula hB'))
  pts_pl L using [eA,eB]
end LogicSetup
namespace SpecializedCode
variable (B : SpecializedCode S)
def round (y : Expr S) := B.relational.channel.round B.baseType y
theorem round_rename (y : Expr S) (ρ : Nat → Nat) :
    (B.round y).rename ρ = (B.rename ρ).round (y.rename ρ) := by
  simp only [round,ChannelCode.round_rename,baseType_rename,SpecializedCode.rename,relational,
    ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem round_typed {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    HasType P Γ (B.round y) B.yType ∧ WellModed γ (B.round y) .data := by
  have hh := H.relational_formed.channel.round_typed H.base_sorted H.base_mode (H.shape ▸ hy) my
  exact ⟨H.shape.symm ▸ hh.1,hh.2⟩

theorem middle_sorted : SortedAt P Γ (B.observation.copies.middleType B.relational.probe.carrier) p :=
  H.observation.inner.sorted (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted)
theorem middle_mode : WellModed γ (B.observation.copies.middleType B.relational.probe.carrier) .data :=
  H.observation.inner.mode (H.relational_formed.probe.raw.mode H.relational_formed.probe.carrier_mode)

theorem outer_eval_round {y Q : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hQ : L.Family (B.observation.copies.middleType B.relational.probe.carrier) Q) :
    Equivalent P Γ γ
      (B.observation.outer.eval (B.observation.copies.middleType B.relational.probe.carrier) (B.round y) Q)
      (B.observation.outer.eval (B.observation.copies.middleType B.relational.probe.carrier) y Q) := by
  have hq := (H.observation.outer.first.sound H.middle_sorted H.middle_mode).1 Q hQ
  have he := H.relational_formed.channel.primitive_round H.base_sorted H.base_mode
    (H.shape ▸ hy) my (H.outer_first_shape ▸ hq.1) hq.2
  simpa only [DoubleCode.eval,H.outer_second_shape,H.outer_first_shape,round,RelationalCode.channel] using he

theorem bitOuter_round {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.observation.bitOuter L.code (B.round y)) (B.observation.bitOuter L.code y) :=
  H.outer_eval_round hy my (.constant L.top_formula)

theorem outer_recover_round {y Q : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hQ : L.Family (B.observation.copies.middleType B.relational.probe.carrier) Q) :
    Equivalent P Γ γ
      (B.observation.outer.recover L.code (B.observation.copies.middleType B.relational.probe.carrier) (B.round y) Q)
      (B.observation.outer.recover L.code (B.observation.copies.middleType B.relational.probe.carrier) y Q) := by
  have hr := H.round_typed hy my
  exact L.recover_equivalent (H.observation.bitOuter_formula hr.1 hr.2) (H.observation.bitOuter_formula hy my)
    (H.observation.outer.eval_formula H.middle_sorted H.middle_mode hr.1 hr.2 hQ)
    (H.observation.outer.eval_formula H.middle_sorted H.middle_mode hy my hQ)
    (H.bitOuter_round hy my) (H.outer_eval_round hy my hQ)

theorem bitInner_round {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.observation.bitInner L.code (B.round y)) (B.observation.bitInner L.code y) :=
  H.outer_recover_round hy my (H.observation.inner.bitBody_family
    (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted)
    (H.relational_formed.probe.raw.mode H.relational_formed.probe.carrier_mode))

theorem observe_round {y i : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    Equivalent P Γ γ (B.observation.observe L.code KY.code KP.code i (B.round y))
      (B.observation.observe L.code KY.code KP.code i y) := by
  have hp := H.relational_formed.probeFor_typed KY KP hi mi
  exact H.outer_recover_round hy my (H.observation.inner.recBody_family
    (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted)
    (H.relational_formed.probe.raw.mode H.relational_formed.probe.carrier_mode)
    (H.relational_formed.probe.raw.contraCallback_family H.relational_formed.probe.carrier_sorted
      H.relational_formed.probe.carrier_mode hp.1 hp.2))

theorem ae_round {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Proves P Γ γ (B.observation.ae L.code KY.code KP.code (B.round y) y) := by
  have hr := H.round_typed hy my
  apply H.observation.ae_intro KY KP hr.1 hr.2 hy my (H.bitInner_round hy my) (H.bitOuter_round hy my)
  apply H.observation.compare_intro KY KP hr.1 hr.2 hy my
  intro Δ δ e i hi mi
  rw [round_rename]
  exact (H.rename e).observe_round (KY.rename e) (KP.rename e)
    (by simpa only [yType_rename] using e.typing hy) (e.moded my) hi mi
end Formed
end SpecializedCode

namespace SpecializedCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem gAt_intro {v y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) z,
      HasType P Δ z (B.rename e.names).yType → WellModed δ z .data →
      Proves P Δ δ ((B.rename e.names).gStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) (y.rename e.names) z)) : Proves P Γ γ (B.gAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.gAtBody_family KY KP hv mv hy my)
  intro Δ δ e z hz mz
  rw [gAtBody_rename,gAtBody_instantiate]
  exact hh Δ δ e z (by simpa only [yType_rename] using hz) mz

theorem gAt_elim {v y z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hp : Proves P Γ γ (B.gAt L.code KY.code KP.code v y)) :
    Proves P Γ γ (B.gStep L.code KY.code KP.code v y z) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.gAtBody_family KY KP hv mv hy my) hz mz hp
  simpa only [gAtBody_instantiate] using hh

theorem propertyG_intro {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y (B.rename e.names).yType → WellModed δ y .data →
      Proves P Δ δ ((B.rename e.names).gAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) y)) : Proves P Γ γ (B.propertyG L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.gBody_family KY KP hv mv)
  intro Δ δ e y hy my
  rw [gBody_rename,gBody_instantiate]
  exact hh Δ δ e y (by simpa only [yType_rename] using hy) my

theorem propertyG_elim_one {v y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
    Proves P Γ γ (B.gAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.gBody_family KY KP hv mv) hy my hp
  simpa only [gBody_instantiate] using hh

theorem propertyG_elim {v y z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hp : Proves P Γ γ (B.propertyG L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.observation.ae L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.ev v y) (B.ev v z) := by
  have hh := H.gAt_elim KY KP hv mv hy my hz mz (H.propertyG_elim_one KY KP hv mv hy my hp)
  have hc := L.imp_elim (H.observation.ae_formula KY KP hy my hz mz)
    (L.iff_formula (H.ev_formula hv mv hy my) (H.ev_formula hv mv hz mz)) hh he
  exact L.equivalent_of_iff (H.ev_formula hv mv hy my) (H.ev_formula hv mv hz mz) hc

theorem propertyG_round {v y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.ev v y) (B.ev v (B.round y)) := by
  have hr := H.round_typed hy my
  exact (H.propertyG_elim KY KP hv mv hr.1 hr.2 hy my hp (H.ae_round KY KP hy my)).symm

theorem propertyG_roundRespect {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hp : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.channel.roundRespect L.code KY.code B.baseType v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY (H.relational_formed.channel.logical_sorted H.base_sorted)
    (H.relational_formed.channel.logical_mode H.base_mode)
    (H.relational_formed.channel.logical_sorted H.base_sorted s hs)
    (H.relational_formed.channel.roundRespectBody_family H.base_sorted H.base_mode hv mv)
  intro Δ δ e y hy my
  rw [ChannelCode.roundRespectBody_rename,ChannelCode.roundRespectBody_instantiate]
  have hp' := hp.rename e
  simp only [propertyG_rename] at hp'
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    rw [(H.rename e).shape]
    simpa only [ChannelCode.logicalType_rename,baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,
      RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hy
  have hv' := v_typed_rename (B := B) e hv
  have hr := (H.rename e).round_typed hy' my
  have hf := (L.rename e).iff_of_equivalent ((H.rename e).ev_formula hv' (e.moded mv) hy' my)
    ((H.rename e).ev_formula hv' (e.moded mv) hr.1 hr.2)
    ((H.rename e).propertyG_round (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' my hp')
  simpa only [ev,round,baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,
    RelationalCode.rename,ChannelCode.rename,ProbeCode.rename,←LogicSetup.code_rename,LogicSetup.code_iff] using hf
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
def good (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  L.conj (B.relational.channel.roundRespect L KY B.baseType v) (B.query L KY KP 0 v)
def goodBody (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.goodBody L KY B.type (B.parameter L KY KP)
def relation (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  B.relational.channel.relation L KP B.baseType (B.goodBody L KY KP) y z

theorem goodBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :
    (B.goodBody L KY KP).instantiate v = B.good L KY KP v := by
  simp only [goodBody,RelationalCode.goodBody,ChannelCode.goodBody_instantiate,
    RelationalCode.queryBody,DoubleCode.queryPredBody_instantiate,good,query,baseType]
theorem good_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.good L KY KP v).rename ρ = (B.rename ρ).good (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [good,LogicCode.conj_rename,ChannelCode.roundRespect_rename,baseType_rename,query_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename]
theorem goodBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.goodBody L KY KP).rename (Expr.liftRen ρ) = (B.rename ρ).goodBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [goodBody,RelationalCode.goodBody_rename,parameter_rename,
    SpecializedCode.rename,relational,ObservationCode.rename]
theorem relation_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (B.relation L KY KP y z).rename ρ = (B.rename ρ).relation (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [relation,ChannelCode.relation_rename,baseType_rename,goodBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem good_formula {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    L.Formula (B.good L.code KY.code KP.code v) :=
  L.conj_formula (H.relational_formed.channel.roundRespect_formula KY H.base_sorted H.base_mode hv mv)
    (H.parameter_query_formula KY KP 0 hv mv)
theorem goodBody_family : L.Family B.predType (B.goodBody L.code KY.code KP.code) := by
  have hm := H.parameter_typed KY KP
  exact H.relational_formed.goodBody_family KY H.type_sorted H.type_mode hm.1 hm.2

theorem good_forward {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hg : Proves P Γ γ (B.good L.code KY.code KP.code v)) :
    Proves P Γ γ (B.propertyG L.code KY.code KP.code v) := by
  have hq := L.conj_right (H.relational_formed.channel.roundRespect_formula KY H.base_sorted H.base_mode hv mv)
    (H.parameter_query_formula KY KP 0 hv mv) hg
  exact (H.parameter_query KY KP 0 hv mv).1.prove hq

theorem good_backward {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hg : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
    Proves P Γ γ (B.good L.code KY.code KP.code v) := by
  exact L.conj_intro (H.relational_formed.channel.roundRespect_formula KY H.base_sorted H.base_mode hv mv)
    (H.parameter_query_formula KY KP 0 hv mv) (H.propertyG_roundRespect KY KP hv mv hg)
    ((H.parameter_query KY KP 0 hv mv).2.prove hg)

theorem good_equivalent {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.good L.code KY.code KP.code v) (B.propertyG L.code KY.code KP.code v) := by
  have fg := H.good_formula KY KP hv mv
  have fp := H.propertyG_formula KY KP hv mv
  apply L.equivalent_of_iff fg fp
  apply L.conj_intro (L.imp_formula fg fp) (L.imp_formula fp fg)
  · apply L.imp_intro_future fg fp
    intro Δ δ e hg
    simp only [good_rename] at hg
    rw [propertyG_rename]
    exact (H.rename e).good_forward (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv) hg
  · apply L.imp_intro_future fp fg
    intro Δ δ e hg
    simp only [propertyG_rename] at hg
    rw [good_rename]
    exact (H.rename e).good_backward (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv) hg

end Formed
end SpecializedCode
end

section
universe u
variable {S : Type u}
namespace SpecializedCode
variable (B : SpecializedCode S)
def queries (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) :=
  B.relational.queryBody L t B.type (B.parameter L KY KP)
def classPred (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) :=
  B.relational.channel.classPred L KP B.baseType (B.goodBody L KY KP) y
def unionPred (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) :=
  B.relational.channel.unionPred L KP B.baseType (B.goodBody L KY KP) y z
def isClass (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (y : Expr S) :=
  B.relational.channel.isClass L KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) t y
def edge (L : LogicCode S) (KY KP : QuantifierCode S) (t : Bool) (y z : Expr S) :=
  B.relational.channel.edge L KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) t y z
def pairForm (L : LogicCode S) (KY KP : QuantifierCode S) (p a z : Expr S) :=
  B.relational.channel.pairForm L KY KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) p a z
def pair (L : LogicCode S) (KY KP : QuantifierCode S) (p a : Expr S) :=
  B.relational.pair L KY KP B.type (B.parameter L KY KP) p a

theorem queries_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :
    (B.queries L KY KP t).instantiate v = B.query L KY KP t v := by
  simp only [queries,RelationalCode.queryBody,DoubleCode.queryPredBody_instantiate,query]
theorem queries_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (ρ : Nat → Nat) :
    (B.queries L KY KP t).rename (Expr.liftRen ρ) = (B.rename ρ).queries (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t := by
  simp only [queries,RelationalCode.queryBody_rename,parameter_rename,SpecializedCode.rename,relational,ObservationCode.rename]
theorem isClass_eq (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (y : Expr S) :
    B.isClass L KY KP t y = B.query L KY KP (ChannelCode.classTag t) (B.classPred L KY KP y) := by
  simp only [isClass,ChannelCode.isClass,queries_instantiate,classPred]
theorem edge_eq (L : LogicCode S) (KY KP : QuantifierCode S) (t : Bool) (y z : Expr S) :
    B.edge L KY KP t y z = L.conj (B.isClass L KY KP 0 y)
      (L.conj (B.isClass L KY KP (if t then 2 else 1) z)
        (B.query L KY KP (ChannelCode.edgeTag t) (B.unionPred L KY KP y z))) := by
  simp only [edge,ChannelCode.edge,queries_instantiate,isClass,unionPred]

theorem classPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (ρ : Nat → Nat) :
    (B.classPred L KY KP y).rename ρ = (B.rename ρ).classPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) := by
  simp only [classPred,ChannelCode.classPred_rename,baseType_rename,goodBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]

theorem unionPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (B.unionPred L KY KP y z).rename ρ = (B.rename ρ).unionPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [unionPred,ChannelCode.unionPred_rename,baseType_rename,goodBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]

theorem isClass_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (y : Expr S) (ρ : Nat → Nat) :
    (B.isClass L KY KP t y).rename ρ = (B.rename ρ).isClass (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (y.rename ρ) := by
  simp only [isClass,ChannelCode.isClass_rename,baseType_rename,goodBody_rename,queries_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]

theorem edge_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Bool) (y z : Expr S) (ρ : Nat → Nat) :
    (B.edge L KY KP t y z).rename ρ = (B.rename ρ).edge (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (y.rename ρ) (z.rename ρ) := by
  simp only [edge,ChannelCode.edge_rename,baseType_rename,goodBody_rename,queries_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]

theorem pairForm_rename (L : LogicCode S) (KY KP : QuantifierCode S) (p a z : Expr S) (ρ : Nat → Nat) :
    (B.pairForm L KY KP p a z).rename ρ = (B.rename ρ).pairForm (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (p.rename ρ) (a.rename ρ) (z.rename ρ) := by
  simp only [pairForm,ChannelCode.pairForm_rename,baseType_rename,goodBody_rename,queries_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]

theorem pair_rename (L : LogicCode S) (KY KP : QuantifierCode S) (p a : Expr S) (ρ : Nat → Nat) :
    (B.pair L KY KP p a).rename ρ = (B.rename ρ).pair (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (p.rename ρ) (a.rename ρ) := by
  simp only [pair,RelationalCode.pair_rename,parameter_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename]
end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}
inductive ObservationFeature (S : Type u) where
  | inner | outer | probe (i : Expr S)
namespace ObservationFeature
def rename (f : ObservationFeature S) (ρ : Nat → Nat) : ObservationFeature S :=
  match f with | .inner => .inner | .outer => .outer | .probe i => .probe (i.rename ρ)
def subst (f : ObservationFeature S) (σ : Nat → Expr S) : ObservationFeature S :=
  match f with | .inner => .inner | .outer => .outer | .probe i => .probe (i.subst σ)
theorem rename_comp (f : ObservationFeature S) (ρ τ : Nat → Nat) :
    (f.rename τ).rename ρ = f.rename (ρ ∘ τ) := by cases f <;> simp only [rename,Expr.rename_comp]
theorem subst_rename (f : ObservationFeature S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (f.rename ρ).subst σ = f.subst (σ ∘ ρ) := by cases f <;> simp only [rename,subst,Expr.subst_rename]
theorem rename_subst (f : ObservationFeature S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (f.subst σ).rename ρ = f.subst (fun i => (σ i).rename ρ) := by cases f <;> simp only [rename,subst,Expr.rename_subst]
theorem instantiate_raise (f : ObservationFeature S) (a : Expr S) :
    (f.rename Nat.succ).subst (Expr.single a) = f := by cases f <;> simp only [rename,subst,Expr.subst_lift_single]
end ObservationFeature
namespace SpecializedCode
variable (B : SpecializedCode S)
def feature (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (y : Expr S) :=
  match f with
  | .inner => B.observation.bitInner L y
  | .outer => B.observation.bitOuter L y
  | .probe i => B.observation.observe L KY KP i y
def featureBody (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) :=
  (B.rename Nat.succ).feature (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (f.rename Nat.succ) (.var 0)
def featurePred (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) :=
  B.relational.channel.pred B.baseType (B.featureBody L KY KP f)
def FeatureFormed (Γ : List (Expr S)) (γ : Nat → Mode) (f : ObservationFeature S) : Prop :=
  match f with
  | .inner | .outer => True
  | .probe i => HasType P Γ i (B.relational.channel.predicateType B.relational.probe.carrier) ∧ WellModed γ i .data

theorem feature_rename (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (y : Expr S) (ρ : Nat → Nat) :
    (B.feature L KY KP f y).rename ρ = (B.rename ρ).feature (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (f.rename ρ) (y.rename ρ) := by
  cases f <;> simp only [feature,ObservationCode.bitInner_rename,ObservationCode.bitOuter_rename,
    ObservationCode.observe_rename,ObservationFeature.rename,SpecializedCode.rename]
theorem feature_subst (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (y : Expr S) (σ : Nat → Expr S) :
    (B.feature L KY KP f y).subst σ = (B.subst σ).feature (L.subst σ) (KY.subst σ) (KP.subst σ) (f.subst σ) (y.subst σ) := by
  cases f <;> simp only [feature,ObservationCode.bitInner_subst,ObservationCode.bitOuter_subst,
    ObservationCode.observe_subst,ObservationFeature.subst,SpecializedCode.subst]
theorem featureBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (ρ : Nat → Nat) :
    (B.featureBody L KY KP f).rename (Expr.liftRen ρ) = (B.rename ρ).featureBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (f.rename ρ) := by
  simp only [featureBody,feature_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,ObservationFeature.rename_comp,
    Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem featureBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (y : Expr S) :
    (B.featureBody L KY KP f).instantiate y = B.feature L KY KP f y := by
  simp only [featureBody,Expr.instantiate,feature_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,ObservationFeature.instantiate_raise,Expr.subst,Expr.single]
theorem featurePred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (f : ObservationFeature S) (ρ : Nat → Nat) :
    (B.featurePred L KY KP f).rename ρ = (B.rename ρ).featurePred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (f.rename ρ) := by
  simp only [featurePred,ChannelCode.pred_rename,baseType_rename,featureBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]
namespace FeatureFormed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {B : SpecializedCode S} {f : ObservationFeature S}
theorem rename (hf : B.FeatureFormed (P := P) Γ γ f) (e : Embedding P Γ γ Δ δ) :
    (B.rename e.names).FeatureFormed (P := P) Δ δ (f.rename e.names) := by
  cases f with
  | inner => trivial
  | outer => trivial
  | probe i =>
    refine ⟨?_,e.moded hf.2⟩
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,SpecializedCode.rename,relational,
      ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using e.typing hf.1
end FeatureFormed
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem feature_formula {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    L.Formula (B.feature L.code KY.code KP.code f y) := by
  cases f with
  | inner => exact H.observation.bitInner_formula hy my
  | outer => exact H.observation.bitOuter_formula hy my
  | probe i => exact H.observation.observe_formula KY KP hf.1 hf.2 hy my

theorem featureBody_family {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f) :
    L.Family B.yType (B.featureBody L.code KY.code KP.code f) := by
  intro Δ δ e y hy my
  rw [featureBody_rename,featureBody_instantiate]
  exact (H.rename e).feature_formula (KY.rename e) (KP.rename e) (FeatureFormed.rename hf e)
    (by simpa only [yType_rename] using hy) my

theorem feature_round {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.feature L.code KY.code KP.code f (B.round y)) (B.feature L.code KY.code KP.code f y) := by
  cases f with
  | inner => exact H.bitInner_round hy my
  | outer => exact H.bitOuter_round hy my
  | probe i => exact H.observe_round KY KP hy my hf.1 hf.2

theorem feature_respect {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.observation.ae L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.feature L.code KY.code KP.code f y) (B.feature L.code KY.code KP.code f z) := by
  obtain ⟨hi,ho,hc⟩ := H.observation.ae_elim KY KP hy my hz mz he
  cases f with
  | inner => exact hi
  | outer => exact ho
  | probe i => exact H.observation.compare_elim KY KP hy my hz mz hf.1 hf.2 hc

theorem featurePred_typed {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f) :
    HasType P Γ (B.featurePred L.code KY.code KP.code f) B.predType ∧
      WellModed γ (B.featurePred L.code KY.code KP.code f) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.base_sorted H.base_mode (H.shape ▸ H.featureBody_family KY KP hf)
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem featurePred_evaluation {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.ev (B.featurePred L.code KY.code KP.code f) y) (B.feature L.code KY.code KP.code f y) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.base_sorted H.base_mode (H.shape ▸ H.featureBody_family KY KP hf)
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs) (H.shape ▸ hy) my
  rw [featureBody_instantiate] at he
  have ht := H.featurePred_typed KY KP hf
  have hr := H.round_typed hy my
  exact (H.ev_formula ht.1 ht.2 hy my).equivalent_trans (H.feature_formula KY KP hf hr.1 hr.2)
    (H.feature_formula KY KP hf hy my) he (H.feature_round KY KP hf hy my)
end Formed
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem featurePred_respect {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.observation.ae L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.ev (B.featurePred L.code KY.code KP.code f) y) (B.ev (B.featurePred L.code KY.code KP.code f) z) := by
  have hp := H.featurePred_typed KY KP hf
  have ey := H.featurePred_evaluation KY KP hf hy my
  have ez := H.featurePred_evaluation KY KP hf hz mz
  have ec := H.feature_respect KY KP hf hy my hz mz he
  have fy := H.ev_formula hp.1 hp.2 hy my
  have fz := H.ev_formula hp.1 hp.2 hz mz
  have gy := H.feature_formula KY KP hf hy my
  have gz := H.feature_formula KY KP hf hz mz
  exact fy.equivalent_trans gz fz (fy.equivalent_trans gy gz ey ec) ez.symm

theorem feature_gStep {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Proves P Γ γ (B.gStep L.code KY.code KP.code (B.featurePred L.code KY.code KP.code f) y z) := by
  have hp := H.featurePred_typed KY KP hf
  apply L.imp_intro_future (H.observation.ae_formula KY KP hy my hz mz)
    (L.iff_formula (H.ev_formula hp.1 hp.2 hy my) (H.ev_formula hp.1 hp.2 hz mz))
  intro Δ δ e he
  simp only [ObservationCode.ae_rename] at he
  rw [LogicSetup.iff_rename,ev_rename,ev_rename,featurePred_rename]
  have hp' := (H.rename e).featurePred_typed (KY.rename e) (KP.rename e) (FeatureFormed.rename hf e)
  have hy' := y_typed_rename (B := B) e hy
  have hz' := y_typed_rename (B := B) e hz
  exact (L.rename e).iff_of_equivalent ((H.rename e).ev_formula hp'.1 hp'.2 hy' (e.moded my))
    ((H.rename e).ev_formula hp'.1 hp'.2 hz' (e.moded mz))
    ((H.rename e).featurePred_respect (KY.rename e) (KP.rename e) (FeatureFormed.rename hf e) hy' (e.moded my) hz' (e.moded mz) he)

theorem feature_gAt {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Proves P Γ γ (B.gAt L.code KY.code KP.code (B.featurePred L.code KY.code KP.code f) y) := by
  have hp := H.featurePred_typed KY KP hf
  apply H.gAt_intro KY KP hp.1 hp.2 hy my
  intro Δ δ e z hz mz
  rw [featurePred_rename]
  exact (H.rename e).feature_gStep (KY.rename e) (KP.rename e) (FeatureFormed.rename hf e)
    (y_typed_rename (B := B) e hy) (e.moded my) hz mz

theorem feature_propertyG {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f) :
    Proves P Γ γ (B.propertyG L.code KY.code KP.code (B.featurePred L.code KY.code KP.code f)) := by
  have hp := H.featurePred_typed KY KP hf
  apply H.propertyG_intro KY KP hp.1 hp.2
  intro Δ δ e y hy my
  rw [featurePred_rename]
  exact (H.rename e).feature_gAt (KY.rename e) (KP.rename e) (FeatureFormed.rename hf e) hy my

theorem feature_good {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f) :
    Proves P Γ γ (B.good L.code KY.code KP.code (B.featurePred L.code KY.code KP.code f)) := by
  have hp := H.featurePred_typed KY KP hf
  exact H.good_backward KY KP hp.1 hp.2 (H.feature_propertyG KY KP hf)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem relation_formula {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    L.Formula (B.relation L.code KY.code KP.code y z) :=
  H.relational_formed.channel.relation_formula KP H.base_sorted H.base_mode (H.goodBody_family KY KP)
    (H.shape ▸ hy) my (H.shape ▸ hz) mz

theorem relation_elim {v y z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z))
    (hg : Proves P Γ γ (B.good L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.ev v y) (B.ev v z) :=
  H.relational_formed.channel.relation_elim KP H.base_sorted H.base_mode (H.goodBody_family KY KP)
    (H.shape ▸ hy) my (H.shape ▸ hz) mz hv mv he (by rw [goodBody_instantiate]; exact hg)

theorem relation_to_feature {f : ObservationFeature S} (hf : B.FeatureFormed (P := P) Γ γ f)
    {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.feature L.code KY.code KP.code f y) (B.feature L.code KY.code KP.code f z) := by
  have hp := H.featurePred_typed KY KP hf
  have ee := H.relation_elim KY KP hp.1 hp.2 hy my hz mz he (H.feature_good KY KP hf)
  have ey := H.featurePred_evaluation KY KP hf hy my
  have ez := H.featurePred_evaluation KY KP hf hz mz
  have fy := H.ev_formula hp.1 hp.2 hy my
  have fz := H.ev_formula hp.1 hp.2 hz mz
  have gy := H.feature_formula KY KP hf hy my
  have gz := H.feature_formula KY KP hf hz mz
  exact gy.equivalent_trans fz gz (gy.equivalent_trans fy fz ey.symm ee) ez

theorem relation_forward {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z)) :
    Proves P Γ γ (B.observation.ae L.code KY.code KP.code y z) := by
  apply H.observation.ae_intro KY KP hy my hz mz
  · exact H.relation_to_feature KY KP (f := .inner) trivial hy my hz mz he
  · exact H.relation_to_feature KY KP (f := .outer) trivial hy my hz mz he
  · apply H.observation.compare_intro KY KP hy my hz mz
    intro Δ δ e i hi mi
    have he' := he.rename e
    simp only [relation_rename] at he'
    exact (H.rename e).relation_to_feature (KY.rename e) (KP.rename e) (f := .probe i) ⟨hi,mi⟩
      (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz) he'

theorem relation_backward {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.observation.ae L.code KY.code KP.code y z)) :
    Proves P Γ γ (B.relation L.code KY.code KP.code y z) := by
  apply H.relational_formed.channel.relation_intro KP H.base_sorted H.base_mode (H.goodBody_family KY KP)
    (H.shape ▸ hy) my (H.shape ▸ hz) mz
  intro Δ δ e v hv mv hg
  rw [goodBody_rename,goodBody_instantiate] at hg
  have hv' : HasType P Δ v (B.rename e.names).predType := by
    simpa only [predType,baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,
      RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hv
  have he' := he.rename e
  simp only [ObservationCode.ae_rename] at he'
  have hgood := (H.rename e).good_forward (KY.rename e) (KP.rename e) hv' mv hg
  have hh := (H.rename e).propertyG_elim (KY.rename e) (KP.rename e) hv' mv
    (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz) hgood he'
  simpa only [ev,baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,
    RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hh

theorem observation_equivalence {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (B.relation L.code KY.code KP.code y z) (B.observation.ae L.code KY.code KP.code y z) := by
  have fr := H.relation_formula KY KP hy my hz mz
  have fa := H.observation.ae_formula KY KP hy my hz mz
  apply L.equivalent_of_iff fr fa
  apply L.conj_intro (L.imp_formula fr fa) (L.imp_formula fa fr)
  · apply L.imp_intro_future fr fa
    intro Δ δ e he
    simp only [relation_rename] at he
    rw [ObservationCode.ae_rename]
    exact (H.rename e).relation_forward (KY.rename e) (KP.rename e)
      (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz) he
  · apply L.imp_intro_future fa fr
    intro Δ δ e he
    simp only [ObservationCode.ae_rename] at he
    rw [relation_rename]
    exact (H.rename e).relation_backward (KY.rename e) (KP.rename e)
      (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz) he
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem cAt_intro (t : Fin 3) {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) w,
      HasType P Δ w (B.rename e.names).yType → WellModed δ w .data →
      Proves P Δ δ ((B.rename e.names).cStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        t (v.rename e.names) (x.rename e.names) w)) :
    Proves P Γ γ (B.cAt L.code KY.code KP.code t v x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.cAtBody_family KY KP t hv mv hx mx)
  intro Δ δ e w hw mw
  rw [cAtBody_rename,cAtBody_instantiate]
  exact hh Δ δ e w (by simpa only [yType_rename] using hw) mw

theorem cAt_elim (t : Fin 3) {v x w : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    (hp : Proves P Γ γ (B.cAt L.code KY.code KP.code t v x)) :
    Proves P Γ γ (B.cStep L.code KY.code KP.code t v x w) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.cAtBody_family KY KP t hv mv hx mx) hw mw hp
  simpa only [cAtBody_instantiate] using hh

theorem propertyC_intro (t : Fin 3) {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.cAt L.code KY.code KP.code t v x)) :
    Proves P Γ γ (B.propertyC L.code KY.code KP.code t v) := by
  apply L.ex_intro KY H.x_sorted H.x_mode (H.cBody_family KY KP t hv mv) hx mx
  simpa only [cBody_instantiate] using hp

theorem propertyC_elim (t : Fin 3) {v D : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) (hd : L.Formula D)
    (hp : Proves P Γ γ (B.propertyC L.code KY.code KP.code t v))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((B.rename e.names).cAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        t (v.rename e.names) x) → Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  apply L.ex_elim KY H.x_sorted H.x_mode (H.cBody_family KY KP t hv mv) hd hp
  intro Δ δ e x hx mx hxv
  rw [cBody_rename,cBody_instantiate] at hxv
  exact hh Δ δ e x (by simpa only [xType_rename] using hx) mx hxv

theorem eAt_intro (t : Fin 3) {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) w,
      HasType P Δ w (B.rename e.names).yType → WellModed δ w .data →
      Proves P Δ δ ((B.rename e.names).eStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        t (v.rename e.names) (x.rename e.names) w)) :
    Proves P Γ γ (B.eAt L.code KY.code KP.code t v x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.eAtBody_family KY KP t hv mv hx mx)
  intro Δ δ e w hw mw
  rw [eAtBody_rename,eAtBody_instantiate]
  exact hh Δ δ e w (by simpa only [yType_rename] using hw) mw

theorem eAt_elim (t : Fin 3) {v x w : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    (hp : Proves P Γ γ (B.eAt L.code KY.code KP.code t v x)) :
    Proves P Γ γ (B.eStep L.code KY.code KP.code t v x w) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.eAtBody_family KY KP t hv mv hx mx) hw mw hp
  simpa only [eAtBody_instantiate] using hh

theorem propertyE_intro (t : Fin 3) {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.eAt L.code KY.code KP.code t v x)) :
    Proves P Γ γ (B.propertyE L.code KY.code KP.code t v) := by
  apply L.ex_intro KY H.x_sorted H.x_mode (H.eBody_family KY KP t hv mv) hx mx
  simpa only [eBody_instantiate] using hp

theorem propertyE_elim (t : Fin 3) {v D : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) (hd : L.Formula D)
    (hp : Proves P Γ γ (B.propertyE L.code KY.code KP.code t v))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((B.rename e.names).eAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        t (v.rename e.names) x) → Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  apply L.ex_elim KY H.x_sorted H.x_mode (H.eBody_family KY KP t hv mv) hd hp
  intro Δ δ e x hx mx hxv
  rw [eBody_rename,eBody_instantiate] at hxv
  exact hh Δ δ e x (by simpa only [xType_rename] using hx) mx hxv
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem queries_family (t : Fin 7) : L.Family B.predType (B.queries L.code KY.code KP.code t) :=
  H.relational_formed.queryBody_family t H.type_sorted H.type_mode
    (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2

theorem classPred_typed {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    HasType P Γ (B.classPred L.code KY.code KP.code y) B.predType ∧
      WellModed γ (B.classPred L.code KY.code KP.code y) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.classPred_typed KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.shape ▸ hy) my (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem unionPred_typed {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    HasType P Γ (B.unionPred L.code KY.code KP.code y z) B.predType ∧
      WellModed γ (B.unionPred L.code KY.code KP.code y z) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.unionPred_typed KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.shape ▸ hy) my (H.shape ▸ hz) mz
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem isClass_formula (t : Fin 3) {y : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    L.Formula (B.isClass L.code KY.code KP.code t y) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.isClass_formula KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.queries_family KY KP)
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs) t (H.shape ▸ hy) my

theorem edge_formula (t : Bool) {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    L.Formula (B.edge L.code KY.code KP.code t y z) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.edge_formula KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.queries_family KY KP)
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs) t (H.shape ▸ hy) my (H.shape ▸ hz) mz

theorem pairForm_formula {v a z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    L.Formula (B.pairForm L.code KY.code KP.code v a z) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pairForm_formula KY KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.queries_family KY KP)
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs) hv mv (H.shape ▸ ha) ma (H.shape ▸ hz) mz

theorem pair_typed {v a : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data) :
    HasType P Γ (B.pair L.code KY.code KP.code v a) B.predType ∧
      WellModed γ (B.pair L.code KY.code KP.code v a) .data :=
  H.relational_formed.pair_typed KY KP H.type_sorted H.type_mode
    (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 hv mv (H.shape ▸ ha) ma

theorem class_evaluation {y w : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (B.ev (B.classPred L.code KY.code KP.code y) w)
      (B.relation L.code KY.code KP.code w y) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.class_evaluation KP H.base_sorted H.base_mode KY
    (H.queries_family KY KP 0) (H.shape ▸ hy) my (H.shape ▸ hw) mw
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem class_observation_evaluation {y w : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (B.ev (B.classPred L.code KY.code KP.code y) w)
      (B.observation.ae L.code KY.code KP.code w y) := by
  have ht := H.classPred_typed KY KP hy my
  exact (H.ev_formula ht.1 ht.2 hw mw).equivalent_trans (H.relation_formula KY KP hw mw hy my)
    (H.observation.ae_formula KY KP hw mw hy my) (H.class_evaluation KY KP hy my hw mw)
    (H.observation_equivalence KY KP hw mw hy my)

theorem union_evaluation {y z w : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (B.ev (B.unionPred L.code KY.code KP.code y z) w)
      (L.disj (B.relation L.code KY.code KP.code w y) (B.relation L.code KY.code KP.code w z)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.union_evaluation KP KY H.base_sorted H.base_mode
    (H.queries_family KY KP 0) (H.shape ▸ hy) my (H.shape ▸ hz) mz (H.shape ▸ hw) mw
    (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem union_observation_evaluation {y z w : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (B.ev (B.unionPred L.code KY.code KP.code y z) w)
      (L.disj (B.observation.ae L.code KY.code KP.code w y) (B.observation.ae L.code KY.code KP.code w z)) := by
  have ht := H.unionPred_typed KY KP hy my hz mz
  have fy := H.relation_formula KY KP hw mw hy my
  have fz := H.relation_formula KY KP hw mw hz mz
  have gy := H.observation.ae_formula KY KP hw mw hy my
  have gz := H.observation.ae_formula KY KP hw mw hz mz
  exact (H.ev_formula ht.1 ht.2 hw mw).equivalent_trans (L.disj_formula fy fz)
    (L.disj_formula gy gz) (H.union_evaluation KY KP hy my hz mz hw mw)
    (L.disj_congr fy gy fz gz (H.observation_equivalence KY KP hw mw hy my)
      (H.observation_equivalence KY KP hw mw hz mz))

end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem relation_refl {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Proves P Γ γ (B.relation L.code KY.code KP.code y y) :=
  H.relational_formed.channel.relation_refl KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.shape ▸ hy) my

theorem relation_symm {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z)) :
    Proves P Γ γ (B.relation L.code KY.code KP.code z y) :=
  H.relational_formed.channel.relation_symm KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.shape ▸ hy) my (H.shape ▸ hz) mz he

theorem relation_trans {y z w : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z))
    (hf : Proves P Γ γ (B.relation L.code KY.code KP.code z w)) :
    Proves P Γ γ (B.relation L.code KY.code KP.code y w) :=
  H.relational_formed.channel.relation_trans KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.shape ▸ hy) my (H.shape ▸ hz) mz (H.shape ▸ hw) mw he hf

theorem relation_congr {a b c d : Expr S}
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (hc : HasType P Γ c B.yType) (mc : WellModed γ c .data)
    (hd : HasType P Γ d B.yType) (md : WellModed γ d .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code a b))
    (hf : Proves P Γ γ (B.relation L.code KY.code KP.code c d)) :
    Equivalent P Γ γ (B.relation L.code KY.code KP.code a c) (B.relation L.code KY.code KP.code b d) :=
  H.relational_formed.channel.relation_congr KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.shape ▸ ha) ma (H.shape ▸ hb) mb (H.shape ▸ hc) mc (H.shape ▸ hd) md he hf

theorem relation_tagged_same (t : Fin 3) {x z : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hz : HasType P Γ z B.xType) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (B.relation L.code KY.code KP.code (B.observation.tagged L.code t x) (B.observation.tagged L.code t z))
      (B.relational.xCompare L.code KY.code KP.code x z) := by
  have ht := H.observation.tagged_typed t hx mx
  have hu := H.observation.tagged_typed t hz mz
  exact (H.relation_formula KY KP ht.1 ht.2 hu.1 hu.2).equivalent_trans
    (H.observation.ae_formula KY KP ht.1 ht.2 hu.1 hu.2)
    (H.relational_formed.xCompare_formula KY KP hx mx hz mz)
    (H.observation_equivalence KY KP ht.1 ht.2 hu.1 hu.2)
    (H.observation.ae_tagged_same KY KP t hx mx hz mz)

theorem relation_tagged_distinct (t u : Fin 3) (htu : t ≠ u) {x z : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hz : HasType P Γ z B.xType) (mz : WellModed γ z .data) :
    Proves P Γ γ (L.neg (B.relation L.code KY.code KP.code (B.observation.tagged L.code t x) (B.observation.tagged L.code u z))) := by
  have ht := H.observation.tagged_typed t hx mx
  have hu := H.observation.tagged_typed u hz mz
  have he := H.observation_equivalence KY KP ht.1 ht.2 hu.1 hu.2
  have hn := H.observation.ae_tagged_distinct KY KP t u htu hx mx hz mz
  have hf := H.relation_formula KY KP ht.1 ht.2 hu.1 hu.2
  have fa := H.observation.ae_formula KY KP ht.1 ht.2 hu.1 hu.2
  pts_pl L using [he,hn]

theorem class_self {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Proves P Γ γ (B.ev (B.classPred L.code KY.code KP.code y) y) :=
  (H.class_evaluation KY KP hy my hy my).2.prove (H.relation_refl KY KP hy my)

theorem class_query (t : Fin 3) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.query L.code KY.code KP.code (ChannelCode.classTag t) v)
      (B.propertyC L.code KY.code KP.code t v) := by
  fin_cases t
  · exact H.parameter_query KY KP 1 hv mv
  · exact H.parameter_query KY KP 2 hv mv
  · exact H.parameter_query KY KP 3 hv mv

theorem class_witness_elim (t : Fin 3) {y D : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) (hd : L.Formula D)
    (hi : Proves P Γ γ (B.isClass L.code KY.code KP.code t y))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (y.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) t x)) →
      Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  have ht := H.classPred_typed KY KP hy my
  rw [isClass_eq] at hi
  have hp := (H.class_query KY KP t ht.1 ht.2).1.prove hi
  apply H.propertyC_elim KY KP t ht.1 ht.2 hd hp
  intro Δ δ e x hx mx hc
  simp only [classPred_rename] at hc
  have hy' := y_typed_rename (B := B) e hy
  have ht' := (H.rename e).classPred_typed (KY.rename e) (KP.rename e) hy' (e.moded my)
  have he := (H.rename e).cAt_elim (KY.rename e) (KP.rename e) t ht'.1 ht'.2 hx mx hy' (e.moded my) hc
  have htag := (H.rename e).observation.tagged_typed t hx mx
  have hf := (H.rename e).ev_formula ht'.1 ht'.2 hy' (e.moded my)
  have hg := (H.rename e).observation.ae_formula (KY.rename e) (KP.rename e) hy' (e.moded my) htag.1 htag.2
  have hae := ((L.rename e).equivalent_of_iff hf hg he).1.prove
    ((H.rename e).class_self (KY.rename e) (KP.rename e) hy' (e.moded my))
  exact hh Δ δ e x hx mx ((H.rename e).relation_backward (KY.rename e) (KP.rename e)
    hy' (e.moded my) htag.1 htag.2 hae)

theorem class_at_witness (t : Fin 3) {y x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code t x))) :
    Proves P Γ γ (B.cAt L.code KY.code KP.code t (B.classPred L.code KY.code KP.code y) x) := by
  have ht := H.classPred_typed KY KP hy my
  apply H.cAt_intro KY KP t ht.1 ht.2 hx mx
  intro Δ δ e w hw mw
  simp only [cStep,classPred_rename]
  have hy' := y_typed_rename (B := B) e hy
  have hx' := x_typed_rename (B := B) e hx
  have ht' := (H.rename e).classPred_typed (KY.rename e) (KP.rename e) hy' (e.moded my)
  have htag := (H.rename e).observation.tagged_typed t hx' (e.moded mx)
  have he' := he.rename e
  simp only [relation_rename,ObservationCode.tagged_rename] at he'
  have ee := (H.rename e).relation_congr (KY.rename e) (KP.rename e) hw mw hw mw hy' (e.moded my)
    htag.1 htag.2 ((H.rename e).relation_refl (KY.rename e) (KP.rename e) hw mw) he'
  have ec := (H.rename e).class_evaluation (KY.rename e) (KP.rename e) hy' (e.moded my) hw mw
  have ea := (H.rename e).observation_equivalence (KY.rename e) (KP.rename e) hw mw htag.1 htag.2
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).ev_formula ht'.1 ht'.2 hw mw)
    ((H.rename e).observation.ae_formula (KY.rename e) (KP.rename e) hw mw htag.1 htag.2)
    (((H.rename e).ev_formula ht'.1 ht'.2 hw mw).equivalent_trans
      ((H.rename e).relation_formula (KY.rename e) (KP.rename e) hw mw hy' (e.moded my))
      ((H.rename e).observation.ae_formula (KY.rename e) (KP.rename e) hw mw htag.1 htag.2) ec
      (((H.rename e).relation_formula (KY.rename e) (KP.rename e) hw mw hy' (e.moded my)).equivalent_trans
        ((H.rename e).relation_formula (KY.rename e) (KP.rename e) hw mw htag.1 htag.2)
        ((H.rename e).observation.ae_formula (KY.rename e) (KP.rename e) hw mw htag.1 htag.2) ee ea))

theorem class_witness_intro (t : Fin 3) {y x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code t x))) :
    Proves P Γ γ (B.isClass L.code KY.code KP.code t y) := by
  have ht := H.classPred_typed KY KP hy my
  rw [isClass_eq]
  exact (H.class_query KY KP t ht.1 ht.2).2.prove
    (H.propertyC_intro KY KP t ht.1 ht.2 hx mx (H.class_at_witness KY KP t hy my hx mx he))
end SpecializedCode.Formed

namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {A A' B B' : Expr S}
theorem select_disj_left (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B')
    (hab : Proves P Γ γ (L.disj A' B')) (hn : Proves P Γ γ (L.neg B)) :
    Proves P Γ γ A := by pts_pl L using [eA,eB,hab,hn]
theorem select_disj_right (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B')
    (hab : Proves P Γ γ (L.disj A' B')) (hn : Proves P Γ γ (L.neg A)) :
    Proves P Γ γ B := by pts_pl L using [eA,eB,hab,hn]
end LogicSetup
namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem tag_witness_incompatible (t u : Fin 3) (htu : t ≠ u) {y a x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (ha : HasType P Γ a B.xType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code t a))) :
    Proves P Γ γ (L.neg (B.relation L.code KY.code KP.code y (B.observation.tagged L.code u x))) := by
  have ht := H.observation.tagged_typed t ha ma
  have hu := H.observation.tagged_typed u hx mx
  have ee := H.relation_congr KY KP hy my ht.1 ht.2 hu.1 hu.2 hu.1 hu.2 he
    (H.relation_refl KY KP hu.1 hu.2)
  exact (L.neg_equivalent (H.relation_formula KY KP hy my hu.1 hu.2)
    (H.relation_formula KY KP ht.1 ht.2 hu.1 hu.2) ee).2.prove
    (H.relation_tagged_distinct KY KP t u htu ha ma hx mx)

theorem union_left_hit {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Proves P Γ γ (B.ev (B.unionPred L.code KY.code KP.code y z) y) := by
  apply (H.union_evaluation KY KP hy my hz mz hy my).2.prove
  have haa := H.relation_formula KY KP hy my hy my
  have hab := H.relation_formula KY KP hy my hz mz
  have hrefl := H.relation_refl KY KP hy my
  pts_pl L using [hrefl]

theorem union_right_hit {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Proves P Γ γ (B.ev (B.unionPred L.code KY.code KP.code y z) z) := by
  apply (H.union_evaluation KY KP hy my hz mz hz mz).2.prove
  have haa := H.relation_formula KY KP hz mz hy my
  have hab := H.relation_formula KY KP hz mz hz mz
  have hrefl := H.relation_refl KY KP hz mz
  pts_pl L using [hrefl]

theorem edge_witness_core (t : Fin 3) (ht : t ≠ 0) {y z a b x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (ha : HasType P Γ a B.xType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.xType) (mb : WellModed γ b .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 a)))
    (eb : Proves P Γ γ (B.relation L.code KY.code KP.code z (B.observation.tagged L.code t b)))
    (he : Proves P Γ γ (B.eAt L.code KY.code KP.code t (B.unionPred L.code KY.code KP.code y z) x)) :
    Proves P Γ γ (L.conj (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x))
      (B.relation L.code KY.code KP.code z (B.observation.tagged L.code t x))) := by
  have hu := H.unionPred_typed KY KP hy my hz mz
  have hx0 := H.observation.tagged_typed 0 hx mx
  have hxt := H.observation.tagged_typed t hx mx
  have fy := H.relation_formula KY KP hy my hx0.1 hx0.2
  have fyn := H.relation_formula KY KP hy my hxt.1 hxt.2
  have fz := H.relation_formula KY KP hz mz hxt.1 hxt.2
  have fzn := H.relation_formula KY KP hz mz hx0.1 hx0.2
  apply L.conj_intro fy fz
  · have ey := H.eAt_elim KY KP t hu.1 hu.2 hx mx hy my he
    have fay := H.observation.ae_formula KY KP hy my hx0.1 hx0.2
    have fayn := H.observation.ae_formula KY KP hy my hxt.1 hxt.2
    have eay := (L.equivalent_of_iff (H.ev_formula hu.1 hu.2 hy my) (L.disj_formula fay fayn) ey).1.prove
      (H.union_left_hit KY KP hy my hz mz)
    have sy := H.observation_equivalence KY KP hy my hx0.1 hx0.2
    have syn := H.observation_equivalence KY KP hy my hxt.1 hxt.2
    have hn := H.tag_witness_incompatible KY KP 0 t (Ne.symm ht) hy my ha ma hx mx ea
    exact L.select_disj_left fy fay fyn fayn sy syn eay hn
  · have ez := H.eAt_elim KY KP t hu.1 hu.2 hx mx hz mz he
    have fazn := H.observation.ae_formula KY KP hz mz hx0.1 hx0.2
    have faz := H.observation.ae_formula KY KP hz mz hxt.1 hxt.2
    have eaz := (L.equivalent_of_iff (H.ev_formula hu.1 hu.2 hz mz) (L.disj_formula fazn faz) ez).1.prove
      (H.union_right_hit KY KP hy my hz mz)
    have sz := H.observation_equivalence KY KP hz mz hxt.1 hxt.2
    have szn := H.observation_equivalence KY KP hz mz hx0.1 hx0.2
    have hn := H.tag_witness_incompatible KY KP t 0 ht hz mz hb mb hx mx eb
    exact L.select_disj_right fzn fazn fz faz szn sz eaz hn

theorem edge_query (t : Bool) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.query L.code KY.code KP.code (ChannelCode.edgeTag t) v)
      (B.propertyE L.code KY.code KP.code (if t then 2 else 1) v) := by
  cases t
  · exact H.parameter_query KY KP 4 hv mv
  · exact H.parameter_query KY KP 5 hv mv
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem relation_observation_congr {a b w : Expr S}
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (hw : HasType P Γ w B.yType) (mw : WellModed γ w .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Equivalent P Γ γ (B.relation L.code KY.code KP.code w a) (B.observation.ae L.code KY.code KP.code w b) :=
  (H.relation_formula KY KP hw mw ha ma).equivalent_trans
    (H.relation_formula KY KP hw mw hb mb) (H.observation.ae_formula KY KP hw mw hb mb)
    (H.relation_congr KY KP hw mw hw mw ha ma hb mb (H.relation_refl KY KP hw mw) he)
    (H.observation_equivalence KY KP hw mw hb mb)

theorem union_at_witness (t : Fin 3) {y z x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (ey : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x)))
    (ez : Proves P Γ γ (B.relation L.code KY.code KP.code z (B.observation.tagged L.code t x))) :
    Proves P Γ γ (B.eAt L.code KY.code KP.code t (B.unionPred L.code KY.code KP.code y z) x) := by
  have hu := H.unionPred_typed KY KP hy my hz mz
  apply H.eAt_intro KY KP t hu.1 hu.2 hx mx
  intro Δ δ e w hw mw
  simp only [eStep,unionPred_rename]
  have hy' := y_typed_rename (B := B) e hy
  have hz' := y_typed_rename (B := B) e hz
  have hx' := x_typed_rename (B := B) e hx
  have ey' := ey.rename e
  have ez' := ez.rename e
  simp only [relation_rename,ObservationCode.tagged_rename] at ey' ez'
  have ht0 := (H.rename e).observation.tagged_typed 0 hx' (e.moded mx)
  have htt := (H.rename e).observation.tagged_typed t hx' (e.moded mx)
  have hu' := (H.rename e).unionPred_typed (KY.rename e) (KP.rename e) hy' (e.moded my) hz' (e.moded mz)
  have fy := (H.rename e).relation_formula (KY.rename e) (KP.rename e) hw mw hy' (e.moded my)
  have fz := (H.rename e).relation_formula (KY.rename e) (KP.rename e) hw mw hz' (e.moded mz)
  have gy := (H.rename e).observation.ae_formula (KY.rename e) (KP.rename e) hw mw ht0.1 ht0.2
  have gz := (H.rename e).observation.ae_formula (KY.rename e) (KP.rename e) hw mw htt.1 htt.2
  have ee := (H.rename e).union_evaluation (KY.rename e) (KP.rename e) hy' (e.moded my) hz' (e.moded mz) hw mw
  have ec := (L.rename e).disj_congr fy gy fz gz
    ((H.rename e).relation_observation_congr (KY.rename e) (KP.rename e) hy' (e.moded my) ht0.1 ht0.2 hw mw ey')
    ((H.rename e).relation_observation_congr (KY.rename e) (KP.rename e) hz' (e.moded mz) htt.1 htt.2 hw mw ez')
  exact (L.rename e).iff_of_equivalent ((H.rename e).ev_formula hu'.1 hu'.2 hw mw)
    ((L.rename e).disj_formula gy gz)
    (((H.rename e).ev_formula hu'.1 hu'.2 hw mw).equivalent_trans
      ((L.rename e).disj_formula fy fz) ((L.rename e).disj_formula gy gz) ee ec)

theorem edge_witness_intro (t : Bool) {y z x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (ey : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x)))
    (ez : Proves P Γ γ (B.relation L.code KY.code KP.code z (B.observation.tagged L.code (if t then 2 else 1) x))) :
    Proves P Γ γ (B.edge L.code KY.code KP.code t y z) := by
  rw [edge_eq]
  have fy := H.isClass_formula KY KP 0 hy my
  have fz := H.isClass_formula KY KP (if t then 2 else 1) hz mz
  have hu := H.unionPred_typed KY KP hy my hz mz
  have fq := H.parameter_query_formula KY KP (ChannelCode.edgeTag t) hu.1 hu.2
  exact L.conj_intro fy (L.conj_formula fz fq)
    (H.class_witness_intro KY KP 0 hy my hx mx ey)
    (L.conj_intro fz fq (H.class_witness_intro KY KP (if t then 2 else 1) hz mz hx mx ez)
      ((H.edge_query KY KP t hu.1 hu.2).2.prove
        (H.propertyE_intro KY KP (if t then 2 else 1) hu.1 hu.2 hx mx
          (H.union_at_witness KY KP (if t then 2 else 1) hy my hz mz hx mx ey ez))))
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem edge_property_witness_elim (t : Fin 3) (ht : t ≠ 0) {y z a b D : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (ha : HasType P Γ a B.xType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.xType) (mb : WellModed γ b .data) (hd : L.Formula D)
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 a)))
    (eb : Proves P Γ γ (B.relation L.code KY.code KP.code z (B.observation.tagged L.code t b)))
    (he : Proves P Γ γ (B.propertyE L.code KY.code KP.code t (B.unionPred L.code KY.code KP.code y z)))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((L.code.rename e.names).conj
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (y.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) 0 x))
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (z.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) t x))) →
      Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  have hu := H.unionPred_typed KY KP hy my hz mz
  apply H.propertyE_elim KY KP t hu.1 hu.2 hd he
  intro Δ δ e x hx mx heAt
  simp only [unionPred_rename] at heAt
  have ea' := ea.rename e
  have eb' := eb.rename e
  simp only [relation_rename,ObservationCode.tagged_rename] at ea' eb'
  exact hh Δ δ e x hx mx ((H.rename e).edge_witness_core (KY.rename e) (KP.rename e) t ht
    (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz)
    (x_typed_rename (B := B) e ha) (e.moded ma) (x_typed_rename (B := B) e hb) (e.moded mb)
    hx mx ea' eb' heAt)

theorem edge_given_left_elim (t : Fin 3) (ht : t ≠ 0) {y z a D : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (ha : HasType P Γ a B.xType) (ma : WellModed γ a .data) (hd : L.Formula D)
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 a)))
    (hzClass : Proves P Γ γ (B.isClass L.code KY.code KP.code t z))
    (he : Proves P Γ γ (B.propertyE L.code KY.code KP.code t (B.unionPred L.code KY.code KP.code y z)))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((L.code.rename e.names).conj
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (y.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) 0 x))
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (z.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) t x))) →
      Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  apply H.class_witness_elim KY KP t hz mz hd hzClass
  intro Δ δ e b hb mb eb
  have ea' := ea.rename e
  have he' := he.rename e
  simp only [relation_rename,ObservationCode.tagged_rename] at ea'
  simp only [propertyE_rename,unionPred_rename] at he'
  apply (H.rename e).edge_property_witness_elim (KY.rename e) (KP.rename e) t ht
    (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz)
    (x_typed_rename (B := B) e ha) (e.moded ma) hb mb (hd.rename e) ea' eb he'
  intro Θ θ f x hx mx hp
  have hx' : HasType P Θ x (B.rename (e.comp f).names).xType := by
    simpa only [rename_comp,Embedding.comp] using hx
  have bo : (B.rename e.names).observation = B.observation.rename e.names := rfl
  have hh' := hh Θ θ (e.comp f) x hx' mx (by
    simpa only [QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProofWrapper.rename_comp,bo,LogicSetup.code_rename,rename_comp,LogicCode.rename_comp,
      QuantifierCode.rename_comp,ObservationCode.rename_comp,Expr.rename_comp,Embedding.comp] using hp)
  simpa only [Expr.rename_comp,Embedding.comp] using hh'

theorem edge_classes_witness_elim (t : Fin 3) (ht : t ≠ 0) {y z D : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) (hd : L.Formula D)
    (hyClass : Proves P Γ γ (B.isClass L.code KY.code KP.code 0 y))
    (hzClass : Proves P Γ γ (B.isClass L.code KY.code KP.code t z))
    (he : Proves P Γ γ (B.propertyE L.code KY.code KP.code t (B.unionPred L.code KY.code KP.code y z)))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((L.code.rename e.names).conj
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (y.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) 0 x))
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (z.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) t x))) →
      Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  apply H.class_witness_elim KY KP 0 hy my hd hyClass
  intro Δ δ e a ha ma ea
  have hzClass' := hzClass.rename e
  have he' := he.rename e
  simp only [isClass_rename] at hzClass'
  simp only [propertyE_rename,unionPred_rename] at he'
  apply (H.rename e).edge_given_left_elim (KY.rename e) (KP.rename e) t ht
    (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz)
    ha ma (hd.rename e) ea hzClass' he'
  intro Θ θ f x hx mx hp
  have hx' : HasType P Θ x (B.rename (e.comp f).names).xType := by
    simpa only [rename_comp,Embedding.comp] using hx
  have bo : (B.rename e.names).observation = B.observation.rename e.names := rfl
  have hh' := hh Θ θ (e.comp f) x hx' mx (by
    simpa only [QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProofWrapper.rename_comp,bo,LogicSetup.code_rename,rename_comp,LogicCode.rename_comp,
      QuantifierCode.rename_comp,ObservationCode.rename_comp,Expr.rename_comp,Embedding.comp] using hp)
  simpa only [Expr.rename_comp,Embedding.comp] using hh'

theorem edge_witness_elim (t : Bool) {y z D : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) (hd : L.Formula D)
    (he : Proves P Γ γ (B.edge L.code KY.code KP.code t y z))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((L.code.rename e.names).conj
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (y.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) 0 x))
        ((B.rename e.names).relation (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
          (z.rename e.names) ((B.observation.rename e.names).tagged (L.code.rename e.names) (if t then 2 else 1) x))) →
      Proves P Δ δ (D.rename e.names)) : Proves P Γ γ D := by
  rw [edge_eq] at he
  have fy := H.isClass_formula KY KP 0 hy my
  have fz := H.isClass_formula KY KP (if t then 2 else 1) hz mz
  have hu := H.unionPred_typed KY KP hy my hz mz
  have fq := H.parameter_query_formula KY KP (ChannelCode.edgeTag t) hu.1 hu.2
  have hyClass := L.conj_left fy (L.conj_formula fz fq) he
  have he' := L.conj_right fy (L.conj_formula fz fq) he
  have hzClass := L.conj_left fz fq he'
  have hq := L.conj_right fz fq he'
  have hp := (H.edge_query KY KP t hu.1 hu.2).1.prove hq
  exact H.edge_classes_witness_elim KY KP (if t then 2 else 1) (by cases t <;> decide)
    hy my hz mz hd hyClass hzClass hp hh
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem edge_transport (t : Bool) {y z y' z' : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hy' : HasType P Γ y' B.yType) (my' : WellModed γ y' .data)
    (hz' : HasType P Γ z' B.yType) (mz' : WellModed γ z' .data)
    (ey : Proves P Γ γ (B.relation L.code KY.code KP.code y' y))
    (ez : Proves P Γ γ (B.relation L.code KY.code KP.code z' z))
    (he : Proves P Γ γ (B.edge L.code KY.code KP.code t y z)) :
    Proves P Γ γ (B.edge L.code KY.code KP.code t y' z') := by
  apply H.edge_witness_elim KY KP t hy my hz mz (H.edge_formula KY KP t hy' my' hz' mz') he
  intro Δ δ e x hx mx hp
  rw [edge_rename]
  have h0 := (H.rename e).observation.tagged_typed 0 hx mx
  have ht := (H.rename e).observation.tagged_typed (if t then 2 else 1) hx mx
  have f0 := (H.rename e).relation_formula (KY.rename e) (KP.rename e)
    (y_typed_rename (B := B) e hy) (e.moded my) h0.1 h0.2
  have ft := (H.rename e).relation_formula (KY.rename e) (KP.rename e)
    (y_typed_rename (B := B) e hz) (e.moded mz) ht.1 ht.2
  have eyx := (L.rename e).conj_left f0 ft hp
  have ezx := (L.rename e).conj_right f0 ft hp
  have eyE := ey.rename e
  have ezE := ez.rename e
  simp only [relation_rename] at eyE ezE
  exact (H.rename e).edge_witness_intro (KY.rename e) (KP.rename e) t
    (y_typed_rename (B := B) e hy') (e.moded my') (y_typed_rename (B := B) e hz') (e.moded mz') hx mx
    ((H.rename e).relation_trans (KY.rename e) (KP.rename e)
      (y_typed_rename (B := B) e hy') (e.moded my') (y_typed_rename (B := B) e hy) (e.moded my)
      h0.1 h0.2 eyE eyx)
    ((H.rename e).relation_trans (KY.rename e) (KP.rename e)
      (y_typed_rename (B := B) e hz') (e.moded mz') (y_typed_rename (B := B) e hz) (e.moded mz)
      ht.1 ht.2 ezE ezx)

theorem edge_congr (t : Bool) {y z y' z' : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hy' : HasType P Γ y' B.yType) (my' : WellModed γ y' .data)
    (hz' : HasType P Γ z' B.yType) (mz' : WellModed γ z' .data)
    (ey : Proves P Γ γ (B.relation L.code KY.code KP.code y y'))
    (ez : Proves P Γ γ (B.relation L.code KY.code KP.code z z')) :
    Equivalent P Γ γ (B.edge L.code KY.code KP.code t y z) (B.edge L.code KY.code KP.code t y' z') := by
  have f := H.edge_formula KY KP t hy my hz mz
  have f' := H.edge_formula KY KP t hy' my' hz' mz'
  apply L.equivalent_of_iff f f'
  apply L.conj_intro (L.imp_formula f f') (L.imp_formula f' f)
  · apply L.imp_intro_future f f'
    intro Δ δ e he
    simp only [edge_rename] at he ⊢
    have eyE := ey.rename e
    have ezE := ez.rename e
    simp only [relation_rename] at eyE ezE
    exact (H.rename e).edge_transport (KY.rename e) (KP.rename e) t
      (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz)
      (y_typed_rename (B := B) e hy') (e.moded my') (y_typed_rename (B := B) e hz') (e.moded mz')
      ((H.rename e).relation_symm (KY.rename e) (KP.rename e)
        (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hy') (e.moded my') eyE)
      ((H.rename e).relation_symm (KY.rename e) (KP.rename e)
        (y_typed_rename (B := B) e hz) (e.moded mz) (y_typed_rename (B := B) e hz') (e.moded mz') ezE) he
  · apply L.imp_intro_future f' f
    intro Δ δ e he
    simp only [edge_rename] at he ⊢
    have eyE := ey.rename e
    have ezE := ez.rename e
    simp only [relation_rename] at eyE ezE
    exact (H.rename e).edge_transport (KY.rename e) (KP.rename e) t
      (y_typed_rename (B := B) e hy') (e.moded my') (y_typed_rename (B := B) e hz') (e.moded mz')
      (y_typed_rename (B := B) e hy) (e.moded my) (y_typed_rename (B := B) e hz) (e.moded mz) eyE ezE he
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
def formExBody (L : LogicCode S) (KY KP : QuantifierCode S) (p z : Expr S) :=
  B.relational.channel.formExBody L KP B.baseType (B.goodBody L KY KP) (B.queries L KY KP) p z

theorem formExBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (p z y : Expr S) :
    (B.formExBody L KY KP p z).instantiate y = L.conj (B.edge L KY KP false y z) (B.ev p y) := by
  simp only [formExBody,ChannelCode.formExBody_instantiate,edge,ev]
theorem formExBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (p z : Expr S) (ρ : Nat → Nat) :
    (B.formExBody L KY KP p z).rename (Expr.liftRen ρ) =
      (B.rename ρ).formExBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (p.rename ρ) (z.rename ρ) := by
  simp only [formExBody,ChannelCode.formExBody_rename,baseType_rename,goodBody_rename,queries_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename]
end SpecializedCode
namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem formExBody_family {v z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    L.Family B.yType (B.formExBody L.code KY.code KP.code v z) := by
  intro Δ δ e y hy my
  rw [formExBody_rename,formExBody_instantiate]
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    simpa only [yType_rename] using hy
  exact (L.rename e).conj_formula
    ((H.rename e).edge_formula (KY.rename e) (KP.rename e) false hy' my
      (y_typed_rename (B := B) e hz) (e.moded mz))
    ((H.rename e).ev_formula (v_typed_rename (B := B) e hv) (e.moded mv) hy' my)

theorem pairForm_eq (v a z : Expr S) :
    B.pairForm L.code KY.code KP.code v a z =
      L.disj (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code v z))
        (B.edge L.code KY.code KP.code true a z) := by
  simp only [pairForm,ChannelCode.pairForm,H.shape,formExBody,edge ]
  rfl

theorem formEx_intro {v z y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.edge L.code KY.code KP.code false y z))
    (hp : Proves P Γ γ (B.ev v y)) :
    Proves P Γ γ (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code v z)) := by
  apply L.ex_intro KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv hz mz) hy my
  rw [formExBody_instantiate]
  exact L.conj_intro (H.edge_formula KY KP false hy my hz mz) (H.ev_formula hv mv hy my) he hp
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem formEx_congr {v z z' : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hz' : HasType P Γ z' B.yType) (mz' : WellModed γ z' .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code z z')) :
    Equivalent P Γ γ (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code v z))
      (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code v z')) := by
  apply L.ex_equivalent_future KY H.y_sorted H.y_mode
    (H.formExBody_family KY KP hv mv hz mz) (H.formExBody_family KY KP hv mv hz' mz')
  intro Δ δ e y hy my
  simp only [formExBody_rename,formExBody_instantiate]
  have hy' : HasType P Δ y (B.rename e.names).yType := by simpa only [yType_rename] using hy
  have hzE := y_typed_rename (B := B) e hz
  have hzE' := y_typed_rename (B := B) e hz'
  have f := (H.rename e).edge_formula (KY.rename e) (KP.rename e) false hy' my hzE (e.moded mz)
  have f' := (H.rename e).edge_formula (KY.rename e) (KP.rename e) false hy' my hzE' (e.moded mz')
  have g := (H.rename e).ev_formula (v_typed_rename (B := B) e hv) (e.moded mv) hy' my
  have heE := he.rename e
  simp only [relation_rename] at heE
  exact (L.rename e).conj_equivalent f f' g g
    ((H.rename e).edge_congr (KY.rename e) (KP.rename e) false hy' my hzE (e.moded mz) hy' my hzE' (e.moded mz')
      ((H.rename e).relation_refl (KY.rename e) (KP.rename e) hy' my) heE) g.equivalent_refl

theorem pairForm_congr {v a z z' : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hz' : HasType P Γ z' B.yType) (mz' : WellModed γ z' .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code z z')) :
    Equivalent P Γ γ (B.pairForm L.code KY.code KP.code v a z) (B.pairForm L.code KY.code KP.code v a z') := by
  rw [H.pairForm_eq KY KP,H.pairForm_eq KY KP]
  exact L.disj_congr
    (L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv hz mz))
    (L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv hz' mz'))
    (H.edge_formula KY KP true ha ma hz mz) (H.edge_formula KY KP true ha ma hz' mz')
    (H.formEx_congr KY KP hv mv hz mz hz' mz' he)
    (H.edge_congr KY KP true ha ma hz mz ha ma hz' mz' (H.relation_refl KY KP ha ma) he)

theorem pair_evaluation_rounded {v a z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) z)
      (B.pairForm L.code KY.code KP.code v a (B.round z)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pairPred_evaluation KY KP H.base_sorted H.base_mode
    (H.goodBody_family KY KP) (H.queries_family KY KP) (H.relational_formed.probe.raw_sorted H.type_sorted s hs)
    hv mv (H.shape ▸ ha) ma (H.shape ▸ hz) mz

theorem pair_evaluation {v a z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) z)
      (B.pairForm L.code KY.code KP.code v a z) := by
  have hp := H.pair_typed KY KP hv mv ha ma
  have hr := H.round_typed hz mz
  have er := (H.observation_equivalence KY KP hr.1 hr.2 hz mz).2.prove (H.ae_round KY KP hz mz)
  exact (H.ev_formula hp.1 hp.2 hz mz).equivalent_trans
    (H.pairForm_formula KY KP hv mv ha ma hr.1 hr.2) (H.pairForm_formula KY KP hv mv ha ma hz mz)
    (H.pair_evaluation_rounded KY KP hv mv ha ma hz mz) (H.pairForm_congr KY KP hv mv ha ma hr.1 hr.2 hz mz er)
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem comparison_intro {v c : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y (B.rename e.names).yType → WellModed δ y .data →
      Equivalent P Δ δ ((B.rename e.names).ev (v.rename e.names) y) ((B.rename e.names).ev (c.rename e.names) y)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c) := by
  apply H.relational_formed.channel.predCompare_intro H.base_sorted H.base_mode KY hv mv hc mc
  intro Δ δ e y hy my
  have hhshape : (B.rename e.names).yType = (B.relational.channel.rename e.names).logicalType (B.baseType.rename e.names) := by
    rw [← ChannelCode.logicalType_rename,← H.shape,yType_rename]
  simpa only [ev,baseType_rename, SpecializedCode.rename,relational,ObservationCode.rename,
    RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hh Δ δ e y (hhshape.symm ▸ hy) my

theorem formEx_pred_congr {v c z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c)) :
    Equivalent P Γ γ (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code v z))
      (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code c z)) := by
  apply L.ex_equivalent_future KY H.y_sorted H.y_mode
    (H.formExBody_family KY KP hv mv hz mz) (H.formExBody_family KY KP hc mc hz mz)
  intro Δ δ e y hy my
  simp only [formExBody_rename,formExBody_instantiate]
  have hy' : HasType P Δ y (B.rename e.names).yType := by simpa only [yType_rename] using hy
  have hzE := y_typed_rename (B := B) e hz
  have f := (H.rename e).edge_formula (KY.rename e) (KP.rename e) false hy' my hzE (e.moded mz)
  have gv := (H.rename e).ev_formula (v_typed_rename (B := B) e hv) (e.moded mv) hy' my
  have gc := (H.rename e).ev_formula (v_typed_rename (B := B) e hc) (e.moded mc) hy' my
  exact (L.rename e).conj_equivalent f f gv gc f.equivalent_refl
    ((H.rename e).ev_compare (KY.rename e) (v_typed_rename (B := B) e hv) (e.moded mv)
      (v_typed_rename (B := B) e hc) (e.moded mc) hy' my (comparison_rename KY e he))

theorem pairForm_input_congr {v c a b z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (ep : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c))
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Equivalent P Γ γ (B.pairForm L.code KY.code KP.code v a z) (B.pairForm L.code KY.code KP.code c b z) := by
  rw [H.pairForm_eq KY KP,H.pairForm_eq KY KP]
  exact L.disj_congr
    (L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv hz mz))
    (L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hc mc hz mz))
    (H.edge_formula KY KP true ha ma hz mz) (H.edge_formula KY KP true hb mb hz mz)
    (H.formEx_pred_congr KY KP hv mv hc mc hz mz ep)
    (H.edge_congr KY KP true ha ma hz mz hb mb hz mz ea (H.relation_refl KY KP hz mz))

theorem pair_input_evaluation_congr {v c a b z : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (ep : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c))
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) z) (B.ev (B.pair L.code KY.code KP.code c b) z) := by
  have hp := H.pair_typed KY KP hv mv ha ma
  have hq := H.pair_typed KY KP hc mc hb mb
  have fp := H.ev_formula hp.1 hp.2 hz mz
  have fq := H.ev_formula hq.1 hq.2 hz mz
  have gp := H.pairForm_formula KY KP hv mv ha ma hz mz
  have gq := H.pairForm_formula KY KP hc mc hb mb hz mz
  exact fp.equivalent_trans gq fq (fp.equivalent_trans gp gq
    (H.pair_evaluation KY KP hv mv ha ma hz mz) (H.pairForm_input_congr KY KP hv mv hc mc ha ma hb mb hz mz ep ea))
    (H.pair_evaluation KY KP hc mc hb mb hz mz).symm

theorem pair_comparison {v c a b : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.predType) (mc : WellModed γ c .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (ep : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType v c))
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType
      (B.pair L.code KY.code KP.code v a) (B.pair L.code KY.code KP.code c b)) := by
  have hp := H.pair_typed KY KP hv mv ha ma
  have hq := H.pair_typed KY KP hc mc hb mb
  apply H.comparison_intro KY hp.1 hp.2 hq.1 hq.2
  intro Δ δ e z hz mz
  simp only [pair_rename]
  have eaE := ea.rename e
  simp only [relation_rename] at eaE
  exact (H.rename e).pair_input_evaluation_congr (KY.rename e) (KP.rename e)
    (v_typed_rename (B := B) e hv) (e.moded mv) (v_typed_rename (B := B) e hc) (e.moded mc)
    (y_typed_rename (B := B) e ha) (e.moded ma) (y_typed_rename (B := B) e hb) (e.moded mb) hz mz
    (comparison_rename KY e ep) eaE
end SpecializedCode.Formed
end PureTypeSystem.Labelled

end OAI
