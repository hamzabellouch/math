import OAI.Computability.TypeSystem.Equivalence

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode
variable (R : RelationalCode S)
theorem recoverLift_convertA (L : LogicCode S) (KY KP : QuantifierCode S)
    {A B : Expr S} (i w : Expr S) (h : Converts A B) :
    Converts (R.recoverLift L KY KP A i w) (R.recoverLift L KY KP B i w) := by
  let body := (R.rename Nat.succ).recoverLift (L.rename Nat.succ) (KY.rename Nat.succ)
    (KP.rename Nat.succ) (.var 0) (i.rename Nat.succ) (w.rename Nat.succ)
  have hh := h.instantiate_right body
  simpa only [body,Expr.instantiate,recoverLift_subst,instantiate_raise,
    LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single] using hh

theorem probeFor_body_specialize (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) :
    (((R.rename Nat.succ).recoverLiftBody (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
      ((R.probe.lifting.rename Nat.succ).project (.var 0)) (i.rename Nat.succ)).subst
      (Expr.liftSub (Expr.single (R.probe.lifting.inject A)))) =
    R.recoverLiftBody L KY KP (R.probe.lifting.project (R.probe.lifting.inject A)) i := by
  simp only [recoverLiftBody_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,PositiveDataWrapper.project_subst,
    PositiveDataWrapper.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
/-- Uniform-probe evaluation before access recovery. No non-dummy assumption is
needed for the uniform lambda's beta and wrapper cancellations. -/
theorem probeFor_evaluation {A i w : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hw : HasType P Γ w (R.probe.singleType A)) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (R.probe.observe A (R.probeFor L.code KY.code KP.code i) w)
      (R.recoverLift L.code KY.code KP.code A i w) := by
  let A' := R.probe.lifting.project (R.probe.lifting.inject A)
  have hA' : HasType P Γ A' (.sort R.probe.seed) := H.probe.project_typed ((H.probe.lifting.typed H.probe.seed_sorted).1 _ hA)
  have mA' : WellModed γ A' .data := H.probe.project_mode (H.probe.lifting.modes.2.1 _ mA)
  have hc : Converts A' A := (R.probe.lifting.cancel A).converts
  have hv := H.probeFor_typed KY KP hi mi
  have hQ := H.recoverLiftBody_family KY KP hA' mA' hi mi
  have ha := H.probe.uniform_evaluation hA mA hv.1 hv.2
    (by simpa only [probeFor_body_specialize] using hQ) hw mw
  have ha' : Equivalent P Γ γ (R.probe.observe A (R.probeFor L.code KY.code KP.code i) w)
      (R.recoverLift L.code KY.code KP.code A' i w) := by
    simpa only [probeFor, A', probeFor_body_specialize,recoverLiftBody_instantiate] using ha
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  have hw' : HasType P Γ w (R.probe.singleType A') :=
    hw.conversion (H.probe.single_sorted hA' s hs) (.symm _ _ (R.probe.singleType_converts hc))
  have hf := H.recoverLift_formula KY KP hA mA hi mi hw mw
  have hf' := H.recoverLift_formula KY KP hA' mA' hi mi hw' mw
  have ho := H.probe.observe_formula hA mA hv.1 hv.2 hw mw
  obtain ⟨t,ht⟩ := L.triple.codomain.1
  exact ha'.trans (Equivalent.of_conversion (hf'.1 t ht) (hf.1 t ht)
    (R.recoverLift_convertA L.code KY.code KP.code i w hc))
    (ho.1 t ht) (hf'.1 t ht) (hf.1 t ht)

/-- The source rounded probe law. The assumption is the explicit non-dummy
conjunct of Adm; all other equalities are typed cancellation proofs. -/
theorem probeFor_rounded {A m i y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data)
    (hnd : Proves P Γ γ (L.neg (R.probe.doubled.isDummy L.code (R.probe.rawType A) m))) :
    Equivalent P Γ γ (R.diamond L.code A m (R.probeFor L.code KY.code KP.code i) y)
      (R.channel.eval R.probe.carrier i (R.lift L.code KY.code KP.code A m
        (R.channel.round (R.baseType A) y))) := by
  have hw := H.bundle_typed hA mA hm mm hy my
  have hu := H.probeFor_evaluation KY KP hA mA hi mi hw.1 hw.2
  have hmap := H.predLiftMap_typed KY KP hA mA hi mi
  have h₀ := H.rawTop_typed hA mA
  have hc := H.channel.toRaw_typed (H.base_sorted hA) (H.base_mode mA) hy my
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.probe.mainTriple.product.1
  have har := H.probe.doubled_formed.access_recovery H.channel.predicate
    H.probe.funTriple.domain.1 KP.triple.domain.1 (H.probe.raw_sorted hA) (H.probe.raw_mode mA)
    hmap hm mm h₀.1 h₀.2 hc.1 hc.2 (H.probe.raw_sorted hA s hs)
    (H.probe.doubled_formed.bp_sorted (H.probe.raw_sorted hA) r hr) hnd
  have har' : Equivalent P Γ γ
      (R.recoverLift L.code KY.code KP.code A i (R.bundle L.code A m y))
      (R.channel.eval (R.baseType A) (R.predLift L.code KY.code KP.code A m i) y) := by
    simpa only [recoverLift,bundle,point,predLiftMap_instantiate,ChannelCode.eval,
      RelationalCode.channel,ProbeCode.rawType,ProbeCode.paramType,ChannelCode.rawType,baseType] using har
  have hp := H.channel.pred_evaluation (H.base_sorted hA) (H.base_mode mA)
    (H.liftEvalBody_family KY KP hA mA hm mm hi mi) (H.probe.raw_sorted hA s hs) hy my
  have hp' : Equivalent P Γ γ
      (R.channel.eval (R.baseType A) (R.predLift L.code KY.code KP.code A m i) y)
      (R.channel.eval R.probe.carrier i (R.lift L.code KY.code KP.code A m (R.channel.round (R.baseType A) y))) := by
    simpa only [predLift,liftEvalBody_instantiate] using hp
  have hv := H.probeFor_typed KY KP hi mi
  have f₁ := H.diamond_formula hA mA hm mm hv.1 hv.2 hy my
  have f₂ := H.recoverLift_formula KY KP hA mA hi mi hw.1 hw.2
  have hpred := H.predLift_typed KY KP hA mA hm mm hi mi
  have f₃ := H.channel.eval_formula (H.base_sorted hA) (H.base_mode mA) hpred.1 hpred.2 hy my
  have hyr := H.channel.round_typed (H.base_sorted hA) (H.base_mode mA) hy my
  have hl := H.lift_typed KY KP hA mA hm mm hyr.1 hyr.2
  have f₄ := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hl.1 hl.2
  obtain ⟨t,ht⟩ := L.triple.codomain.1
  exact (hu.trans har' (f₁.1 t ht) (f₂.1 t ht) (f₃.1 t ht)).trans hp'
    (f₁.1 t ht) (f₃.1 t ht) (f₄.1 t ht)
end Formed
end RelationalCode

namespace SpecializedCode
variable (B : SpecializedCode S)
def diamond (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  B.relational.diamond L B.type (B.parameter L KY KP) v y
def part (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.part L B.type (B.parameter L KY KP) v
def sb (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  B.relational.sb L KY KP B.type (B.parameter L KY KP) v y
def lift (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) :=
  B.relational.lift L KY KP B.type (B.parameter L KY KP) y

theorem diamond_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.diamond L KY KP v y).rename ρ = (B.rename ρ).diamond (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [diamond,RelationalCode.diamond_rename,parameter_rename,relational_rename]
  rfl
theorem part_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.part L KY KP v).rename ρ = (B.rename ρ).part (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [part,RelationalCode.part_rename,parameter_rename,relational_rename]
  rfl
theorem sb_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.sb L KY KP v y).rename ρ = (B.rename ρ).sb (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [sb,RelationalCode.sb_rename,parameter_rename,relational_rename]
  rfl
theorem lift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (ρ : Nat → Nat) :
    (B.lift L KY KP y).rename ρ = (B.rename ρ).lift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) := by
  simp only [lift,RelationalCode.lift_rename,parameter_rename,relational_rename]
  rfl
end SpecializedCode
namespace SpecializedCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem carrier_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) :
    HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
  simpa only [ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hv

omit H in
theorem xPred_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.xPredType) : HasType P Δ (v.rename e.names) (B.rename e.names).xPredType := by
  simpa only [xPredType_rename] using e.typing hv

theorem part_typed {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    HasType P Γ (B.part L.code KY.code KP.code v) B.predType ∧ WellModed γ (B.part L.code KY.code KP.code v) .data :=
  H.relational_formed.part_typed H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 hv mv

theorem diamond_formula {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    L.Formula (B.diamond L.code KY.code KP.code v y) :=
  H.relational_formed.diamond_formula H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 hv mv (H.shape ▸ hy) my

theorem part_evaluation {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.ev (B.part L.code KY.code KP.code v) y) (B.diamond L.code KY.code KP.code v (B.round y)) :=
  H.relational_formed.part_evaluation H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 hv mv (H.shape ▸ hy) my

theorem lift_typed {y : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    HasType P Γ (B.lift L.code KY.code KP.code y) B.xType ∧ WellModed γ (B.lift L.code KY.code KP.code y) .data :=
  H.relational_formed.lift_typed KY KP H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 (H.shape ▸ hy) my

theorem sb_formula {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    L.Formula (B.sb L.code KY.code KP.code v y) :=
  H.relational_formed.sb_formula KY KP H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 hv mv (H.shape ▸ hy) my

theorem lift_primitive_evaluation {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.relational.logical.observe B.relational.probe.carrier (B.lift L.code KY.code KP.code y) v)
      (B.sb L.code KY.code KP.code v y) :=
  H.relational_formed.lift_evaluation KY KP H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 (H.shape ▸ hy) my hv mv

theorem lift_evaluation {i y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.lift L.code KY.code KP.code y))
      (B.sb L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y) :=
  H.lift_primitive_evaluation KY KP (H.relational_formed.probeFor_typed KY KP hi mi).1
    (H.relational_formed.probeFor_typed KY KP hi mi).2 hy my

theorem probe_rounded {i y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.diamond L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y)
      (B.relational.channel.eval B.relational.probe.carrier i (B.lift L.code KY.code KP.code (B.round y))) :=
  H.relational_formed.probeFor_rounded KY KP H.type_sorted H.type_mode (H.parameter_typed KY KP).1
    (H.parameter_typed KY KP).2 hi mi (H.shape ▸ hy) my (H.parameter_not_dummy KY KP)
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem goodBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.goodBody L KY KP).subst (Expr.liftSub σ) = (B.subst σ).goodBody (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [goodBody,RelationalCode.goodBody_subst,parameter_subst,
    SpecializedCode.subst,relational,ObservationCode.subst]
theorem relation_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (B.relation L KY KP y z).subst σ = (B.subst σ).relation (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [relation,ChannelCode.relation_subst,baseType_subst,goodBody_subst,
    SpecializedCode.subst,relational,ObservationCode.subst,RelationalCode.subst,RelationalCode.channel,ChannelCode.subst,ProbeCode.subst]

theorem relational_subst (σ : Nat → Expr S) : B.relational.subst σ = (B.subst σ).relational := rfl
theorem diamond_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.diamond L KY KP v y).subst σ = (B.subst σ).diamond (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [diamond,RelationalCode.diamond_subst,parameter_subst,relational_subst]
  rfl
def respStep (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :=
  L.imp (B.relation L KY KP y z) (L.iff (B.diamond L KY KP v y) (B.diamond L KY KP v z))
def respAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  (B.rename Nat.succ).respStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (y.rename Nat.succ) (.var 0)
def respAt (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :=
  KY.all B.yType (B.respAtBody L KY KP v y)
def respBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).respAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def response (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  KY.all B.yType (B.respBody L KY KP v)
theorem respStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (ρ : Nat → Nat) :
    (B.respStep L KY KP v y z).rename ρ = (B.rename ρ).respStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [respStep,LogicCode.imp_rename,LogicCode.iff_rename,relation_rename,diamond_rename]
theorem respStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (σ : Nat → Expr S) :
    (B.respStep L KY KP v y z).subst σ = (B.subst σ).respStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [respStep,LogicCode.imp_subst,LogicCode.iff_subst,relation_subst,diamond_subst]
theorem respAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.respAtBody L KY KP v y).rename (Expr.liftRen ρ) = (B.rename ρ).respAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [respAtBody,respStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem respAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.respAtBody L KY KP v y).subst (Expr.liftSub σ) = (B.subst σ).respAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [respAtBody,respStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem respAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :
    (B.respAtBody L KY KP v y).instantiate z = B.respStep L KY KP v y z := by
  simp only [respAtBody,Expr.instantiate,respStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem respAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.respAt L KY KP v y).rename ρ = (B.rename ρ).respAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [respAt,QuantifierCode.all_rename,yType_rename,respAtBody_rename]
theorem respAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.respAt L KY KP v y).subst σ = (B.subst σ).respAt (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [respAt,QuantifierCode.all_subst,yType_subst,respAtBody_subst]
theorem respBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.respBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).respBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [respBody,respAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem respBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.respBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).respBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [respBody,respAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem respBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :
    (B.respBody L KY KP v).instantiate y = B.respAt L KY KP v y := by
  simp only [respBody,Expr.instantiate,respAt_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem response_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.response L KY KP v).rename ρ = (B.rename ρ).response (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [response,QuantifierCode.all_rename,yType_rename,respBody_rename]
theorem response_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.response L KY KP v).subst σ = (B.subst σ).response (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [response,QuantifierCode.all_subst,yType_subst,respBody_subst]
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem respStep_formula {v y z : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    : L.Formula (B.respStep L.code KY.code KP.code v y z) := 
  L.imp_formula (H.relation_formula KY KP hy my hz mz) (L.iff_formula (H.diamond_formula KY KP hv mv hy my) (H.diamond_formula KY KP hv mv hz mz))

theorem respAtBody_family {v y : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    : L.Family B.yType (B.respAtBody L.code KY.code KP.code v y) := by
  intro Δ δ e z hz mz
  rw [respAtBody_rename,respAtBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
    exact carrier_typed_rename e hv
  have hy' : HasType P Δ (y.rename e.names) (B.rename e.names).yType := by
    simpa only [yType_rename] using e.typing hy
  have hz' : HasType P Δ z (B.rename e.names).yType := by
    simpa only [yType_rename] using hz
  exact (H.rename e).respStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' (e.moded my) hz' mz

theorem respAt_formula {v y : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    : L.Formula (B.respAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respAtBody_family KY KP hv mv hy my)

theorem respBody_family {v : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    : L.Family B.yType (B.respBody L.code KY.code KP.code v) := by
  intro Δ δ e y hy my
  rw [respBody_rename,respBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
    exact carrier_typed_rename e hv
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    simpa only [yType_rename] using hy
  exact (H.rename e).respAt_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' my

theorem response_formula {v : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    : L.Formula (B.response L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respBody_family KY KP hv mv)

end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem respAt_intro {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) z,
      HasType P Δ z (B.rename e.names).yType → WellModed δ z .data →
      Proves P Δ δ ((B.rename e.names).respStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) (y.rename e.names) z)) : Proves P Γ γ (B.respAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respAtBody_family KY KP hv mv hy my)
  intro Δ δ e z hz mz
  rw [respAtBody_rename,respAtBody_instantiate]
  exact hh Δ δ e z (by simpa only [yType_rename] using hz) mz

theorem respAt_elim {v y z : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hp : Proves P Γ γ (B.respAt L.code KY.code KP.code v y)) :
    Proves P Γ γ (B.respStep L.code KY.code KP.code v y z) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respAtBody_family KY KP hv mv hy my) hz mz hp
  simpa only [respAtBody_instantiate] using hh

theorem response_intro {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y (B.rename e.names).yType → WellModed δ y .data →
      Proves P Δ δ ((B.rename e.names).respAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) y)) : Proves P Γ γ (B.response L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respBody_family KY KP hv mv)
  intro Δ δ e y hy my
  rw [respBody_rename,respBody_instantiate]
  exact hh Δ δ e y (by simpa only [yType_rename] using hy) my

theorem response_elim_one {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.respAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respBody_family KY KP hv mv) hy my hp
  simpa only [respBody_instantiate] using hh

theorem response_elim {v y z : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hp : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.diamond L.code KY.code KP.code v y) (B.diamond L.code KY.code KP.code v z) := by
  have hh := H.respAt_elim KY KP hv mv hy my hz mz (H.response_elim_one KY KP hv mv hy my hp)
  have hc := L.imp_elim (H.relation_formula KY KP hy my hz mz)
    (L.iff_formula (H.diamond_formula KY KP hv mv hy my) (H.diamond_formula KY KP hv mv hz mz)) hh he
  exact L.equivalent_of_iff (H.diamond_formula KY KP hv mv hy my) (H.diamond_formula KY KP hv mv hz mz) hc

end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
def responsePredStep (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :=
  B.diamond L KY KP v (B.observation.tagged L 0 x)
def responsePredBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).responsePredStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def responsePred (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.responsePredBody L KY KP v)
theorem responsePredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.responsePredStep L KY KP v x).rename ρ = (B.rename ρ).responsePredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [responsePredStep,diamond_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem responsePredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.responsePredStep L KY KP v x).subst σ = (B.subst σ).responsePredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [responsePredStep,diamond_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem responsePredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.responsePredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).responsePredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [responsePredBody,responsePredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem responsePredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.responsePredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).responsePredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [responsePredBody,responsePredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem responsePredBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.responsePredBody L KY KP v).instantiate x = B.responsePredStep L KY KP v x := by
  simp only [responsePredBody,Expr.instantiate,responsePredStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem responsePred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.responsePred L KY KP v).rename ρ = (B.rename ρ).responsePred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [responsePred,ChannelCode.pred_rename,ProbeCode.carrier_rename,responsePredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem responsePred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.responsePred L KY KP v).subst σ = (B.subst σ).responsePred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [responsePred,ChannelCode.pred_subst,ProbeCode.carrier_subst,responsePredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responsePredStep_formula {v x : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.responsePredStep L.code KY.code KP.code v x) := by
  have ht := H.tagged_typed 0 hx mx
  exact H.diamond_formula KY KP hv mv ht.1 ht.2

theorem responsePredBody_family {v : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    : L.Family B.xType (B.responsePredBody L.code KY.code KP.code v) := by
  intro Δ δ e x hx mx
  rw [responsePredBody_rename,responsePredBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
    exact carrier_typed_rename e hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).responsePredStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' mx

theorem responsePred_typed {v : Expr S} (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    HasType P Γ (B.responsePred L.code KY.code KP.code v) B.xPredType ∧ WellModed γ (B.responsePred L.code KY.code KP.code v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.responsePredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs)

theorem responsePred_evaluation {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) x)
      (B.responsePredStep L.code KY.code KP.code v (B.relational.channel.round B.relational.probe.carrier x)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.responsePredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs) hx mx
  simpa only [responsePredBody_instantiate,responsePred] using he

end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem comparison_refl {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Proves P Γ γ (B.predCompare L.code KY.code v v) := by
  apply H.comparison_intro KY hv mv hv mv
  intro Δ δ e y hy my
  exact ((H.rename e).ev_formula (v_typed_rename (B := B) e hv) (e.moded mv) hy my).equivalent_refl

theorem sb_equivalent {v w a b : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hw : HasType P Γ w B.relational.probe.carrier) (mw : WellModed γ w .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (ep : Proves P Γ γ (B.predCompare L.code KY.code (B.part L.code KY.code KP.code v) (B.part L.code KY.code KP.code w)))
    (ea : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Equivalent P Γ γ (B.sb L.code KY.code KP.code v a) (B.sb L.code KY.code KP.code w b) := by
  have hp := H.part_typed KY KP hv mv
  have hq := H.part_typed KY KP hw mw
  have pp := H.pair_typed KY KP hp.1 hp.2 ha ma
  have pq := H.pair_typed KY KP hq.1 hq.2 hb mb
  exact H.query_equivalent KY KP 6 pp.1 pp.2 pq.1 pq.2 (H.pair_comparison KY KP hp.1 hp.2 hq.1 hq.2 ha ma hb mb ep ea)

theorem le_lift_congr {i a b : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.lift L.code KY.code KP.code a))
      (B.relational.le L.code KY.code KP.code i (B.lift L.code KY.code KP.code b)) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have hp := H.part_typed KY KP hz.1 hz.2
  have la := H.lift_typed KY KP ha ma
  have lb := H.lift_typed KY KP hb mb
  have fa := H.relational_formed.le_formula KY KP hi mi la.1 la.2
  have fb := H.relational_formed.le_formula KY KP hi mi lb.1 lb.2
  have ga := H.sb_formula KY KP hz.1 hz.2 ha ma
  have gb := H.sb_formula KY KP hz.1 hz.2 hb mb
  exact fa.equivalent_trans gb fb (fa.equivalent_trans ga gb (H.lift_evaluation KY KP hi mi ha ma)
    (H.sb_equivalent KY KP hz.1 hz.2 hz.1 hz.2 ha ma hb mb (H.comparison_refl KY hp.1 hp.2) he))
    (H.lift_evaluation KY KP hi mi hb mb).symm

theorem lift_congr {a b : Expr S}
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hb : HasType P Γ b B.yType) (mb : WellModed γ b .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code a b)) :
    Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code (B.lift L.code KY.code KP.code a) (B.lift L.code KY.code KP.code b)) := by
  have la := H.lift_typed KY KP ha ma
  have lb := H.lift_typed KY KP hb mb
  apply H.relational_formed.xCompare_intro KY KP la.1 la.2 lb.1 lb.2
  intro Δ δ e i hi mi
  rw [lift_rename,lift_rename]
  have he' := he.rename e
  simp only [relation_rename] at he'
  exact (H.rename e).le_lift_congr (KY.rename e) (KP.rename e) hi mi
    (y_typed_rename (B := B) e ha) (e.moded ma) (y_typed_rename (B := B) e hb) (e.moded mb) he'
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem part_probe_eval_compare {i c y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier i c)) :
    Equivalent P Γ γ (B.ev (B.part L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i)) y)
      (B.ev (B.part L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code c)) y) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have hz' := H.relational_formed.probeFor_typed KY KP hc mc
  have hp := H.part_typed KY KP hz.1 hz.2
  have hp' := H.part_typed KY KP hz'.1 hz'.2
  have hr := H.round_typed hy my
  have hrr := H.round_typed hr.1 hr.2
  have hl := H.lift_typed KY KP hrr.1 hrr.2
  have e1 := H.part_evaluation KY KP hz.1 hz.2 hy my
  have e2 := H.probe_rounded KY KP hi mi hr.1 hr.2
  have e3 := H.relational_formed.channel.predCompare_elim H.relational_formed.probe.carrier_sorted
    H.relational_formed.probe.carrier_mode KY hi mi hc mc hl.1 hl.2 he
  have e4 := H.probe_rounded KY KP hc mc hr.1 hr.2
  have e5 := H.part_evaluation KY KP hz'.1 hz'.2 hy my
  have f1 := H.ev_formula hp.1 hp.2 hy my
  have f2 := H.diamond_formula KY KP hz.1 hz.2 hr.1 hr.2
  have f3 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hl.1 hl.2
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hc mc hl.1 hl.2
  have f5 := H.diamond_formula KY KP hz'.1 hz'.2 hr.1 hr.2
  have f6 := H.ev_formula hp'.1 hp'.2 hy my
  exact f1.equivalent_trans f5 f6 (f1.equivalent_trans f4 f5 (f1.equivalent_trans f3 f4
    (f1.equivalent_trans f2 f3 e1 e2) e3) e4.symm) e5.symm

theorem part_probe_compare {i c : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier i c)) :
    Proves P Γ γ (B.predCompare L.code KY.code (B.part L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i))
      (B.part L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code c))) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have hz' := H.relational_formed.probeFor_typed KY KP hc mc
  have hp := H.part_typed KY KP hz.1 hz.2
  have hp' := H.part_typed KY KP hz'.1 hz'.2
  apply H.comparison_intro KY hp.1 hp.2 hp'.1 hp'.2
  intro Δ δ e y hy my
  simp only [part_rename,RelationalCode.probeFor_rename,relational_rename]
  have he' := he.rename e
  simp only [ChannelCode.predCompare_rename,ProbeCode.carrier_rename] at he'
  exact (H.rename e).part_probe_eval_compare (KY.rename e) (KP.rename e)
    (xPred_typed_rename e hi) (e.moded mi) (xPred_typed_rename e hc) (e.moded mc) hy my he'

theorem lift_le_pred_congr {i c a : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier i c)) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.lift L.code KY.code KP.code a))
      (B.relational.le L.code KY.code KP.code c (B.lift L.code KY.code KP.code a)) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have hz' := H.relational_formed.probeFor_typed KY KP hc mc
  have la := H.lift_typed KY KP ha ma
  have fa := H.relational_formed.le_formula KY KP hi mi la.1 la.2
  have fb := H.relational_formed.le_formula KY KP hc mc la.1 la.2
  have ga := H.sb_formula KY KP hz.1 hz.2 ha ma
  have gb := H.sb_formula KY KP hz'.1 hz'.2 ha ma
  exact fa.equivalent_trans gb fb (fa.equivalent_trans ga gb (H.lift_evaluation KY KP hi mi ha ma)
    (H.sb_equivalent KY KP hz.1 hz.2 hz'.1 hz'.2 ha ma ha ma (H.part_probe_compare KY KP hi mi hc mc he) (H.relation_refl KY KP ha ma)))
    (H.lift_evaluation KY KP hc mc ha ma).symm

theorem lift_validStep {i c a : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data) :
    Proves P Γ γ (B.relational.validStep L.code KY.code KP.code (B.lift L.code KY.code KP.code a) i c) := by
  have la := H.lift_typed KY KP ha ma
  apply L.imp_intro_future
    (H.relational_formed.channel.predCompare_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY hi mi hc mc)
    (L.iff_formula (H.relational_formed.le_formula KY KP hi mi la.1 la.2) (H.relational_formed.le_formula KY KP hc mc la.1 la.2))
  intro Δ δ e he
  simp only [ChannelCode.predCompare_rename,ProbeCode.carrier_rename] at he
  simp only [LogicSetup.iff_rename,RelationalCode.le_rename,lift_rename,relational_rename]
  have hi' := xPred_typed_rename e hi
  have hc' := xPred_typed_rename e hc
  have ha' := y_typed_rename (B := B) e ha
  have la' := (H.rename e).lift_typed (KY.rename e) (KP.rename e) ha' (e.moded ma)
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).relational_formed.le_formula (KY.rename e) (KP.rename e) hi' (e.moded mi) la'.1 la'.2)
    ((H.rename e).relational_formed.le_formula (KY.rename e) (KP.rename e) hc' (e.moded mc) la'.1 la'.2)
    ((H.rename e).lift_le_pred_congr (KY.rename e) (KP.rename e) hi' (e.moded mi) hc' (e.moded mc) ha' (e.moded ma) he)

theorem lift_validAt {i a : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data) :
    Proves P Γ γ (B.relational.validAt L.code KY.code KP.code (B.lift L.code KY.code KP.code a) i) := by
  have la := H.lift_typed KY KP ha ma
  apply H.relational_formed.validAt_intro KY KP la.1 la.2 hi mi
  intro Δ δ e c hc mc
  rw [lift_rename]
  exact (H.rename e).lift_validStep (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) hc mc
    (y_typed_rename (B := B) e ha) (e.moded ma)

theorem lift_valid {a : Expr S}
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data) :
    Proves P Γ γ (B.relational.valid L.code KY.code KP.code (B.lift L.code KY.code KP.code a)) := by
  have la := H.lift_typed KY KP ha ma
  apply H.relational_formed.valid_intro KY KP la.1 la.2
  intro Δ δ e i hi mi
  rw [lift_rename]
  exact (H.rename e).lift_validAt (KY.rename e) (KP.rename e) hi mi (y_typed_rename (B := B) e ha) (e.moded ma)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem round_relation {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Proves P Γ γ (B.relation L.code KY.code KP.code (B.round y) y) := by
  have hr := H.round_typed hy my
  exact H.relation_backward KY KP hr.1 hr.2 hy my (H.ae_round KY KP hy my)

theorem part_exact {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.ev (B.part L.code KY.code KP.code v) y) (B.diamond L.code KY.code KP.code v y) := by
  have hr := H.round_typed hy my
  have hpart := H.part_typed KY KP hv mv
  exact (H.ev_formula hpart.1 hpart.2 hy my).equivalent_trans
    (H.diamond_formula KY KP hv mv hr.1 hr.2) (H.diamond_formula KY KP hv mv hy my)
    (H.part_evaluation KY KP hv mv hy my) (H.response_elim KY KP hv mv hr.1 hr.2 hy my hp (H.round_relation KY KP hy my))

theorem probe_exact {i y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ (B.diamond L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y)
      (B.relational.channel.eval B.relational.probe.carrier i (B.lift L.code KY.code KP.code y)) := by
  have hr := H.round_typed hy my
  have hlr := H.lift_typed KY KP hr.1 hr.2
  have hl := H.lift_typed KY KP hy my
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have ee := H.relational_formed.extensional_elim KY KP hi mi hlr.1 hlr.2 hl.1 hl.2 hex
    (H.lift_congr KY KP hr.1 hr.2 hy my (H.round_relation KY KP hy my))
  have fr := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hlr.1 hlr.2
  have fy := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hl.1 hl.2
  exact (H.diamond_formula KY KP hz.1 hz.2 hy my).equivalent_trans fr fy (H.probe_rounded KY KP hi mi hy my) ee

theorem probe_respStep {i y z : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.respStep L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y z) := by
  have hp := H.relational_formed.probeFor_typed KY KP hi mi
  apply L.imp_intro_future (H.relation_formula KY KP hy my hz mz)
    (L.iff_formula (H.diamond_formula KY KP hp.1 hp.2 hy my) (H.diamond_formula KY KP hp.1 hp.2 hz mz))
  intro Δ δ e he
  simp only [relation_rename] at he
  simp only [LogicSetup.iff_rename,diamond_rename,RelationalCode.probeFor_rename,relational_rename]
  have hi' := xPred_typed_rename e hi
  have hy' := y_typed_rename (B := B) e hy
  have hz' := y_typed_rename (B := B) e hz
  have hex' := hex.rename e
  simp only [RelationalCode.extensional_rename] at hex'
  have ly := (H.rename e).lift_typed (KY.rename e) (KP.rename e) hy' (e.moded my)
  have lz := (H.rename e).lift_typed (KY.rename e) (KP.rename e) hz' (e.moded mz)
  have pr := (H.rename e).relational_formed.probeFor_typed (KY.rename e) (KP.rename e) hi' (e.moded mi)
  have e1 := (H.rename e).probe_exact (KY.rename e) (KP.rename e) hi' (e.moded mi) hy' (e.moded my) hex'
  have e3 := (H.rename e).probe_exact (KY.rename e) (KP.rename e) hi' (e.moded mi) hz' (e.moded mz) hex'
  have e2 := (H.rename e).relational_formed.extensional_elim (KY.rename e) (KP.rename e) hi' (e.moded mi) ly.1 ly.2 lz.1 lz.2 hex'
    ((H.rename e).lift_congr (KY.rename e) (KP.rename e) hy' (e.moded my) hz' (e.moded mz) he)
  have f1 := (H.rename e).diamond_formula (KY.rename e) (KP.rename e) pr.1 pr.2 hy' (e.moded my)
  have f4 := (H.rename e).diamond_formula (KY.rename e) (KP.rename e) pr.1 pr.2 hz' (e.moded mz)
  have f2 := (H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode hi' (e.moded mi) ly.1 ly.2
  have f3 := (H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode hi' (e.moded mi) lz.1 lz.2
  exact (L.rename e).iff_of_equivalent f1 f4 (f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 e1 e2) e3.symm)

theorem probe_respAt {i y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.respAt L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y) := by
  have hp := H.relational_formed.probeFor_typed KY KP hi mi
  apply H.respAt_intro KY KP hp.1 hp.2 hy my
  intro Δ δ e z hz mz
  simp only [RelationalCode.probeFor_rename]
  have hex' := hex.rename e
  simp only [RelationalCode.extensional_rename] at hex'
  exact (H.rename e).probe_respStep (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
    (y_typed_rename (B := B) e hy) (e.moded my) hz mz hex'

theorem probe_response {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.response L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i)) := by
  have hp := H.relational_formed.probeFor_typed KY KP hi mi
  apply H.response_intro KY KP hp.1 hp.2
  intro Δ δ e y hy my
  simp only [RelationalCode.probeFor_rename]
  have hex' := hex.rename e
  simp only [RelationalCode.extensional_rename] at hex'
  exact (H.rename e).probe_respAt (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) hy my hex'
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responsePred_exact {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) x)
      (B.diamond L.code KY.code KP.code v (B.observation.tagged L.code 0 x)) := by
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have tx := H.tagged_typed 0 hx mx
  have tr := H.tagged_typed 0 rx.1 rx.2
  have iv := H.responsePred_typed KY KP hv mv
  have ee := H.response_elim KY KP hv mv tx.1 tx.2 tr.1 tr.2 hr
    ((H.relation_tagged_same KY KP 0 hx mx rx.1 rx.2).2.prove (H.relational_formed.xCompare_round KY KP hx mx))
  exact (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx).equivalent_trans
    (H.diamond_formula KY KP hv mv tr.1 tr.2) (H.diamond_formula KY KP hv mv tx.1 tx.2)
    (H.responsePred_evaluation KY KP hv mv hx mx) ee.symm

theorem responsePred_respect {v x y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) y) := by
  have tx := H.tagged_typed 0 hx mx
  have ty := H.tagged_typed 0 hy my
  have iv := H.responsePred_typed KY KP hv mv
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my
  have f2 := H.diamond_formula KY KP hv mv tx.1 tx.2
  have f3 := H.diamond_formula KY KP hv mv ty.1 ty.2
  have e1 := H.responsePred_exact KY KP hv mv hx mx hr
  have e3 := H.responsePred_exact KY KP hv mv hy my hr
  have e2 := H.response_elim KY KP hv mv tx.1 tx.2 ty.1 ty.2 hr ((H.relation_tagged_same KY KP 0 hx mx hy my).2.prove he)
  exact f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 e1 e2) e3.symm

theorem responsePred_extStep {v x y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extStep L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x y) := by
  have iv := H.responsePred_typed KY KP hv mv
  apply L.imp_intro_future (H.relational_formed.xCompare_formula KY KP hx mx hy my)
    (L.iff_formula (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my))
  intro Δ δ e he
  simp only [RelationalCode.xCompare_rename] at he
  simp only [LogicSetup.iff_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,responsePred_rename]
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  have hv' := carrier_typed_rename e hv
  have hx' := x_typed_rename (B := B) e hx
  have hy' := x_typed_rename (B := B) e hy
  have iv' := (H.rename e).responsePred_typed (KY.rename e) (KP.rename e) hv' (e.moded mv)
  have ee := (H.rename e).responsePred_respect (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' (e.moded mx) hy' (e.moded my) hr' he
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hx' (e.moded mx))
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hy' (e.moded my)) ee

theorem responsePred_extAt {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extAt L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x) := by
  have iv := H.responsePred_typed KY KP hv mv
  apply H.relational_formed.extAt_intro KY KP iv.1 iv.2 hx mx
  intro Δ δ e y hy my
  simp only [responsePred_rename]
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  exact (H.rename e).responsePred_extStep (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv)
    (x_typed_rename (B := B) e hx) (e.moded mx) hy my hr'

theorem responsePred_extensional {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extensional L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v)) := by
  have iv := H.responsePred_typed KY KP hv mv
  apply H.relational_formed.extensional_intro KY KP iv.1 iv.2
  intro Δ δ e x hx mx
  simp only [responsePred_rename]
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  exact (H.rename e).responsePred_extAt (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv) hx mx hr'
end SpecializedCode.Formed
end PureTypeSystem.Labelled

end OAI
