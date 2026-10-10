import OAI.Computability.TypeSystem.Pairs

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}

/-- Fixed syntax shared by both source logical channels and the A-independent
probe type. The raw path is literally shared, not an isomorphism hypothesis. -/
structure RelationalCode (S : Type u) where
  probe : ProbeCode S
  logical : DataWrapper S true
  predicate : DataWrapper S true
namespace RelationalCode
variable (R : RelationalCode S)
def rename (ρ : Nat → Nat) : RelationalCode S :=
  ⟨R.probe.rename ρ,R.logical.rename ρ,R.predicate.rename ρ⟩
def subst (σ : Nat → Expr S) : RelationalCode S :=
  ⟨R.probe.subst σ,R.logical.subst σ,R.predicate.subst σ⟩
def channel : ChannelCode S := ⟨R.logical,R.probe.raw,R.predicate⟩
def baseType (A : Expr S) := R.probe.initial.apply A
def queryBody (L : LogicCode S) (t : Fin 7) (A m : Expr S) :=
  R.probe.doubled.queryPredBody R.predicate L t.castSucc (R.probe.rawType A) m
def goodBody (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) :=
  R.channel.goodBody L KY (R.baseType A) (R.queryBody L 0 A m)
def pair (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) :=
  R.channel.pairPred L KY KP (R.baseType A) (R.goodBody L KY A m)
    (fun t => R.queryBody L t A m) p a
/-- The source's fixed c_top in the raw wrapper, used only by the markers. -/
def rawTop (L : LogicCode S) (A : Expr S) :=
  R.probe.raw.build (R.baseType A) (L.top.rename Nat.succ)
def point (L : LogicCode S) (A y : Expr S) :=
  R.probe.doubled.point R.predicate L (R.probe.rawType A) (R.rawTop L A)
    (R.channel.toRaw (R.baseType A) y)
def bundle (L : LogicCode S) (A m y : Expr S) :=
  R.probe.doubled.bundle L (R.probe.paramType A)
    (R.probe.doubled.dummy L (R.probe.rawType A)) m (R.point L A y)
def diamond (L : LogicCode S) (A m v y : Expr S) :=
  R.probe.observe A v (R.bundle L A m y)
def partBody (L : LogicCode S) (A m v : Expr S) :=
  (R.rename Nat.succ).diamond (L.rename Nat.succ) (A.rename Nat.succ)
    (m.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def part (L : LogicCode S) (A m v : Expr S) :=
  R.channel.pred (R.baseType A) (R.partBody L A m v)
def sb (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) :=
  R.probe.doubled.query R.predicate L 6 (R.probe.rawType A) m
    (R.pair L KY KP A m (R.part L A m v) a)
def liftBody (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) :=
  (R.rename Nat.succ).sb (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (A.rename Nat.succ) (m.rename Nat.succ) (.var 0) (a.rename Nat.succ)
def lift (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) :=
  R.logical.build R.probe.carrier (R.liftBody L KY KP A m a)

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
structure Formed : Prop where
  probe : R.probe.Formed L I J k p n g
  channel : R.channel.Formed L k j p h
end RelationalCode

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C}
def relational (K : ChannelSetup L) : RelationalCode S :=
  ⟨K.probe,K.channel.logical,K.channel.predicate⟩
theorem relational_formed (K : ChannelSetup L) :
    K.relational.Formed L K.domain K.codomain K.base K.rawVertex K.tailVertex K.funVertex K.logicalVertex K.predVertex :=
  ⟨K.probe_formed,K.channelFormed⟩
end ChannelSetup
end

section
universe u
variable {S : Type u}
namespace ProbeCode
variable (R : ProbeCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp,PositiveDataWrapper.rename_comp,DataTail.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename,PositiveDataWrapper.subst_rename,DataTail.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst,PositiveDataWrapper.rename_subst,DataTail.rename_subst]
theorem carrier_rename (ρ : Nat → Nat) : R.carrier.rename ρ = (R.rename ρ).carrier := by
  simp only [carrier,body,domain,Expr.rename,DataWrapper.apply_rename,PositiveDataWrapper.apply_rename,
    funType_rename,PositiveDataWrapper.project_rename,DataWrapper.rename_comp,PositiveDataWrapper.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename,DataTail.rename_comp]
  rfl
theorem carrier_subst (σ : Nat → Expr S) : R.carrier.subst σ = (R.subst σ).carrier := by
  simp only [carrier,body,domain,Expr.subst,DataWrapper.apply_subst,PositiveDataWrapper.apply_subst,
    funType_subst,PositiveDataWrapper.project_subst,DataWrapper.subst_rename,
    PositiveDataWrapper.subst_rename,
    subst_rename,rename_subst,Expr.liftSub]
  simp only [subst,DataWrapper.rename_subst,PositiveDataWrapper.rename_subst]
  rfl
theorem readBody_rename (w : Expr S) (ρ : Nat → Nat) :
    (R.readBody w).rename (Expr.liftRen ρ) = (R.rename ρ).readBody (w.rename ρ) := by
  simp only [readBody,DataTail.read_rename,DataTail.rename_comp,Expr.rename,Expr.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename]
  rfl
theorem readBody_subst (w : Expr S) (σ : Nat → Expr S) :
    (R.readBody w).subst (Expr.liftSub σ) = (R.subst σ).readBody (w.subst σ) := by
  simp only [readBody,DataTail.read_subst,DataTail.subst_rename,DataTail.rename_subst,
    Expr.subst,Expr.liftSub,Expr.subst_rename,Expr.rename_subst,subst]
  rfl
theorem observe_rename (A v w : Expr S) (ρ : Nat → Nat) :
    (R.observe A v w).rename ρ = (R.rename ρ).observe (A.rename ρ) (v.rename ρ) (w.rename ρ) := by
  simp only [observe,DataWrapper.observe_rename,funType_rename,specialize,Expr.rename,
    PositiveDataWrapper.inject_rename,readBody_rename,DataWrapper.argRen,Bool.not_false,ite_true,rename]
theorem observe_subst (A v w : Expr S) (σ : Nat → Expr S) :
    (R.observe A v w).subst σ = (R.subst σ).observe (A.subst σ) (v.subst σ) (w.subst σ) := by
  simp only [observe,DataWrapper.observe_subst,funType_subst,specialize,Expr.subst,
    PositiveDataWrapper.inject_subst,readBody_subst,DataWrapper.argSub,Bool.not_false,ite_true,subst]
end ProbeCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem decodeMap_rename (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.decodeMap U L T).rename (Expr.liftRen ρ) =
      (R.rename ρ).decodeMap (U.rename ρ) (L.rename ρ) (T.rename ρ) := by
  simp only [decodeMap,decode_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Expr.rename]
  rfl
 theorem markBody_rename (L : LogicCode S) (t : Fin 8) (T c : Expr S) (ρ : Nat → Nat) :
    (R.markBody L t T c).rename (Expr.liftRen ρ) =
      (R.rename ρ).markBody (L.rename ρ) t (T.rename ρ) (c.rename ρ) := by
  simp only [markBody,DataWrapper.contraCallback_rename,big_rename,tagged_rename,rename_first]
 theorem pointBody_rename (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (ρ : Nat → Nat) :
    (R.pointBody U L T c₀ c).rename (Expr.liftRen ρ) =
      (R.rename ρ).pointBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (c₀.rename ρ) (c.rename ρ) := by
  simp only [pointBody,LogicCode.conj_rename,markBody_rename,Expr.compose_rename,
    DataWrapper.contraCallback_rename,decodeMap_rename,LogicCode.rename_comp]
  rfl
 theorem point_rename (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (ρ : Nat → Nat) :
    (R.point U L T c₀ c).rename ρ =
      (R.rename ρ).point (U.rename ρ) (L.rename ρ) (T.rename ρ) (c₀.rename ρ) (c.rename ρ) := by
  simp only [point,DataWrapper.build_rename,bpType_rename,DataWrapper.argRen,ite_true,
    pointBody_rename,rename_second]
 theorem dummy_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.dummy L T).rename ρ = (R.rename ρ).dummy (L.rename ρ) (T.rename ρ) := by
  simp only [dummy,DataWrapper.build_rename,bpType_rename,DataWrapper.argRen,ite_true,
    rename_second,Expr.rename_comp,← LogicCode.top_rename]
  rfl
 theorem bundle_rename (L : LogicCode S) (A d m y : Expr S) (ρ : Nat → Nat) :
    (R.bundle L A d m y).rename ρ =
      (R.rename ρ).bundle (L.rename ρ) (A.rename ρ) (d.rename ρ) (m.rename ρ) (y.rename ρ) := by
  simp only [bundle,bundleBody,DataWrapper.build_rename,DataWrapper.apply_rename,DataWrapper.argRen,ite_true,
    LogicCode.cond_rename,DataWrapper.contraCallback_rename,rename_first,rename_second,LogicCode.rename_comp]
  rfl
theorem decodeMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.decodeMap U L T).subst (Expr.liftSub σ) =
      (R.subst σ).decodeMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [decodeMap,decode_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
 theorem markBody_subst (L : LogicCode S) (t : Fin 8) (T c : Expr S) (σ : Nat → Expr S) :
    (R.markBody L t T c).subst (Expr.liftSub σ) =
      (R.subst σ).markBody (L.subst σ) t (T.subst σ) (c.subst σ) := by
  simp only [markBody,DataWrapper.contraCallback_subst,big_subst,tagged_subst,subst_first]
 theorem pointBody_subst (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (σ : Nat → Expr S) :
    (R.pointBody U L T c₀ c).subst (Expr.liftSub σ) =
      (R.subst σ).pointBody (U.subst σ) (L.subst σ) (T.subst σ) (c₀.subst σ) (c.subst σ) := by
  simp only [pointBody,LogicCode.conj_subst,markBody_subst,Expr.compose_subst,
    DataWrapper.contraCallback_subst,decodeMap_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
 theorem point_subst (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (σ : Nat → Expr S) :
    (R.point U L T c₀ c).subst σ =
      (R.subst σ).point (U.subst σ) (L.subst σ) (T.subst σ) (c₀.subst σ) (c.subst σ) := by
  simp only [point,DataWrapper.build_subst,bpType_subst,DataWrapper.argSub,ite_true,
    pointBody_subst,subst_second]
 theorem dummy_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummy L T).subst σ = (R.subst σ).dummy (L.subst σ) (T.subst σ) := by
  simp only [dummy,DataWrapper.build_subst,bpType_subst,DataWrapper.argSub,ite_true,
    subst_second,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
 theorem bundle_subst (L : LogicCode S) (A d m y : Expr S) (σ : Nat → Expr S) :
    (R.bundle L A d m y).subst σ =
      (R.subst σ).bundle (L.subst σ) (A.subst σ) (d.subst σ) (m.subst σ) (y.subst σ) := by
  simp only [bundle,bundleBody,DataWrapper.build_subst,DataWrapper.apply_subst,DataWrapper.argSub,ite_true,
    LogicCode.cond_subst,DataWrapper.contraCallback_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
end DoubleCode

namespace ChannelCode
variable (R : ChannelCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst]
theorem goodBody_subst (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.goodBody L K T Q).subst (Expr.liftSub σ) =
      (R.subst σ).goodBody (L.subst σ) (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [goodBody,LogicCode.conj_subst,roundRespect_subst,subst_rename,rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl
end ChannelCode
namespace RelationalCode
variable (R : RelationalCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,ProbeCode.rename_comp,DataWrapper.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,ProbeCode.subst_rename,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,ProbeCode.rename_subst,DataWrapper.rename_subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,ProbeCode.instantiate_raise,DataWrapper.instantiate_raise]
theorem channel_rename (ρ : Nat → Nat) : (R.rename ρ).channel = R.channel.rename ρ := rfl
theorem baseType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.baseType A).rename ρ = (R.rename ρ).baseType  (A.rename ρ) :=
  R.probe.initial.apply_rename A ρ
theorem queryBody_rename (L : LogicCode S) (t : Fin 7) (A m : Expr S) (ρ : Nat → Nat) :
    (R.queryBody L t A m).rename (Expr.liftRen ρ) = (R.rename ρ).queryBody (L.rename ρ) t (A.rename ρ) (m.rename ρ) := by
  simp only [queryBody,DoubleCode.queryPredBody_rename,ProbeCode.rawType_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem goodBody_rename (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) (ρ : Nat → Nat) :
    (R.goodBody L KY A m).rename (Expr.liftRen ρ) = (R.rename ρ).goodBody (L.rename ρ) (KY.rename ρ) (A.rename ρ) (m.rename ρ) := by
  simp only [goodBody,ChannelCode.goodBody_rename,baseType_rename,queryBody_rename,channel_rename]
theorem pair_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) (ρ : Nat → Nat) :
    (R.pair L KY KP A m p a).rename ρ = (R.rename ρ).pair (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (p.rename ρ) (a.rename ρ) := by
  simp only [pair,ChannelCode.pairPred_rename,baseType_rename,goodBody_rename,queryBody_rename,channel_rename]
theorem rawTop_rename (L : LogicCode S) (A : Expr S) (ρ : Nat → Nat) :
    (R.rawTop L A).rename ρ = (R.rename ρ).rawTop (L.rename ρ) (A.rename ρ) := by
  simp only [rawTop,DataWrapper.build_rename,baseType_rename,DataWrapper.argRen,ite_true,rename,Expr.rename_comp,← LogicCode.top_rename]
  rfl
theorem point_rename (L : LogicCode S) (A y : Expr S) (ρ : Nat → Nat) :
    (R.point L A y).rename ρ = (R.rename ρ).point (L.rename ρ) (A.rename ρ) (y.rename ρ) := by
  simp only [point,DoubleCode.point_rename,ProbeCode.rawType_rename,rawTop_rename,ChannelCode.toRaw_rename,baseType_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem bundle_rename (L : LogicCode S) (A m y : Expr S) (ρ : Nat → Nat) :
    (R.bundle L A m y).rename ρ = (R.rename ρ).bundle (L.rename ρ) (A.rename ρ) (m.rename ρ) (y.rename ρ) := by
  simp only [bundle,DoubleCode.bundle_rename,DoubleCode.dummy_rename,ProbeCode.paramType_rename,ProbeCode.rawType_rename,point_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem diamond_rename (L : LogicCode S) (A m v y : Expr S) (ρ : Nat → Nat) :
    (R.diamond L A m v y).rename ρ = (R.rename ρ).diamond (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [diamond,ProbeCode.observe_rename,bundle_rename,rename]
theorem partBody_rename (L : LogicCode S) (A m v : Expr S) (ρ : Nat → Nat) :
    (R.partBody L A m v).rename (Expr.liftRen ρ) = (R.rename ρ).partBody (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) := by
  simp only [partBody,diamond_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
 theorem part_rename (L : LogicCode S) (A m v : Expr S) (ρ : Nat → Nat) :
    (R.part L A m v).rename ρ = (R.rename ρ).part (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) := by
  simp only [part,ChannelCode.pred_rename,baseType_rename,partBody_rename,channel_rename]
 theorem sb_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) (ρ : Nat → Nat) :
    (R.sb L KY KP A m v a).rename ρ = (R.rename ρ).sb (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (v.rename ρ) (a.rename ρ) := by
  simp only [sb,DoubleCode.query_rename,ProbeCode.rawType_rename,pair_rename,part_rename,
    ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
 theorem liftBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (ρ : Nat → Nat) :
    (R.liftBody L KY KP A m a).rename (Expr.liftRen ρ) = (R.rename ρ).liftBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (a.rename ρ) := by
  simp only [liftBody,sb_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen,QuantifierCode.rename,
    ProofWrapper.rename_comp]
  rfl
 theorem lift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (ρ : Nat → Nat) :
    (R.lift L KY KP A m a).rename ρ = (R.rename ρ).lift (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (a.rename ρ) := by
  simp only [lift,DataWrapper.build_rename,ProbeCode.carrier_rename,DataWrapper.argRen,ite_true,
    liftBody_rename,rename]
theorem channel_subst (σ : Nat → Expr S) : (R.subst σ).channel = R.channel.subst σ := rfl
theorem baseType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.baseType A).subst σ = (R.subst σ).baseType  (A.subst σ) :=
  R.probe.initial.apply_subst A σ
theorem queryBody_subst (L : LogicCode S) (t : Fin 7) (A m : Expr S) (σ : Nat → Expr S) :
    (R.queryBody L t A m).subst (Expr.liftSub σ) = (R.subst σ).queryBody (L.subst σ) t (A.subst σ) (m.subst σ) := by
  simp only [queryBody,DoubleCode.queryPredBody_subst,ProbeCode.rawType_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem goodBody_subst (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) (σ : Nat → Expr S) :
    (R.goodBody L KY A m).subst (Expr.liftSub σ) = (R.subst σ).goodBody (L.subst σ) (KY.subst σ) (A.subst σ) (m.subst σ) := by
  simp only [goodBody,ChannelCode.goodBody_subst,baseType_subst,queryBody_subst,channel_subst]
theorem pair_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) (σ : Nat → Expr S) :
    (R.pair L KY KP A m p a).subst σ = (R.subst σ).pair (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (p.subst σ) (a.subst σ) := by
  simp only [pair,ChannelCode.pairPred_subst,baseType_subst,goodBody_subst,queryBody_subst,channel_subst]
theorem rawTop_subst (L : LogicCode S) (A : Expr S) (σ : Nat → Expr S) :
    (R.rawTop L A).subst σ = (R.subst σ).rawTop (L.subst σ) (A.subst σ) := by
  simp only [rawTop,DataWrapper.build_subst,baseType_subst,DataWrapper.argSub,ite_true,subst,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem point_subst (L : LogicCode S) (A y : Expr S) (σ : Nat → Expr S) :
    (R.point L A y).subst σ = (R.subst σ).point (L.subst σ) (A.subst σ) (y.subst σ) := by
  simp only [point,DoubleCode.point_subst,ProbeCode.rawType_subst,rawTop_subst,ChannelCode.toRaw_subst,baseType_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem bundle_subst (L : LogicCode S) (A m y : Expr S) (σ : Nat → Expr S) :
    (R.bundle L A m y).subst σ = (R.subst σ).bundle (L.subst σ) (A.subst σ) (m.subst σ) (y.subst σ) := by
  simp only [bundle,DoubleCode.bundle_subst,DoubleCode.dummy_subst,ProbeCode.paramType_subst,ProbeCode.rawType_subst,point_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem diamond_subst (L : LogicCode S) (A m v y : Expr S) (σ : Nat → Expr S) :
    (R.diamond L A m v y).subst σ = (R.subst σ).diamond (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [diamond,ProbeCode.observe_subst,bundle_subst,subst]
theorem partBody_subst (L : LogicCode S) (A m v : Expr S) (σ : Nat → Expr S) :
    (R.partBody L A m v).subst (Expr.liftSub σ) = (R.subst σ).partBody (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) := by
  simp only [partBody,diamond_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
 theorem part_subst (L : LogicCode S) (A m v : Expr S) (σ : Nat → Expr S) :
    (R.part L A m v).subst σ = (R.subst σ).part (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) := by
  simp only [part,ChannelCode.pred_subst,baseType_subst,partBody_subst,channel_subst]
 theorem sb_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) (σ : Nat → Expr S) :
    (R.sb L KY KP A m v a).subst σ = (R.subst σ).sb (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (v.subst σ) (a.subst σ) := by
  simp only [sb,DoubleCode.query_subst,ProbeCode.rawType_subst,pair_subst,part_subst,
    ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
 theorem liftBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (σ : Nat → Expr S) :
    (R.liftBody L KY KP A m a).subst (Expr.liftSub σ) = (R.subst σ).liftBody (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (a.subst σ) := by
  simp only [liftBody,sb_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
 theorem lift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (σ : Nat → Expr S) :
    (R.lift L KY KP A m a).subst σ = (R.subst σ).lift (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (a.subst σ) := by
  simp only [lift,DataWrapper.build_subst,ProbeCode.carrier_subst,DataWrapper.argSub,ite_true,
    liftBody_subst,subst]
theorem partBody_instantiate (L : LogicCode S) (A m v y : Expr S) :
    (R.partBody L A m v).instantiate y = R.diamond L A m v y := by
  simp only [partBody,Expr.instantiate,diamond_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem liftBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A m a v : Expr S) :
    (R.liftBody L KY KP A m a).instantiate v = R.sb L KY KP A m v a := by
  simp only [liftBody,Expr.instantiate,sb_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h)
include H
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g j h :=
  ⟨H.probe.rename e,H.channel.rename e⟩
theorem base_sorted {A : Expr S} (hA : HasType P Γ A (.sort R.probe.seed)) :
    SortedAt P Γ (R.baseType A) k :=
  H.probe.initial.sorted (fun s hs => by cases hs; exact hA)
theorem base_mode {A : Expr S} (mA : WellModed γ A .data) :
    WellModed γ (R.baseType A) .data := H.probe.initial.mode mA
theorem queryBody_family (t : Fin 7) {A m : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data) :
    L.Family (R.channel.predicateType (R.baseType A)) (R.queryBody L.code t A m) :=
  H.probe.doubled_formed.queryPredBody_family H.channel.predicate t.castSucc
    (H.probe.raw_sorted hA) (H.probe.raw_mode mA) hm mm
theorem goodBody_family (KY : QuantifierRoute L.witnesses C L.base j) {A m : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data) :
    L.Family (R.channel.predicateType (R.baseType A)) (R.goodBody L.code KY.code A m) :=
  H.channel.goodBody_family KY (H.base_sorted hA) (H.base_mode mA) (H.queryBody_family 0 hA mA hm mm)
theorem pair_typed (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m q a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hq : HasType P Γ q (R.channel.predicateType (R.baseType A))) (mq : WellModed γ q .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    HasType P Γ (R.pair L.code KY.code KP.code A m q a) (R.channel.predicateType (R.baseType A)) ∧
      WellModed γ (R.pair L.code KY.code KP.code A m q a) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  exact H.channel.pairPred_typed KY KP (H.base_sorted hA) (H.base_mode mA)
    (H.goodBody_family KY hA mA hm mm) (fun t => H.queryBody_family t hA mA hm mm)
    (H.probe.raw_sorted hA s hs) hq mq ha ma
theorem rawTop_typed {A : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data) :
    HasType P Γ (R.rawTop L.code A) (R.probe.rawType A) ∧ WellModed γ (R.rawTop L.code A) .data :=
  (H.probe.raw.sound (H.base_sorted hA) (H.base_mode mA)).1 _ (.constant L.top_formula)
theorem point_typed {A y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    HasType P Γ (R.point L.code A y) (R.probe.paramType A) ∧ WellModed γ (R.point L.code A y) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.probe.mainTriple.product.1
  have ht := H.rawTop_typed hA mA
  have hc := H.channel.toRaw_typed (H.base_sorted hA) (H.base_mode mA) hy my
  exact H.probe.doubled_formed.point_typed H.channel.predicate (H.probe.raw_sorted hA)
    (H.probe.raw_mode mA) ht.1 ht.2 hc.1 hc.2 (H.probe.raw_sorted hA s hs)
    (H.probe.doubled_formed.bp_sorted (H.probe.raw_sorted hA) r hr)
theorem bundle_typed {A m y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    HasType P Γ (R.bundle L.code A m y) (R.probe.singleType A) ∧ WellModed γ (R.bundle L.code A m y) .data := by
  have hd := H.probe.doubled_formed.dummy_typed (H.probe.raw_sorted hA) (H.probe.raw_mode mA)
  have hp := H.point_typed hA mA hy my
  exact H.probe.doubled_formed.bundle_typed (H.probe.param_sorted hA) (H.probe.param_mode mA)
    hd.1 hd.2 hm mm hp.1 hp.2
theorem diamond_formula {A m v y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    L.Formula (R.diamond L.code A m v y) := by
  have hb := H.bundle_typed hA mA hm mm hy my
  exact H.probe.observe_formula hA mA hv mv hb.1 hb.2
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h)
include H
theorem partBody_family {A m v : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data) :
    L.Family (R.channel.logicalType (R.baseType A)) (R.partBody L.code A m v) := by
  intro Δ δ e y hy my
  rw [partBody_rename,partBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P Δ (m.rename e.names) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename] using e.typing hm
  have hv' : HasType P Δ (v.rename e.names) (R.rename e.names).probe.carrier := by
    simpa only [ProbeCode.carrier_rename,RelationalCode.rename] using e.typing hv
  have hy' : HasType P Δ y ((R.rename e.names).channel.logicalType ((R.rename e.names).baseType (A.rename e.names))) := by
    simpa only [ChannelCode.logicalType_rename,baseType_rename,channel_rename] using hy
  exact (H.rename e).diamond_formula hA' (e.moded mA) hm' (e.moded mm) hv' (e.moded mv) hy' my
theorem part_typed {A m v : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data) :
    HasType P Γ (R.part L.code A m v) (R.channel.predicateType (R.baseType A)) ∧
      WellModed γ (R.part L.code A m v) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  exact H.channel.pred_typed (H.base_sorted hA) (H.base_mode mA)
    (H.partBody_family hA mA hm mm hv mv) (H.probe.raw_sorted hA s hs)
theorem part_evaluation {A m v y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    Equivalent P Γ γ (R.channel.eval (R.baseType A) (R.part L.code A m v) y)
      (R.diamond L.code A m v (R.channel.round (R.baseType A) y)) := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  simpa only [part,partBody_instantiate] using H.channel.pred_evaluation (H.base_sorted hA) (H.base_mode mA)
    (H.partBody_family hA mA hm mm hv mv) (H.probe.raw_sorted hA s hs) hy my
theorem sb_formula (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m v a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    L.Formula (R.sb L.code KY.code KP.code A m v a) := by
  have hp := H.part_typed hA mA hm mm hv mv
  have hq := H.pair_typed KY KP hA mA hm mm hp.1 hp.2 ha ma
  exact H.probe.doubled_formed.query_formula H.channel.predicate 6 (H.probe.raw_sorted hA)
    (H.probe.raw_mode mA) hm mm hq.1 hq.2
theorem liftBody_family (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    L.Family R.probe.carrier (R.liftBody L.code KY.code KP.code A m a) := by
  intro Δ δ e v hv mv
  rw [liftBody_rename,liftBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P Δ (m.rename e.names) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename] using e.typing hm
  have hv' : HasType P Δ v (R.rename e.names).probe.carrier := by
    simpa only [ProbeCode.carrier_rename,RelationalCode.rename] using hv
  have ha' : HasType P Δ (a.rename e.names) ((R.rename e.names).channel.logicalType ((R.rename e.names).baseType (A.rename e.names))) := by
    simpa only [ChannelCode.logicalType_rename,baseType_rename,channel_rename] using e.typing ha
  exact (H.rename e).sb_formula (KY.rename e) (KP.rename e) hA' (e.moded mA) hm' (e.moded mm) hv' mv ha' (e.moded ma)
theorem lift_typed (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    HasType P Γ (R.lift L.code KY.code KP.code A m a) (R.channel.logicalType R.probe.carrier) ∧
      WellModed γ (R.lift L.code KY.code KP.code A m a) .data :=
  (H.channel.logical.sound H.probe.carrier_sorted H.probe.carrier_mode).1 _ (H.liftBody_family KY KP hA mA hm mm ha ma)
theorem lift_evaluation (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m a v : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (R.logical.observe R.probe.carrier (R.lift L.code KY.code KP.code A m a) v)
      (R.sb L.code KY.code KP.code A m v a) := by
  simpa only [lift,RelationalCode.channel,DataWrapper.cancelFormula,ite_true,liftBody_instantiate] using H.channel.logical.cancellation H.probe.carrier_sorted H.probe.carrier_mode
    (H.liftBody_family KY KP hA mA hm mm ha ma) ⟨hv,mv⟩
end RelationalCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
theorem accessBody_rename (L : LogicCode S) (A guard w fi : Expr S) (ρ : Nat → Nat) :
    (R.accessBody L A guard w fi).rename (Expr.liftRen ρ) =
      (R.rename ρ).accessBody (L.rename ρ) (A.rename ρ) (guard.rename (Expr.liftRen ρ)) (w.rename ρ) (fi.rename (Expr.liftRen ρ)) := by
  simp only [accessBody,LogicCode.cond_rename,Expr.compose_rename,DataWrapper.evalCallback_rename,
    DataWrapper.apply_rename,rename_first,rename_second,LogicCode.rename_comp,Expr.rename_comp,← LogicCode.top_rename]
  rfl
theorem accessBody_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.accessBody L A guard w fi).subst (Expr.liftSub σ) =
      (R.subst σ).accessBody (L.subst σ) (A.subst σ) (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [accessBody,LogicCode.cond_subst,Expr.compose_subst,DataWrapper.evalCallback_subst,
    DataWrapper.apply_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst,
    Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem access_rename (L : LogicCode S) (A guard w fi : Expr S) (ρ : Nat → Nat) :
    (R.access L A guard w fi).rename ρ = (R.rename ρ).access (L.rename ρ) (A.rename ρ)
      (guard.rename (Expr.liftRen ρ)) (w.rename ρ) (fi.rename (Expr.liftRen ρ)) := by
  simp only [access,accessProbe,DataWrapper.observe_rename,DataWrapper.apply_rename,
    DataWrapper.build_rename,accessBody_rename,rename_first,rename_second,DataWrapper.argRen,
    Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
theorem access_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.access L A guard w fi).subst σ = (R.subst σ).access (L.subst σ) (A.subst σ)
      (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [access,accessProbe,DataWrapper.observe_subst,DataWrapper.apply_subst,
    DataWrapper.build_subst,accessBody_subst,subst_first,subst_second,DataWrapper.argSub,
    Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
theorem innerMap_rename (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.innerMap U L T).rename (Expr.liftRen ρ) = (R.rename ρ).innerMap (U.rename ρ) (L.rename ρ) (T.rename ρ) := by
  simp only [innerMap,innerProbe_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem innerMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.innerMap U L T).subst (Expr.liftSub σ) = (R.subst σ).innerMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [innerMap,innerProbe_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverAccess_rename (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (ρ : Nat → Nat) :
    (R.recoverAccess U L T w pMap).rename ρ = (R.rename ρ).recoverAccess (U.rename ρ) (L.rename ρ)
      (T.rename ρ) (w.rename ρ) (pMap.rename (Expr.liftRen ρ)) := by
  simp only [recoverAccess,access_rename,paramType_rename,dummyBody_rename,accessMap,Expr.compose_rename,innerMap_rename]
theorem recoverAccess_subst (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (σ : Nat → Expr S) :
    (R.recoverAccess U L T w pMap).subst σ = (R.subst σ).recoverAccess (U.subst σ) (L.subst σ)
      (T.subst σ) (w.subst σ) (pMap.subst (Expr.liftSub σ)) := by
  simp only [recoverAccess,access_subst,paramType_subst,dummyBody_subst,accessMap,Expr.compose_subst,innerMap_subst]
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H) (hI : I.Nonempty) (hH : H.Nonempty)
include h hU hI hH
theorem recoverAccess_formula {T w pMap : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap)
    (hw : HasType P Γ w (R.carrier (R.paramType T))) (mw : WellModed γ w .data) :
    L.Formula (R.recoverAccess U L.code T w pMap) := by
  have hf := h.accessMap_typed hU hI hH hT mT hp
  obtain ⟨s,hs⟩ := hI
  have ha := h.accessProbe_typed (h.param_sorted hT) (h.param_mode mT)
    (h.dummyBody_family hT mT) hw mw hf (h.param_sorted hT s hs)
  exact (h.second.sound (h.first.sorted (h.param_sorted hT)) (h.first.mode (h.param_mode mT))).2 _ _ hw mw ha
end Formed
end DoubleCode
end

section
universe u
variable {S : Type u}
namespace RelationalCode
variable (R : RelationalCode S)
/-- The genuine logical-element binder in i@lift_m(y). -/
def liftEvalBody (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) :=
  (R.channel.rename Nat.succ).eval (R.probe.carrier.rename Nat.succ) (i.rename Nat.succ)
    ((R.rename Nat.succ).lift (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
      (A.rename Nat.succ) (m.rename Nat.succ) (.var 0))
def predLift (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) :=
  R.channel.pred (R.baseType A) (R.liftEvalBody L KY KP A m i)
/-- The data parameter binder, not an assumed semantic universal. -/
def predLiftMap (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) :=
  (R.rename Nat.succ).predLift (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (A.rename Nat.succ) (.var 0) (i.rename Nat.succ)
def recoverLift (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) :=
  R.probe.doubled.recoverAccess R.predicate L (R.probe.rawType A) w (R.predLiftMap L KY KP A i)
def recoverLiftBody (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) :=
  (R.rename Nat.succ).recoverLift (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (A.rename Nat.succ) (i.rename Nat.succ) (.var 0)
/-- The source z_i: the body abstracts z:Z, then w:Single(z↓).
No distinguished A or m occurs in this term. -/
def probeFor (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  R.probe.uniform ((R.rename Nat.succ).recoverLiftBody (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    ((R.probe.lifting.rename Nat.succ).project (.var 0)) (i.rename Nat.succ))
def le (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  R.logical.observe R.probe.carrier x (R.probeFor L KY KP i)
theorem liftEvalBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (ρ : Nat → Nat) :
    (R.liftEvalBody L KY KP A m i).rename (Expr.liftRen ρ) = (R.rename ρ).liftEvalBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (i.rename ρ) := by
  simp only [liftEvalBody,ChannelCode.eval_rename,lift_rename,channel_rename,ProbeCode.carrier_rename,ChannelCode.rename_comp,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  simp only [rename,ProbeCode.rename_comp]
  rfl
theorem predLift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (ρ : Nat → Nat) :
    (R.predLift L KY KP A m i).rename ρ = (R.rename ρ).predLift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (i.rename ρ) := by
  simp only [predLift,ChannelCode.pred_rename,baseType_rename,liftEvalBody_rename,channel_rename]
theorem predLiftMap_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (ρ : Nat → Nat) :
    (R.predLiftMap L KY KP A i).rename (Expr.liftRen ρ) = (R.rename ρ).predLiftMap (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) := by
  simp only [predLiftMap,predLift_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem recoverLift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) (ρ : Nat → Nat) :
    (R.recoverLift L KY KP A i w).rename ρ = (R.rename ρ).recoverLift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) (w.rename ρ) := by
  simp only [recoverLift,DoubleCode.recoverAccess_rename,ProbeCode.rawType_rename,predLiftMap_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem recoverLiftBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (ρ : Nat → Nat) :
    (R.recoverLiftBody L KY KP A i).rename (Expr.liftRen ρ) = (R.rename ρ).recoverLiftBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) := by
  simp only [recoverLiftBody,recoverLift_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem liftEvalBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (σ : Nat → Expr S) :
    (R.liftEvalBody L KY KP A m i).subst (Expr.liftSub σ) = (R.subst σ).liftEvalBody (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (i.subst σ) := by
  simp only [liftEvalBody,ChannelCode.eval_subst,lift_subst,channel_subst,ProbeCode.carrier_subst,ChannelCode.subst_rename,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub,ChannelCode.rename_subst]
  simp only [subst,ProbeCode.carrier_rename,ProbeCode.rename_subst]
  rfl
theorem predLift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (σ : Nat → Expr S) :
    (R.predLift L KY KP A m i).subst σ = (R.subst σ).predLift (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (i.subst σ) := by
  simp only [predLift,ChannelCode.pred_subst,baseType_subst,liftEvalBody_subst,channel_subst]
theorem predLiftMap_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (σ : Nat → Expr S) :
    (R.predLiftMap L KY KP A i).subst (Expr.liftSub σ) = (R.subst σ).predLiftMap (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) := by
  simp only [predLiftMap,predLift_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverLift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) (σ : Nat → Expr S) :
    (R.recoverLift L KY KP A i w).subst σ = (R.subst σ).recoverLift (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) (w.subst σ) := by
  simp only [recoverLift,DoubleCode.recoverAccess_subst,ProbeCode.rawType_subst,predLiftMap_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem recoverLiftBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (σ : Nat → Expr S) :
    (R.recoverLiftBody L KY KP A i).subst (Expr.liftSub σ) = (R.subst σ).recoverLiftBody (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) := by
  simp only [recoverLiftBody,recoverLift_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem liftEvalBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A m i y : Expr S) :
    (R.liftEvalBody L KY KP A m i).instantiate y = R.channel.eval R.probe.carrier i (R.lift L KY KP A m y) := by
  simp only [liftEvalBody,Expr.instantiate,ChannelCode.eval_subst,lift_subst,
    instantiate_raise,ChannelCode.instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem predLiftMap_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A i m : Expr S) :
    (R.predLiftMap L KY KP A i).instantiate m = R.predLift L KY KP A m i := by
  simp only [predLiftMap,Expr.instantiate,predLift_subst,
    instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem recoverLiftBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) :
    (R.recoverLiftBody L KY KP A i).instantiate w = R.recoverLift L KY KP A i w := by
  simp only [recoverLiftBody,Expr.instantiate,recoverLift_subst,
    instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
end RelationalCode

namespace ProbeCode
variable (R : ProbeCode S)
theorem uniform_rename (Q : Expr S) (ρ : Nat → Nat) :
    (R.uniform Q).rename ρ = (R.rename ρ).uniform (Q.rename (Expr.liftRen (Expr.liftRen ρ))) := by
  simp only [uniform,Expr.rename,domain,PositiveDataWrapper.apply_rename,wrappedBuild_rename,
    PositiveDataWrapper.project_rename,PositiveDataWrapper.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename]
  simp only [DataWrapper.rename_comp,DataTail.rename_comp]
  rfl
theorem uniform_subst (Q : Expr S) (σ : Nat → Expr S) :
    (R.uniform Q).subst σ = (R.subst σ).uniform (Q.subst (Expr.liftSub (Expr.liftSub σ))) := by
  simp only [uniform,Expr.subst,domain,PositiveDataWrapper.apply_subst,wrappedBuild_subst,
    PositiveDataWrapper.project_subst,subst_rename,rename_subst,PositiveDataWrapper.subst_rename,
    Expr.liftSub]
  simp only [subst,PositiveDataWrapper.rename_subst]
  rfl
end ProbeCode
namespace RelationalCode
variable (R : RelationalCode S)
theorem probeFor_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.probeFor L KY KP i).rename ρ =
      (R.rename ρ).probeFor (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [probeFor,ProbeCode.uniform_rename,recoverLiftBody_rename,
    LogicCode.rename_comp,QuantifierCode.rename_comp,PositiveDataWrapper.project_rename,
    PositiveDataWrapper.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen,rename,ProbeCode.rename]
  simp only [DataWrapper.rename_comp,DataTail.rename_comp]
  rfl
theorem probeFor_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.probeFor L KY KP i).subst σ =
      (R.subst σ).probeFor (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [probeFor,ProbeCode.uniform_subst,recoverLiftBody_subst,subst_rename,rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,PositiveDataWrapper.project_subst,
    PositiveDataWrapper.subst_rename,Expr.subst_rename,
    Expr.rename_subst,Expr.subst,Expr.liftSub]
  simp only [subst,ProbeCode.subst,PositiveDataWrapper.rename_subst]
  rfl
theorem le_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.le L KY KP i x).rename ρ = (R.rename ρ).le (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [le,DataWrapper.observe_rename,ProbeCode.carrier_rename,probeFor_rename,DataWrapper.argRen,rename]
  rfl
theorem le_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.le L KY KP i x).subst σ = (R.subst σ).le (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [le,DataWrapper.observe_subst,ProbeCode.carrier_subst,probeFor_subst,DataWrapper.argSub,subst]
  rfl
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem liftEvalBody_family {A m i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.channel.logicalType (R.baseType A)) (R.liftEvalBody L.code KY.code KP.code A m i) := by
  intro Δ δ e y hy my
  rw [liftEvalBody_rename,liftEvalBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P Δ (m.rename e.names) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename] using e.typing hm
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have hy' : HasType P Δ y ((R.rename e.names).channel.logicalType ((R.rename e.names).baseType (A.rename e.names))) := by
    simpa only [ChannelCode.logicalType_rename,baseType_rename,channel_rename] using hy
  have hl := (H.rename e).lift_typed (KY.rename e) (KP.rename e) hA' (e.moded mA) hm' (e.moded mm) hy' my
  exact (H.rename e).channel.eval_formula (H.rename e).probe.carrier_sorted (H.rename e).probe.carrier_mode hi' (e.moded mi) hl.1 hl.2
theorem predLift_typed {A m i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    HasType P Γ (R.predLift L.code KY.code KP.code A m i) (R.channel.predicateType (R.baseType A)) ∧
      WellModed γ (R.predLift L.code KY.code KP.code A m i) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  exact H.channel.pred_typed (H.base_sorted hA) (H.base_mode mA)
    (H.liftEvalBody_family KY KP hA mA hm mm hi mi) (H.probe.raw_sorted hA s hs)
theorem predLiftMap_typed {A i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    DataMap P Γ γ (R.probe.paramType A) (R.channel.predicateType (R.baseType A)) (R.predLiftMap L.code KY.code KP.code A i) := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  let e : Embedding P Γ γ (R.probe.paramType A :: Γ) (modeCons .data γ) := Embedding.cons (H.probe.param_sorted hA s hs) .data
  have hA' : HasType P (R.probe.paramType A :: Γ) (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P (R.probe.paramType A :: Γ) (.var 0) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename,e,Embedding.cons] using HasType.var (H.probe.param_sorted hA s hs)
  have hi' : HasType P (R.probe.paramType A :: Γ) (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have ht := (H.rename e).predLift_typed (KY.rename e) (KP.rename e) hA' (e.moded mA) hm' (.var 0) hi' (e.moded mi)
  simpa only [DataMap,predLiftMap,LogicSetup.code_rename,QuantifierRoute.code_rename,
    ChannelCode.predicateType_rename,baseType_rename,channel_rename,e,Embedding.cons,
    QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename] using ht
theorem recoverLift_formula {A i w : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hw : HasType P Γ w (R.probe.singleType A)) (mw : WellModed γ w .data) :
    L.Formula (R.recoverLift L.code KY.code KP.code A i w) := by
  exact H.probe.doubled_formed.recoverAccess_formula H.channel.predicate H.probe.funTriple.domain.1 KP.triple.domain.1
    (H.probe.raw_sorted hA) (H.probe.raw_mode mA) (H.predLiftMap_typed KY KP hA mA hi mi) hw mw
theorem recoverLiftBody_family {A i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.probe.singleType A) (R.recoverLiftBody L.code KY.code KP.code A i) := by
  intro Δ δ e w hw mw
  rw [recoverLiftBody_rename,recoverLiftBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have hw' : HasType P Δ w ((R.rename e.names).probe.singleType (A.rename e.names)) := by
    simpa only [ProbeCode.singleType_rename,RelationalCode.rename] using hw
  exact (H.rename e).recoverLift_formula (KY.rename e) (KP.rename e) hA' (e.moded mA) hi' (e.moded mi) hw' mw
theorem probeFor_typed {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    HasType P Γ (R.probeFor L.code KY.code KP.code i) R.probe.carrier ∧
      WellModed γ (R.probeFor L.code KY.code KP.code i) .data := by
  obtain ⟨s,hs⟩ := H.probe.mainTriple.domain.1
  let e : Embedding P Γ γ (R.probe.domain :: Γ) (modeCons .data γ) := Embedding.cons (H.probe.domain_sorted s hs) .data
  have hi' : HasType P (R.probe.domain :: Γ) (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have hf := (H.rename e).recoverLiftBody_family (KY.rename e) (KP.rename e)
    (H.probe.raised_project (H.probe.domain_sorted s hs))
    ((H.probe.rename e).project_mode (.var 0)) hi' (e.moded mi)
  exact H.probe.uniform_typed (H.probe.domain_sorted s hs) hf
theorem le_formula {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Formula (R.le L.code KY.code KP.code i x) := by
  have ht := H.probeFor_typed KY KP hi mi
  exact (H.channel.logical.sound H.probe.carrier_sorted H.probe.carrier_mode).2 _ _ hx mx ht
end RelationalCode.Formed

namespace RelationalCode
variable (R : RelationalCode S)
/-- Binder i:P_X for le(i,x). -/
def leBody (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  (R.rename Nat.succ).le (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (.var 0) (x.rename Nat.succ)
def xCompareBody (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) :=
  (L.rename Nat.succ).iff (R.leBody L KY KP x) (R.leBody L KY KP y)
def xCompare (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) :=
  KP.all (R.channel.predicateType R.probe.carrier) (R.xCompareBody L KY KP x y)

theorem leBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.leBody L KY KP x).rename (Expr.liftRen ρ) =
      (R.rename ρ).leBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [leBody,le_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem leBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.leBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).leBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [leBody,le_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem leBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :
    (R.leBody L KY KP x).instantiate i = R.le L KY KP i x := by
  simp only [leBody,Expr.instantiate,le_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem xCompareBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (ρ : Nat → Nat) :
    (R.xCompareBody L KY KP x y).rename (Expr.liftRen ρ) =
      (R.rename ρ).xCompareBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [xCompareBody,LogicCode.iff_rename,leBody_rename,LogicCode.rename_comp]
  rfl
theorem xCompareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompareBody L KY KP x y).subst (Expr.liftSub σ) =
      (R.subst σ).xCompareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompareBody,LogicCode.iff_subst,leBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem xCompareBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x y i : Expr S) :
    (R.xCompareBody L KY KP x y).instantiate i = L.iff (R.le L KY KP i x) (R.le L KY KP i y) := by
  change ((L.rename Nat.succ).iff (R.leBody L KY KP x) (R.leBody L KY KP y)).subst (Expr.single i) = _
  rw [LogicCode.iff_subst,LogicCode.instantiate_raise]
  change L.iff ((R.leBody L KY KP x).instantiate i) ((R.leBody L KY KP y).instantiate i) = _
  rw [leBody_instantiate,leBody_instantiate]
theorem xCompare_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (ρ : Nat → Nat) :
    (R.xCompare L KY KP x y).rename ρ =
      (R.rename ρ).xCompare (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [xCompare,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,
    channel_rename,xCompareBody_rename]
  rfl
theorem xCompare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompare L KY KP x y).subst σ =
      (R.subst σ).xCompare (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,
    channel_subst,xCompareBody_subst]
  rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem leBody_family {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.leBody L.code KY.code KP.code x) := by
  intro Δ δ e i hi mi
  rw [leBody_rename,leBody_instantiate]
  have hi' : HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using hi
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hx
  exact (H.rename e).le_formula (KY.rename e) (KP.rename e) hi' mi hx' (e.moded mx)
theorem xCompareBody_family {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.xCompareBody L.code KY.code KP.code x y) :=
  (H.leBody_family KY KP hx mx).code_iff (H.leBody_family KY KP hy my)
theorem xCompare_formula {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data) :
    L.Formula (R.xCompare L.code KY.code KP.code x y) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.xCompareBody_family KY KP hx mx hy my)
theorem xCompare_elim {x y i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (R.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (R.le L.code KY.code KP.code i x) (R.le L.code KY.code KP.code i y) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have hh := L.all_elim_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.xCompareBody_family KY KP hx mx hy my) hi mi he
  rw [xCompareBody_instantiate,LogicSetup.code_iff] at hh
  exact L.equivalent_of_iff (H.le_formula KY KP hi mi hx mx) (H.le_formula KY KP hi mi hy my) hh
theorem xCompare_intro {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) i,
      HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) → WellModed δ i .data →
      Equivalent P Δ δ ((R.rename e.names).le (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) i (x.rename e.names))
        ((R.rename e.names).le (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) i (y.rename e.names))) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code x y) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.xCompareBody_family KY KP hx mx hy my)
  intro Δ δ e i hi mi
  rw [xCompareBody_rename,xCompareBody_instantiate]
  have hi' : HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using hi
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hx
  have hy' : HasType P Δ (y.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hy
  exact (L.rename e).iff_of_equivalent ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi' mi hx' (e.moded mx))
    ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi' mi hy' (e.moded my)) (hh Δ δ e i hi' mi)
end Formed
end RelationalCode
end

section
universe u
namespace RelationalCode
variable {S : Type u} (R : RelationalCode S)
def extStep (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) :=
  L.imp (R.xCompare L KY KP x y)
    (L.iff (R.channel.eval R.probe.carrier i x) (R.channel.eval R.probe.carrier i y))
def extAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  (R.rename Nat.succ).extStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (i.rename Nat.succ) (x.rename Nat.succ) (.var 0)
def extAt (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  KY.all (R.channel.logicalType R.probe.carrier) (R.extAtBody L KY KP i x)
def extBody (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  (R.rename Nat.succ).extAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (i.rename Nat.succ) (.var 0)
def extensional (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  KY.all (R.channel.logicalType R.probe.carrier) (R.extBody L KY KP i)
def validStep (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) :=
  L.imp (R.channel.predCompare L KY R.probe.carrier i i')
    (L.iff (R.le L KY KP i x) (R.le L KY KP i' x))
def validAtBody (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :=
  (R.rename Nat.succ).validStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (x.rename Nat.succ) (i.rename Nat.succ) (.var 0)
def validAt (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :=
  KP.all (R.channel.predicateType R.probe.carrier) (R.validAtBody L KY KP x i)
def validBody (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  (R.rename Nat.succ).validAt (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (x.rename Nat.succ) (.var 0)
def valid (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  KP.all (R.channel.predicateType R.probe.carrier) (R.validBody L KY KP x)

theorem extStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (ρ : Nat → Nat) :
    (R.extStep L KY KP i x y).rename ρ =
      (R.rename ρ).extStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [extStep,LogicCode.imp_rename,LogicCode.iff_rename,xCompare_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,channel_rename]
  try rfl

theorem extStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (σ : Nat → Expr S) :
    (R.extStep L KY KP i x y).subst σ =
      (R.subst σ).extStep (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [extStep,LogicCode.imp_subst,LogicCode.iff_subst,xCompare_subst,ChannelCode.eval_subst,ProbeCode.carrier_subst,channel_subst]
  try rfl

theorem extAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.extAtBody L KY KP i x).rename (Expr.liftRen ρ) =
      (R.rename ρ).extAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [extAtBody,extStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem extAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAtBody L KY KP i x).subst (Expr.liftSub σ) =
      (R.subst σ).extAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAtBody,extStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (i x a : Expr S) :
    (R.extAtBody L KY KP i x).instantiate a = R.extStep L KY KP i x a := by
  simp only [extAtBody,Expr.instantiate,extStep_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem extAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.extAt L KY KP i x).rename ρ =
      (R.rename ρ).extAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [extAt,QuantifierCode.all_rename,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,extAtBody_rename]
  try rfl

theorem extAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAt L KY KP i x).subst σ =
      (R.subst σ).extAt (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAt,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extAtBody_subst]
  try rfl

theorem extBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.extBody L KY KP i).rename (Expr.liftRen ρ) =
      (R.rename ρ).extBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [extBody,extAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem extBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extBody L KY KP i).subst (Expr.liftSub σ) =
      (R.subst σ).extBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extBody,extAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (i a : Expr S) :
    (R.extBody L KY KP i).instantiate a = R.extAt L KY KP i a := by
  simp only [extBody,Expr.instantiate,extAt_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem extensional_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.extensional L KY KP i).rename ρ =
      (R.rename ρ).extensional (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [extensional,QuantifierCode.all_rename,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,extBody_rename]
  try rfl

theorem extensional_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extensional L KY KP i).subst σ =
      (R.subst σ).extensional (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extensional,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extBody_subst]
  try rfl

theorem validStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (ρ : Nat → Nat) :
    (R.validStep L KY KP x i i').rename ρ =
      (R.rename ρ).validStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) (i'.rename ρ) := by
  simp only [validStep,LogicCode.imp_rename,LogicCode.iff_rename,ChannelCode.predCompare_rename,ProbeCode.carrier_rename,channel_rename,le_rename]
  try rfl

theorem validStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (σ : Nat → Expr S) :
    (R.validStep L KY KP x i i').subst σ =
      (R.subst σ).validStep (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) (i'.subst σ) := by
  simp only [validStep,LogicCode.imp_subst,LogicCode.iff_subst,ChannelCode.predCompare_subst,ProbeCode.carrier_subst,channel_subst,le_subst]
  try rfl

theorem validAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (ρ : Nat → Nat) :
    (R.validAtBody L KY KP x i).rename (Expr.liftRen ρ) =
      (R.rename ρ).validAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) := by
  simp only [validAtBody,validStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem validAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAtBody L KY KP x i).subst (Expr.liftSub σ) =
      (R.subst σ).validAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAtBody,validStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem validAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x i a : Expr S) :
    (R.validAtBody L KY KP x i).instantiate a = R.validStep L KY KP x i a := by
  simp only [validAtBody,Expr.instantiate,validStep_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem validAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (ρ : Nat → Nat) :
    (R.validAt L KY KP x i).rename ρ =
      (R.rename ρ).validAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) := by
  simp only [validAt,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,validAtBody_rename]
  try rfl

theorem validAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAt L KY KP x i).subst σ =
      (R.subst σ).validAt (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAt,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validAtBody_subst]
  try rfl

theorem validBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.validBody L KY KP x).rename (Expr.liftRen ρ) =
      (R.rename ρ).validBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [validBody,validAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem validBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.validBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).validBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [validBody,validAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem validBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x a : Expr S) :
    (R.validBody L KY KP x).instantiate a = R.validAt L KY KP x a := by
  simp only [validBody,Expr.instantiate,validAt_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem valid_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.valid L KY KP x).rename ρ =
      (R.rename ρ).valid (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [valid,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,validBody_rename]
  try rfl

theorem valid_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.valid L KY KP x).subst σ =
      (R.subst σ).valid (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [valid,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validBody_subst]
  try rfl
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem x_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) :
    HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
  simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
    RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hx

theorem xCompare_refl {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code x x) := by
  apply H.xCompare_intro KY KP hx mx hx mx
  intro Δ δ e i hi mi
  exact ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi mi
    (x_typed_rename (R := R) e hx) (e.moded mx)).equivalent_refl

theorem xCompare_symm {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.xCompare L.code KY.code KP.code x y)) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code y x) := by
  apply H.xCompare_intro KY KP hy my hx mx
  intro Δ δ e i hi mi
  have he' : Proves P Δ δ ((R.rename e.names).xCompare (L.rename e).code
      (KY.rename e).code (KP.rename e).code (x.rename e.names) (y.rename e.names)) := by
    simpa only [xCompare_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using he.rename e
  exact ((H.rename e).xCompare_elim (KY.rename e) (KP.rename e)
    (x_typed_rename (R := R) e hx) (e.moded mx) (x_typed_rename (R := R) e hy) (e.moded my) hi mi he').symm

theorem xCompare_trans {x y z : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.channel.logicalType R.probe.carrier)) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (R.xCompare L.code KY.code KP.code x y))
    (hf : Proves P Γ γ (R.xCompare L.code KY.code KP.code y z)) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code x z) := by
  apply H.xCompare_intro KY KP hx mx hz mz
  intro Δ δ e i hi mi
  have he' : Proves P Δ δ ((R.rename e.names).xCompare (L.rename e).code
      (KY.rename e).code (KP.rename e).code (x.rename e.names) (y.rename e.names)) := by
    simpa only [xCompare_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using he.rename e
  have hf' : Proves P Δ δ ((R.rename e.names).xCompare (L.rename e).code
      (KY.rename e).code (KP.rename e).code (y.rename e.names) (z.rename e.names)) := by
    simpa only [xCompare_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using hf.rename e
  have hxy := (H.rename e).xCompare_elim (KY.rename e) (KP.rename e)
    (x_typed_rename (R := R) e hx) (e.moded mx) (x_typed_rename (R := R) e hy) (e.moded my) hi mi he'
  have hyz := (H.rename e).xCompare_elim (KY.rename e) (KP.rename e)
    (x_typed_rename (R := R) e hy) (e.moded my) (x_typed_rename (R := R) e hz) (e.moded mz) hi mi hf'
  exact ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi mi (x_typed_rename (R := R) e hx) (e.moded mx)).equivalent_trans
    ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi mi (x_typed_rename (R := R) e hy) (e.moded my))
    ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi mi (x_typed_rename (R := R) e hz) (e.moded mz)) hxy hyz

theorem xCompare_round {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code x (R.channel.round R.probe.carrier x)) := by
  have hr := H.channel.round_typed H.probe.carrier_sorted H.probe.carrier_mode hx mx
  apply H.xCompare_intro KY KP hx mx hr.1 hr.2
  intro Δ δ e i hi mi
  have hv := (H.rename e).probeFor_typed (KY.rename e) (KP.rename e) hi mi
  have hh := (H.rename e).channel.primitive_round (H.rename e).probe.carrier_sorted
    (H.rename e).probe.carrier_mode (x_typed_rename (R := R) e hx) (e.moded mx) hv.1 hv.2
  simpa only [le,ChannelCode.round_rename,ProbeCode.carrier_rename,channel_rename,
    LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,
    RelationalCode.rename,RelationalCode.channel, ChannelCode.rename, ProbeCode.rename] using hh.symm
end RelationalCode.Formed

namespace RelationalCode
variable (R : RelationalCode S)
theorem x_type_rename (ρ : Nat → Nat) :
    (R.channel.logicalType R.probe.carrier).rename ρ =
      (R.rename ρ).channel.logicalType (R.rename ρ).probe.carrier := by
  simp only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename]
  rfl
theorem p_type_rename (ρ : Nat → Nat) :
    (R.channel.predicateType R.probe.carrier).rename ρ =
      (R.rename ρ).channel.predicateType (R.rename ρ).probe.carrier := by
  simp only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename]
  rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem extStep_formula {i x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data) :
    L.Formula (R.extStep L.code KY.code KP.code i x y) :=
  L.imp_formula (H.xCompare_formula KY KP hx mx hy my)
    (L.iff_formula (H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hx mx)
      (H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hy my))

theorem validStep_formula {x i c : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data) :
    L.Formula (R.validStep L.code KY.code KP.code x i c) :=
  L.imp_formula (H.channel.predCompare_formula H.probe.carrier_sorted H.probe.carrier_mode KY hi mi hc mc)
    (L.iff_formula (H.le_formula KY KP hi mi hx mx) (H.le_formula KY KP hc mc hx mx))

theorem extAtBody_family {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Family (R.channel.logicalType R.probe.carrier) (R.extAtBody L.code KY.code KP.code i x) := by
  intro Δ δ e y hy my
  rw [extAtBody_rename,extAtBody_instantiate]
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using e.typing hi
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using e.typing hx
  have hy' : HasType P Δ y ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using hy
  exact (H.rename e).extStep_formula (KY.rename e) (KP.rename e) hi' (e.moded mi) hx' (e.moded mx) hy' my

theorem extAt_formula {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Formula (R.extAt L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extAtBody_family KY KP hi mi hx mx)

theorem extBody_family {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.channel.logicalType R.probe.carrier) (R.extBody L.code KY.code KP.code i) := by
  intro Δ δ e x hx mx
  rw [extBody_rename,extBody_instantiate]
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using e.typing hi
  have hx' : HasType P Δ x ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using hx
  exact (H.rename e).extAt_formula (KY.rename e) (KP.rename e) hi' (e.moded mi) hx' mx

theorem extensional_formula {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Formula (R.extensional L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extBody_family KY KP hi mi)

theorem validAtBody_family {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.validAtBody L.code KY.code KP.code x i) := by
  intro Δ δ e c hc mc
  rw [validAtBody_rename,validAtBody_instantiate]
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using e.typing hx
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using e.typing hi
  have hc' : HasType P Δ c ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using hc
  exact (H.rename e).validStep_formula (KY.rename e) (KP.rename e) hx' (e.moded mx) hi' (e.moded mi) hc' mc

theorem validAt_formula {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Formula (R.validAt L.code KY.code KP.code x i) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validAtBody_family KY KP hx mx hi mi)

theorem validBody_family {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.validBody L.code KY.code KP.code x) := by
  intro Δ δ e i hi mi
  rw [validBody_rename,validBody_instantiate]
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using e.typing hx
  have hi' : HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using hi
  exact (H.rename e).validAt_formula (KY.rename e) (KP.rename e) hx' (e.moded mx) hi' mi

theorem valid_formula {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Formula (R.valid L.code KY.code KP.code x) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validBody_family KY KP hx mx)
end Formed
end RelationalCode

namespace RelationalCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem extAt_intro {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) → WellModed δ y .data →
      Proves P Δ δ ((R.rename e.names).extStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) (i.rename e.names) (x.rename e.names) y)) :
    Proves P Γ γ (R.extAt L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extAtBody_family KY KP hi mi hx mx)
  intro Δ δ e y hy my
  rw [extAtBody_rename,extAtBody_instantiate]
  exact hh Δ δ e y (by simpa only [x_type_rename] using hy) my

theorem extAt_elim_one {i x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (R.extAt L.code KY.code KP.code i x)) :
    Proves P Γ γ (R.extStep L.code KY.code KP.code i x y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extAtBody_family KY KP hi mi hx mx) hy my hp
  simpa only [extAtBody_instantiate] using hh

theorem extensional_intro {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) → WellModed δ x .data →
      Proves P Δ δ ((R.rename e.names).extAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) (i.rename e.names) x)) :
    Proves P Γ γ (R.extensional L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extBody_family KY KP hi mi)
  intro Δ δ e x hx mx
  rw [extBody_rename,extBody_instantiate]
  exact hh Δ δ e x (by simpa only [x_type_rename] using hx) mx

theorem extensional_elim_one {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (R.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (R.extAt L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extBody_family KY KP hi mi) hx mx hp
  simpa only [extBody_instantiate] using hh

theorem validAt_intro {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) c,
      HasType P Δ c ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) → WellModed δ c .data →
      Proves P Δ δ ((R.rename e.names).validStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) (x.rename e.names) (i.rename e.names) c)) :
    Proves P Γ γ (R.validAt L.code KY.code KP.code x i) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validAtBody_family KY KP hx mx hi mi)
  intro Δ δ e c hc mc
  rw [validAtBody_rename,validAtBody_instantiate]
  exact hh Δ δ e c (by simpa only [p_type_rename] using hc) mc

theorem validAt_elim_one {x i c : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (hp : Proves P Γ γ (R.validAt L.code KY.code KP.code x i)) :
    Proves P Γ γ (R.validStep L.code KY.code KP.code x i c) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have hh := L.all_elim_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validAtBody_family KY KP hx mx hi mi) hc mc hp
  simpa only [validAtBody_instantiate] using hh

theorem valid_intro {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) i,
      HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) → WellModed δ i .data →
      Proves P Δ δ ((R.rename e.names).validAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) (x.rename e.names) i)) :
    Proves P Γ γ (R.valid L.code KY.code KP.code x) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validBody_family KY KP hx mx)
  intro Δ δ e i hi mi
  rw [validBody_rename,validBody_instantiate]
  exact hh Δ δ e i (by simpa only [p_type_rename] using hi) mi

theorem valid_elim_one {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hp : Proves P Γ γ (R.valid L.code KY.code KP.code x)) :
    Proves P Γ γ (R.validAt L.code KY.code KP.code x i) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have hh := L.all_elim_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validBody_family KY KP hx mx) hi mi hp
  simpa only [validBody_instantiate] using hh

theorem extensional_elim {i x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.extensional L.code KY.code KP.code i))
    (hr : Proves P Γ γ (R.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (R.channel.eval R.probe.carrier i x) (R.channel.eval R.probe.carrier i y) := by
  have hh := H.extAt_elim_one KY KP hi mi hx mx hy my (H.extensional_elim_one KY KP hi mi hx mx he)
  have fx := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hx mx
  have fy := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hy my
  exact L.equivalent_of_iff fx fy (L.imp_elim (H.xCompare_formula KY KP hx mx hy my) (L.iff_formula fx fy) hh hr)

theorem valid_elim {x i c : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (hv : Proves P Γ γ (R.valid L.code KY.code KP.code x))
    (he : Proves P Γ γ (R.channel.predCompare L.code KY.code R.probe.carrier i c)) :
    Equivalent P Γ γ (R.le L.code KY.code KP.code i x) (R.le L.code KY.code KP.code c x) := by
  have hh := H.validAt_elim_one KY KP hx mx hi mi hc mc (H.valid_elim_one KY KP hx mx hi mi hv)
  have fi := H.le_formula KY KP hi mi hx mx
  have fc := H.le_formula KY KP hc mc hx mx
  exact L.equivalent_of_iff fi fc (L.imp_elim
    (H.channel.predCompare_formula H.probe.carrier_sorted H.probe.carrier_mode KY hi mi hc mc)
    (L.iff_formula fi fc) hh he)
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem p_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) :
    HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
  simpa only [p_type_rename] using e.typing hi

theorem extStep_respect {i c x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.channel.predCompare L.code KY.code R.probe.carrier i c)) :
    Equivalent P Γ γ (R.extStep L.code KY.code KP.code i x y) (R.extStep L.code KY.code KP.code c x y) := by
  have ex := H.channel.predCompare_elim H.probe.carrier_sorted H.probe.carrier_mode KY hi mi hc mc hx mx he
  have ey := H.channel.predCompare_elim H.probe.carrier_sorted H.probe.carrier_mode KY hi mi hc mc hy my he
  have fi := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hx mx
  have fc := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hc mc hx mx
  have fi' := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hy my
  have fc' := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hc mc hy my
  have fr := H.xCompare_formula KY KP hx mx hy my
  apply L.equivalent_of_iff (H.extStep_formula KY KP hi mi hx mx hy my)
    (H.extStep_formula KY KP hc mc hx mx hy my)
  change Proves P Γ γ (L.iff (L.imp _ (L.iff _ _)) (L.imp _ (L.iff _ _)))
  pts_pl L using [ex,ey]

omit H in
theorem predComparison_rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (e : Embedding P Γ γ Δ δ) {i c : Expr S}
    (he : Proves P Γ γ (R.channel.predCompare L.code KY.code R.probe.carrier i c)) :
    Proves P Δ δ ((R.rename e.names).channel.predCompare (L.rename e).code (KY.rename e).code
      (R.rename e.names).probe.carrier (i.rename e.names) (c.rename e.names)) := by
  simpa only [ChannelCode.predCompare_rename,channel_rename,ProbeCode.carrier_rename,
    LogicSetup.code_rename,QuantifierRoute.code_rename,RelationalCode.rename,ProbeCode.rename,
    RelationalCode.channel,ChannelCode.rename] using he.rename e

theorem extAt_respect {i c x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (R.channel.predCompare L.code KY.code R.probe.carrier i c)) :
    Equivalent P Γ γ (R.extAt L.code KY.code KP.code i x) (R.extAt L.code KY.code KP.code c x) := by
  apply L.all_equivalent_future KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.extAtBody_family KY KP hi mi hx mx)
    (H.extAtBody_family KY KP hc mc hx mx)
  intro Δ δ e y hy my
  rw [extAtBody_rename,extAtBody_rename,extAtBody_instantiate,extAtBody_instantiate]
  exact (H.rename e).extStep_respect (KY.rename e) (KP.rename e)
    (p_typed_rename (R := R) e hi) (e.moded mi) (p_typed_rename (R := R) e hc) (e.moded mc)
    (x_typed_rename (R := R) e hx) (e.moded mx) (by simpa only [x_type_rename] using hy) my
    (predComparison_rename (R := R) KY e he)

/-- Manuscript ExtC: predicate comparison respects the exact Ext formula. -/
theorem extensional_respect {i c : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (R.channel.predCompare L.code KY.code R.probe.carrier i c)) :
    Equivalent P Γ γ (R.extensional L.code KY.code KP.code i) (R.extensional L.code KY.code KP.code c) := by
  apply L.all_equivalent_future KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.extBody_family KY KP hi mi)
    (H.extBody_family KY KP hc mc)
  intro Δ δ e x hx mx
  rw [extBody_rename,extBody_rename,extBody_instantiate,extBody_instantiate]
  exact (H.rename e).extAt_respect (KY.rename e) (KP.rename e)
    (p_typed_rename (R := R) e hi) (e.moded mi) (p_typed_rename (R := R) e hc) (e.moded mc)
    (by simpa only [x_type_rename] using hx) mx (predComparison_rename (R := R) KY e he)
end RelationalCode.Formed
end

universe u
variable {S : Type u}
namespace ThreeCopyCode
variable (R : ThreeCopyCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp,DoubleCode.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename,DoubleCode.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun i => (σ i).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst,DoubleCode.rename_subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise,DoubleCode.instantiate_raise]
theorem firstType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.firstType T).rename ρ = (R.rename ρ).firstType (T.rename ρ) := by
  simp only [firstType,DataWrapper.apply_rename,rename]
theorem firstType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.firstType T).subst σ = (R.subst σ).firstType (T.subst σ) := by
  simp only [firstType,DataWrapper.apply_subst,subst]
theorem middleType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.middleType T).rename ρ = (R.rename ρ).middleType (T.rename ρ) := by
  simp only [middleType,DoubleCode.carrier_rename,firstType_rename,rename]
theorem middleType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.middleType T).subst σ = (R.subst σ).middleType (T.subst σ) := by
  simp only [middleType,DoubleCode.carrier_subst,firstType_subst,subst]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,DoubleCode.carrier_rename,middleType_rename,rename]
theorem carrier_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.carrier T).subst σ = (R.subst σ).carrier (T.subst σ) := by
  simp only [carrier,DoubleCode.carrier_subst,middleType_subst,subst]
theorem bitInner_rename (L : LogicCode S) (T y : Expr S) (ρ : Nat → Nat) :
    (R.bitInner L T y).rename ρ = (R.rename ρ).bitInner (L.rename ρ) (T.rename ρ) (y.rename ρ) := by
  simp only [bitInner,DoubleCode.rec_rename,DoubleCode.bitBody_rename,middleType_rename,firstType_rename,rename]
theorem bitInner_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitInner L T y).subst σ = (R.subst σ).bitInner (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitInner,DoubleCode.rec_subst,DoubleCode.bitBody_subst,middleType_subst,firstType_subst,subst]
theorem bitOuter_rename (L : LogicCode S) (T y : Expr S) (ρ : Nat → Nat) :
    (R.bitOuter L T y).rename ρ = (R.rename ρ).bitOuter (L.rename ρ) (T.rename ρ) (y.rename ρ) := by
  simp only [bitOuter,DoubleCode.bit_rename,middleType_rename,rename]
theorem bitOuter_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitOuter L T y).subst σ = (R.subst σ).bitOuter (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitOuter,DoubleCode.bit_subst,middleType_subst,subst]
theorem observe_rename (L : LogicCode S) (T y a : Expr S) (ρ : Nat → Nat) :
    (R.observe L T y a).rename ρ = (R.rename ρ).observe (L.rename ρ) (T.rename ρ) (y.rename ρ) (a.rename ρ) := by
  simp only [observe,DoubleCode.rec_rename,DoubleCode.recBody_rename,DataWrapper.contraCallback_rename,middleType_rename,firstType_rename,rename]
theorem observe_subst (L : LogicCode S) (T y a : Expr S) (σ : Nat → Expr S) :
    (R.observe L T y a).subst σ = (R.subst σ).observe (L.subst σ) (T.subst σ) (y.subst σ) (a.subst σ) := by
  simp only [observe,DoubleCode.rec_subst,DoubleCode.recBody_subst,DataWrapper.contraCallback_subst,middleType_subst,firstType_subst,subst]
theorem tagged_rename (L : LogicCode S) (t : Fin 3) (T x : Expr S) (ρ : Nat → Nat) :
    (R.tagged L t T x).rename ρ = (R.rename ρ).tagged (L.rename ρ) t (T.rename ρ) (x.rename ρ) := by
  simp only [tagged,DoubleCode.emb_rename,DataWrapper.reencode_rename,middleType_rename,firstType_rename,rename]
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (T x : Expr S) (σ : Nat → Expr S) :
    (R.tagged L t T x).subst σ = (R.subst σ).tagged (L.subst σ) t (T.subst σ) (x.subst σ) := by
  simp only [tagged,DoubleCode.emb_subst,DataWrapper.reencode_subst,middleType_subst,firstType_subst,subst]
end ThreeCopyCode
end PureTypeSystem.Labelled

end OAI
