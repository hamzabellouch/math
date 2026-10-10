import OAI.Computability.TypeSystem.Response

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode
variable (B : SpecializedCode S)
theorem lift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (B.lift L KY KP x).subst σ = (B.subst σ).lift (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [lift,RelationalCode.lift_subst,parameter_subst,relational_subst]
  rfl

def delta (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :=
  B.lift L KY KP (B.observation.tagged L 0 x)
theorem delta_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (B.delta L KY KP x).rename ρ = (B.rename ρ).delta (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [delta,lift_rename,ObservationCode.tagged_rename,observation_rename]
theorem delta_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (B.delta L KY KP x).subst σ = (B.subst σ).delta (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [delta,lift_subst,ObservationCode.tagged_subst,SpecializedCode.subst,ObservationCode.subst]
def shiftPredStep (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :=
  B.relational.channel.eval B.relational.probe.carrier v (B.delta L KY KP x)
def shiftPredBody (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  (B.rename Nat.succ).shiftPredStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (v.rename Nat.succ) (.var 0)
def shiftPred (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.shiftPredBody L KY KP v)
theorem shiftPredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.shiftPredStep L KY KP v x).rename ρ = (B.rename ρ).shiftPredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [shiftPredStep,ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename,relational,RelationalCode.channel,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem shiftPredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.shiftPredStep L KY KP v x).subst σ = (B.subst σ).shiftPredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [shiftPredStep,ChannelCode.eval_subst,ProbeCode.carrier_subst,delta_subst,relational,RelationalCode.channel,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem shiftPredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.shiftPredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).shiftPredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [shiftPredBody,shiftPredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem shiftPredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.shiftPredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).shiftPredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [shiftPredBody,shiftPredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem shiftPredBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.shiftPredBody L KY KP v).instantiate x = B.shiftPredStep L KY KP v x := by
  simp only [shiftPredBody,Expr.instantiate,shiftPredStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem shiftPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.shiftPred L KY KP v).rename ρ = (B.rename ρ).shiftPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [shiftPred,ChannelCode.pred_rename,ProbeCode.carrier_rename,shiftPredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem shiftPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.shiftPred L KY KP v).subst σ = (B.subst σ).shiftPred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [shiftPred,ChannelCode.pred_subst,ProbeCode.carrier_subst,shiftPredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl

def qStep (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :=
  L.imp (B.relational.extensional L KY KP i) (L.imp (B.relational.le L KY KP i x) (B.relational.channel.eval B.relational.probe.carrier i (B.delta L KY KP x)))
def qBody (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  (B.rename Nat.succ).qStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (i.rename Nat.succ) (.var 0)
def diagonalQ (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  KP.all B.xPredType (B.qBody L KY KP i)
theorem qStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.qStep L KY KP v x).rename ρ = (B.rename ρ).qStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [qStep,LogicCode.imp_rename,RelationalCode.extensional_rename,RelationalCode.le_rename,ChannelCode.eval_rename,delta_rename,ProbeCode.carrier_rename,relational,RelationalCode.channel,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem qStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.qStep L KY KP v x).subst σ = (B.subst σ).qStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [qStep,LogicCode.imp_subst,RelationalCode.extensional_subst,RelationalCode.le_subst,ChannelCode.eval_subst,delta_subst,ProbeCode.carrier_subst,relational,RelationalCode.channel,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem qBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.qBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).qBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [qBody,qStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem qBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.qBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).qBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [qBody,qStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem qBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.qBody L KY KP v).instantiate x = B.qStep L KY KP v x := by
  simp only [qBody,Expr.instantiate,qStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem diagonalQ_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (B.diagonalQ L KY KP i).rename ρ = (B.rename ρ).diagonalQ (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [diagonalQ,QuantifierCode.all_rename,xPredType_rename,qBody_rename]
theorem diagonalQ_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (B.diagonalQ L KY KP i).subst σ = (B.subst σ).diagonalQ (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [diagonalQ,QuantifierCode.all_subst,xPredType_subst,qBody_subst]
def diagonalBody (L : LogicCode S) (KY KP : QuantifierCode S) :=
  (L.rename Nat.succ).neg ((B.rename Nat.succ).diagonalQ (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (.var 0))
def diagonalPred (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.channel.pred B.relational.probe.carrier (B.diagonalBody L KY KP)
theorem diagonalBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.diagonalBody L KY KP).rename (Expr.liftRen ρ) = (B.rename ρ).diagonalBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [diagonalBody,LogicCode.neg_rename,diagonalQ_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem diagonalBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.diagonalBody L KY KP).subst (Expr.liftSub σ) = (B.subst σ).diagonalBody (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [diagonalBody,LogicCode.neg_subst,diagonalQ_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem diagonalBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) :
    (B.diagonalBody L KY KP).instantiate x = L.neg (B.diagonalQ L KY KP x) := by
  simp only [diagonalBody,Expr.instantiate,LogicCode.neg_subst,diagonalQ_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst,Expr.single]
theorem diagonalPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.diagonalPred L KY KP).rename ρ = (B.rename ρ).diagonalPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [diagonalPred,ChannelCode.pred_rename,ProbeCode.carrier_rename,diagonalBody_rename,relational,rename,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  rfl
theorem diagonalPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.diagonalPred L KY KP).subst σ = (B.subst σ).diagonalPred (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [diagonalPred,ChannelCode.pred_subst,ProbeCode.carrier_subst,diagonalBody_subst,relational,subst,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  rfl
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem delta_typed {x : Expr S} (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    HasType P Γ (B.delta L.code KY.code KP.code x) B.xType ∧ WellModed γ (B.delta L.code KY.code KP.code x) .data := by
  have ht := H.tagged_typed 0 hx mx
  exact H.lift_typed KY KP ht.1 ht.2

theorem delta_valid {x : Expr S} (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Proves P Γ γ (B.relational.valid L.code KY.code KP.code (B.delta L.code KY.code KP.code x)) := by
  have ht := H.tagged_typed 0 hx mx
  exact H.lift_valid KY KP ht.1 ht.2

theorem delta_congr {x y : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code (B.delta L.code KY.code KP.code x) (B.delta L.code KY.code KP.code y)) := by
  have tx := H.tagged_typed 0 hx mx
  have ty := H.tagged_typed 0 hy my
  exact H.lift_congr KY KP tx.1 tx.2 ty.1 ty.2 ((H.relation_tagged_same KY KP 0 hx mx hy my).2.prove he)

theorem shiftPredStep_formula {v x : Expr S} 
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.shiftPredStep L.code KY.code KP.code v x) := by
  have ht := H.delta_typed KY KP hx mx
  exact H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv ht.1 ht.2

theorem shiftPredBody_family {v : Expr S} 
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    : L.Family B.xType (B.shiftPredBody L.code KY.code KP.code v) := by
  intro Δ δ e x hx mx
  rw [shiftPredBody_rename,shiftPredBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).xPredType := by
    exact xPred_typed_rename e hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).shiftPredStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' mx

theorem shiftPred_typed {v : Expr S} (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data) :
    HasType P Γ (B.shiftPred L.code KY.code KP.code v) B.xPredType ∧ WellModed γ (B.shiftPred L.code KY.code KP.code v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.shiftPredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs)

theorem shiftPred_evaluation {v x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) x)
      (B.shiftPredStep L.code KY.code KP.code v (B.relational.channel.round B.relational.probe.carrier x)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.shiftPredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs) hx mx
  simpa only [shiftPredBody_instantiate,shiftPred] using he

end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem qStep_formula {x i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    L.Formula (B.qStep L.code KY.code KP.code x i) := by
  have dx := H.delta_typed KY KP hx mx
  exact L.imp_formula (H.relational_formed.extensional_formula KY KP hi mi)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2))

theorem qBody_family {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    L.Family B.xPredType (B.qBody L.code KY.code KP.code x) := by
  intro Δ δ e i hi mi
  rw [qBody_rename,qBody_instantiate]
  exact (H.rename e).qStep_formula (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx)
    (by simpa only [xPredType_rename] using hi) mi

theorem diagonalQ_formula {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    L.Formula (B.diagonalQ L.code KY.code KP.code x) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted)
    (H.relational_formed.channel.predicate_mode H.relational_formed.probe.carrier_mode)
    (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted s hs) (H.qBody_family KY KP hx mx)

theorem diagonalQ_intro {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) i,
      HasType P Δ i (B.rename e.names).xPredType → WellModed δ i .data →
      Proves P Δ δ ((B.rename e.names).qStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (x.rename e.names) i)) : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted)
    (H.relational_formed.channel.predicate_mode H.relational_formed.probe.carrier_mode)
    (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted s hs) (H.qBody_family KY KP hx mx)
  intro Δ δ e i hi mi
  rw [qBody_rename,qBody_instantiate]
  exact hh Δ δ e i (by change HasType P Δ i (B.xPredType.rename e.names) at hi; simpa only [xPredType_rename] using hi) mi

theorem diagonalQ_elim_one {x i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hp : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x)) :
    Proves P Γ γ (B.qStep L.code KY.code KP.code x i) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have he := L.all_elim_family KP (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted)
    (H.relational_formed.channel.predicate_mode H.relational_formed.probe.carrier_mode)
    (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted s hs) (H.qBody_family KY KP hx mx) hi mi hp
  simpa only [qBody_instantiate] using he

theorem diagonalQ_elim {x i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hp : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x))
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code i x)) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code x)) := by
  have dx := H.delta_typed KY KP hx mx
  have fe := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2
  have fl := H.relational_formed.le_formula KY KP hi mi hx mx
  exact L.imp_elim fl fe (L.imp_elim (H.relational_formed.extensional_formula KY KP hi mi) (L.imp_formula fl fe)
    (H.diagonalQ_elim_one KY KP hx mx hi mi hp) he) ht

theorem diagonalBody_family : L.Family B.xType (B.diagonalBody L.code KY.code KP.code) := by
  intro Δ δ e x hx mx
  rw [diagonalBody_rename,diagonalBody_instantiate]
  exact (L.rename e).neg_formula ((H.rename e).diagonalQ_formula (KY.rename e) (KP.rename e) (by simpa only [xType_rename] using hx) mx)

theorem diagonalPred_typed : HasType P Γ (B.diagonalPred L.code KY.code KP.code) B.xPredType ∧ WellModed γ (B.diagonalPred L.code KY.code KP.code) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.diagonalBody_family KY KP) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs)

theorem diagonalPred_evaluation {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.diagonalPred L.code KY.code KP.code) x)
      (L.neg (B.diagonalQ L.code KY.code KP.code (B.relational.channel.round B.relational.probe.carrier x))) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.diagonalBody_family KY KP) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs) hx mx
  simpa only [diagonalBody_instantiate,diagonalPred,LogicSetup.code_neg] using he
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem qConsequence_respect {x y i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y))
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ
      (L.imp (B.relational.le L.code KY.code KP.code i x) (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code x)))
      (L.imp (B.relational.le L.code KY.code KP.code i y) (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code y))) := by
  have dx := H.delta_typed KY KP hx mx
  have dy := H.delta_typed KY KP hy my
  have ee := H.relational_formed.extensional_elim KY KP hi mi dx.1 dx.2 dy.1 dy.2 hex (H.delta_congr KY KP hx mx hy my he)
  exact L.imp_equivalent (H.relational_formed.le_formula KY KP hi mi hx mx) (H.relational_formed.le_formula KY KP hi mi hy my)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dy.1 dy.2)
    (H.relational_formed.xCompare_elim KY KP hx mx hy my hi mi he) ee

theorem qStep_respect {x y i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (B.qStep L.code KY.code KP.code x i) (B.qStep L.code KY.code KP.code y i) := by
  have dx := H.delta_typed KY KP hx mx
  have dy := H.delta_typed KY KP hy my
  apply L.guarded_equivalent_future (H.relational_formed.extensional_formula KY KP hi mi)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2))
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi hy my)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dy.1 dy.2))
  intro Δ δ e hex
  simp only [RelationalCode.extensional_rename] at hex
  have he' := he.rename e
  simp only [RelationalCode.xCompare_rename] at he'
  simpa only [LogicSetup.imp_rename,ChannelCode.eval_rename,delta_rename,ProbeCode.carrier_rename,RelationalCode.le_rename,
    relational_rename,LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,relational,SpecializedCode.rename,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).qConsequence_respect (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx)
      (x_typed_rename (B := B) e hy) (e.moded my) (xPred_typed_rename e hi) (e.moded mi) he' hex

theorem diagonalQ_respect {x y : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (B.diagonalQ L.code KY.code KP.code x) (B.diagonalQ L.code KY.code KP.code y) := by
  apply L.all_equivalent_future KP (H.relational_formed.channel.predicate_sorted H.relational_formed.probe.carrier_sorted)
    (H.relational_formed.channel.predicate_mode H.relational_formed.probe.carrier_mode) (H.qBody_family KY KP hx mx) (H.qBody_family KY KP hy my)
  intro Δ δ e i hi mi
  rw [qBody_rename,qBody_rename,qBody_instantiate,qBody_instantiate]
  have he' := he.rename e
  simp only [RelationalCode.xCompare_rename] at he'
  exact (H.rename e).qStep_respect (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx)
    (x_typed_rename (B := B) e hy) (e.moded my) (by change HasType P Δ i (B.xPredType.rename e.names) at hi; simpa only [xPredType_rename] using hi) mi he'
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem diagonalPred_exact {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.diagonalPred L.code KY.code KP.code) x)
      (L.neg (B.diagonalQ L.code KY.code KP.code x)) := by
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have iv := H.diagonalPred_typed KY KP
  have ee := L.neg_equivalent (H.diagonalQ_formula KY KP rx.1 rx.2) (H.diagonalQ_formula KY KP hx mx)
    (H.diagonalQ_respect KY KP hx mx rx.1 rx.2 (H.relational_formed.xCompare_round KY KP hx mx)).symm
  exact (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx).equivalent_trans
    (L.neg_formula (H.diagonalQ_formula KY KP rx.1 rx.2)) (L.neg_formula (H.diagonalQ_formula KY KP hx mx)) (H.diagonalPred_evaluation KY KP hx mx) ee

theorem diagonalPred_respect {x y : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.diagonalPred L.code KY.code KP.code) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.diagonalPred L.code KY.code KP.code) y) := by
  have iv := H.diagonalPred_typed KY KP
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my
  have f2 := L.neg_formula (H.diagonalQ_formula KY KP hx mx)
  have f3 := L.neg_formula (H.diagonalQ_formula KY KP hy my)
  have e1 := H.diagonalPred_exact KY KP hx mx
  have e3 := H.diagonalPred_exact KY KP hy my
  have e2 := L.neg_equivalent (H.diagonalQ_formula KY KP hx mx) (H.diagonalQ_formula KY KP hy my) (H.diagonalQ_respect KY KP hx mx hy my he)
  exact f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 e1 e2) e3.symm

theorem diagonalPred_extStep {x y : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    :
    Proves P Γ γ (B.relational.extStep L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code) x y) := by
  have iv := H.diagonalPred_typed KY KP
  apply L.imp_intro_future (H.relational_formed.xCompare_formula KY KP hx mx hy my)
    (L.iff_formula (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my))
  intro Δ δ e he
  simp only [RelationalCode.xCompare_rename] at he
  simp only [LogicSetup.iff_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,diagonalPred_rename]
  have hx' := x_typed_rename (B := B) e hx
  have hy' := x_typed_rename (B := B) e hy
  have iv' := (H.rename e).diagonalPred_typed (KY.rename e) (KP.rename e)
  have ee := (H.rename e).diagonalPred_respect (KY.rename e) (KP.rename e) hx' (e.moded mx) hy' (e.moded my) he
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hx' (e.moded mx))
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hy' (e.moded my)) ee

theorem diagonalPred_extAt {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    :
    Proves P Γ γ (B.relational.extAt L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code) x) := by
  have iv := H.diagonalPred_typed KY KP
  apply H.relational_formed.extAt_intro KY KP iv.1 iv.2 hx mx
  intro Δ δ e y hy my
  simp only [diagonalPred_rename]
  exact (H.rename e).diagonalPred_extStep (KY.rename e) (KP.rename e)
    (x_typed_rename (B := B) e hx) (e.moded mx) hy my

theorem diagonalPred_extensional
    :
    Proves P Γ γ (B.relational.extensional L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code)) := by
  have iv := H.diagonalPred_typed KY KP
  apply H.relational_formed.extensional_intro KY KP iv.1 iv.2
  intro Δ δ e x hx mx
  simp only [diagonalPred_rename]
  exact (H.rename e).diagonalPred_extAt (KY.rename e) (KP.rename e) hx mx
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem shiftPred_exact {v x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) x)
      (B.relational.channel.eval B.relational.probe.carrier v (B.delta L.code KY.code KP.code x)) := by
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have dx := H.delta_typed KY KP hx mx
  have dr := H.delta_typed KY KP rx.1 rx.2
  have iv := H.shiftPred_typed KY KP hv mv
  have ee := H.relational_formed.extensional_elim KY KP hv mv dx.1 dx.2 dr.1 dr.2 hr
    (H.delta_congr KY KP hx mx rx.1 rx.2 (H.relational_formed.xCompare_round KY KP hx mx))
  exact (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx).equivalent_trans
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dr.1 dr.2)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dx.1 dx.2)
    (H.shiftPred_evaluation KY KP hv mv hx mx) ee.symm

theorem shiftPred_respect {v x y : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) y) := by
  have dx := H.delta_typed KY KP hx mx
  have dy := H.delta_typed KY KP hy my
  have iv := H.shiftPred_typed KY KP hv mv
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my
  have f2 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dx.1 dx.2
  have f3 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dy.1 dy.2
  have e1 := H.shiftPred_exact KY KP hv mv hx mx hr
  have e3 := H.shiftPred_exact KY KP hv mv hy my hr
  have e2 := H.relational_formed.extensional_elim KY KP hv mv dx.1 dx.2 dy.1 dy.2 hr (H.delta_congr KY KP hx mx hy my he)
  exact f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 e1 e2) e3.symm

theorem shiftPred_extStep {v x y : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extStep L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code v) x y) := by
  have iv := H.shiftPred_typed KY KP hv mv
  apply L.imp_intro_future (H.relational_formed.xCompare_formula KY KP hx mx hy my)
    (L.iff_formula (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my))
  intro Δ δ e he
  simp only [RelationalCode.xCompare_rename] at he
  simp only [LogicSetup.iff_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,shiftPred_rename]
  have hr' := hr.rename e
  simp only [RelationalCode.extensional_rename] at hr'
  have hv' := xPred_typed_rename e hv
  have hx' := x_typed_rename (B := B) e hx
  have hy' := x_typed_rename (B := B) e hy
  have iv' := (H.rename e).shiftPred_typed (KY.rename e) (KP.rename e) hv' (e.moded mv)
  have ee := (H.rename e).shiftPred_respect (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' (e.moded mx) hy' (e.moded my) hr' he
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hx' (e.moded mx))
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hy' (e.moded my)) ee

theorem shiftPred_extAt {v x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extAt L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code v) x) := by
  have iv := H.shiftPred_typed KY KP hv mv
  apply H.relational_formed.extAt_intro KY KP iv.1 iv.2 hx mx
  intro Δ δ e y hy my
  simp only [shiftPred_rename]
  have hr' := hr.rename e
  simp only [RelationalCode.extensional_rename] at hr'
  exact (H.rename e).shiftPred_extStep (KY.rename e) (KP.rename e) (xPred_typed_rename e hv) (e.moded mv)
    (x_typed_rename (B := B) e hx) (e.moded mx) hy my hr'

theorem shiftPred_extensional {v : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extensional L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code v)) := by
  have iv := H.shiftPred_typed KY KP hv mv
  apply H.relational_formed.extensional_intro KY KP iv.1 iv.2
  intro Δ δ e x hx mx
  simp only [shiftPred_rename]
  have hr' := hr.rename e
  simp only [RelationalCode.extensional_rename] at hr'
  exact (H.rename e).shiftPred_extAt (KY.rename e) (KP.rename e) (xPred_typed_rename e hv) (e.moded mv) hx mx hr'
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem edge_wrong_tag (t : Bool) (u : Fin 3) (htu : u ≠ (if t then 2 else 1)) {y x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Proves P Γ γ (L.neg (B.edge L.code KY.code KP.code t y (B.observation.tagged L.code u x))) := by
  have ht := H.observation.tagged_typed u hx mx
  apply L.imp_intro_future (H.edge_formula KY KP t hy my ht.1 ht.2) L.bottom_formula
  intro Δ δ e he
  simp only [edge_rename,ObservationCode.tagged_rename] at he
  rw [LogicSetup.bottom_rename]
  have hy' := y_typed_rename (B := B) e hy
  have hx' := x_typed_rename (B := B) e hx
  have ht' := (H.rename e).observation.tagged_typed u hx' (e.moded mx)
  apply (H.rename e).edge_witness_elim (KY.rename e) (KP.rename e) t hy' (e.moded my) ht'.1 ht'.2 (L.rename e).bottom_formula he
  intro Θ θ f a ha ma hp
  rw [LogicSetup.bottom_rename]
  simp only [ObservationCode.tagged_rename] at hp
  have ht0 := ((H.rename e).rename f).observation.tagged_typed 0 ha ma
  have hta := ((H.rename e).rename f).observation.tagged_typed (if t then 2 else 1) ha ma
  have hx'' := x_typed_rename (B := B.rename e.names) f hx'
  have htx := ((H.rename e).rename f).observation.tagged_typed u hx'' (f.moded (e.moded mx))
  have fy := ((H.rename e).rename f).relation_formula ((KY.rename e).rename f) ((KP.rename e).rename f)
    (y_typed_rename (B := B.rename e.names) f hy') (f.moded (e.moded my)) ht0.1 ht0.2
  have fx := ((H.rename e).rename f).relation_formula ((KY.rename e).rename f) ((KP.rename e).rename f) htx.1 htx.2 hta.1 hta.2
  have hrel := ((L.rename e).rename f).conj_right fy fx hp
  have hn := ((H.rename e).rename f).relation_tagged_distinct ((KY.rename e).rename f) ((KP.rename e).rename f)
    u (if t then 2 else 1) htu hx'' (f.moded (e.moded mx)) ha ma
  exact ((L.rename e).rename f).imp_elim fx ((L.rename e).rename f).bottom_formula hn hrel

theorem edge_to_tagged (t : Bool) {y x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.edge L.code KY.code KP.code t y (B.observation.tagged L.code (if t then 2 else 1) x))) :
    Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x)) := by
  have hxt := H.observation.tagged_typed (if t then 2 else 1) hx mx
  have hx0 := H.observation.tagged_typed 0 hx mx
  apply H.edge_witness_elim KY KP t hy my hxt.1 hxt.2 (H.relation_formula KY KP hy my hx0.1 hx0.2) he
  intro Δ δ e a ha ma hp
  simp only [relation_rename,ObservationCode.tagged_rename] at hp ⊢
  have hy' := y_typed_rename (B := B) e hy
  have hx' := x_typed_rename (B := B) e hx
  have hxt' := (H.rename e).observation.tagged_typed (if t then 2 else 1) hx' (e.moded mx)
  have hx0' := (H.rename e).observation.tagged_typed 0 hx' (e.moded mx)
  have hat := (H.rename e).observation.tagged_typed (if t then 2 else 1) ha ma
  have ha0 := (H.rename e).observation.tagged_typed 0 ha ma
  have fy := (H.rename e).relation_formula (KY.rename e) (KP.rename e) hy' (e.moded my) ha0.1 ha0.2
  have fx := (H.rename e).relation_formula (KY.rename e) (KP.rename e) hxt'.1 hxt'.2 hat.1 hat.2
  have ey := (L.rename e).conj_left fy fx hp
  have ex := (L.rename e).conj_right fy fx hp
  have eu := ((H.rename e).relation_tagged_same (KY.rename e) (KP.rename e) (if t then 2 else 1) hx' (e.moded mx) ha ma).1.prove ex
  have eux := (H.rename e).relational_formed.xCompare_symm (KY.rename e) (KP.rename e) hx' (e.moded mx) ha ma eu
  have e0 := ((H.rename e).relation_tagged_same (KY.rename e) (KP.rename e) 0 ha ma hx' (e.moded mx)).2.prove eux
  exact (H.rename e).relation_trans (KY.rename e) (KP.rename e) hy' (e.moded my) ha0.1 ha0.2 hx0'.1 hx0'.2 ey e0

theorem edge_from_tagged (t : Bool) {y x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x))) :
    Proves P Γ γ (B.edge L.code KY.code KP.code t y (B.observation.tagged L.code (if t then 2 else 1) x)) := by
  have ht := H.observation.tagged_typed (if t then 2 else 1) hx mx
  exact H.edge_witness_intro KY KP t hy my ht.1 ht.2 hx mx he (H.relation_refl KY KP ht.1 ht.2)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem formEx_elim {v z F : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hF : L.Formula F)
    (he : Proves P Γ γ (L.code.ex KY.code B.yType (B.formExBody L.code KY.code KP.code v z)))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y (B.rename e.names).yType → WellModed δ y .data →
      Proves P Δ δ ((B.rename e.names).edge (L.rename e).code (KY.rename e).code (KP.rename e).code false y (z.rename e.names)) →
      Proves P Δ δ ((B.rename e.names).ev (v.rename e.names) y) → Proves P Δ δ (F.rename e.names)) :
    Proves P Γ γ F := by
  apply L.ex_elim KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv hz mz) hF he
  intro Δ δ e y hy my hp
  simp only [formExBody_rename,formExBody_instantiate] at hp
  have hy' : HasType P Δ y (B.rename e.names).yType := by simpa only [yType_rename] using hy
  have fe := (H.rename e).edge_formula (KY.rename e) (KP.rename e) false hy' my (y_typed_rename (B := B) e hz) (e.moded mz)
  have fp := (H.rename e).ev_formula (v_typed_rename (B := B) e hv) (e.moded mv) hy' my
  exact hh Δ δ e y hy' my ((L.rename e).conj_left fe fp hp) ((L.rename e).conj_right fe fp hp)

theorem formEx_right_false {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Proves P Γ γ (L.neg (L.code.ex KY.code B.yType
      (B.formExBody L.code KY.code KP.code v (B.observation.tagged L.code 2 x)))) := by
  have ht := H.observation.tagged_typed 2 hx mx
  apply L.imp_intro_future (L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv ht.1 ht.2)) L.bottom_formula
  intro Δ δ e he
  simp only [LogicCode.ex_rename,formExBody_rename,ObservationCode.tagged_rename,yType_rename] at he
  rw [LogicSetup.bottom_rename]
  have hx' := x_typed_rename (B := B) e hx
  have ht' := (H.rename e).observation.tagged_typed 2 hx' (e.moded mx)
  apply (H.rename e).formEx_elim (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv) ht'.1 ht'.2 (L.rename e).bottom_formula he
  intro Θ θ f y hy my hed _
  rw [LogicSetup.bottom_rename]
  simp only [ObservationCode.tagged_rename] at hed
  have hx'' := x_typed_rename (B := B.rename e.names) f hx'
  have ht'' := ((H.rename e).rename f).observation.tagged_typed 2 hx'' (f.moded (e.moded mx))
  have hn := ((H.rename e).rename f).edge_wrong_tag ((KY.rename e).rename f) ((KP.rename e).rename f) false 2 (by decide) hy my hx'' (f.moded (e.moded mx))
  exact ((L.rename e).rename f).imp_elim (((H.rename e).rename f).edge_formula ((KY.rename e).rename f) ((KP.rename e).rename f) false hy my ht''.1 ht''.2) ((L.rename e).rename f).bottom_formula hn hed

theorem pair_left_forward {v a x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hg : Proves P Γ γ (B.good L.code KY.code KP.code v))
    (hp : Proves P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) (B.observation.tagged L.code 1 x))) :
    Proves P Γ γ (B.ev v (B.observation.tagged L.code 0 x)) := by
  have ht := H.observation.tagged_typed 1 hx mx
  have h₀ := H.observation.tagged_typed 0 hx mx
  have fp := L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv ht.1 ht.2)
  have fq := H.edge_formula KY KP true ha ma ht.1 ht.2
  have hp' := (H.pair_evaluation KY KP hv mv ha ma ht.1 ht.2).1.prove hp
  rw [H.pairForm_eq KY KP] at hp'
  have he := L.select_disj_left fp fp fq fq fp.equivalent_refl fq.equivalent_refl hp'
    (H.edge_wrong_tag KY KP true 1 (by decide) ha ma hx mx)
  apply H.formEx_elim KY KP hv mv ht.1 ht.2 (H.ev_formula hv mv h₀.1 h₀.2) he
  intro Δ δ e y hy my hed hpv
  simp only [ev_rename,ObservationCode.tagged_rename]
  simp only [ObservationCode.tagged_rename] at hed
  have hx' := x_typed_rename (B := B) e hx
  have h₀' := (H.rename e).observation.tagged_typed 0 hx' (e.moded mx)
  have hg' := hg.rename e
  simp only [good_rename] at hg'
  have er := (H.rename e).edge_to_tagged (KY.rename e) (KP.rename e) false hy my hx' (e.moded mx) hed
  exact ((H.rename e).relation_elim (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv) hy my h₀'.1 h₀'.2 er hg').1.prove hpv

theorem pair_left_backward {v a x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.ev v (B.observation.tagged L.code 0 x))) :
    Proves P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) (B.observation.tagged L.code 1 x)) := by
  have ht := H.observation.tagged_typed 1 hx mx
  have h₀ := H.observation.tagged_typed 0 hx mx
  apply (H.pair_evaluation KY KP hv mv ha ma ht.1 ht.2).2.prove
  rw [H.pairForm_eq KY KP]
  have fp := L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv ht.1 ht.2)
  have fq := H.edge_formula KY KP true ha ma ht.1 ht.2
  have he := H.edge_from_tagged KY KP false h₀.1 h₀.2 hx mx (H.relation_refl KY KP h₀.1 h₀.2)
  have hpe := H.formEx_intro KY KP hv mv ht.1 ht.2 h₀.1 h₀.2 he hp
  pts_pl L using [hpe]

theorem pair_right_forward {v a x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) (B.observation.tagged L.code 2 x))) :
    Proves P Γ γ (B.relation L.code KY.code KP.code a (B.observation.tagged L.code 0 x)) := by
  have ht := H.observation.tagged_typed 2 hx mx
  have fp := L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv ht.1 ht.2)
  have fq := H.edge_formula KY KP true ha ma ht.1 ht.2
  have hp' := (H.pair_evaluation KY KP hv mv ha ma ht.1 ht.2).1.prove hp
  rw [H.pairForm_eq KY KP] at hp'
  have he := L.select_disj_right fp fp fq fq fp.equivalent_refl fq.equivalent_refl hp' (H.formEx_right_false KY KP hv mv hx mx)
  exact H.edge_to_tagged KY KP true ha ma hx mx he

theorem pair_right_backward {v a x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.relation L.code KY.code KP.code a (B.observation.tagged L.code 0 x))) :
    Proves P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) (B.observation.tagged L.code 2 x)) := by
  have ht := H.observation.tagged_typed 2 hx mx
  apply (H.pair_evaluation KY KP hv mv ha ma ht.1 ht.2).2.prove
  rw [H.pairForm_eq KY KP]
  have fp := L.ex_formula KY H.y_sorted H.y_mode (H.formExBody_family KY KP hv mv ht.1 ht.2)
  have fq := H.edge_formula KY KP true ha ma ht.1 ht.2
  have he := H.edge_from_tagged KY KP true ha ma hx mx hp
  pts_pl L using [he]
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem part_respect {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hresp : Proves P Γ γ (B.response L.code KY.code KP.code v))
    {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (B.observation.ae L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.ev (B.part L.code KY.code KP.code v) y) (B.ev (B.part L.code KY.code KP.code v) z) := by
  have hp := H.part_typed KY KP hv mv
  have ey := H.part_exact KY KP hv mv hy my hresp
  have ez := H.part_exact KY KP hv mv hz mz hresp
  have er := H.relation_backward KY KP hy my hz mz he
  have ec := H.response_elim KY KP hv mv hy my hz mz hresp er
  have fy := H.ev_formula hp.1 hp.2 hy my
  have fz := H.ev_formula hp.1 hp.2 hz mz
  have gy := H.diamond_formula KY KP hv mv hy my
  have gz := H.diamond_formula KY KP hv mv hz mz
  exact fy.equivalent_trans gz fz (fy.equivalent_trans gy gz ey ec) ez.symm

theorem part_gStep {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hresp : Proves P Γ γ (B.response L.code KY.code KP.code v))
    {y z : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    Proves P Γ γ (B.gStep L.code KY.code KP.code (B.part L.code KY.code KP.code v) y z) := by
  have hp := H.part_typed KY KP hv mv
  apply L.imp_intro_future (H.observation.ae_formula KY KP hy my hz mz)
    (L.iff_formula (H.ev_formula hp.1 hp.2 hy my) (H.ev_formula hp.1 hp.2 hz mz))
  intro Δ δ e he
  have hr := hresp.rename e
  simp only [response_rename] at hr
  simp only [ObservationCode.ae_rename] at he
  rw [LogicSetup.iff_rename,ev_rename,ev_rename,part_rename]
  have hp' := (H.rename e).part_typed (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv)
  have hy' := y_typed_rename (B := B) e hy
  have hz' := y_typed_rename (B := B) e hz
  exact (L.rename e).iff_of_equivalent ((H.rename e).ev_formula hp'.1 hp'.2 hy' (e.moded my))
    ((H.rename e).ev_formula hp'.1 hp'.2 hz' (e.moded mz))
    ((H.rename e).part_respect (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv) hr hy' (e.moded my) hz' (e.moded mz) he)

theorem part_gAt {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hresp : Proves P Γ γ (B.response L.code KY.code KP.code v))
    {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Proves P Γ γ (B.gAt L.code KY.code KP.code (B.part L.code KY.code KP.code v) y) := by
  have hp := H.part_typed KY KP hv mv
  apply H.gAt_intro KY KP hp.1 hp.2 hy my
  intro Δ δ e z hz mz
  have hr := hresp.rename e
  simp only [response_rename] at hr
  rw [part_rename]
  exact (H.rename e).part_gStep (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv) hr
    (y_typed_rename (B := B) e hy) (e.moded my) hz mz

theorem part_propertyG {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hresp : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.propertyG L.code KY.code KP.code (B.part L.code KY.code KP.code v)) := by
  have hp := H.part_typed KY KP hv mv
  apply H.propertyG_intro KY KP hp.1 hp.2
  intro Δ δ e y hy my
  have hr := hresp.rename e
  simp only [response_rename] at hr
  rw [part_rename]
  exact (H.rename e).part_gAt (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv) hr hy my

theorem part_good {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hresp : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.good L.code KY.code KP.code (B.part L.code KY.code KP.code v)) := by
  have hp := H.part_typed KY KP hv mv
  exact H.good_backward KY KP hp.1 hp.2 (H.part_propertyG KY KP hv mv hresp)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem pair_left_equivalent {v a x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hg : Proves P Γ γ (B.good L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) (B.observation.tagged L.code 1 x))
      (B.ev v (B.observation.tagged L.code 0 x)) := by
  have hp := H.pair_typed KY KP hv mv ha ma
  have ht := H.tagged_typed 1 hx mx
  have h0 := H.tagged_typed 0 hx mx
  apply (H.ev_formula hp.1 hp.2 ht.1 ht.2).equivalent_of_future
    (H.ev_formula hv mv h0.1 h0.2)
  · intro Δ δ e he
    simp only [ev_rename,pair_rename,ObservationCode.tagged_rename] at he
    simp only [ev_rename,ObservationCode.tagged_rename]
    have hg' := hg.rename e
    simp only [good_rename] at hg'
    exact (H.rename e).pair_left_forward (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv)
      (y_typed_rename (B := B) e ha) (e.moded ma) (x_typed_rename (B := B) e hx) (e.moded mx) hg' he
  · intro Δ δ e he
    simp only [ev_rename,ObservationCode.tagged_rename] at he
    simp only [ev_rename,pair_rename,ObservationCode.tagged_rename]
    exact (H.rename e).pair_left_backward (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv)
      (y_typed_rename (B := B) e ha) (e.moded ma) (x_typed_rename (B := B) e hx) (e.moded mx) he

theorem pair_right_equivalent {v a x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code v a) (B.observation.tagged L.code 2 x))
      (B.relation L.code KY.code KP.code a (B.observation.tagged L.code 0 x)) := by
  have hp := H.pair_typed KY KP hv mv ha ma
  have ht := H.tagged_typed 2 hx mx
  have h0 := H.tagged_typed 0 hx mx
  apply (H.ev_formula hp.1 hp.2 ht.1 ht.2).equivalent_of_future
    (H.relation_formula KY KP ha ma h0.1 h0.2)
  · intro Δ δ e he
    simp only [ev_rename,pair_rename,ObservationCode.tagged_rename] at he
    simp only [relation_rename,ObservationCode.tagged_rename]
    exact (H.rename e).pair_right_forward (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv)
      (y_typed_rename (B := B) e ha) (e.moded ma) (x_typed_rename (B := B) e hx) (e.moded mx) he
  · intro Δ δ e he
    simp only [relation_rename,ObservationCode.tagged_rename] at he
    simp only [ev_rename,pair_rename,ObservationCode.tagged_rename]
    exact (H.rename e).pair_right_backward (KY.rename e) (KP.rename e) (v_typed_rename (B := B) e hv) (e.moded mv)
      (y_typed_rename (B := B) e ha) (e.moded ma) (x_typed_rename (B := B) e hx) (e.moded mx) he

theorem responsePair_left {v a x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) a) (B.observation.tagged L.code 1 x))
      (B.diamond L.code KY.code KP.code v (B.observation.tagged L.code 0 x)) := by
  have pv := H.part_typed KY KP hv mv
  have pp := H.pair_typed KY KP pv.1 pv.2 ha ma
  have t1 := H.tagged_typed 1 hx mx
  have t0 := H.tagged_typed 0 hx mx
  exact (H.ev_formula pp.1 pp.2 t1.1 t1.2).equivalent_trans (H.ev_formula pv.1 pv.2 t0.1 t0.2)
    (H.diamond_formula KY KP hv mv t0.1 t0.2) (H.pair_left_equivalent KY KP pv.1 pv.2 ha ma hx mx (H.part_good KY KP hv mv hr))
    (H.part_exact KY KP hv mv t0.1 t0.2 hr)

theorem responsePair_right {v a x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.xType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.ev (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 a)) (B.observation.tagged L.code 2 x))
      (B.relational.xCompare L.code KY.code KP.code a x) := by
  have pv := H.part_typed KY KP hv mv
  have ta := H.tagged_typed 0 ha ma
  have pp := H.pair_typed KY KP pv.1 pv.2 ta.1 ta.2
  have t2 := H.tagged_typed 2 hx mx
  have t0 := H.tagged_typed 0 hx mx
  exact (H.ev_formula pp.1 pp.2 t2.1 t2.2).equivalent_trans (H.relation_formula KY KP ta.1 ta.2 t0.1 t0.2)
    (H.relational_formed.xCompare_formula KY KP ha ma hx mx) (H.pair_right_equivalent KY KP pv.1 pv.2 ta.1 ta.2 hx mx)
    (H.relation_tagged_same KY KP 0 ha ma hx mx)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem rAll_intro {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y (B.rename e.names).xType → WellModed δ y .data →
      Proves P Δ δ ((B.rename e.names).rStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) y)) : Proves P Γ γ (B.rAll L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.rBody_family KY KP hv mv)
  intro Δ δ e y hy my
  rw [rBody_rename,rBody_instantiate]
  exact hh Δ δ e y (by simpa only [xType_rename] using hy) my

theorem rAll_elim_one {v y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (B.rAll L.code KY.code KP.code v)) :
    Proves P Γ γ (B.rStep L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.rBody_family KY KP hv mv) hy my hp
  simpa only [rBody_instantiate] using hh

theorem propertyR_elim {v x : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hg : Proves P Γ γ (B.propertyR L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code (B.rPred L.code KY.code KP.code v)))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (hp : Proves P Γ γ (B.ev v (B.observation.tagged L.code 2 x))) :
    Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.rPred L.code KY.code KP.code v) x) := by
  have iv := H.rPred_typed KY KP hv mv
  have ht := H.tagged_typed 2 hx mx
  have hall := L.imp_elim (H.relational_formed.extensional_formula KY KP iv.1 iv.2) (H.rAll_formula KY KP hv mv) hg he
  have hstep := H.rAll_elim_one KY KP hv mv hx mx hall
  have hcon := L.imp_elim (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.ev_formula hv mv ht.1 ht.2) (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx)) hstep hu
  exact L.imp_elim (H.ev_formula hv mv ht.1 ht.2) (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx) hcon hp
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responsePair_pred_compare_at {v a x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Equivalent P Γ γ
      (B.relational.channel.eval B.relational.probe.carrier (B.rPred L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) a)) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) x) := by
  have pv := H.part_typed KY KP hv mv
  have px := H.pair_typed KY KP pv.1 pv.2 ha ma
  have ir := H.rPred_typed KY KP px.1 px.2
  have iv := H.responsePred_typed KY KP hv mv
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have t1 := H.tagged_typed 1 rx.1 rx.2
  have t0 := H.tagged_typed 0 rx.1 rx.2
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode ir.1 ir.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx
  have f2 := H.ev_formula px.1 px.2 t1.1 t1.2
  have f3 := H.diamond_formula KY KP hv mv t0.1 t0.2
  have e1 := H.rPred_evaluation KY KP px.1 px.2 hx mx
  have e2 := H.responsePair_left KY KP hv mv ha ma rx.1 rx.2 hr
  have e3 := H.responsePred_evaluation KY KP hv mv hx mx
  exact f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 e1 e2) e3.symm

theorem responsePair_pred_compare {v a : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier
      (B.rPred L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) a))
      (B.responsePred L.code KY.code KP.code v)) := by
  have pv := H.part_typed KY KP hv mv
  have px := H.pair_typed KY KP pv.1 pv.2 ha ma
  have ir := H.rPred_typed KY KP px.1 px.2
  have iv := H.responsePred_typed KY KP hv mv
  apply H.relational_formed.channel.predCompare_intro H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY ir.1 ir.2 iv.1 iv.2
  intro Δ δ e x hx mx
  simp only [rPred_rename,responsePred_rename,pair_rename,part_rename]
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  simpa only [LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).responsePair_pred_compare_at (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv)
      (y_typed_rename (B := B) e ha) (e.moded ma)
      (by simpa only [ProbeCode.carrier_rename,xType,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hx) mx hr'

theorem responsePair_pred_extensional {v a : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a B.yType) (ma : WellModed γ a .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extensional L.code KY.code KP.code
      (B.rPred L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) a))) := by
  have pv := H.part_typed KY KP hv mv
  have px := H.pair_typed KY KP pv.1 pv.2 ha ma
  have ir := H.rPred_typed KY KP px.1 px.2
  have iv := H.responsePred_typed KY KP hv mv
  exact (H.relational_formed.extensional_respect KY KP ir.1 ir.2 iv.1 iv.2 (H.responsePair_pred_compare KY KP hv mv ha ma hr)).2.prove
    (H.responsePred_extensional KY KP hv mv hr)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responsePair_R_forward {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (hg : Proves P Γ γ (B.propertyR L.code KY.code KP.code
      (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x)))) :
    Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have ir := H.rPred_typed KY KP px.1 px.2
  have iv := H.responsePred_typed KY KP hv mv
  have exP := H.responsePair_pred_extensional KY KP hv mv tx.1 tx.2 hr
  have self := (H.responsePair_right KY KP hv mv hx mx hx mx).2.prove (H.relational_formed.xCompare_refl KY KP hx mx)
  have hle := H.propertyR_elim KY KP px.1 px.2 hx mx hg exP hu self
  exact (H.relational_formed.valid_elim KY KP hx mx ir.1 ir.2 iv.1 iv.2 hu
    (H.responsePair_pred_compare KY KP hv mv tx.1 tx.2 hr)).1.prove hle

theorem responsePair_member_le {v x y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hl : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code y))
    (hp : Proves P Γ γ (B.ev (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x)) (B.observation.tagged L.code 2 y))) :
    Proves P Γ γ (B.relational.le L.code KY.code KP.code
      (B.rPred L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x))) y) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have ir := H.rPred_typed KY KP px.1 px.2
  have iv := H.responsePred_typed KY KP hv mv
  have ee := (H.responsePair_right KY KP hv mv hx mx hy my).1.prove hp
  have hly := (H.relational_formed.xCompare_elim KY KP hx mx hy my iv.1 iv.2 ee).1.prove hl
  exact (H.relational_formed.valid_elim KY KP hy my ir.1 ir.2 iv.1 iv.2 hu
    (H.responsePair_pred_compare KY KP hv mv tx.1 tx.2 hr)).2.prove hly

theorem responsePair_member_imp {v x y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hl : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code y)) :
    Proves P Γ γ (L.imp (B.ev (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x)) (B.observation.tagged L.code 2 y)) (B.relational.le L.code KY.code KP.code (B.rPred L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x))) y)) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have ir := H.rPred_typed KY KP px.1 px.2
  have ty := H.tagged_typed 2 hy my
  apply L.imp_intro_future (H.ev_formula px.1 px.2 ty.1 ty.2) (H.relational_formed.le_formula KY KP ir.1 ir.2 hy my)
  intro Δ δ e hp
  simp only [RelationalCode.le_rename,rPred_rename,ev_rename,pair_rename,part_rename,ObservationCode.tagged_rename] at hp ⊢
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  have hl' := hl.rename e
  simp only [RelationalCode.le_rename,responsePred_rename] at hl'
  have hv' := carrier_typed_rename e hv
  have hx' := x_typed_rename (B := B) e hx
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  exact (H.rename e).responsePair_member_le (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' (e.moded mx)
    (x_typed_rename (B := B) e hy) (e.moded my) hr' hl' hu' hp

theorem responsePair_rStep {v x y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hl : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x)) :
    Proves P Γ γ (B.rStep L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x)) y) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have ir := H.rPred_typed KY KP px.1 px.2
  have ty := H.tagged_typed 2 hy my
  apply L.imp_intro_future (H.relational_formed.valid_formula KY KP hy my)
    (L.imp_formula (H.ev_formula px.1 px.2 ty.1 ty.2) (H.relational_formed.le_formula KY KP ir.1 ir.2 hy my))
  intro Δ δ e hu
  simp only [RelationalCode.valid_rename] at hu
  simp only [LogicSetup.imp_rename,RelationalCode.le_rename,rPred_rename,ev_rename,pair_rename,part_rename,ObservationCode.tagged_rename]
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  have hl' := hl.rename e
  simp only [RelationalCode.le_rename,responsePred_rename] at hl'
  have hv' := carrier_typed_rename e hv
  have hx' := x_typed_rename (B := B) e hx
  exact (H.rename e).responsePair_member_imp (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' (e.moded mx)
    (x_typed_rename (B := B) e hy) (e.moded my) hr' hl' hu

theorem responsePair_rAll {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hl : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x)) :
    Proves P Γ γ (B.rAll L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x))) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  apply H.rAll_intro KY KP px.1 px.2
  intro Δ δ e y hy my
  simp only [pair_rename,part_rename,ObservationCode.tagged_rename]
  have hr' := hr.rename e
  simp only [response_rename] at hr'
  have hl' := hl.rename e
  simp only [RelationalCode.le_rename,responsePred_rename] at hl'
  have hv' := carrier_typed_rename e hv
  have hx' := x_typed_rename (B := B) e hx
  exact (H.rename e).responsePair_rStep (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' (e.moded mx) hy my hr' hl'

theorem responsePair_R_backward {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hl : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x)) :
    Proves P Γ γ (B.propertyR L.code KY.code KP.code (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x))) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have ir := H.rPred_typed KY KP px.1 px.2
  have hh := H.responsePair_rAll KY KP hv mv hx mx hr hl
  have hA := H.relational_formed.extensional_formula KY KP ir.1 ir.2
  have hB := H.rAll_formula KY KP px.1 px.2
  change Proves P Γ γ (L.imp _ _)
  pts_pl L using [hh]

theorem responsePair_R_equivalent {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Equivalent P Γ γ (B.propertyR L.code KY.code KP.code
      (B.pair L.code KY.code KP.code (B.part L.code KY.code KP.code v) (B.observation.tagged L.code 0 x)))
      (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have iv := H.responsePred_typed KY KP hv mv
  apply (H.propertyR_formula KY KP px.1 px.2).equivalent_of_future (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx)
  · intro Δ δ e hg
    simp only [propertyR_rename,pair_rename,part_rename,ObservationCode.tagged_rename] at hg
    simp only [RelationalCode.le_rename,responsePred_rename]
    have hr' := hr.rename e
    simp only [response_rename] at hr'
    have hu' := hu.rename e
    simp only [RelationalCode.valid_rename] at hu'
    exact (H.rename e).responsePair_R_forward (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv)
      (x_typed_rename (B := B) e hx) (e.moded mx) hr' hu' hg
  · intro Δ δ e hl
    simp only [RelationalCode.le_rename,responsePred_rename] at hl
    simp only [propertyR_rename,pair_rename,part_rename,ObservationCode.tagged_rename]
    have hr' := hr.rename e
    simp only [response_rename] at hr'
    exact (H.rename e).responsePair_R_backward (KY.rename e) (KP.rename e) (carrier_typed_rename e hv) (e.moded mv)
      (x_typed_rename (B := B) e hx) (e.moded mx) hr' hl

theorem sb_law {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Equivalent P Γ γ (B.sb L.code KY.code KP.code v (B.observation.tagged L.code 0 x))
      (B.relational.le L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v) x) := by
  have pv := H.part_typed KY KP hv mv
  have tx := H.tagged_typed 0 hx mx
  have px := H.pair_typed KY KP pv.1 pv.2 tx.1 tx.2
  have iv := H.responsePred_typed KY KP hv mv
  exact (H.sb_formula KY KP hv mv tx.1 tx.2).equivalent_trans (H.propertyR_formula KY KP px.1 px.2)
    (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx) (H.parameter_query KY KP 6 px.1 px.2)
    (H.responsePair_R_equivalent KY KP hv mv hx mx hr hu)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem shift_compare_at {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ
      (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i)) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code i) x) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have ri := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  have tx := H.tagged_typed 0 hx mx
  have dx := H.delta_typed KY KP hx mx
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode ri.1 ri.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode si.1 si.2 hx mx
  have f2 := H.diamond_formula KY KP zi.1 zi.2 tx.1 tx.2
  have f3 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2
  exact f1.equivalent_trans f3 f4
    (f1.equivalent_trans f2 f3 (H.responsePred_exact KY KP zi.1 zi.2 hx mx (H.probe_response KY KP hi mi he))
      (H.probe_exact KY KP hi mi tx.1 tx.2 he)) (H.shiftPred_exact KY KP hi mi hx mx he).symm

theorem shift_compare {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier
      (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i))
      (B.shiftPred L.code KY.code KP.code i)) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have ri := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  apply H.relational_formed.channel.predCompare_intro H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY ri.1 ri.2 si.1 si.2
  intro Δ δ e x hx mx
  simp only [responsePred_rename,RelationalCode.probeFor_rename,shiftPred_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  simpa only [LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).shift_compare_at (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
      (by simpa only [ProbeCode.carrier_rename,xType,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hx) mx he'

theorem shift_predecessor {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.delta L.code KY.code KP.code x))
      (B.relational.le L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i) x) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have ri := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  have tx := H.tagged_typed 0 hx mx
  have dx := H.delta_typed KY KP hx mx
  have f1 := H.relational_formed.le_formula KY KP hi mi dx.1 dx.2
  have f2 := H.sb_formula KY KP zi.1 zi.2 tx.1 tx.2
  have f3 := H.relational_formed.le_formula KY KP ri.1 ri.2 hx mx
  have f4 := H.relational_formed.le_formula KY KP si.1 si.2 hx mx
  exact f1.equivalent_trans f3 f4
    (f1.equivalent_trans f2 f3 (H.lift_evaluation KY KP hi mi tx.1 tx.2)
      (H.sb_law KY KP zi.1 zi.2 hx mx (H.probe_response KY KP hi mi he) hu))
    (H.relational_formed.valid_elim KY KP hx mx ri.1 ri.2 si.1 si.2 hu (H.shift_compare KY KP hi mi he))
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem positive_shift_member {x i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (hq : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x))
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code i (B.delta L.code KY.code KP.code x))) : Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code (B.delta L.code KY.code KP.code x))) := by
  have si := H.shiftPred_typed KY KP hi mi
  have dx := H.delta_typed KY KP hx mx
  exact (H.shiftPred_exact KY KP hi mi dx.1 dx.2 he).1.prove
    (H.diagonalQ_elim KY KP hx mx si.1 si.2 hq (H.shiftPred_extensional KY KP hi mi he)
      ((H.shift_predecessor KY KP hi mi hx mx he hu).1.prove ht))

theorem positive_shift_imp {x i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (hq : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x))
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) : Proves P Γ γ (L.imp (B.relational.le L.code KY.code KP.code i (B.delta L.code KY.code KP.code x)) (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code (B.delta L.code KY.code KP.code x)))) := by
  have dx := H.delta_typed KY KP hx mx
  have ddx := H.delta_typed KY KP dx.1 dx.2
  apply L.imp_intro_future (H.relational_formed.le_formula KY KP hi mi dx.1 dx.2)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi ddx.1 ddx.2)
  intro Δ δ e ht
  simp only [RelationalCode.le_rename,delta_rename] at ht
  simp only [ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename]
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  have hq' := hq.rename e
  simp only [diagonalQ_rename] at hq'
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  exact (H.rename e).positive_shift_member (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx)
    (xPred_typed_rename e hi) (e.moded mi) hu' hq' he' ht

theorem positive_shift_step {x i : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (hq : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x)) :
    Proves P Γ γ (B.qStep L.code KY.code KP.code (B.delta L.code KY.code KP.code x) i) := by
  have dx := H.delta_typed KY KP hx mx
  have ddx := H.delta_typed KY KP dx.1 dx.2
  apply L.imp_intro_future (H.relational_formed.extensional_formula KY KP hi mi)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi dx.1 dx.2)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi ddx.1 ddx.2))
  intro Δ δ e he
  simp only [RelationalCode.extensional_rename] at he
  simp only [LogicSetup.imp_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename]
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  have hq' := hq.rename e
  simp only [diagonalQ_rename] at hq'
  exact (H.rename e).positive_shift_imp (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx)
    (xPred_typed_rename e hi) (e.moded mi) hu' hq' he

theorem positive_shift {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (hq : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x)) :
    Proves P Γ γ (B.diagonalQ L.code KY.code KP.code (B.delta L.code KY.code KP.code x)) := by
  have dx := H.delta_typed KY KP hx mx
  apply H.diagonalQ_intro KY KP dx.1 dx.2
  intro Δ δ e i hi mi
  simp only [delta_rename]
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  have hq' := hq.rename e
  simp only [diagonalQ_rename] at hq'
  exact (H.rename e).positive_shift_step (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx) hi mi hu' hq'
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
def indStep (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) :=
  L.imp (B.relational.valid L KY KP x) (L.imp (B.relational.le L KY KP i x) (B.relational.channel.eval B.relational.probe.carrier i x))
def indBody (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  (B.rename Nat.succ).indStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (i.rename Nat.succ) (.var 0)
def induction (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) :=
  KY.all B.xType (B.indBody L KY KP i)
theorem indStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.indStep L KY KP v x).rename ρ = (B.rename ρ).indStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [indStep,LogicCode.imp_rename,RelationalCode.valid_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,relational,RelationalCode.channel,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem indStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.indStep L KY KP v x).subst σ = (B.subst σ).indStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [indStep,LogicCode.imp_subst,RelationalCode.valid_subst,RelationalCode.le_subst,ChannelCode.eval_subst,ProbeCode.carrier_subst,relational,RelationalCode.channel,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem indBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.indBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).indBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [indBody,indStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem indBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.indBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).indBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [indBody,indStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem indBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.indBody L KY KP v).instantiate x = B.indStep L KY KP v x := by
  simp only [indBody,Expr.instantiate,indStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem induction_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (B.induction L KY KP i).rename ρ = (B.rename ρ).induction (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [induction,QuantifierCode.all_rename,xType_rename,indBody_rename]
theorem induction_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (B.induction L KY KP i).subst σ = (B.subst σ).induction (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [induction,QuantifierCode.all_subst,xType_subst,indBody_subst]

def wfStep (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :=
  B.induction L KY KP (B.responsePred L KY KP v)
def wfBody (L : LogicCode S) (KY KP : QuantifierCode S) :=
  (B.rename Nat.succ).wfStep (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ) (.var 0)
def wf (L : LogicCode S) (KY KP : QuantifierCode S) :=
  B.relational.logical.build B.relational.probe.carrier (B.wfBody L KY KP)
theorem wfStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.wfStep L KY KP v).rename ρ = (B.rename ρ).wfStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [wfStep,induction_rename,responsePred_rename]
theorem wfBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.wfBody L KY KP).rename (Expr.liftRen ρ) = (B.rename ρ).wfBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [wfBody,wfStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem wfStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.wfStep L KY KP v).subst σ = (B.subst σ).wfStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [wfStep,induction_subst,responsePred_subst]
theorem wfBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.wfBody L KY KP).subst (Expr.liftSub σ) = (B.subst σ).wfBody (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [wfBody,wfStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem wfBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :
    (B.wfBody L KY KP).instantiate v = B.wfStep L KY KP v := by
  simp only [wfBody,Expr.instantiate,wfStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst,Expr.single]
theorem wf_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.wf L KY KP).rename ρ = (B.rename ρ).wf (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [wf,DataWrapper.build_rename,DataWrapper.argRen,ite_true,wfBody_rename,ProbeCode.carrier_rename,relational,rename,ObservationCode.rename,RelationalCode.rename]
theorem wf_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.wf L KY KP).subst σ = (B.subst σ).wf (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [wf,DataWrapper.build_subst,DataWrapper.argSub,ite_true,wfBody_subst,ProbeCode.carrier_subst,relational,subst,ObservationCode.subst,RelationalCode.subst]
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem indStep_formula {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    L.Formula (B.indStep L.code KY.code KP.code i x) := by
  exact L.imp_formula (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hx mx))

theorem indBody_family {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    L.Family B.xType (B.indBody L.code KY.code KP.code i) := by
  intro Δ δ e x hx mx
  rw [indBody_rename,indBody_instantiate]
  exact (H.rename e).indStep_formula (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
    (by simpa only [xType_rename] using hx) mx

theorem induction_formula {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    L.Formula (B.induction L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.indBody_family KY KP hi mi)

theorem induction_intro {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x (B.rename e.names).xType → WellModed δ x .data →
      Proves P Δ δ ((B.rename e.names).indStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (i.rename e.names) x)) : Proves P Γ γ (B.induction L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.indBody_family KY KP hi mi)
  intro Δ δ e x hx mx
  rw [indBody_rename,indBody_instantiate]
  exact hh Δ δ e x (by simpa only [xType_rename] using hx) mx

theorem induction_elim_one {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.induction L.code KY.code KP.code i)) :
    Proves P Γ γ (B.indStep L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have he := L.all_elim_family KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.indBody_family KY KP hi mi) hx mx hp
  simpa only [indBody_instantiate] using he

theorem induction_elim {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (B.induction L.code KY.code KP.code i))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code i x)) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier i x) := by
  have fe := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hx mx
  have fl := H.relational_formed.le_formula KY KP hi mi hx mx
  exact L.imp_elim fl fe (L.imp_elim (H.relational_formed.valid_formula KY KP hx mx) (L.imp_formula fl fe)
    (H.induction_elim_one KY KP hi mi hx mx hp) hu) ht
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem wfStep_formula {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    L.Formula (B.wfStep L.code KY.code KP.code v) := by
  have hi := H.responsePred_typed KY KP hv mv
  exact H.induction_formula KY KP hi.1 hi.2

theorem wfBody_family : L.Family B.relational.probe.carrier (B.wfBody L.code KY.code KP.code) := by
  intro Δ δ e v hv mv
  rw [wfBody_rename,wfBody_instantiate]
  exact (H.rename e).wfStep_formula (KY.rename e) (KP.rename e)
    (by simpa only [ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename] using hv) mv

theorem wf_typed : HasType P Γ (B.wf L.code KY.code KP.code) B.xType ∧ WellModed γ (B.wf L.code KY.code KP.code) .data :=
  (H.relational_formed.channel.logical.sound H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode).1 _ (H.wfBody_family KY KP)

theorem wf_primitive_evaluation {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.relational.logical.observe B.relational.probe.carrier (B.wf L.code KY.code KP.code) v)
      (B.induction L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v)) := by
  simpa only [wf,RelationalCode.channel,DataWrapper.cancelFormula,ite_true,wfBody_instantiate,wfStep] using
    H.relational_formed.channel.logical.cancellation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode (H.wfBody_family KY KP) ⟨hv,mv⟩

theorem wf_evaluation {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.induction L.code KY.code KP.code (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i))) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  exact H.wf_primitive_evaluation KY KP hz.1 hz.2
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem indConsequence_respect {v c x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Equivalent P Γ γ
      (L.imp (B.relational.le L.code KY.code KP.code v x) (B.relational.channel.eval B.relational.probe.carrier v x))
      (L.imp (B.relational.le L.code KY.code KP.code c x) (B.relational.channel.eval B.relational.probe.carrier c x)) := by
  have evc := H.relational_formed.channel.predCompare_elim H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY hv mv hc mc hx mx he
  have el := H.relational_formed.valid_elim KY KP hx mx hv mv hc mc hu he
  exact L.imp_equivalent (H.relational_formed.le_formula KY KP hv mv hx mx) (H.relational_formed.le_formula KY KP hc mc hx mx)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv hx mx)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hc mc hx mx) el evc

omit H in
theorem xComparison_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v c : Expr S}
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c)) :
    Proves P Δ δ ((B.rename e.names).relational.channel.predCompare (L.rename e).code (KY.rename e).code
      (B.rename e.names).relational.probe.carrier (v.rename e.names) (c.rename e.names)) := by
  simpa only [ChannelCode.predCompare_rename,ProbeCode.carrier_rename,relational_rename,LogicSetup.code_rename,QuantifierRoute.code_rename,relational,SpecializedCode.rename,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using he.rename e

theorem indStep_respect {v c x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c)) :
    Equivalent P Γ γ (B.indStep L.code KY.code KP.code v x) (B.indStep L.code KY.code KP.code c x) := by
  apply L.guarded_equivalent_future (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.relational_formed.le_formula KY KP hv mv hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv hx mx))
    (L.imp_formula (H.relational_formed.le_formula KY KP hc mc hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hc mc hx mx))
  intro Δ δ e hu
  have hu' : Proves P Δ δ ((B.rename e.names).relational.valid (L.rename e).code (KY.rename e).code (KP.rename e).code (x.rename e.names)) := by
    simpa only [RelationalCode.valid_rename,relational_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using hu
  simpa only [LogicSetup.imp_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,RelationalCode.le_rename,
    relational_rename,LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,relational,SpecializedCode.rename,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).indConsequence_respect (KY.rename e) (KP.rename e)
      (xPred_typed_rename e hv) (e.moded mv) (xPred_typed_rename e hc) (e.moded mc)
      (x_typed_rename (B := B) e hx) (e.moded mx) (xComparison_rename KY e he) hu'

theorem induction_respect {v c : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c)) :
    Equivalent P Γ γ (B.induction L.code KY.code KP.code v) (B.induction L.code KY.code KP.code c) := by
  apply L.all_equivalent_future KY H.x_sorted H.x_mode (H.indBody_family KY KP hv mv)
    (H.indBody_family KY KP hc mc)
  intro Δ δ e x hx mx
  rw [indBody_rename,indBody_rename,indBody_instantiate,indBody_instantiate]
  exact (H.rename e).indStep_respect (KY.rename e) (KP.rename e)
    (xPred_typed_rename e hv) (e.moded mv) (xPred_typed_rename e hc) (e.moded mc)
    (by simpa only [xType_rename] using hx) mx (xComparison_rename KY e he)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responseProbe_compare_at {i c x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier i c)) :
    Equivalent P Γ γ
      (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i)) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code c)) x) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have hz' := H.relational_formed.probeFor_typed KY KP hc mc
  have hp := H.responsePred_typed KY KP hz.1 hz.2
  have hp' := H.responsePred_typed KY KP hz'.1 hz'.2
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have tx := H.tagged_typed 0 rx.1 rx.2
  have rt := H.round_typed tx.1 tx.2
  have hl := H.lift_typed KY KP rt.1 rt.2
  have e1 := H.responsePred_evaluation KY KP hz.1 hz.2 hx mx
  have e2 := H.probe_rounded KY KP hi mi tx.1 tx.2
  have e3 := H.relational_formed.channel.predCompare_elim H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY hi mi hc mc hl.1 hl.2 he
  have e4 := H.probe_rounded KY KP hc mc tx.1 tx.2
  have e5 := H.responsePred_evaluation KY KP hz'.1 hz'.2 hx mx
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hp.1 hp.2 hx mx
  have f2 := H.diamond_formula KY KP hz.1 hz.2 tx.1 tx.2
  have f3 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hl.1 hl.2
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hc mc hl.1 hl.2
  have f5 := H.diamond_formula KY KP hz'.1 hz'.2 tx.1 tx.2
  have f6 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hp'.1 hp'.2 hx mx
  exact f1.equivalent_trans f5 f6 (f1.equivalent_trans f4 f5 (f1.equivalent_trans f3 f4
    (f1.equivalent_trans f2 f3 e1 e2) e3) e4.symm) e5.symm

theorem responseProbe_compare {i c : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier i c)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier
      (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i))
      (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code c))) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  have hz' := H.relational_formed.probeFor_typed KY KP hc mc
  have hp := H.responsePred_typed KY KP hz.1 hz.2
  have hp' := H.responsePred_typed KY KP hz'.1 hz'.2
  apply H.relational_formed.channel.predCompare_intro H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY hp.1 hp.2 hp'.1 hp'.2
  intro Δ δ e x hx mx
  simp only [responsePred_rename,RelationalCode.probeFor_rename]
  simpa only [LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).responseProbe_compare_at (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) (xPred_typed_rename e hc) (e.moded mc)
      (by simpa only [ProbeCode.carrier_rename,xType,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hx) mx (xComparison_rename KY e he)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem wf_le_congr {i c : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier i c)) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.relational.le L.code KY.code KP.code c (B.wf L.code KY.code KP.code)) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have zc := H.relational_formed.probeFor_typed KY KP hc mc
  have pi := H.responsePred_typed KY KP zi.1 zi.2
  have pc := H.responsePred_typed KY KP zc.1 zc.2
  have wt := H.wf_typed KY KP
  have f1 := H.relational_formed.le_formula KY KP hi mi wt.1 wt.2
  have f2 := H.induction_formula KY KP pi.1 pi.2
  have f3 := H.induction_formula KY KP pc.1 pc.2
  have f4 := H.relational_formed.le_formula KY KP hc mc wt.1 wt.2
  exact f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 (H.wf_evaluation KY KP hi mi)
    (H.induction_respect KY KP pi.1 pi.2 pc.1 pc.2 (H.responseProbe_compare KY KP hi mi hc mc he))) (H.wf_evaluation KY KP hc mc).symm

theorem wf_validStep {i c : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    :
    Proves P Γ γ (B.relational.validStep L.code KY.code KP.code (B.wf L.code KY.code KP.code) i c) := by
  have la := H.wf_typed KY KP
  apply L.imp_intro_future
    (H.relational_formed.channel.predCompare_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY hi mi hc mc)
    (L.iff_formula (H.relational_formed.le_formula KY KP hi mi la.1 la.2) (H.relational_formed.le_formula KY KP hc mc la.1 la.2))
  intro Δ δ e he
  simp only [ChannelCode.predCompare_rename,ProbeCode.carrier_rename] at he
  simp only [LogicSetup.iff_rename,RelationalCode.le_rename,wf_rename,relational_rename]
  have hi' := xPred_typed_rename e hi
  have hc' := xPred_typed_rename e hc
  have la' := (H.rename e).wf_typed (KY.rename e) (KP.rename e)
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).relational_formed.le_formula (KY.rename e) (KP.rename e) hi' (e.moded mi) la'.1 la'.2)
    ((H.rename e).relational_formed.le_formula (KY.rename e) (KP.rename e) hc' (e.moded mc) la'.1 la'.2)
    ((H.rename e).wf_le_congr (KY.rename e) (KP.rename e) hi' (e.moded mi) hc' (e.moded mc) he)

theorem wf_validAt {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    :
    Proves P Γ γ (B.relational.validAt L.code KY.code KP.code (B.wf L.code KY.code KP.code) i) := by
  have la := H.wf_typed KY KP
  apply H.relational_formed.validAt_intro KY KP la.1 la.2 hi mi
  intro Δ δ e c hc mc
  rw [wf_rename]
  exact (H.rename e).wf_validStep (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) hc mc

theorem wf_valid :
    Proves P Γ γ (B.relational.valid L.code KY.code KP.code (B.wf L.code KY.code KP.code)) := by
  have la := H.wf_typed KY KP
  apply H.relational_formed.valid_intro KY KP la.1 la.2
  intro Δ δ e i hi mi
  rw [wf_rename]
  exact (H.rename e).wf_validAt (KY.rename e) (KP.rename e) hi mi
theorem wf_shift_evaluation {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.induction L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i)) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have pi := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  exact (H.relational_formed.le_formula KY KP hi mi (H.wf_typed KY KP).1 (H.wf_typed KY KP).2).equivalent_trans
    (H.induction_formula KY KP pi.1 pi.2) (H.induction_formula KY KP si.1 si.2) (H.wf_evaluation KY KP hi mi)
    (H.induction_respect KY KP pi.1 pi.2 si.1 si.2 (H.shift_compare KY KP hi mi he))
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem shift_ind_member {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (hl : Proves P Γ γ (B.induction L.code KY.code KP.code i))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i) x)) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code i) x) := by
  have dx := H.delta_typed KY KP hx mx
  exact (H.shiftPred_exact KY KP hi mi hx mx he).2.prove (H.induction_elim KY KP hi mi dx.1 dx.2 hl
    (H.delta_valid KY KP hx mx) ((H.shift_predecessor KY KP hi mi hx mx he hu).2.prove ht))

theorem shift_ind_imp {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (hl : Proves P Γ γ (B.induction L.code KY.code KP.code i))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Proves P Γ γ (L.imp (B.relational.le L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code i) x)) := by
  have si := H.shiftPred_typed KY KP hi mi
  apply L.imp_intro_future (H.relational_formed.le_formula KY KP si.1 si.2 hx mx)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode si.1 si.2 hx mx)
  intro Δ δ e ht
  simp only [RelationalCode.le_rename,shiftPred_rename] at ht
  simp only [ChannelCode.eval_rename,ProbeCode.carrier_rename,shiftPred_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  have hl' := hl.rename e
  simp only [induction_rename] at hl'
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  exact (H.rename e).shift_ind_member (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
    (x_typed_rename (B := B) e hx) (e.moded mx) he' hl' hu' ht

theorem shift_ind_step {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (hl : Proves P Γ γ (B.induction L.code KY.code KP.code i)) :
    Proves P Γ γ (B.indStep L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i) x) := by
  have si := H.shiftPred_typed KY KP hi mi
  apply L.imp_intro_future (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.relational_formed.le_formula KY KP si.1 si.2 hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode si.1 si.2 hx mx))
  intro Δ δ e hu
  simp only [RelationalCode.valid_rename] at hu
  simp only [LogicSetup.imp_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,shiftPred_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  have hl' := hl.rename e
  simp only [induction_rename] at hl'
  exact (H.rename e).shift_ind_imp (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
    (x_typed_rename (B := B) e hx) (e.moded mx) he' hl' hu

theorem shift_induction {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (hl : Proves P Γ γ (B.induction L.code KY.code KP.code i)) :
    Proves P Γ γ (B.induction L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i)) := by
  have si := H.shiftPred_typed KY KP hi mi
  apply H.induction_intro KY KP si.1 si.2
  intro Δ δ e x hx mx
  simp only [shiftPred_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  have hl' := hl.rename e
  simp only [induction_rename] at hl'
  exact (H.rename e).shift_ind_step (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) hx mx he' hl'

theorem induction_builder {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (hl : Proves P Γ γ (B.induction L.code KY.code KP.code i)) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier i (B.wf L.code KY.code KP.code)) := by
  exact H.induction_elim KY KP hi mi (H.wf_typed KY KP).1 (H.wf_typed KY KP).2 hl (H.wf_valid KY KP)
    ((H.wf_shift_evaluation KY KP hi mi he).2.prove (H.shift_induction KY KP hi mi he hl))
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem negative_ind_bottom {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code) x))
    (hq : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code x)) : Proves P Γ γ L.bottom := by
  have dx := H.delta_typed KY KP hx mx
  have iv := H.diagonalPred_typed KY KP
  have hn := (H.diagonalPred_exact KY KP dx.1 dx.2).1.prove
    (H.diagonalQ_elim KY KP hx mx iv.1 iv.2 hq (H.diagonalPred_extensional KY KP) ht)
  exact L.imp_elim (H.diagonalQ_formula KY KP dx.1 dx.2) L.bottom_formula hn (H.positive_shift KY KP hx mx hu hq)

theorem negative_ind_member {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code) x)) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.diagonalPred L.code KY.code KP.code) x) := by
  apply (H.diagonalPred_exact KY KP hx mx).2.prove
  apply L.imp_intro_future (H.diagonalQ_formula KY KP hx mx) L.bottom_formula
  intro Δ δ e hq
  simp only [diagonalQ_rename] at hq
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  have ht' := ht.rename e
  simp only [RelationalCode.le_rename,diagonalPred_rename] at ht'
  exact (H.rename e).negative_ind_bottom (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx) hu' ht' hq

theorem negative_ind_imp {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Proves P Γ γ (L.imp (B.relational.le L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.diagonalPred L.code KY.code KP.code) x)) := by
  have iv := H.diagonalPred_typed KY KP
  apply L.imp_intro_future (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx)
  intro Δ δ e ht
  simp only [RelationalCode.le_rename,diagonalPred_rename] at ht
  simp only [ChannelCode.eval_rename,ProbeCode.carrier_rename,diagonalPred_rename]
  have hu' := hu.rename e
  simp only [RelationalCode.valid_rename] at hu'
  exact (H.rename e).negative_ind_member (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx) hu' ht

theorem negative_ind_step {x : Expr S}
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Proves P Γ γ (B.indStep L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code) x) := by
  have iv := H.diagonalPred_typed KY KP
  apply L.imp_intro_future (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.relational_formed.le_formula KY KP iv.1 iv.2 hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx))
  intro Δ δ e hu
  simp only [RelationalCode.valid_rename] at hu
  simp only [LogicSetup.imp_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,diagonalPred_rename]
  exact (H.rename e).negative_ind_imp (KY.rename e) (KP.rename e) (x_typed_rename (B := B) e hx) (e.moded mx) hu

theorem negative_induction :
    Proves P Γ γ (B.induction L.code KY.code KP.code (B.diagonalPred L.code KY.code KP.code)) := by
  have iv := H.diagonalPred_typed KY KP
  apply H.induction_intro KY KP iv.1 iv.2
  intro Δ δ e x hx mx
  simp only [diagonalPred_rename]
  exact (H.rename e).negative_ind_step (KY.rename e) (KP.rename e) hx mx
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem wfQ_member {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code (B.wf L.code KY.code KP.code))) := by
  have si := H.shiftPred_typed KY KP hi mi
  have wf := H.wf_typed KY KP
  exact (H.shiftPred_exact KY KP hi mi wf.1 wf.2 he).1.prove
    (H.induction_builder KY KP si.1 si.2 (H.shiftPred_extensional KY KP hi mi he)
      ((H.wf_shift_evaluation KY KP hi mi he).1.prove ht))

theorem wfQ_imp {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (L.imp (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code (B.wf L.code KY.code KP.code)))) := by
  have wf := H.wf_typed KY KP
  have dx := H.delta_typed KY KP wf.1 wf.2
  apply L.imp_intro_future (H.relational_formed.le_formula KY KP hi mi wf.1 wf.2)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2)
  intro Δ δ e ht
  simp only [RelationalCode.le_rename,wf_rename] at ht
  simp only [ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename,wf_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  exact (H.rename e).wfQ_member (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) he' ht

theorem wfQ_step {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    Proves P Γ γ (B.qStep L.code KY.code KP.code (B.wf L.code KY.code KP.code) i) := by
  have wf := H.wf_typed KY KP
  have dx := H.delta_typed KY KP wf.1 wf.2
  apply L.imp_intro_future (H.relational_formed.extensional_formula KY KP hi mi)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi wf.1 wf.2)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2))
  intro Δ δ e he
  simp only [RelationalCode.extensional_rename] at he
  simp only [LogicSetup.imp_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename,wf_rename]
  exact (H.rename e).wfQ_imp (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) he

theorem wfQ : Proves P Γ γ (B.diagonalQ L.code KY.code KP.code (B.wf L.code KY.code KP.code)) := by
  have wf := H.wf_typed KY KP
  apply H.diagonalQ_intro KY KP wf.1 wf.2
  intro Δ δ e i hi mi
  simp only [wf_rename]
  exact (H.rename e).wfQ_step (KY.rename e) (KP.rename e) hi mi

include KY KP in
/-- The ambient bottom inhabitant, with actual encodings
and no extensional equality or relational law supplied as a hypothesis. -/
theorem relational_bottom : Proves P Γ γ L.bottom := by
  have wf := H.wf_typed KY KP
  have iv := H.diagonalPred_typed KY KP
  have hn := (H.diagonalPred_exact KY KP wf.1 wf.2).1.prove
    (H.induction_builder KY KP iv.1 iv.2 (H.diagonalPred_extensional KY KP) (H.negative_induction KY KP))
  exact L.imp_elim (H.diagonalQ_formula KY KP wf.1 wf.2) L.bottom_formula hn (H.wfQ KY KP)
end SpecializedCode.Formed
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.ChannelReturn
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} {L : LogicSetup P Γ γ C} {K : ChannelSetup L} (R : ChannelReturn K)
def specialized : SpecializedCode S := ⟨⟨K.relational,R.firstDouble,R.outerDouble⟩,R.type⟩
theorem specialized_formed : R.specialized.Formed L K.domain K.codomain K.base K.rawVertex K.tailVertex K.funVertex K.logicalVertex K.predVertex := by
  refine ⟨⟨K.relational_formed,R.firstDouble_formed,R.outerDouble_formed⟩,R.type_sorted,R.type_mode,R.factorization,rfl,?_⟩
  change R.fourth.apply (R.firstDouble.carrier (K.channel.raw.apply K.probe.carrier)) = K.initial.apply R.type
  simp only [fourth_apply,firstDouble,DoubleCode.carrier,ChannelSetup.doubled,type]
end PureTypeSystem.Labelled.ChannelReturn

end OAI
