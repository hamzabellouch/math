import OAI.Computability.TypeSystem.Channels

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace ChannelCode
variable (R : ChannelCode S)
/-- The predicate-variable callback P ↦ P@y. -/
def evalPredBody (T y : Expr S) := (R.rename Nat.succ).eval (T.rename Nat.succ) (.var 0) (y.rename Nat.succ)
def compareBody (L : LogicCode S) (T y z : Expr S) :=
  (L.rename Nat.succ).iff (R.evalPredBody T y) (R.evalPredBody T z)
/-- Source observational relation, with its actual Good predicate callback. -/
def relation (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) :=
  L.guardAll K (R.predicateType T) G (R.compareBody L T y z)

theorem evalPredBody_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.evalPredBody T y).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalPredBody (T.rename ρ) (y.rename ρ) := by
  simp only [evalPredBody,eval_rename,rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem evalPredBody_instantiate (T y p : Expr S) :
    (R.evalPredBody T y).instantiate p = R.eval T p y := by
  simp only [evalPredBody,Expr.instantiate,eval_subst,instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem compareBody_rename (L : LogicCode S) (T y z : Expr S) (ρ : Nat → Nat) :
    (R.compareBody L T y z).rename (Expr.liftRen ρ) =
      (R.rename ρ).compareBody (L.rename ρ) (T.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compareBody,LogicCode.iff_rename,LogicCode.rename_comp,evalPredBody_rename]
  rfl
theorem compareBody_instantiate (L : LogicCode S) (T y z p : Expr S) :
    (R.compareBody L T y z).instantiate p = L.iff (R.eval T p y) (R.eval T p z) := by
  change ((L.rename Nat.succ).iff (R.evalPredBody T y) (R.evalPredBody T z)).subst
    (Expr.single p) = _
  rw [LogicCode.iff_subst,LogicCode.instantiate_raise]
  change L.iff ((R.evalPredBody T y).instantiate p) ((R.evalPredBody T z).instantiate p) = _
  rw [evalPredBody_instantiate,evalPredBody_instantiate]

theorem relation_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.relation L K T G y z).rename ρ =
      (R.rename ρ).relation (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [relation,LogicCode.guardAll_rename,predicateType_rename,compareBody_rename]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) {T y z : Expr S}
include h
 theorem evalPredBody_family (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Family (R.predicateType T) (R.evalPredBody T y) := by
  intro Δ δ e p hp mp
  rw [evalPredBody_rename,evalPredBody_instantiate]
  apply (h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT) _ mp _ (e.moded my)
  · simpa only [predicateType_rename] using hp
  · simpa only [logicalType_rename] using e.typing hy
 theorem compareBody_family (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Family (R.predicateType T) (R.compareBody L.code T y z) :=
  (h.evalPredBody_family hT mT hy my).code_iff (h.evalPredBody_family hT mT hz mz)

 theorem relation_formula (K : QuantifierRoute L.witnesses C L.base H)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {G : Expr S} (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Formula (R.relation L.code K.code T G y z) :=
  L.guardAll_formula K (h.predicate_sorted hT) (h.predicate_mode mT) hG
    (h.compareBody_family hT mT hy my hz mz)

 theorem relation_elim (K : QuantifierRoute L.witnesses C L.base H)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {G p : Expr S} (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (he : Proves P Γ γ (R.relation L.code K.code T G y z))
    (hg : Proves P Γ γ (G.instantiate p)) :
    Equivalent P Γ γ (R.eval T p y) (R.eval T p z) := by
  have hh := L.guardAll_elim K (h.predicate_sorted hT) (h.predicate_mode mT) hG
    (h.compareBody_family hT mT hy my hz mz) hp mp he hg
  have hi : Proves P Γ γ (L.iff (R.eval T p y) (R.eval T p z)) := by
    simpa only [compareBody_instantiate,LogicSetup.code_iff] using hh
  exact L.equivalent_of_iff (h.eval_formula hT mT hp mp hy my) (h.eval_formula hT mT hp mp hz mz) hi

 theorem relation_intro (K : QuantifierRoute L.witnesses C L.base H)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {G : Expr S} (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    (hh : ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
      ∀ p, HasType P Δ p ((R.rename e.names).predicateType (T.rename e.names)) → WellModed δ p .data →
      Proves P Δ δ ((G.rename (Expr.liftRen e.names)).instantiate p) →
      Equivalent P Δ δ ((R.rename e.names).eval (T.rename e.names) p (y.rename e.names))
        ((R.rename e.names).eval (T.rename e.names) p (z.rename e.names))) :
    Proves P Γ γ (R.relation L.code K.code T G y z) := by
  apply L.guardAll_intro K (h.predicate_sorted hT) (h.predicate_mode mT) hG
    (h.compareBody_family hT mT hy my hz mz)
  intro Δ δ e p hp mp hg
  have ht : HasType P Δ p ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using hp
  have hy' : HasType P Δ (y.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hy
  have hz' : HasType P Δ (z.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hz
  have hfy := (h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT) ht mp hy' (e.moded my)
  have hfz := (h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT) ht mp hz' (e.moded mz)
  simpa only [compareBody_rename,compareBody_instantiate,← LogicSetup.code_rename,LogicSetup.code_iff] using
    (L.rename e).iff_of_equivalent hfy hfz (hh Δ δ e p ht mp hg)
end Formed
end ChannelCode

namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {A B D : Expr S}
theorem Formula.equivalent_refl (hA : L.Formula A) : Equivalent P Γ γ A A := by
  obtain ⟨s,hs⟩ := hA.sorted L
  exact .refl hs

theorem Formula.equivalent_trans (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hab : Equivalent P Γ γ A B) (hbd : Equivalent P Γ γ B D) : Equivalent P Γ γ A D := by
  obtain ⟨s,hs⟩ := hA.sorted L
  obtain ⟨t,ht⟩ := hB.sorted L
  obtain ⟨r,hr⟩ := hD.sorted L
  exact hab.trans hbd hs ht hr
end LogicSetup
namespace ChannelCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (K : QuantifierRoute L.witnesses C L.base H)
    {T G y z w : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hG : L.Family (R.predicateType T) G)
include h hT mT hG
 theorem relation_refl (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    Proves P Γ γ (R.relation L.code K.code T G y y) := by
  apply h.relation_intro K hT mT hG hy my hy my
  intro Δ δ e p hp mp _
  exact ((h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT) hp mp
    (by simpa only [logicalType_rename] using e.typing hy) (e.moded my)).equivalent_refl

 theorem relation_symm (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    (he : Proves P Γ γ (R.relation L.code K.code T G y z)) :
    Proves P Γ γ (R.relation L.code K.code T G z y) := by
  apply h.relation_intro K hT mT hG hz mz hy my
  intro Δ δ e p hp mp hg
  have hg' : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
      (G.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hG.rename e
  have he' : Proves P Δ δ ((R.rename e.names).relation (L.rename e).code (K.rename e).code
      (T.rename e.names) (G.rename (Expr.liftRen e.names)) (y.rename e.names) (z.rename e.names)) := by
    simpa only [relation_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using he.rename e
  exact ((h.rename e).relation_elim (K.rename e) (fun s hs => e.typing (hT s hs)) (e.moded mT) hg'
    (by simpa only [logicalType_rename] using e.typing hy) (e.moded my)
    (by simpa only [logicalType_rename] using e.typing hz) (e.moded mz) hp mp he' hg).symm

 theorem relation_trans (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    (hw : HasType P Γ w (R.logicalType T)) (mw : WellModed γ w .data)
    (he : Proves P Γ γ (R.relation L.code K.code T G y z))
    (hf : Proves P Γ γ (R.relation L.code K.code T G z w)) :
    Proves P Γ γ (R.relation L.code K.code T G y w) := by
  apply h.relation_intro K hT mT hG hy my hw mw
  intro Δ δ e p hp mp hg
  have hg' : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
      (G.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hG.rename e
  have he' : Proves P Δ δ ((R.rename e.names).relation (L.rename e).code (K.rename e).code
      (T.rename e.names) (G.rename (Expr.liftRen e.names)) (y.rename e.names) (z.rename e.names)) := by
    simpa only [relation_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using he.rename e
  have hf' : Proves P Δ δ ((R.rename e.names).relation (L.rename e).code (K.rename e).code
      (T.rename e.names) (G.rename (Expr.liftRen e.names)) (z.rename e.names) (w.rename e.names)) := by
    simpa only [relation_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using hf.rename e
  have hy' : HasType P Δ (y.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hy
  have hz' : HasType P Δ (z.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hz
  have hw' : HasType P Δ (w.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hw
  have ht := fun s hs => e.typing (hT s hs)
  exact ((h.rename e).eval_formula ht (e.moded mT) hp mp hy' (e.moded my)).equivalent_trans
    ((h.rename e).eval_formula ht (e.moded mT) hp mp hz' (e.moded mz))
    ((h.rename e).eval_formula ht (e.moded mT) hp mp hw' (e.moded mw))
    ((h.rename e).relation_elim (K.rename e) ht (e.moded mT) hg' hy' (e.moded my) hz' (e.moded mz) hp mp he' hg)
    ((h.rename e).relation_elim (K.rename e) ht (e.moded mT) hg' hz' (e.moded mz) hw' (e.moded mw) hp mp hf' hg)
end ChannelCode.Formed

/-- Five odd segments and the original source channel for tagged copies. -/
structure ThreeCopyCode (S : Type u) where
  source : DataWrapper S true
  first : DataWrapper S true
  inner : DoubleCode S
  outer : DoubleCode S
namespace ThreeCopyCode
variable (R : ThreeCopyCode S)
def rename (ρ : Nat → Nat) : ThreeCopyCode S :=
  ⟨R.source.rename ρ,R.first.rename ρ,R.inner.rename ρ,R.outer.rename ρ⟩
def subst (σ : Nat → Expr S) : ThreeCopyCode S :=
  ⟨R.source.subst σ,R.first.subst σ,R.inner.subst σ,R.outer.subst σ⟩
def firstType (T : Expr S) := R.first.apply T
def middleType (T : Expr S) := R.inner.carrier (R.firstType T)
def carrier (T : Expr S) := R.outer.carrier (R.middleType T)
def bitInner (L : LogicCode S) (T y : Expr S) :=
  R.outer.recover L (R.middleType T) y (R.inner.bitBody L (R.firstType T))
def bitOuter (L : LogicCode S) (T y : Expr S) := R.outer.bit L (R.middleType T) y
def observe (L : LogicCode S) (T y a : Expr S) :=
  R.outer.recover L (R.middleType T) y
    (R.inner.recBody L (R.firstType T) (R.first.contraCallback T a))
def tagged (L : LogicCode S) (t : Fin 3) (T x : Expr S) :=
  R.outer.emb L (t == 2) (R.middleType T)
    (R.inner.emb L (t == 1) (R.firstType T) (DataWrapper.reencode R.source R.first T x))

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
structure Formed (L : LogicSetup P Γ γ C) (I X J₁ J₂ J₃ J₄ J₅ : Set S) : Prop where
  source : R.source.Formed L I X
  first : R.first.Formed L I J₁
  inner : R.inner.Formed L J₁ J₂ J₃
  outer : R.outer.Formed L J₃ J₄ J₅
namespace Formed
variable {R : ThreeCopyCode S} {L : LogicSetup P Γ γ C} {I X J₁ J₂ J₃ J₄ J₅ : Set S}
    (h : R.Formed L I X J₁ J₂ J₃ J₄ J₅)
include h
theorem rename (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I X J₁ J₂ J₃ J₄ J₅ :=
  ⟨h.source.rename e,h.first.rename e,h.inner.rename e,h.outer.rename e⟩
variable {T y a x : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
include hT mT
theorem tagged_typed (t : Fin 3) (hx : HasType P Γ x (R.source.apply T)) (mx : WellModed γ x .data) :
    HasType P Γ (R.tagged L.code t T x) (R.carrier T) ∧ WellModed γ (R.tagged L.code t T x) .data := by
  have hy := h.source.reencode_typed h.first hT mT hx mx
  have hz := h.inner.emb_typed (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2
  exact h.outer.emb_typed (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT)) (t == 2) hz.1 hz.2

theorem bitOuter_formula (hy : HasType P Γ y (R.carrier T)) (my : WellModed γ y .data) :
    L.Formula (R.bitOuter L.code T y) :=
  h.outer.bit_formula (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT)) hy my

theorem bitInner_formula (hy : HasType P Γ y (R.carrier T)) (my : WellModed γ y .data) :
    L.Formula (R.bitInner L.code T y) :=
  h.outer.rec_formula (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT)) hy my
    (h.inner.bitBody_family (h.first.sorted hT) (h.first.mode mT))

theorem observe_formula (hy : HasType P Γ y (R.carrier T)) (my : WellModed γ y .data)
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) : L.Formula (R.observe L.code T y a) :=
  h.outer.rec_formula (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT)) hy my
    (h.inner.recBody_family (h.first.sorted hT) (h.first.mode mT)
      (h.first.contraCallback_family hT mT ha ma))

theorem tagged_bitOuter (t : Fin 3) (hx : HasType P Γ x (R.source.apply T)) (mx : WellModed γ x .data) :
    Proves P Γ γ (L.code.sign (t == 2) (R.bitOuter L.code T (R.tagged L.code t T x))) := by
  have hy := h.source.reencode_typed h.first hT mT hx mx
  have hz := h.inner.emb_typed (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2
  exact h.outer.emb_bit (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT)) (t == 2) hz.1 hz.2

theorem tagged_bitInner (t : Fin 3) (hx : HasType P Γ x (R.source.apply T)) (mx : WellModed γ x .data) :
    Proves P Γ γ (L.code.sign (t == 1) (R.bitInner L.code T (R.tagged L.code t T x))) := by
  have hy := h.source.reencode_typed h.first hT mT hx mx
  have hz := h.inner.emb_typed (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2
  have he := h.outer.emb_recovery (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT))
    (t == 2) hz.1 hz.2 (h.inner.bitBody_family (h.first.sorted hT) (h.first.mode mT))
  rw [DoubleCode.bitBody_instantiate] at he
  have ht := h.tagged_typed hT mT t hx mx
  have hb := h.inner.bit_formula (h.first.sorted hT) (h.first.mode mT) hz.1 hz.2
  exact (L.sign_equivalent (t == 1) (h.bitInner_formula hT mT ht.1 ht.2) hb he).2.prove
    (h.inner.emb_bit (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2)

theorem tagged_observe (t : Fin 3) (hx : HasType P Γ x (R.source.apply T)) (mx : WellModed γ x .data)
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    Equivalent P Γ γ (R.observe L.code T (R.tagged L.code t T x) a) (R.source.observe T x a) := by
  have hy := h.source.reencode_typed h.first hT mT hx mx
  have hz := h.inner.emb_typed (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2
  have hw := h.tagged_typed hT mT t hx mx
  have hq := h.first.contraCallback_family hT mT ha ma
  have hq' := h.inner.recBody_family (h.first.sorted hT) (h.first.mode mT) hq
  have he := h.outer.emb_recovery (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT))
    (t == 2) hz.1 hz.2 hq'
  rw [DoubleCode.recBody_instantiate] at he
  have he' := h.inner.emb_recovery (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2 hq
  rw [DataWrapper.contraCallback_instantiate] at he'
  have he'' := h.source.reencode_evaluation h.first hT mT hx mx ha ma
  have f₁ := h.observe_formula hT mT hw.1 hw.2 ha ma
  have f₂ := h.inner.rec_formula (h.first.sorted hT) (h.first.mode mT) hz.1 hz.2 hq
  have f₃ := (h.first.sound hT mT).2 _ a hy.1 hy.2 ⟨ha,ma⟩
  have f₄ := (h.source.sound hT mT).2 _ a hx mx ⟨ha,ma⟩
  exact f₁.equivalent_trans f₃ f₄ (f₁.equivalent_trans f₂ f₃ he he') he''
end Formed
end ThreeCopyCode

namespace ChannelReturn
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {K : ChannelSetup L} (R : ChannelReturn K)
def copies : ThreeCopyCode S := ⟨K.channel.logical,K.channel.raw,R.firstDouble,R.outerDouble⟩
theorem copies_formed : R.copies.Formed L K.base K.logicalVertex K.rawVertex K.base K.rawVertex K.base K.logicalVertex :=
  ⟨K.channelFormed.logical,K.channelFormed.raw,R.firstDouble_formed,R.outerDouble_formed⟩
theorem copies_type : R.copies.carrier K.probe.carrier = K.channel.logicalType (K.initial.apply R.type) :=
  R.factorization
end ChannelReturn

namespace ChannelCode
variable (R : ChannelCode S)
def roundRespectBody (L : LogicCode S) (T p : Expr S) :=
  (L.rename Nat.succ).iff ((R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ) (.var 0))
    ((R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ)
      ((R.rename Nat.succ).round (T.rename Nat.succ) (.var 0)))
def roundRespect (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) :=
  K.all (R.logicalType T) (R.roundRespectBody L T p)
def goodBody (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) :=
  (L.rename Nat.succ).conj
    ((R.rename Nat.succ).roundRespect (L.rename Nat.succ) (K.rename Nat.succ) (T.rename Nat.succ) (.var 0)) Q

theorem roundRespectBody_rename (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.roundRespectBody L T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).roundRespectBody (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [roundRespectBody,LogicCode.iff_rename,eval_rename,round_rename,rename_comp,
    LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem roundRespectBody_instantiate (L : LogicCode S) (T p y : Expr S) :
    (R.roundRespectBody L T p).instantiate y = L.iff (R.eval T p y) (R.eval T p (R.round T y)) := by
  simp only [roundRespectBody,Expr.instantiate,LogicCode.iff_subst,LogicCode.instantiate_raise,
    eval_subst,round_subst,instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem roundRespect_rename (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.roundRespect L K T p).rename ρ =
      (R.rename ρ).roundRespect (L.rename ρ) (K.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [roundRespect,QuantifierCode.all_rename,logicalType_rename,roundRespectBody_rename]

theorem roundRespectBody_subst (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.roundRespectBody L T p).subst (Expr.liftSub σ) =
      (R.subst σ).roundRespectBody (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [roundRespectBody,LogicCode.iff_subst,eval_subst,round_subst,subst,rename,
    LogicCode.subst,LogicCode.rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl

theorem roundRespect_subst (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.roundRespect L K T p).subst σ =
      (R.subst σ).roundRespect (L.subst σ) (K.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [roundRespect,QuantifierCode.all_subst,logicalType_subst,roundRespectBody_subst]

theorem goodBody_rename (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.goodBody L K T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).goodBody (L.rename ρ) (K.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [goodBody,LogicCode.conj_rename,roundRespect_rename,rename_comp,LogicCode.rename_comp,
    QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem goodBody_instantiate (L : LogicCode S) (K : QuantifierCode S) (T Q p : Expr S) :
    (R.goodBody L K T Q).instantiate p = L.conj (R.roundRespect L K T p) (Q.instantiate p) := by
  simp only [goodBody,Expr.instantiate,LogicCode.conj_subst,roundRespect_subst,
    instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) {T p Q : Expr S}
include h
theorem roundRespectBody_family (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data) :
    L.Family (R.logicalType T) (R.roundRespectBody L.code T p) := by
  intro Δ δ e y hy my
  rw [roundRespectBody_rename,roundRespectBody_instantiate]
  have ht := fun s hs => e.typing (hT s hs)
  have hp' : HasType P Δ (p.rename e.names) ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using e.typing hp
  have hy' : HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hy
  have hr := (h.rename e).round_typed ht (e.moded mT) hy' my
  exact (L.rename e).iff_formula ((h.rename e).eval_formula ht (e.moded mT) hp' (e.moded mp) hy' my)
    ((h.rename e).eval_formula ht (e.moded mT) hp' (e.moded mp) hr.1 hr.2)

theorem roundRespect_formula (K : QuantifierRoute L.witnesses C L.base J)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data) :
    L.Formula (R.roundRespect L.code K.code T p) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.all_formula_family K (h.logical_sorted hT) (h.logical_mode mT)
    (h.logical_sorted hT s hs) (h.roundRespectBody_family hT mT hp mp)

theorem roundRespect_elim (K : QuantifierRoute L.witnesses C L.base J)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    {y : Expr S} (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.roundRespect L.code K.code T p)) :
    Equivalent P Γ γ (R.eval T p y) (R.eval T p (R.round T y)) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have hi := L.all_elim_family K (h.logical_sorted hT) (h.logical_mode mT)
    (h.logical_sorted hT s hs) (h.roundRespectBody_family hT mT hp mp) hy my he
  rw [roundRespectBody_instantiate,LogicSetup.code_iff] at hi
  have hr := h.round_typed hT mT hy my
  exact L.equivalent_of_iff (h.eval_formula hT mT hp mp hy my) (h.eval_formula hT mT hp mp hr.1 hr.2) hi

theorem goodBody_family (K : QuantifierRoute L.witnesses C L.base J)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family (R.predicateType T) Q) :
    L.Family (R.predicateType T) (R.goodBody L.code K.code T Q) := by
  intro Δ δ e p hp mp
  rw [goodBody_rename,goodBody_instantiate]
  have hp' : HasType P Δ p ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using hp
  exact (L.rename e).conj_formula ((h.rename e).roundRespect_formula (K.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT) hp' mp) (hQ _ _ e p hp mp)

theorem good_round (K : QuantifierRoute L.witnesses C L.base J)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family (R.predicateType T) Q)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    {y : Expr S} (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hg : Proves P Γ γ ((R.goodBody L.code K.code T Q).instantiate p)) :
    Equivalent P Γ γ (R.eval T p y) (R.eval T p (R.round T y)) := by
  rw [goodBody_instantiate,LogicSetup.code_conj] at hg
  exact h.roundRespect_elim K hT mT hp mp hy my
    (L.conj_left (h.roundRespect_formula K hT mT hp mp) (hQ.instantiate hp mp) hg)
end Formed
end ChannelCode

namespace LogicSetup.Formula
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {A B : Expr S}
/-- Binder-safe packaging of a pair of uniform proof transformers. -/
theorem equivalent_of_future (hA : L.Formula A) (hB : L.Formula B)
    (hab : ∀ Δ δ (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names))
    (hba : ∀ Δ δ (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (B.rename e.names) → Proves P Δ δ (A.rename e.names)) : Equivalent P Γ γ A B := by
  obtain ⟨s,hs⟩ := hA.sorted L
  obtain ⟨t,ht⟩ := hB.sorted L
  exact ⟨hab _ _ (Embedding.cons hs .proof) (Proves.of_var hs),
    hba _ _ (Embedding.cons ht .proof) (Proves.of_var ht)⟩
end LogicSetup.Formula
namespace ChannelCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (KY : QuantifierRoute L.witnesses C L.base J)
    (KP : QuantifierRoute L.witnesses C L.base H)
    {T Q y : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family (R.predicateType T) Q)
include h hT mT hQ
 theorem relation_round (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    Proves P Γ γ (R.relation L.code KP.code T (R.goodBody L.code KY.code T Q) y (R.round T y)) := by
  have hr := h.round_typed hT mT hy my
  apply h.relation_intro KP hT mT (h.goodBody_family KY hT mT hQ) hy my hr.1 hr.2
  intro Δ δ e p hp mp hg
  have hq : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
      (Q.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hQ.rename e
  have hg' : Proves P Δ δ (((R.rename e.names).goodBody (L.rename e).code (KY.rename e).code
    (T.rename e.names) (Q.rename (Expr.liftRen e.names))).instantiate p) := by
    simpa only [goodBody_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using hg
  simpa only [round_rename] using (h.rename e).good_round (KY.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT) hq hp mp
    (by simpa only [logicalType_rename] using e.typing hy) (e.moded my) hg'
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (K : QuantifierRoute L.witnesses C L.base H)
    {T G a a' c c' : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hG : L.Family (R.predicateType T) G)
include h hT mT hG
 theorem relation_congr (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data)
    (ha' : HasType P Γ a' (R.logicalType T)) (ma' : WellModed γ a' .data)
    (hc : HasType P Γ c (R.logicalType T)) (mc : WellModed γ c .data)
    (hc' : HasType P Γ c' (R.logicalType T)) (mc' : WellModed γ c' .data)
    (he : Proves P Γ γ (R.relation L.code K.code T G a a'))
    (hf : Proves P Γ γ (R.relation L.code K.code T G c c')) :
    Equivalent P Γ γ (R.relation L.code K.code T G a c) (R.relation L.code K.code T G a' c') := by
  have h₁ := h.relation_formula K hT mT hG ha ma hc mc
  have h₂ := h.relation_formula K hT mT hG ha' ma' hc' mc'
  have forward (a b c d : Expr S) (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data)
      (hb : HasType P Γ b (R.logicalType T)) (mb : WellModed γ b .data)
      (hc : HasType P Γ c (R.logicalType T)) (mc : WellModed γ c .data)
      (hd : HasType P Γ d (R.logicalType T)) (md : WellModed γ d .data)
      (he : Proves P Γ γ (R.relation L.code K.code T G a b))
      (hf : Proves P Γ γ (R.relation L.code K.code T G c d)) :
      ∀ Δ δ (e : Embedding P Γ γ Δ δ),
        Proves P Δ δ ((R.relation L.code K.code T G a c).rename e.names) →
        Proves P Δ δ ((R.relation L.code K.code T G b d).rename e.names) := by
    intro Δ δ e hu
    have ht := fun s hs => e.typing (hT s hs)
    have mt := e.moded mT
    have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
        (G.rename (Expr.liftRen e.names)) := by simpa only [predicateType_rename] using hG.rename e
    have ta : HasType P Δ (a.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
      simpa only [logicalType_rename] using e.typing ha
    have tb : HasType P Δ (b.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
      simpa only [logicalType_rename] using e.typing hb
    have tc : HasType P Δ (c.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
      simpa only [logicalType_rename] using e.typing hc
    have td : HasType P Δ (d.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
      simpa only [logicalType_rename] using e.typing hd
    have he' := he.rename e
    have hf' := hf.rename e
    simp only [relation_rename] at hu he' hf' ⊢
    exact (h.rename e).relation_trans (K.rename e) ht mt hg tb (e.moded mb) ta (e.moded ma) td (e.moded md)
      ((h.rename e).relation_symm (K.rename e) ht mt hg ta (e.moded ma) tb (e.moded mb) he')
      ((h.rename e).relation_trans (K.rename e) ht mt hg ta (e.moded ma) tc (e.moded mc) td (e.moded md) hu hf')
  exact h₁.equivalent_of_future h₂ (forward a a' c c' ha ma ha' ma' hc mc hc' mc' he hf)
    (forward a' a c' c ha' ma' ha ma hc' mc' hc mc
      (h.relation_symm K hT mT hG ha ma ha' ma' he) (h.relation_symm K hT mT hG hc mc hc' mc' hf))
end ChannelCode.Formed

namespace Expr
theorem liftSub_single_liftRen_succ (a : Expr S) :
    liftSub (single a) ∘ liftRen Nat.succ = var := by
  funext n; cases n <;> rfl
end Expr
namespace LogicCode
variable (L : LogicCode S)
theorem guardBody_subst (G Q : Expr S) (σ : Nat → Expr S) :
    (L.guardBody G Q).subst (Expr.liftSub σ) =
      (L.subst σ).guardBody (G.subst (Expr.liftSub σ)) (Q.subst (Expr.liftSub σ)) := by
  simp only [guardBody,imp_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem guardAll_subst (K : QuantifierCode S) (T G Q : Expr S) (σ : Nat → Expr S) :
    (L.guardAll K T G Q).subst σ =
      (L.subst σ).guardAll (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (Q.subst (Expr.liftSub σ)) := by
  simp only [guardAll,QuantifierCode.all_subst,guardBody_subst]
end LogicCode
namespace ChannelCode
variable (R : ChannelCode S)
theorem evalPredBody_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.evalPredBody T y).subst (Expr.liftSub σ) =
      (R.subst σ).evalPredBody (T.subst σ) (y.subst σ) := by
  simp only [evalPredBody,eval_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem compareBody_subst (L : LogicCode S) (T y z : Expr S) (σ : Nat → Expr S) :
    (R.compareBody L T y z).subst (Expr.liftSub σ) =
      (R.subst σ).compareBody (L.subst σ) (T.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,evalPredBody_subst,LogicCode.subst,LogicCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem relation_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.relation L K T G y z).subst σ =
      (R.subst σ).relation (L.subst σ) (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [relation,LogicCode.guardAll_subst,predicateType_subst,compareBody_subst]

/-- Source class callback w ↦ (w ∼ y); G retains its predicate binder. -/
def classBody (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) :=
  (R.rename Nat.succ).relation (L.rename Nat.succ) (K.rename Nat.succ) (T.rename Nat.succ)
    (G.rename (Expr.liftRen Nat.succ)) (.var 0) (y.rename Nat.succ)
def classPred (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) :=
  R.pred T (R.classBody L K T G y)
def unionBody (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) :=
  (L.rename Nat.succ).disj (R.classBody L K T G y) (R.classBody L K T G z)
def unionPred (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) :=
  R.pred T (R.unionBody L K T G y z)

theorem classBody_rename (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (ρ : Nat → Nat) :
    (R.classBody L K T G y).rename (Expr.liftRen ρ) =
      (R.rename ρ).classBody (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) := by
  simp only [classBody,relation_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem classBody_instantiate (L : LogicCode S) (K : QuantifierCode S) (T G y w : Expr S) :
    (R.classBody L K T G y).instantiate w = R.relation L K T G w y := by
  simp only [classBody,Expr.instantiate,relation_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_rename,
    Expr.liftSub_single_liftRen_succ,Expr.subst,Expr.single,
    show Expr.single w ∘ Nat.succ = (Expr.var : Nat → Expr S) from rfl,Expr.subst_var]

theorem unionBody_instantiate (L : LogicCode S) (K : QuantifierCode S) (T G y z w : Expr S) :
    (R.unionBody L K T G y z).instantiate w =
      L.disj (R.relation L K T G w y) (R.relation L K T G w z) := by
  change ((L.rename Nat.succ).disj (R.classBody L K T G y) (R.classBody L K T G z)).subst (Expr.single w) = _
  rw [LogicCode.disj_subst,LogicCode.instantiate_raise]
  change L.disj ((R.classBody L K T G y).instantiate w) ((R.classBody L K T G z).instantiate w) = _
  rw [classBody_instantiate,classBody_instantiate]

namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (K : QuantifierRoute L.witnesses C L.base H)
    {T G Q y z w : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
include h hT mT
 theorem classBody_family (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Family (R.logicalType T) (R.classBody L.code K.code T G y) := by
  intro Δ δ e w hw mw
  rw [classBody_rename,classBody_instantiate]
  have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
      (G.rename (Expr.liftRen e.names)) := by simpa only [predicateType_rename] using hG.rename e
  exact (h.rename e).relation_formula (K.rename e) (fun s hs => e.typing (hT s hs)) (e.moded mT) hg
    (by simpa only [logicalType_rename] using hw) mw
    (by simpa only [logicalType_rename] using e.typing hy) (e.moded my)

 theorem unionBody_family (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Family (R.logicalType T) (R.unionBody L.code K.code T G y z) :=
  (h.classBody_family K hT mT hG hy my).code_disj (h.classBody_family K hT mT hG hz mz)

 theorem classPred_typed (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    HasType P Γ (R.classPred L.code K.code T G y) (R.predicateType T) ∧
      WellModed γ (R.classPred L.code K.code T G y) .data :=
  h.pred_typed hT mT (h.classBody_family K hT mT hG hy my) hs

 theorem unionPred_typed (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    HasType P Γ (R.unionPred L.code K.code T G y z) (R.predicateType T) ∧
      WellModed γ (R.unionPred L.code K.code T G y z) .data :=
  h.pred_typed hT mT (h.unionBody_family K hT mT hG hy my hz mz) hs

 theorem class_evaluation (KY : QuantifierRoute L.witnesses C L.base J)
    (hQ : L.Family (R.predicateType T) Q)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hw : HasType P Γ w (R.logicalType T)) (mw : WellModed γ w .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    Equivalent P Γ γ (R.eval T (R.classPred L.code K.code T (R.goodBody L.code KY.code T Q) y) w)
      (R.relation L.code K.code T (R.goodBody L.code KY.code T Q) w y) := by
  have hg := h.goodBody_family KY hT mT hQ
  have hb := h.classBody_family K hT mT hg hy my
  have he := h.pred_evaluation hT mT hb hs hw mw
  rw [classBody_instantiate] at he
  have hr := h.round_typed hT mT hw mw
  have hc := h.relation_congr K hT mT hg hw mw hr.1 hr.2 hy my hy my
    (h.relation_round KY K hT mT hQ hw mw) (h.relation_refl K hT mT hg hy my)
  have ht := h.classPred_typed K hT mT hg hy my hs
  exact (h.eval_formula hT mT ht.1 ht.2 hw mw).equivalent_trans
    (h.relation_formula K hT mT hg hr.1 hr.2 hy my)
    (h.relation_formula K hT mT hg hw mw hy my) he hc.symm
end Formed
end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
def negBody (Q : Expr S) := (L.rename Nat.succ).neg Q
def ex (K : QuantifierCode S) (T Q : Expr S) := L.neg (K.all T (L.negBody Q))
theorem negBody_rename (Q : Expr S) (ρ : Nat → Nat) :
    (L.negBody Q).rename (Expr.liftRen ρ) = (L.rename ρ).negBody (Q.rename (Expr.liftRen ρ)) := by
  simp only [negBody,neg_rename,rename_comp]
  rfl
theorem negBody_instantiate (Q a : Expr S) : (L.negBody Q).instantiate a = L.neg (Q.instantiate a) := by
  simp only [negBody,Expr.instantiate,neg_subst,instantiate_raise]
theorem negBody_subst (Q : Expr S) (σ : Nat → Expr S) :
    (L.negBody Q).subst (Expr.liftSub σ) = (L.subst σ).negBody (Q.subst (Expr.liftSub σ)) := by
  simp only [negBody,neg_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem ex_rename (K : QuantifierCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (L.ex K T Q).rename ρ = (L.rename ρ).ex (K.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [ex,neg_rename,QuantifierCode.all_rename,negBody_rename]
theorem ex_subst (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (L.ex K T Q).subst σ = (L.subst σ).ex (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [ex,neg_subst,QuantifierCode.all_subst,negBody_subst]
end LogicCode
namespace LogicSetup

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {I : Set S} (K : QuantifierRoute L.witnesses C L.base I)
    {T Q B : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family T Q)
include hT mT hQ
theorem ex_formula : L.Formula (L.code.ex K.code T Q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.neg_formula (L.all_formula_family K hT mT (hT s hs) hQ.code_neg)

theorem ex_intro {a : Expr S} (ha : HasType P Γ a T) (ma : WellModed γ a .data)
    (hp : Proves P Γ γ (Q.instantiate a)) : Proves P Γ γ (L.code.ex K.code T Q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have hall := L.all_formula_family K hT mT (hT s hs) hQ.code_neg
  apply L.imp_intro_future hall L.bottom_formula
  intro Δ δ e hn
  have ht := fun r hr => e.typing (hT r hr)
  have hq := hQ.rename e
  have han : Proves P Δ δ (all (L := L.rename e) (K.rename e) (T.rename e.names)
      ((L.rename e).code.negBody (Q.rename (Expr.liftRen e.names)))) := by
    change Proves P Δ δ ((K.code.all T (L.code.negBody Q)).rename e.names) at hn
    change Proves P Δ δ ((K.rename e).code.all (T.rename e.names)
      ((L.rename e).code.negBody (Q.rename (Expr.liftRen e.names))))
    simpa only [QuantifierCode.all_rename,LogicCode.negBody_rename,
      LogicSetup.code_rename,QuantifierRoute.code_rename] using hn
  have hi := (L.rename e).all_elim_family (K.rename e) ht (e.moded mT) (e.typing (hT s hs))
    hq.code_neg (e.typing ha) (e.moded ma) han
  change Proves P Δ δ (((L.rename e).code.negBody (Q.rename (Expr.liftRen e.names))).instantiate (a.rename e.names)) at hi
  rw [LogicCode.negBody_instantiate,code_neg] at hi
  have hp' : Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate (a.rename e.names)) := by
    simpa only [Expr.instantiate_rename] using hp.rename e
  have hf := hq.instantiate (e.typing ha) (e.moded ma)
  exact (L.rename e).imp_elim hf (L.rename e).bottom_formula hi hp'

/-- The elimination target has no free locally opened witness. Its callback is
uniform over every future embedding, preserving the source freshness condition. -/
theorem ex_elim (hB : L.Formula B) (hp : Proves P Γ γ (L.code.ex K.code T Q))
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
      HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a) →
      Proves P Δ δ (B.rename e.names)) : Proves P Γ γ B := by
  apply L.dne hB
  apply L.imp_intro_future (L.neg_formula hB) L.bottom_formula
  intro Δ δ e hn
  have ht := fun s hs => e.typing (hT s hs)
  have hq := hQ.rename e
  have hn' : Proves P Δ δ ((L.rename e).neg (B.rename e.names)) := by
    simpa only [neg,imp_rename,bottom_rename] using hn
  have hall : Proves P Δ δ ((L.rename e).code.guardAll (K.rename e).code (T.rename e.names)
      (Q.rename (Expr.liftRen e.names)) ((L.rename e).bottom.rename Nat.succ)) := by
    apply (L.rename e).guardAll_intro (K.rename e) ht (e.moded mT) hq (.constant (L.rename e).bottom_formula)
    intro Θ θ f a ha ma hqa
    have ha' : HasType P Θ a (T.rename (f.names ∘ e.names)) := by
      simpa only [Expr.rename_comp] using ha
    have hqa' : Proves P Θ θ ((Q.rename (Expr.liftRen (f.names ∘ e.names))).instantiate a) := by
      simpa only [Expr.rename_comp,Expr.lifted_comp] using hqa
    have hb' := hh Θ θ (e.comp f) a ha' ma hqa'
    have hf : ((L.rename e).rename f).Formula (B.rename (f.names ∘ e.names)) := by
      simpa only [Expr.rename_comp] using (hB.rename e).rename f
    have hnb : Proves P Θ θ (((L.rename e).rename f).neg (B.rename (f.names ∘ e.names))) := by
      simpa only [neg,imp_rename,bottom_rename,Expr.rename_comp] using hn'.rename f
    have hb'' : Proves P Θ θ (B.rename (f.names ∘ e.names)) := hb'
    have hb0 := ((L.rename e).rename f).imp_elim hf ((L.rename e).rename f).bottom_formula hnb hb''
    have hconst : ((((L.rename e).bottom.rename Nat.succ).rename (Expr.liftRen f.names)).instantiate a) =
        (L.rename e).bottom.rename f.names := by
      rw [Expr.rename_comp]
      rw [show Expr.liftRen f.names ∘ Nat.succ = Nat.succ ∘ f.names from rfl,
        ← Expr.rename_comp,Expr.instantiate_raise]
    exact hconst.symm ▸ hb0
  have hex : Proves P Δ δ ((L.rename e).neg
      ((K.rename e).code.all (T.rename e.names) ((L.rename e).code.negBody (Q.rename (Expr.liftRen e.names))))) := by
    simpa only [LogicCode.ex,LogicCode.neg_rename,QuantifierCode.all_rename,LogicCode.negBody_rename,
      ← LogicSetup.code_neg,LogicSetup.code_rename,QuantifierRoute.code_rename] using hp.rename e
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have hfa := (L.rename e).all_formula_family (K.rename e) ht (e.moded mT) (e.typing (hT s hs)) hq.code_neg
  exact (L.rename e).imp_elim hfa (L.rename e).bottom_formula hex hall
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {I : Set S} (K : QuantifierRoute L.witnesses C L.base I)
    {T Q R : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family T Q) (hR : L.Family T R)
include hT mT hQ hR
/-- Explicit uniform quantifier transport; no fixture of local witnesses leaks. -/
theorem all_map_future
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
      HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a) →
      Proves P Δ δ ((R.rename (Expr.liftRen e.names)).instantiate a))
    (hp : Proves P Γ γ (K.code.all T Q)) : Proves P Γ γ (K.code.all T R) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  apply L.all_intro_future K hT mT (hT s hs) hR
  intro Δ δ e a ha ma
  have hp' : Proves P Δ δ ((K.rename e).code.all (T.rename e.names) (Q.rename (Expr.liftRen e.names))) := by
    simpa only [QuantifierCode.all_rename,QuantifierRoute.code_rename] using hp.rename e
  exact hh Δ δ e a ha ma ((L.rename e).all_elim_family (K.rename e)
    (fun t ht => e.typing (hT t ht)) (e.moded mT) (e.typing (hT s hs)) (hQ.rename e) ha ma hp')

theorem all_equivalent_future
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
      HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Equivalent P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a)
        ((R.rename (Expr.liftRen e.names)).instantiate a)) :
    Equivalent P Γ γ (K.code.all T Q) (K.code.all T R) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have fq := L.all_formula_family K hT mT (hT s hs) hQ
  have fr := L.all_formula_family K hT mT (hT s hs) hR
  have forward {U V : Expr S} (hU : L.Family T U) (hV : L.Family T V)
      (hx : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
        HasType P Δ a (T.rename e.names) → WellModed δ a .data →
        Equivalent P Δ δ ((U.rename (Expr.liftRen e.names)).instantiate a)
          ((V.rename (Expr.liftRen e.names)).instantiate a)) :
      ∀ Δ δ (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ ((K.code.all T U).rename e.names) →
      Proves P Δ δ ((K.code.all T V).rename e.names) := by
    intro Δ δ e hp
    simp only [QuantifierCode.all_rename] at hp ⊢
    apply (L.rename e).all_map_future (K.rename e) (fun t ht => e.typing (hT t ht))
      (e.moded mT) (hU.rename e) (hV.rename e) ?_ hp
    intro Θ θ f a ha ma hu
    have ha' : HasType P Θ a (T.rename (f.names ∘ e.names)) := by
      simpa only [Expr.rename_comp] using ha
    have he := hx Θ θ (e.comp f) a ha' ma
    have hu' : Proves P Θ θ ((U.rename (Expr.liftRen (f.names ∘ e.names))).instantiate a) := by
      simpa only [Expr.rename_comp,Expr.lifted_comp] using hu
    simpa only [Expr.rename_comp,Expr.lifted_comp,Embedding.comp] using he.1.prove hu'
  exact fq.equivalent_of_future fr (forward hQ hR hh)
    (forward hR hQ (fun Δ δ e a ha ma => (hh Δ δ e a ha ma).symm))

theorem ex_equivalent_future
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
      HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Equivalent P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a)
        ((R.rename (Expr.liftRen e.names)).instantiate a)) :
    Equivalent P Γ γ (L.code.ex K.code T Q) (L.code.ex K.code T R) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have he := L.all_equivalent_future K hT mT hQ.code_neg hR.code_neg (by
    intro Δ δ e a ha ma
    change Equivalent P Δ δ (((L.code.negBody Q).rename (Expr.liftRen e.names)).instantiate a)
      (((L.code.negBody R).rename (Expr.liftRen e.names)).instantiate a)
    simp only [LogicCode.negBody_rename,LogicCode.negBody_instantiate]
    exact (L.rename e).neg_equivalent (hQ _ _ e a ha ma) (hR _ _ e a ha ma) (hh _ _ e a ha ma))
  exact L.neg_equivalent (L.all_formula_family K hT mT (hT s hs) hQ.code_neg)
    (L.all_formula_family K hT mT (hT s hs) hR.code_neg) he
end LogicSetup

namespace ChannelCode
variable (R : ChannelCode S)
theorem pred_rename (T Q : Expr S) (ρ : Nat → Nat) :
    (R.pred T Q).rename ρ = (R.rename ρ).pred (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [pred,DataWrapper.build_rename,rawType_rename,Expr.compose_rename,
    DataWrapper.reencodeBody_rename,DataWrapper.argRen,ite_true,rename]

def evalBody (T p : Expr S) := (R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ) (.var 0)
def predCompareBody (L : LogicCode S) (T p q : Expr S) :=
  (L.rename Nat.succ).iff (R.evalBody T p) (R.evalBody T q)
def predCompare (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) :=
  K.all (R.logicalType T) (R.predCompareBody L T p q)

theorem evalBody_rename (T p : Expr S) (ρ : Nat → Nat) :
    (R.evalBody T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalBody (T.rename ρ) (p.rename ρ) := by
  simp only [evalBody,eval_rename,rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem evalBody_instantiate (T p y : Expr S) :
    (R.evalBody T p).instantiate y = R.eval T p y := by
  simp only [evalBody,Expr.instantiate,eval_subst,instantiate_raise,Expr.subst_lift_single,
    Expr.subst,Expr.single]
theorem evalBody_subst (T p : Expr S) (σ : Nat → Expr S) :
    (R.evalBody T p).subst (Expr.liftSub σ) = (R.subst σ).evalBody (T.subst σ) (p.subst σ) := by
  simp only [evalBody,eval_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem predCompareBody_rename (L : LogicCode S) (T p q : Expr S) (ρ : Nat → Nat) :
    (R.predCompareBody L T p q).rename (Expr.liftRen ρ) =
      (R.rename ρ).predCompareBody (L.rename ρ) (T.rename ρ) (p.rename ρ) (q.rename ρ) := by
  simp only [predCompareBody,LogicCode.iff_rename,LogicCode.rename_comp,evalBody_rename]
  rfl
theorem predCompareBody_subst (L : LogicCode S) (T p q : Expr S) (σ : Nat → Expr S) :
    (R.predCompareBody L T p q).subst (Expr.liftSub σ) =
      (R.subst σ).predCompareBody (L.subst σ) (T.subst σ) (p.subst σ) (q.subst σ) := by
  simp only [predCompareBody,LogicCode.iff_subst,evalBody_subst,LogicCode.subst,LogicCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem predCompareBody_instantiate (L : LogicCode S) (T p q y : Expr S) :
    (R.predCompareBody L T p q).instantiate y = L.iff (R.eval T p y) (R.eval T q y) := by
  change ((L.rename Nat.succ).iff (R.evalBody T p) (R.evalBody T q)).subst (Expr.single y) = _
  rw [LogicCode.iff_subst,LogicCode.instantiate_raise]
  change L.iff ((R.evalBody T p).instantiate y) ((R.evalBody T q).instantiate y) = _
  rw [evalBody_instantiate,evalBody_instantiate]
theorem predCompare_rename (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) (ρ : Nat → Nat) :
    (R.predCompare L K T p q).rename ρ =
      (R.rename ρ).predCompare (L.rename ρ) (K.rename ρ) (T.rename ρ) (p.rename ρ) (q.rename ρ) := by
  simp only [predCompare,QuantifierCode.all_rename,logicalType_rename,predCompareBody_rename]
theorem predCompare_subst (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) (σ : Nat → Expr S) :
    (R.predCompare L K T p q).subst σ =
      (R.subst σ).predCompare (L.subst σ) (K.subst σ) (T.subst σ) (p.subst σ) (q.subst σ) := by
  simp only [predCompare,QuantifierCode.all_subst,logicalType_subst,predCompareBody_subst]
namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) {T p q y : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
include h hT mT
 theorem evalBody_family (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data) :
    L.Family (R.logicalType T) (R.evalBody T p) := by
  intro Δ δ e y hy my
  rw [evalBody_rename,evalBody_instantiate]
  exact (h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [predicateType_rename] using e.typing hp) (e.moded mp)
    (by simpa only [logicalType_rename] using hy) my
 theorem predCompareBody_family
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data) :
    L.Family (R.logicalType T) (R.predCompareBody L.code T p q) :=
  (h.evalBody_family hT mT hp mp).code_iff (h.evalBody_family hT mT hq mq)

 theorem predCompare_formula (K : QuantifierRoute L.witnesses C L.base J)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data) :
    L.Formula (R.predCompare L.code K.code T p q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.all_formula_family K (h.logical_sorted hT) (h.logical_mode mT) (h.logical_sorted hT s hs)
    (h.predCompareBody_family hT mT hp mp hq mq)

 theorem predCompare_elim (K : QuantifierRoute L.witnesses C L.base J)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.predCompare L.code K.code T p q)) :
    Equivalent P Γ γ (R.eval T p y) (R.eval T q y) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have he' := L.all_elim_family K (h.logical_sorted hT) (h.logical_mode mT) (h.logical_sorted hT s hs)
    (h.predCompareBody_family hT mT hp mp hq mq) hy my he
  rw [predCompareBody_instantiate,LogicSetup.code_iff] at he'
  exact L.equivalent_of_iff (h.eval_formula hT mT hp mp hy my) (h.eval_formula hT mT hq mq hy my) he'

 theorem predCompare_intro (K : QuantifierRoute L.witnesses C L.base J)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) → WellModed δ y .data →
      Equivalent P Δ δ ((R.rename e.names).eval (T.rename e.names) (p.rename e.names) y)
        ((R.rename e.names).eval (T.rename e.names) (q.rename e.names) y)) :
    Proves P Γ γ (R.predCompare L.code K.code T p q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  apply L.all_intro_future K (h.logical_sorted hT) (h.logical_mode mT) (h.logical_sorted hT s hs)
    (h.predCompareBody_family hT mT hp mp hq mq)
  intro Δ δ e y hy my
  rw [predCompareBody_rename,predCompareBody_instantiate]
  have ht := fun t ht => e.typing (hT t ht)
  have hy' : HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hy
  exact (L.rename e).iff_of_equivalent
    ((h.rename e).eval_formula ht (e.moded mT)
      (by simpa only [predicateType_rename] using e.typing hp) (e.moded mp) hy' my)
    ((h.rename e).eval_formula ht (e.moded mT)
      (by simpa only [predicateType_rename] using e.typing hq) (e.moded mq) hy' my)
    (hh Δ δ e y hy' my)
end Formed
end ChannelCode

namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {A B A' B' : Expr S}
theorem disj_equivalent (hA : L.Formula A) (hB : L.Formula B)
    (hA' : L.Formula A') (hB' : L.Formula B')
    (he : Equivalent P Γ γ A A') (hf : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.disj A B) (L.disj A' B') := by
  apply L.equivalent_of_iff (L.disj_formula hA hB) (L.disj_formula hA' hB')
  pts_pl L using [he,hf]
end LogicSetup
namespace ChannelCode
variable (R : ChannelCode S)
theorem classPred_rename (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (ρ : Nat → Nat) :
    (R.classPred L K T G y).rename ρ =
      (R.rename ρ).classPred (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) := by
  simp only [classPred,pred_rename,classBody_rename]
theorem unionBody_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.unionBody L K T G y z).rename (Expr.liftRen ρ) =
      (R.rename ρ).unionBody (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [unionBody,LogicCode.disj_rename,LogicCode.rename_comp,classBody_rename]
  rfl
theorem unionPred_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.unionPred L K T G y z).rename ρ =
      (R.rename ρ).unionPred (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [unionPred,pred_rename,unionBody_rename]
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (K : QuantifierRoute L.witnesses C L.base H)
    (KY : QuantifierRoute L.witnesses C L.base J)
    {T Q y z w : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family (R.predicateType T) Q)
include h hT mT hQ

theorem union_evaluation
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    (hw : HasType P Γ w (R.logicalType T)) (mw : WellModed γ w .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    Equivalent P Γ γ (R.eval T (R.unionPred L.code K.code T (R.goodBody L.code KY.code T Q) y z) w)
      (L.disj (R.relation L.code K.code T (R.goodBody L.code KY.code T Q) w y)
        (R.relation L.code K.code T (R.goodBody L.code KY.code T Q) w z)) := by
  have hg := h.goodBody_family KY hT mT hQ
  have hb := h.unionBody_family K hT mT hg hy my hz mz
  have he := h.pred_evaluation hT mT hb hs hw mw
  rw [unionBody_instantiate,LogicSetup.code_disj] at he
  have hr := h.round_typed hT mT hw mw
  have hew := h.relation_round KY K hT mT hQ hw mw
  have hcy := h.relation_congr K hT mT hg hw mw hr.1 hr.2 hy my hy my hew
    (h.relation_refl K hT mT hg hy my)
  have hcz := h.relation_congr K hT mT hg hw mw hr.1 hr.2 hz mz hz mz hew
    (h.relation_refl K hT mT hg hz mz)
  have ht := h.unionPred_typed K hT mT hg hy my hz mz hs
  have f₀ := h.eval_formula hT mT ht.1 ht.2 hw mw
  have f₁ := h.relation_formula K hT mT hg hw mw hy my
  have f₂ := h.relation_formula K hT mT hg hw mw hz mz
  have f₃ := h.relation_formula K hT mT hg hr.1 hr.2 hy my
  have f₄ := h.relation_formula K hT mT hg hr.1 hr.2 hz mz
  exact f₀.equivalent_trans (L.disj_formula f₃ f₄) (L.disj_formula f₁ f₂) he
    (L.disj_equivalent f₃ f₄ f₁ f₂ hcy.symm hcz.symm)

theorem class_comparison
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s))
    (he : Proves P Γ γ (R.relation L.code K.code T (R.goodBody L.code KY.code T Q) y z)) :
    Proves P Γ γ (R.predCompare L.code KY.code T
      (R.classPred L.code K.code T (R.goodBody L.code KY.code T Q) y)
      (R.classPred L.code K.code T (R.goodBody L.code KY.code T Q) z)) := by
  have hg := h.goodBody_family KY hT mT hQ
  have hcy := h.classPred_typed K hT mT hg hy my hs
  have hcz := h.classPred_typed K hT mT hg hz mz hs
  apply h.predCompare_intro hT mT KY hcy.1 hcy.2 hcz.1 hcz.2
  intro Δ δ e w hw mw
  simp only [classPred_rename,goodBody_rename]
  have ht := fun t ht => e.typing (hT t ht)
  have hy' : HasType P Δ (y.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hy
  have hz' : HasType P Δ (z.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hz
  have hs' : HasType P Δ ((R.rename e.names).rawType (T.rename e.names)) (.sort s) := by
    simpa only [rawType_rename,Expr.rename] using e.typing hs
  have hq' : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
      (Q.rename (Expr.liftRen e.names)) := by simpa only [predicateType_rename] using hQ.rename e
  have hg' := (h.rename e).goodBody_family (KY.rename e) ht (e.moded mT) hq'
  have he' : Proves P Δ δ ((R.rename e.names).relation (L.rename e).code (K.rename e).code
      (T.rename e.names) ((R.rename e.names).goodBody (L.rename e).code (KY.rename e).code
        (T.rename e.names) (Q.rename (Expr.liftRen e.names))) (y.rename e.names) (z.rename e.names)) := by
    simpa only [relation_rename,goodBody_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using he.rename e
  have ey := (h.rename e).class_evaluation (K.rename e) ht (e.moded mT) (KY.rename e) hq' hy' (e.moded my) hw mw hs'
  have ez := (h.rename e).class_evaluation (K.rename e) ht (e.moded mT) (KY.rename e) hq' hz' (e.moded mz) hw mw hs'
  have ec := (h.rename e).relation_congr (K.rename e) ht (e.moded mT) hg' hw mw hw mw hy' (e.moded my) hz' (e.moded mz)
    ((h.rename e).relation_refl (K.rename e) ht (e.moded mT) hg' hw mw) he'
  have cy := (h.rename e).classPred_typed (K.rename e) ht (e.moded mT) hg' hy' (e.moded my) hs'
  have cz := (h.rename e).classPred_typed (K.rename e) ht (e.moded mT) hg' hz' (e.moded mz) hs'
  have f₀ := (h.rename e).eval_formula ht (e.moded mT) cy.1 cy.2 hw mw
  have f₁ := (h.rename e).eval_formula ht (e.moded mT) cz.1 cz.2 hw mw
  have f₂ := (h.rename e).relation_formula (K.rename e) ht (e.moded mT) hg' hw mw hy' (e.moded my)
  have f₃ := (h.rename e).relation_formula (K.rename e) ht (e.moded mT) hg' hw mw hz' (e.moded mz)
  exact f₀.equivalent_trans f₂ f₁ ey (f₂.equivalent_trans f₃ f₁ ec ez.symm)
end Formed
end ChannelCode
end PureTypeSystem.Labelled

end OAI
