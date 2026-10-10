import OAI.Computability.TypeSystem.Logic

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} (L : LogicSetup P Γ γ C)
    {A B : Expr S}
theorem neg_equivalent (hA : L.Formula A) (hB : L.Formula B) (he : Equivalent P Γ γ A B) :
    Equivalent P Γ γ (L.neg A) (L.neg B) := by
  apply L.equivalent_of_iff (L.neg_formula hA) (L.neg_formula hB)
  pts_pl L using [he]

theorem sign_equivalent (b : Bool) (hA : L.Formula A) (hB : L.Formula B) (he : Equivalent P Γ γ A B) :
    Equivalent P Γ γ (L.code.sign b A) (L.code.sign b B) := by
  cases b
  · exact L.neg_equivalent hA hB he
  · exact he
end LogicSetup

structure DoubleCode (S : Type u) where
  first : DataWrapper S true
  second : DataWrapper S true
namespace DoubleCode
variable (R : DoubleCode S)
def rename (ρ : Nat → Nat) : DoubleCode S := ⟨R.first.rename ρ,R.second.rename ρ⟩
def subst (σ : Nat → Expr S) : DoubleCode S := ⟨R.first.subst σ,R.second.subst σ⟩
def carrier (T : Expr S) := R.second.apply (R.first.apply T)
def emb (L : LogicCode S) (b : Bool) (T t : Expr S) :=
  R.second.build (R.first.apply T) ((L.rename Nat.succ).sign b (R.first.contraCallback T t))
def bit (L : LogicCode S) (T v : Expr S) :=
  R.second.observe (R.first.apply T) v (R.first.build T (L.top.rename Nat.succ))
def eval (T v Q : Expr S) := R.second.observe (R.first.apply T) v (R.first.build T Q)
def recover (L : LogicCode S) (T v Q : Expr S) :=
  L.cond (R.bit L T v) (R.eval T v Q) (L.neg (R.eval T v Q))

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K : Set S)
structure Formed : Prop where
  first : R.first.Formed L I J
  second : R.second.Formed L J K
namespace Formed
variable {R L I J K}
theorem rename (h : Formed R L I J K) (e : Embedding P Γ γ Δ δ) :
    Formed (R.rename e.names) (L.rename e) I J K := ⟨h.first.rename e,h.second.rename e⟩
variable (h : Formed R L I J K) {T t v Q : Expr S}
include h
theorem sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.carrier T) K := h.second.sorted (h.first.sorted hT)
theorem mode (mT : WellModed γ T .data) : WellModed γ (R.carrier T) .data := h.second.mode (h.first.mode mT)

theorem emb_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    HasType P Γ (R.emb L.code b T t) (R.carrier T) ∧ WellModed γ (R.emb L.code b T t) .data :=
  (h.second.sound (h.first.sorted hT) (h.first.mode mT)).1 _
    ((h.first.contraCallback_family hT mT ht mt).code_sign b)

theorem eval_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hv : HasType P Γ v (R.carrier T)) (mv : WellModed γ v .data)
    (hQ : L.Family T Q) : L.Formula (R.eval T v Q) := by
  have hb := (h.first.sound hT mT).1 Q hQ
  exact (h.second.sound (h.first.sorted hT) (h.first.mode mT)).2 v _ hv mv hb

theorem bit_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hv : HasType P Γ v (R.carrier T)) (mv : WellModed γ v .data) :
    L.Formula (R.bit L.code T v) :=
  h.eval_formula hT mT hv mv (.constant L.top_formula)

theorem rec_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hv : HasType P Γ v (R.carrier T)) (mv : WellModed γ v .data)
    (hQ : L.Family T Q) : L.Formula (R.recover L.code T v Q) :=
  L.cond_formula (h.bit_formula hT mT hv mv) (h.eval_formula hT mT hv mv hQ)
    (L.neg_formula (h.eval_formula hT mT hv mv hQ))

theorem emb_evaluation (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data)
    (hQ : L.Family T Q) :
    Equivalent P Γ γ (R.eval T (R.emb L.code b T t) Q) (L.code.sign b (Q.instantiate t)) := by
  have hf := (h.first.sound hT mT).1 Q hQ
  have hcb := (h.first.contraCallback_family hT mT ht mt).code_sign b
  have he := h.second.cancellation (h.first.sorted hT) (h.first.mode mT) hcb hf
  have he' : Equivalent P Γ γ (R.eval T (R.emb L.code b T t) Q)
      (L.code.sign b (R.first.observe T (R.first.build T Q) t)) := by
    simpa only [DataWrapper.cancelFormula,ite_true,LogicCode.sign_instantiate_raise,DataWrapper.contraCallback_instantiate,eval,emb] using he
  have he₁ := h.first.cancellation hT mT hQ ⟨ht,mt⟩
  have ha := (h.first.sound hT mT).2 _ t hf.1 hf.2 ⟨ht,mt⟩
  have hb := hQ.instantiate ht mt
  have he₂ := L.sign_equivalent b ha hb (by simpa only [DataWrapper.cancelFormula,ite_true] using he₁)
  have hv := h.emb_typed hT mT b ht mt
  have hc := h.eval_formula hT mT hv.1 hv.2 hQ
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact he'.trans he₂ (hc.1 s hs) ((L.sign_formula b ha).1 s hs) ((L.sign_formula b hb).1 s hs)

theorem emb_bit (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    Proves P Γ γ (L.code.sign b (R.bit L.code T (R.emb L.code b T t))) := by
  have hv := h.emb_typed hT mT b ht mt
  have hb := h.bit_formula hT mT hv.1 hv.2
  have he := h.emb_evaluation hT mT b ht mt (.constant L.top_formula)
  simp only [Expr.instantiate_raise] at he
  have hp := L.top_intro
  cases b
  · change Proves P Γ γ (L.neg (R.bit L.code T (R.emb L.code false T t)))
    change Equivalent P Γ γ (R.bit L.code T (R.emb L.code false T t)) (L.neg L.top) at he
    pts_pl L using [he,hp]
  · exact he.2.prove hp

theorem emb_recovery (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data)
    (hQ : L.Family T Q) : Equivalent P Γ γ (R.recover L.code T (R.emb L.code b T t) Q) (Q.instantiate t) := by
  have hv := h.emb_typed hT mT b ht mt
  have hb := h.bit_formula hT mT hv.1 hv.2
  have heval := h.eval_formula hT mT hv.1 hv.2 hQ
  have hqt := hQ.instantiate ht mt
  have he := h.emb_evaluation hT mT b ht mt hQ
  have hp := h.emb_bit hT mT b ht mt
  apply L.equivalent_of_iff (h.rec_formula hT mT hv.1 hv.2 hQ) hqt
  change Proves P Γ γ (L.iff (L.code.cond _ _ (L.neg _)) _)
  cases b
  · change Equivalent P Γ γ _ (L.neg (Q.instantiate t)) at he
    change Proves P Γ γ (L.neg _) at hp
    pts_pl L using [he,hp]
  · change Equivalent P Γ γ _ (Q.instantiate t) at he
    change Proves P Γ γ (R.bit L.code T (R.emb L.code true T t)) at hp
    pts_pl L using [he,hp]
end Formed
end DoubleCode

/-- The fixed odd paths of the first (and later probe) observation channel. -/
structure ChannelCode (S : Type u) where
  logical : DataWrapper S true
  raw : DataWrapper S true
  predicate : DataWrapper S true

namespace ChannelCode
variable (R : ChannelCode S)
def rename (ρ : Nat → Nat) : ChannelCode S :=
  ⟨R.logical.rename ρ,R.raw.rename ρ,R.predicate.rename ρ⟩
def subst (σ : Nat → Expr S) : ChannelCode S :=
  ⟨R.logical.subst σ,R.raw.subst σ,R.predicate.subst σ⟩
def logicalType (T : Expr S) := R.logical.apply T
def rawType (T : Expr S) := R.raw.apply T
def predicateType (T : Expr S) := R.predicate.apply (R.raw.apply T)
def toRaw (T y : Expr S) := DataWrapper.reencode R.logical R.raw T y
def toLog (T c : Expr S) := DataWrapper.reencode R.raw R.logical T c
def round (T y : Expr S) := R.toLog T (R.toRaw T y)
def eval (T p y : Expr S) := R.predicate.observe (R.rawType T) p (R.toRaw T y)
def pred (T Q : Expr S) :=
  R.predicate.build (R.rawType T) (Q.compose (DataWrapper.reencodeBody R.raw R.logical T))

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K H : Set S)
structure Formed : Prop where
  logical : R.logical.Formed L I J
  raw : R.raw.Formed L I K
  predicate : R.predicate.Formed L K H

namespace Formed
variable {R L I J K H}
theorem rename (h : Formed R L I J K H) (e : Embedding P Γ γ Δ δ) :
    Formed (R.rename e.names) (L.rename e) I J K H :=
  ⟨h.logical.rename e,h.raw.rename e,h.predicate.rename e⟩

variable (h : Formed R L I J K H) {T y c p Q : Expr S}
include h

theorem logical_sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.logicalType T) J := h.logical.sorted hT
theorem raw_sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.rawType T) K := h.raw.sorted hT
theorem predicate_sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.predicateType T) H := h.predicate.sorted (h.raw.sorted hT)
theorem logical_mode (mT : WellModed γ T .data) : WellModed γ (R.logicalType T) .data := h.logical.mode mT
theorem raw_mode (mT : WellModed γ T .data) : WellModed γ (R.rawType T) .data := h.raw.mode mT
theorem predicate_mode (mT : WellModed γ T .data) : WellModed γ (R.predicateType T) .data := h.predicate.mode (h.raw.mode mT)

theorem toRaw_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    HasType P Γ (R.toRaw T y) (R.rawType T) ∧ WellModed γ (R.toRaw T y) .data :=
  h.logical.reencode_typed h.raw hT mT hy my

theorem toLog_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hc : HasType P Γ c (R.rawType T)) (mc : WellModed γ c .data) :
    HasType P Γ (R.toLog T c) (R.logicalType T) ∧ WellModed γ (R.toLog T c) .data :=
  h.raw.reencode_typed h.logical hT mT hc mc

theorem round_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    HasType P Γ (R.round T y) (R.logicalType T) ∧ WellModed γ (R.round T y) .data := by
  have hh := h.toRaw_typed hT mT hy my
  exact h.toLog_typed hT mT hh.1 hh.2

theorem eval_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Formula (R.eval T p y) := by
  have hh := h.toRaw_typed hT mT hy my
  exact (h.predicate.sound (h.raw.sorted hT) (h.raw.mode mT)).2 p _ hp mp hh

theorem pred_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family (R.logicalType T) Q)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    HasType P Γ (R.pred T Q) (R.predicateType T) ∧ WellModed γ (R.pred T Q) .data :=
  (h.predicate.sound (h.raw.sorted hT) (h.raw.mode mT)).1 _
    (hQ.compose (h.raw.reencode_map h.logical hT mT hs) hs)

theorem primitive_round (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) {a : Expr S}
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    Equivalent P Γ γ (R.logical.observe T (R.round T y) a) (R.logical.observe T y a) := by
  have hraw := h.toRaw_typed hT mT hy my
  have hround := h.round_typed hT mT hy my
  have he₁ := h.raw.reencode_evaluation h.logical hT mT hraw.1 hraw.2 ha ma
  have he₂ := h.logical.reencode_evaluation h.raw hT mT hy my ha ma
  have hf₁ := (h.logical.sound hT mT).2 _ a hround.1 hround.2 ⟨ha,ma⟩
  have hf₂ := (h.raw.sound hT mT).2 _ a hraw.1 hraw.2 ⟨ha,ma⟩
  have hf₃ := (h.logical.sound hT mT).2 _ a hy my ⟨ha,ma⟩
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact he₁.trans he₂ (hf₁.1 s hs) (hf₂.1 s hs) (hf₃.1 s hs)

theorem pred_evaluation (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family (R.logicalType T) Q)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s))
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    Equivalent P Γ γ (R.eval T (R.pred T Q) y) (Q.instantiate (R.round T y)) := by
  have hraw := h.toRaw_typed hT mT hy my
  have hcb := hQ.compose (h.raw.reencode_map h.logical hT mT hs) hs
  simpa only [eval,pred,rawType,DataWrapper.cancelFormula,ite_true,Expr.compose_instantiate,
    DataWrapper.reencodeBody_instantiate,round,toLog] using
      h.predicate.cancellation (h.raw.sorted hT) (h.raw.mode mT) hcb hraw
end Formed
end ChannelCode

namespace DataWrapper.Formed
theorem of_secondary_path {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} (hC : IsComponent (PrimaryEdge P) C)
    {r I J : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    {b : Bool} (hp : SignedPath (SecondaryEdge P C) I J b) :
    ∃ R : DataWrapper S b, R.Formed L I J := by
  cases b <;> exact (DataWrapper.Formed.identity (L := L) (I := I)).path hC hr ho hp
end DataWrapper.Formed

/-- All roles use fixed path syntax selected once from the forbidden
configuration. In particular the shared raw wrapper is not
reselected when constructing a query, bundle, or the second channel. -/
structure ChannelSetup {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) where
  seed : S
  domain : Set S
  codomain : Set S
  base : Set S
  rawVertex : Set S
  tailVertex : Set S
  funVertex : Set S
  logicalVertex : Set S
  predVertex : Set S
  mainTriple : ProfileTriple P domain codomain base
  funTriple : ProfileTriple P rawVertex tailVertex funVertex
  ax : (AxProfile P seed).Nonempty
  directLogical : DirectLayer P C logicalVertex
  directPred : DirectLayer P C predVertex
  initialParity : Bool
  initial : DataWrapper S initialParity
  initialFormed : initial.Formed L {seed} base
  channel : ChannelCode S
  channelFormed : channel.Formed L base logicalVertex rawVertex predVertex
  returnPath : DataWrapper S true
  returnFormed : returnPath.Formed L rawVertex base
  funPath : DataWrapper S false
  funFormed : funPath.Formed L funVertex codomain
  lifting : PositiveDataWrapper S
  liftingFormed : lifting.Formed L.witnesses (AxProfile P seed) domain
  tail : DataTail S
  tailFormed : tail.Formed L tailVertex

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C}

def doubled (K : ChannelSetup L) : DoubleCode S := ⟨K.returnPath,K.channel.raw⟩
theorem doubled_formed (K : ChannelSetup L) : K.doubled.Formed L K.rawVertex K.base K.rawVertex :=
  ⟨K.returnFormed,K.channelFormed.raw⟩

theorem exists_setup (hC : IsComponent (PrimaryEdge P) C)
    (ho : ∃ r ∈ C, SignedPath (PrimaryEdge P) r r true)
    (hf : ForbiddenConfiguration P C) : Nonempty (ChannelSetup L) := by
  obtain ⟨r,hr,ho⟩ := ho
  obtain ⟨D,hD,I,J,k,s,p,n,g,j,h,ht,hJ,hk,hs,hax,hζ,htr,hp,hg,hn,hα,hβ,hκ,hj,hLam,hh,_,hη⟩ := hf.channel_paths
  obtain ⟨b,hδ⟩ := hD.connected hs hk
  obtain ⟨Rδ,hRδ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hδ
  obtain ⟨Rα,hRα⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hα
  obtain ⟨Rβ,hRβ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hβ
  obtain ⟨Rκ,hRκ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hκ
  obtain ⟨RLam,hRLam⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hLam
  obtain ⟨Rη,hRη⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hη
  obtain ⟨Rζ,hRζ⟩ := (PositiveDataWrapper.Formed.identity (W := L.witnesses) (I := AxProfile P s)).path hζ
  obtain ⟨U,hU⟩ := DataTail.Formed.exists_tail (L := L) hC hr ho hn
  exact ⟨⟨s,I,J,k,p,n,g,j,h,ht,htr,hax,hj,hh,b,Rδ,hRδ,
    ⟨RLam,Rα,Rη⟩,⟨hRLam,hRα,hRη⟩,Rβ,hRβ,Rκ,hRκ,Rζ,hRζ,U,hU⟩⟩
end ChannelSetup

namespace LogicCode
variable (L : LogicCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (L.rename ρ).subst σ = L.subst (σ ∘ ρ) := by
  cases L; simp only [rename,subst,Expr.subst_rename,ProofWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (L.subst σ).rename ρ = L.subst (fun i => (σ i).rename ρ) := by
  cases L; simp only [rename,subst,Expr.rename_subst,ProofWrapper.rename_subst]
end LogicCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun i => (σ i).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,rename,DataWrapper.apply_rename]
theorem carrier_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.carrier T).subst σ = (R.subst σ).carrier (T.subst σ) := by
  simp only [carrier,subst,DataWrapper.apply_subst]
theorem emb_rename (L : LogicCode S) (b : Bool) (T t : Expr S) (ρ : Nat → Nat) :
    (R.emb L b T t).rename ρ = (R.rename ρ).emb (L.rename ρ) b (T.rename ρ) (t.rename ρ) := by
  simp only [emb,DataWrapper.build_rename,DataWrapper.apply_rename,DataWrapper.argRen,ite_true,
    LogicCode.sign_rename,LogicCode.rename_comp,DataWrapper.contraCallback_rename,rename]
  rfl
theorem emb_subst (L : LogicCode S) (b : Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.emb L b T t).subst σ = (R.subst σ).emb (L.subst σ) b (T.subst σ) (t.subst σ) := by
  simp only [emb,DataWrapper.build_subst,DataWrapper.apply_subst,DataWrapper.argSub,ite_true,
    LogicCode.sign_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    DataWrapper.contraCallback_subst,subst]
  rfl
theorem eval_rename (T v Q : Expr S) (ρ : Nat → Nat) :
    (R.eval T v Q).rename ρ = (R.rename ρ).eval (T.rename ρ) (v.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [eval,DataWrapper.observe_rename,DataWrapper.build_rename,DataWrapper.apply_rename,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,rename]
theorem eval_subst (T v Q : Expr S) (σ : Nat → Expr S) :
    (R.eval T v Q).subst σ = (R.subst σ).eval (T.subst σ) (v.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [eval,DataWrapper.observe_subst,DataWrapper.build_subst,DataWrapper.apply_subst,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,subst]
theorem bit_rename (L : LogicCode S) (T v : Expr S) (ρ : Nat → Nat) :
    (R.bit L T v).rename ρ = (R.rename ρ).bit (L.rename ρ) (T.rename ρ) (v.rename ρ) := by
  change (R.eval T v (L.top.rename Nat.succ)).rename ρ = _
  rw [eval_rename,Expr.rename_comp]
  change _ = (R.rename ρ).eval _ _ ((L.rename ρ).top.rename Nat.succ)
  rw [← LogicCode.top_rename,Expr.rename_comp]
  rfl
theorem bit_subst (L : LogicCode S) (T v : Expr S) (σ : Nat → Expr S) :
    (R.bit L T v).subst σ = (R.subst σ).bit (L.subst σ) (T.subst σ) (v.subst σ) := by
  change (R.eval T v (L.top.rename Nat.succ)).subst σ = _
  rw [eval_subst,Expr.subst_rename]
  change _ = (R.subst σ).eval _ _ ((L.subst σ).top.rename Nat.succ)
  rw [← LogicCode.top_subst,Expr.rename_subst]
  rfl
theorem rec_rename (L : LogicCode S) (T v Q : Expr S) (ρ : Nat → Nat) :
    (R.recover L T v Q).rename ρ = (R.rename ρ).recover (L.rename ρ) (T.rename ρ) (v.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [recover,LogicCode.cond_rename,LogicCode.neg_rename,bit_rename,eval_rename]
theorem rec_subst (L : LogicCode S) (T v Q : Expr S) (σ : Nat → Expr S) :
    (R.recover L T v Q).subst σ = (R.subst σ).recover (L.subst σ) (T.subst σ) (v.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [recover,LogicCode.cond_subst,LogicCode.neg_subst,bit_subst,eval_subst]

def bitBody (L : LogicCode S) (T : Expr S) : Expr S :=
  (R.rename Nat.succ).bit (L.rename Nat.succ) (T.rename Nat.succ) (.var 0)
def recBody (L : LogicCode S) (T Q : Expr S) : Expr S :=
  (R.rename Nat.succ).recover (L.rename Nat.succ) (T.rename Nat.succ) (.var 0) (Q.rename (Expr.liftRen Nat.succ))
theorem bitBody_instantiate (L : LogicCode S) (T v : Expr S) :
    (R.bitBody L T).instantiate v = R.bit L T v := by
  simp only [bitBody,Expr.instantiate,bit_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem recBody_instantiate (L : LogicCode S) (T Q v : Expr S) :
    (R.recBody L T Q).instantiate v = R.recover L T v Q := by
  simp only [recBody,Expr.instantiate,rec_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
  congr 1
  rw [Expr.subst_rename]
  have he : Expr.liftSub (Expr.single v) ∘ Expr.liftRen Nat.succ = Expr.var := by
    funext n; cases n <;> rfl
  rw [he,Expr.subst_var]
theorem bitBody_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.bitBody L T).rename (Expr.liftRen ρ) = (R.rename ρ).bitBody (L.rename ρ) (T.rename ρ) := by
  simp only [bitBody,bit_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl
theorem recBody_rename (L : LogicCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.recBody L T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).recBody (L.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [recBody,rec_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  congr 1
  congr 1
  funext n; cases n <;> rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {R : DoubleCode S}
theorem bitBody_family (h : R.Formed L I J K) {T : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) : L.Family (R.carrier T) (R.bitBody L.code T) := by
  intro Δ δ e v hv mv
  rw [bitBody_rename,bitBody_instantiate]
  exact (h.rename e).bit_formula (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [carrier_rename] using hv) mv

theorem recBody_family (h : R.Formed L I J K) {T Q : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family T Q) :
    L.Family (R.carrier T) (R.recBody L.code T Q) := by
  intro Δ δ e v hv mv
  rw [recBody_rename,recBody_instantiate]
  exact (h.rename e).rec_formula (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [carrier_rename] using hv) mv (hQ.rename e)
end Formed

def tower : Nat → Expr S → Expr S
  | 0,T => T
  | n+1,T => R.carrier (tower n T)
def embed (L : LogicCode S) : List Bool → Expr S → Expr S → Expr S
  | [],_,t => t
  | b::bs,T,t => R.emb L b (R.tower bs.length T) (embed L bs T t)
def recoveryBody (L : LogicCode S) : Nat → Expr S → Expr S → Expr S
  | 0,_,Q => Q
  | n+1,T,Q => R.recBody L (R.tower n T) (recoveryBody L n T Q)
def tagBody (L : LogicCode S) : List Bool → Expr S → Expr S
  | [],_ => L.top.rename Nat.succ
  | b::bs,T => (L.rename Nat.succ).conj
      ((L.rename Nat.succ).sign b (R.bitBody L (R.tower bs.length T)))
      (R.recBody L (R.tower bs.length T) (tagBody L bs T))

theorem tower_rename (n : Nat) (T : Expr S) (ρ : Nat → Nat) :
    (R.tower n T).rename ρ = (R.rename ρ).tower n (T.rename ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,carrier_rename,ih]
theorem tower_subst (n : Nat) (T : Expr S) (σ : Nat → Expr S) :
    (R.tower n T).subst σ = (R.subst σ).tower n (T.subst σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,carrier_subst,ih]
theorem embed_rename (L : LogicCode S) (bs : List Bool) (T t : Expr S) (ρ : Nat → Nat) :
    (R.embed L bs T t).rename ρ = (R.rename ρ).embed (L.rename ρ) bs (T.rename ρ) (t.rename ρ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_rename,tower_rename,ih]
theorem embed_subst (L : LogicCode S) (bs : List Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.embed L bs T t).subst σ = (R.subst σ).embed (L.subst σ) bs (T.subst σ) (t.subst σ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_subst,tower_subst,ih]
theorem recoveryBody_rename (L : LogicCode S) (n : Nat) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.recoveryBody L n T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).recoveryBody (L.rename ρ) n (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recoveryBody,recBody_rename,tower_rename,ih]
theorem tagBody_rename (L : LogicCode S) (bs : List Bool) (T : Expr S) (ρ : Nat → Nat) :
    (R.tagBody L bs T).rename (Expr.liftRen ρ) =
      (R.rename ρ).tagBody (L.rename ρ) bs (T.rename ρ) := by
  induction bs with
  | nil =>
    simp only [tagBody,Expr.rename_comp,← LogicCode.top_rename]
    rfl
  | cons b bs ih =>
    simp only [tagBody,LogicCode.conj_rename,LogicCode.sign_rename,LogicCode.rename_comp,
      bitBody_rename,recBody_rename,tower_rename,ih]
    rfl

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S}
    (h : R.Formed L I J I)
include h
theorem tower_sorted {T : Expr S} (hT : SortedAt P Γ T I) (n : Nat) : SortedAt P Γ (R.tower n T) I := by
  induction n with
  | zero => exact hT
  | succ n ih => exact h.sorted ih
theorem tower_mode {T : Expr S} (mT : WellModed γ T .data) (n : Nat) : WellModed γ (R.tower n T) .data := by
  induction n with
  | zero => exact mT
  | succ n ih => exact h.mode ih

theorem embed_typed {T t : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs : List Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    HasType P Γ (R.embed L.code bs T t) (R.tower bs.length T) ∧ WellModed γ (R.embed L.code bs T t) .data := by
  induction bs with
  | nil => exact ⟨ht,mt⟩
  | cons b bs ih => exact h.emb_typed (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) b ih.1 ih.2

theorem recoveryBody_family {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (n : Nat) (hQ : L.Family T Q) : L.Family (R.tower n T) (R.recoveryBody L.code n T Q) := by
  induction n with
  | zero => exact hQ
  | succ n ih => exact h.recBody_family (h.tower_sorted hT n) (h.tower_mode mT n) ih

theorem tagBody_family {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs : List Bool) : L.Family (R.tower bs.length T) (R.tagBody L.code bs T) := by
  induction bs with
  | nil => exact .constant L.top_formula
  | cons b bs ih =>
    exact ((h.bitBody_family (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length)).code_sign b).code_conj
      (h.recBody_family (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) ih)

theorem embed_recovery {T t Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs : List Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) (hQ : L.Family T Q) :
    Equivalent P Γ γ ((R.recoveryBody L.code bs.length T Q).instantiate (R.embed L.code bs T t))
      (Q.instantiate t) := by
  induction bs with
  | nil =>
    obtain ⟨s,hs⟩ := L.triple.codomain.1
    exact .refl ((hQ.instantiate ht mt).1 s hs)
  | cons b bs ih =>
    have h₁ := h.embed_typed hT mT bs ht mt
    have h₂ := h.embed_typed hT mT (b::bs) ht mt
    have hc := h.recoveryBody_family hT mT bs.length hQ
    have he := h.emb_recovery (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) b h₁.1 h₁.2 hc
    have hp : Equivalent P Γ γ
        ((R.recoveryBody L.code (b::bs).length T Q).instantiate (R.embed L.code (b::bs) T t))
        ((R.recoveryBody L.code bs.length T Q).instantiate (R.embed L.code bs T t)) := by
      simpa only [List.length_cons,recoveryBody,recBody_instantiate,embed] using he
    obtain ⟨s,hs⟩ := L.triple.codomain.1
    exact hp.trans ih ((h.recoveryBody_family hT mT (b::bs).length hQ |>.instantiate h₂.1 h₂.2).1 s hs)
      ((hc.instantiate h₁.1 h₁.2).1 s hs) ((hQ.instantiate ht mt).1 s hs)
end Formed
end DoubleCode

theorem LogicCode.conj_instantiate_raise (L : LogicCode S) (A B a : Expr S) :
    ((L.rename Nat.succ).conj A B).instantiate a = L.conj (A.instantiate a) (B.instantiate a) := by
  simp only [Expr.instantiate,LogicCode.conj_subst,LogicCode.instantiate_raise]
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
theorem signed_sign (b c : Bool) {A : Expr S} (hA : L.Formula A)
    (hc : Proves P Γ γ (L.code.sign c A)) :
    Proves P Γ γ (L.code.sign (b == c) (L.code.sign b A)) := by
  cases b <;> cases c <;>
    simp only [Bool.true_beq,Bool.false_beq,Bool.not_false,Bool.not_true,
      LogicCode.sign,ite_true,ite_false,Bool.false_eq_true] at hc ⊢ <;>
    pts_pl L using [hc]
theorem signed_conj (b c : Bool) {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (ha : Proves P Γ γ (L.code.sign b A)) (hb : Proves P Γ γ (L.code.sign c B)) :
    Proves P Γ γ (L.code.sign (b && c) (L.conj A B)) := by
  cases b <;> cases c <;>
    simp only [Bool.false_and,Bool.true_and,LogicCode.sign,ite_true,ite_false,Bool.false_eq_true] at ha hb ⊢ <;>
    pts_pl L using [ha,hb]
end LogicSetup
namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} (h : R.Formed L I J I)
include h

theorem embed_tag {T t : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs cs : List Bool) (hl : bs.length = cs.length) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    Proves P Γ γ (L.code.sign (bs == cs)
      ((R.tagBody L.code bs T).instantiate (R.embed L.code cs T t))) := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil =>
      simp only [beq_self_eq_true,DoubleCode.tagBody,LogicCode.sign,ite_true,Expr.instantiate_raise]
      change Proves P Γ γ L.top
      exact L.top_intro
    | cons c cs => simp at hl
  | cons b bs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      have hlen : bs.length = cs.length := Nat.succ.inj hl
      have hp := ih cs hlen
      have hv := h.embed_typed hT mT cs ht mt
      have hv' : HasType P Γ (R.embed L.code cs T t) (R.tower bs.length T) := by rw [hlen]; exact hv.1
      have hq := h.tagBody_family hT mT bs
      have he := h.emb_recovery (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) c hv' hv.2 hq
      have hb := h.emb_bit (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) c hv' hv.2
      have hw := h.emb_typed (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) c hv' hv.2
      have hf := h.bit_formula (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) hw.1 hw.2
      have hr := h.rec_formula (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) hw.1 hw.2 hq
      have hqt := hq.instantiate hv' hv.2
      simp only [DoubleCode.tagBody,DoubleCode.embed,← hlen,
        LogicCode.conj_instantiate_raise,LogicCode.sign_instantiate_raise,
        DoubleCode.bitBody_instantiate,DoubleCode.recBody_instantiate]
      change Proves P Γ γ (L.code.sign ((b::bs) == (c::cs)) (L.conj
        (L.code.sign b (R.bit L.code (R.tower bs.length T)
          (R.emb L.code c (R.tower bs.length T) (R.embed L.code cs T t))))
        (R.recover L.code (R.tower bs.length T)
          (R.emb L.code c (R.tower bs.length T) (R.embed L.code cs T t))
          (R.tagBody L.code bs T))))
      have hbit := L.signed_sign b c hf hb
      have hrec := (L.sign_equivalent (bs == cs) hr hqt he).2.prove hp
      have hh := L.signed_conj (b == c) (bs == cs) (L.sign_formula b hf) hr hbit hrec
      simpa only [List.cons_beq_cons] using hh
end DoubleCode.Formed

/-- Nine distinct finite query strings. Index zero is the payload tag. -/
def queryBits (q : Fin 9) : List Bool :=
  [q.val.testBit 0,q.val.testBit 1,q.val.testBit 2,q.val.testBit 3]
theorem queryBits_length (q : Fin 9) : (queryBits q).length = 4 := rfl
theorem queryBits_injective : Function.Injective queryBits := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [queryBits,Nat.testBit]

def queryTag (t : Fin 8) : Fin 9 := ⟨t.val+1,by omega⟩
theorem queryTag_ne_zero (t : Fin 8) : queryTag t ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp only [queryTag,Fin.val_zero] at this; omega

namespace DoubleCode
variable (R : DoubleCode S)
def big (T : Expr S) := R.tower 4 T
def bpType (T : Expr S) := R.first.apply (R.big T)
def paramType (T : Expr S) := R.second.apply (R.bpType T)
def tagged (L : LogicCode S) (q : Fin 9) (T t : Expr S) := R.embed L (queryBits q) T t

def encodeBody (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) :=
  (L.rename Nat.succ).disj
    ((L.rename Nat.succ).conj (R.tagBody L (queryBits 0) T)
      (R.recoveryBody L 4 T (U.evalCallback T p)))
    (R.tagBody L (queryBits (queryTag t)) T)
def encode (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) :=
  R.first.build (R.big T) (R.encodeBody U L t T p)
def mark (L : LogicCode S) (t : Fin 8) (T c₀ bp : Expr S) :=
  R.first.observe (R.big T) bp (R.tagged L (queryTag t) T c₀)
def query (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T o p : Expr S) :=
  R.second.observe (R.bpType T) o (R.encode U L t T p)

def embedBody (L : LogicCode S) (q : Fin 9) (T : Expr S) :=
  (R.rename Nat.succ).tagged (L.rename Nat.succ) q (T.rename Nat.succ) (.var 0)
def decoderBody (L : LogicCode S) (T bp : Expr S) :=
  (R.first.evalCallback (R.big T) bp).compose (R.embedBody L 0 T)
def decode (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) :=
  U.build T (R.decoderBody L T bp)

theorem tagged_rename (L : LogicCode S) (q : Fin 9) (T t : Expr S) (ρ : Nat → Nat) :
    (R.tagged L q T t).rename ρ = (R.rename ρ).tagged (L.rename ρ) q (T.rename ρ) (t.rename ρ) :=
  R.embed_rename L (queryBits q) T t ρ
theorem tagged_subst (L : LogicCode S) (q : Fin 9) (T t : Expr S) (σ : Nat → Expr S) :
    (R.tagged L q T t).subst σ = (R.subst σ).tagged (L.subst σ) q (T.subst σ) (t.subst σ) :=
  R.embed_subst L (queryBits q) T t σ

theorem encodeBody_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (ρ : Nat → Nat) :
    (R.encodeBody U L t T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).encodeBody (U.rename ρ) (L.rename ρ) t (T.rename ρ) (p.rename ρ) := by
  simp only [encodeBody,LogicCode.disj_rename,LogicCode.conj_rename,tagBody_rename,
    recoveryBody_rename,DataWrapper.evalCallback_rename,LogicCode.rename_comp]
  rfl

theorem embedBody_instantiate (L : LogicCode S) (q : Fin 9) (T t : Expr S) :
    (R.embedBody L q T).instantiate t = R.tagged L q T t := by
  simp only [embedBody,Expr.instantiate,tagged_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem embedBody_rename (L : LogicCode S) (q : Fin 9) (T : Expr S) (ρ : Nat → Nat) :
    (R.embedBody L q T).rename (Expr.liftRen ρ) = (R.rename ρ).embedBody (L.rename ρ) q (T.rename ρ) := by
  simp only [embedBody,tagged_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl

theorem decoderBody_instantiate (L : LogicCode S) (T bp c : Expr S) :
    (R.decoderBody L T bp).instantiate c = R.first.observe (R.big T) bp (R.tagged L 0 T c) := by
  simp only [decoderBody,Expr.compose_instantiate,embedBody_instantiate,DataWrapper.evalCallback_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h

theorem tagged_typed {T c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (q : Fin 9) (hc : HasType P Γ c T) (mc : WellModed γ c .data) :
    HasType P Γ (R.tagged L.code q T c) (R.big T) ∧ WellModed γ (R.tagged L.code q T c) .data :=
  h.embed_typed hT mT (queryBits q) hc mc

theorem bp_sorted {T : Expr S} (hT : SortedAt P Γ T I) : SortedAt P Γ (R.bpType T) J :=
  h.first.sorted (h.tower_sorted hT 4)
theorem bp_mode {T : Expr S} (mT : WellModed γ T .data) : WellModed γ (R.bpType T) .data :=
  h.first.mode (h.tower_mode mT 4)
theorem param_sorted {T : Expr S} (hT : SortedAt P Γ T I) : SortedAt P Γ (R.paramType T) I :=
  h.second.sorted (h.bp_sorted hT)
theorem param_mode {T : Expr S} (mT : WellModed γ T .data) : WellModed γ (R.paramType T) .data :=
  h.second.mode (h.bp_mode mT)

include hU

theorem encodeBody_family {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Family (R.big T) (R.encodeBody U L.code t T p) :=
  ((h.tagBody_family hT mT (queryBits 0)).code_conj
    (h.recoveryBody_family hT mT 4 (hU.evalCallback_family hT mT hp mp))).code_disj
      (h.tagBody_family hT mT (queryBits (queryTag t)))

theorem encode_typed {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    HasType P Γ (R.encode U L.code t T p) (R.bpType T) ∧ WellModed γ (R.encode U L.code t T p) .data :=
  (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).1 _ (h.encodeBody_family hU hT mT t hp mp)

omit hU in
 theorem embedBody_map {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (q : Fin 9) {s : S} (hs : HasType P Γ T (.sort s)) :
    DataMap P Γ γ T (R.big T) (R.embedBody L.code q T) := by
  let e : Embedding P Γ γ (T :: Γ) (modeCons .data γ) := Embedding.cons hs Mode.data
  have hh := (h.rename e).tagged_typed (fun s hs => e.typing (hT s hs)) (e.moded mT) q (HasType.var hs) (.var 0)
  simpa only [DataMap,embedBody,LogicSetup.code_rename,big,tower_rename,e,Embedding.cons] using hh

omit hU in
 theorem decoderBody_family {T bp : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data)
    {s : S} (hs : HasType P Γ T (.sort s)) : L.Family T (R.decoderBody L.code T bp) :=
  (h.first.evalCallback_family (h.tower_sorted hT 4) (h.tower_mode mT 4) hb mb).compose
    (h.embedBody_map hT mT 0 hs) hs

 theorem decode_typed {T bp : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data)
    {s : S} (hs : HasType P Γ T (.sort s)) :
    HasType P Γ (R.decode U L.code T bp) (U.apply T) ∧ WellModed γ (R.decode U L.code T bp) .data :=
  (hU.sound hT mT).1 _ (h.decoderBody_family hT mT hb mb hs)
end Formed
end DoubleCode

namespace DataWrapper
theorem apply_converts {b : Bool} (R : DataWrapper S b) {A B : Expr S}
    (h : Converts A B) : Converts (R.apply A) (R.apply B) := by
  induction R with
  | identity => exact h
  | positive R D e ih => exact .pi (.refl _) (ih.rename Nat.succ)
  | negative R U ih => exact .pi ih (.refl _)
end DataWrapper

/-- The A-independent syntax of the common probe type. -/
structure ProbeCode (S : Type u) where
  seed : S
  initialParity : Bool
  initial : DataWrapper S initialParity
  raw : DataWrapper S true
  back : DataWrapper S true
  funPath : DataWrapper S false
  lifting : PositiveDataWrapper S
  tail : DataTail S

namespace ProbeCode
variable (R : ProbeCode S)
def rename (ρ : Nat → Nat) : ProbeCode S :=
  ⟨R.seed,R.initialParity,R.initial.rename ρ,R.raw.rename ρ,R.back.rename ρ,
    R.funPath.rename ρ,R.lifting.rename ρ,R.tail.rename ρ⟩
def subst (σ : Nat → Expr S) : ProbeCode S :=
  ⟨R.seed,R.initialParity,R.initial.subst σ,R.raw.subst σ,R.back.subst σ,
    R.funPath.subst σ,R.lifting.subst σ,R.tail.subst σ⟩
def doubled : DoubleCode S := ⟨R.back,R.raw⟩
def rawType (A : Expr S) := R.raw.apply (R.initial.apply A)
def paramType (A : Expr S) := R.doubled.paramType (R.rawType A)
def singleType (A : Expr S) := R.doubled.carrier (R.paramType A)
def funType (A : Expr S) := Expr.arrow .dd (R.singleType A) R.tail.carrier
def domain := R.lifting.apply (.sort R.seed)
def body := (R.funPath.rename Nat.succ).apply
  ((R.rename Nat.succ).funType ((R.lifting.rename Nat.succ).project (.var 0)))
def carrier := Expr.pi .dd R.domain R.body

theorem doubled_rename (ρ : Nat → Nat) : (R.rename ρ).doubled = R.doubled.rename ρ := rfl
theorem doubled_subst (σ : Nat → Expr S) : (R.subst σ).doubled = R.doubled.subst σ := rfl

theorem rawType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.rawType A).rename ρ = (R.rename ρ).rawType (A.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.rawType A).subst σ = (R.subst σ).rawType (A.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem paramType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.paramType A).rename ρ = (R.rename ρ).paramType (A.rename ρ) := by
  simp only [paramType,DoubleCode.paramType,DoubleCode.bpType,DoubleCode.big,
    DataWrapper.apply_rename,DoubleCode.tower_rename,rawType_rename,doubled,rename,DoubleCode.rename]
theorem paramType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.paramType A).subst σ = (R.subst σ).paramType (A.subst σ) := by
  simp only [paramType,DoubleCode.paramType,DoubleCode.bpType,DoubleCode.big,
    DataWrapper.apply_subst,DoubleCode.tower_subst,rawType_subst,doubled,subst,DoubleCode.subst]
theorem singleType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.singleType A).rename ρ = (R.rename ρ).singleType (A.rename ρ) := by
  simp only [singleType,DoubleCode.carrier_rename,paramType_rename,doubled_rename]
theorem singleType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.singleType A).subst σ = (R.subst σ).singleType (A.subst σ) := by
  simp only [singleType,DoubleCode.carrier_subst,paramType_subst,doubled_subst]
theorem funType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.funType A).rename ρ = (R.rename ρ).funType (A.rename ρ) := by
  simp only [funType,Expr.arrow_rename,singleType_rename,DataTail.carrier_rename,rename]
theorem funType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.funType A).subst σ = (R.subst σ).funType (A.subst σ) := by
  simp only [funType,Expr.arrow_subst,singleType_subst,DataTail.carrier_subst,subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R
  simp only [rename,subst,DataWrapper.instantiate_raise,PositiveDataWrapper.instantiate_raise,
    DataTail.instantiate_raise]
theorem body_instantiate (a : Expr S) :
    R.body.instantiate a = R.funPath.apply (R.funType (R.lifting.project a)) := by
  simp only [body,Expr.instantiate,DataWrapper.apply_subst,funType_subst,
    PositiveDataWrapper.project_subst,Expr.subst,Expr.single,DataWrapper.instantiate_raise,
    PositiveDataWrapper.instantiate_raise,instantiate_raise]

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  (L : LogicSetup P Γ γ C) (I J k p n g : Set S)
structure Formed : Prop where
  mainTriple : ProfileTriple P I J k
  funTriple : ProfileTriple P p n g
  ax : (AxProfile P R.seed).Nonempty
  initial : R.initial.Formed L {R.seed} k
  raw : R.raw.Formed L k p
  back : R.back.Formed L p k
  funPath : R.funPath.Formed L g J
  lifting : R.lifting.Formed L.witnesses (AxProfile P R.seed) I
  tail : R.tail.Formed L n

namespace Formed
variable {R L I J k p n g} (h : R.Formed L I J k p n g)
include h
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g :=
  ⟨h.mainTriple,h.funTriple,h.ax,h.initial.rename e,h.raw.rename e,h.back.rename e,
    h.funPath.rename e,h.lifting.rename e,h.tail.rename e⟩
omit h in
theorem seed_sorted (_h : R.Formed L I J k p n g) : SortedAt P Γ (.sort R.seed) (AxProfile P R.seed) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact fun t ht => HasType.sort_of_valid (L.bottom_formula.1 s hs).valid ht

theorem domain_sorted : SortedAt P Γ R.domain I := h.lifting.sorted h.seed_sorted
theorem domain_mode : WellModed γ R.domain .data := h.lifting.modes.1 _ (.sort _)
theorem raw_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.rawType A) p := h.raw.sorted (h.initial.sorted (fun s hs => by cases hs; exact ha))
theorem raw_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.rawType A) .data :=
  h.raw.mode (h.initial.mode ma)
theorem doubled_formed : R.doubled.Formed L p k p := ⟨h.back,h.raw⟩
theorem param_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.paramType A) p := h.doubled_formed.param_sorted (h.raw_sorted ha)
theorem param_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.paramType A) .data :=
  h.doubled_formed.param_mode (h.raw_mode ma)
theorem single_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.singleType A) p := h.doubled_formed.sorted (h.param_sorted ha)
theorem single_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.singleType A) .data :=
  h.doubled_formed.mode (h.param_mode ma)
theorem fun_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.funType A) g :=
  (h.single_sorted ha).arrow h.tail.carrier_sorted .dd (by rw [h.funTriple.output])
theorem fun_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.funType A) .data :=
  (h.single_mode ma).arrow h.tail.carrier_mode

theorem body_sorted {s : S} (hs : HasType P Γ R.domain (.sort s)) :
    SortedAt P (R.domain :: Γ) R.body J := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := h.rename e
  have hp : HasType P (R.domain :: Γ) ((R.lifting.rename Nat.succ).project (.var 0)) (.sort R.seed) :=
    (hh.lifting.typed hh.seed_sorted).2 _ (by
      simpa only [domain,PositiveDataWrapper.apply_rename,Expr.rename,e,Embedding.cons,ProbeCode.rename] using HasType.var hs)
  exact hh.funPath.sorted (hh.fun_sorted hp)

theorem body_mode {s : S} (hs : HasType P Γ R.domain (.sort s)) :
    WellModed (modeCons .data γ) R.body .data := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := h.rename e
  exact hh.funPath.mode (hh.fun_mode (hh.lifting.modes.2.2 _ (.var 0)))

theorem carrier_sorted : SortedAt P Γ R.carrier k := by
  intro r hr
  obtain ⟨s,hs,t,ht,hst⟩ := h.mainTriple.output ▸ hr
  exact HasType.product (h.domain_sorted s hs) (h.body_sorted (h.domain_sorted s hs) t ht) hst

theorem carrier_mode : WellModed γ R.carrier .data := by
  obtain ⟨s,hs⟩ := h.mainTriple.domain.1
  exact .pi h.domain_mode (h.body_mode (h.domain_sorted s hs))
end Formed
end ProbeCode

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} {L : LogicSetup P Γ γ C}
def probe (K : ChannelSetup L) : ProbeCode S :=
  ⟨K.seed,K.initialParity,K.initial,K.channel.raw,K.returnPath,K.funPath,K.lifting,K.tail⟩
theorem probe_formed (K : ChannelSetup L) :
    K.probe.Formed L K.domain K.codomain K.base K.rawVertex K.tailVertex K.funVertex :=
  ⟨K.mainTriple,K.funTriple,K.ax,K.initialFormed,K.channelFormed.raw,K.returnFormed,
    K.funFormed,K.liftingFormed,K.tailFormed⟩
end ChannelSetup
end PureTypeSystem.Labelled

namespace PureTypeSystem
namespace IsComponent
variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V}
/-- A secondary return can always be chosen with the outward parity. -/
theorem matched_return (hC : IsComponent E C) {v w : V} {b : Bool}
    (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w b) : SignedPath E w v b := by
  by_cases ho : SignedPath E v v true
  · exact hC.all_parities hv ho hw hv b
  · exact hC.return_parity hv hw hp ho
end IsComponent

namespace Labelled
universe u
variable {S : Type u} {P : Specification S}
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} {L : LogicSetup P Γ γ C}

/-- The parity-matched return is retained alongside, not substituted for,
the fixed channel paths. -/
structure ChannelReturn (K : ChannelSetup L) where
  route : DataWrapper S K.initialParity
  formed : route.Formed L K.base {K.seed}

namespace ChannelSetup
theorem exists_setup_return (hC : IsComponent (PrimaryEdge P) C)
    (ho : ∃ r ∈ C, SignedPath (PrimaryEdge P) r r true)
    (hf : ForbiddenConfiguration P C) : ∃ K : ChannelSetup L, Nonempty (ChannelReturn K) := by
  obtain ⟨r,hr,ho⟩ := ho
  obtain ⟨D,hD,I,J,k,s,p,n,g,j,h,ht,hJ,hk,hs,hax,hζ,htr,hp,hg,hn,hα,hβ,hκ,hj,hLam,hh,_,hη⟩ := hf.channel_paths
  obtain ⟨b,hδ⟩ := hD.connected hs hk
  obtain ⟨Rδ,hRδ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hδ
  obtain ⟨Rret,hRret⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho (hD.matched_return hs hk hδ)
  obtain ⟨Rα,hRα⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hα
  obtain ⟨Rβ,hRβ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hβ
  obtain ⟨Rκ,hRκ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hκ
  obtain ⟨RLam,hRLam⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hLam
  obtain ⟨Rη,hRη⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hη
  obtain ⟨Rζ,hRζ⟩ := (PositiveDataWrapper.Formed.identity (W := L.witnesses) (I := AxProfile P s)).path hζ
  obtain ⟨U,hU⟩ := DataTail.Formed.exists_tail (L := L) hC hr ho hn
  let K : ChannelSetup L := ⟨s,I,J,k,p,n,g,j,h,ht,htr,hax,hj,hh,b,Rδ,hRδ,
    ⟨RLam,Rα,Rη⟩,⟨hRLam,hRα,hRη⟩,Rβ,hRβ,Rκ,hRκ,Rζ,hRζ,U,hU⟩
  exact ⟨K,⟨⟨Rret,hRret⟩⟩⟩
end ChannelSetup

namespace ChannelReturn
variable {K : ChannelSetup L} (R : ChannelReturn K)
def evenLoop : DataWrapper S false := DataWrapper.reindex (by cases K.initialParity <;> rfl)
  (R.route.append K.initial)
def fourth : DataWrapper S true := K.returnPath.append R.evenLoop
def firstDouble (_R : ChannelReturn K) : DoubleCode S := K.doubled
def outerDouble : DoubleCode S := ⟨R.fourth,K.channel.logical⟩
/-- Specific source A0: two fixed odd-pair detours followed by the matched return. -/
def type : Expr S := R.route.apply (K.returnPath.apply (K.channel.raw.apply
    (K.returnPath.apply (K.channel.raw.apply K.probe.carrier))))

theorem evenLoop_formed : R.evenLoop.Formed L K.base K.base :=
  (R.formed.append K.initialFormed).reindex _
theorem fourth_formed : R.fourth.Formed L K.rawVertex K.base :=
  K.returnFormed.append R.evenLoop_formed
theorem firstDouble_formed : R.firstDouble.Formed L K.rawVertex K.base K.rawVertex :=
  K.doubled_formed
theorem outerDouble_formed : R.outerDouble.Formed L K.rawVertex K.base K.logicalVertex :=
  ⟨R.fourth_formed,K.channelFormed.logical⟩

theorem type_sorted : HasType P Γ R.type (.sort K.seed) := by
  exact R.formed.sorted (K.returnFormed.sorted (K.channelFormed.raw.sorted
    (K.returnFormed.sorted (K.channelFormed.raw.sorted K.probe_formed.carrier_sorted)))) K.seed rfl

theorem type_mode : WellModed γ R.type .data :=
  R.formed.mode (K.returnFormed.mode (K.channelFormed.raw.mode
    (K.returnFormed.mode (K.channelFormed.raw.mode K.probe_formed.carrier_mode))))

theorem evenLoop_apply (T : Expr S) : R.evenLoop.apply T = K.initial.apply (R.route.apply T) := by
  simp only [evenLoop,DataWrapper.apply_reindex,DataWrapper.apply_append]
theorem fourth_apply (T : Expr S) : R.fourth.apply T = K.initial.apply (R.route.apply (K.returnPath.apply T)) := by
  simp only [fourth,DataWrapper.apply_append,evenLoop_apply]
/-- The five odd segments have exactly the required endpoint, not merely an
isomorphic or propositionally related placeholder type. -/
theorem factorization :
    R.outerDouble.carrier (R.firstDouble.carrier (K.channel.raw.apply K.probe.carrier)) =
    K.channel.logicalType (K.initial.apply R.type) := by
  simp only [outerDouble,firstDouble,ChannelSetup.doubled,DoubleCode.carrier,ChannelCode.logicalType,
    fourth_apply,type]
end ChannelReturn
end Labelled
end PureTypeSystem

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ChannelCode
variable (R : ChannelCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise]
theorem logicalType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.logicalType T).rename ρ = (R.rename ρ).logicalType (T.rename ρ) := by
  simp only [logicalType,rename,DataWrapper.apply_rename]
theorem logicalType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.logicalType T).subst σ = (R.subst σ).logicalType (T.subst σ) := by
  simp only [logicalType,subst,DataWrapper.apply_subst]
theorem rawType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.rawType T).rename ρ = (R.rename ρ).rawType (T.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.rawType T).subst σ = (R.subst σ).rawType (T.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem predicateType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.predicateType T).rename ρ = (R.rename ρ).predicateType (T.rename ρ) := by
  simp only [predicateType,rename,DataWrapper.apply_rename]
theorem predicateType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.predicateType T).subst σ = (R.subst σ).predicateType (T.subst σ) := by
  simp only [predicateType,subst,DataWrapper.apply_subst]
theorem toRaw_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.toRaw T y).rename ρ = (R.rename ρ).toRaw (T.rename ρ) (y.rename ρ) := by
  simp only [toRaw,DataWrapper.reencode_rename,rename]
theorem toRaw_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.toRaw T y).subst σ = (R.subst σ).toRaw (T.subst σ) (y.subst σ) := by
  simp only [toRaw,DataWrapper.reencode_subst,subst]
theorem toLog_rename (T c : Expr S) (ρ : Nat → Nat) :
    (R.toLog T c).rename ρ = (R.rename ρ).toLog (T.rename ρ) (c.rename ρ) := by
  simp only [toLog,DataWrapper.reencode_rename,rename]
theorem toLog_subst (T c : Expr S) (σ : Nat → Expr S) :
    (R.toLog T c).subst σ = (R.subst σ).toLog (T.subst σ) (c.subst σ) := by
  simp only [toLog,DataWrapper.reencode_subst,subst]
theorem round_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.round T y).rename ρ = (R.rename ρ).round (T.rename ρ) (y.rename ρ) := by
  simp only [round,toRaw_rename,toLog_rename]
theorem round_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.round T y).subst σ = (R.subst σ).round (T.subst σ) (y.subst σ) := by
  simp only [round,toRaw_subst,toLog_subst]
theorem eval_rename (T p y : Expr S) (ρ : Nat → Nat) :
    (R.eval T p y).rename ρ = (R.rename ρ).eval (T.rename ρ) (p.rename ρ) (y.rename ρ) := by
  simp only [eval,DataWrapper.observe_rename,rawType_rename,toRaw_rename,rename,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false]
theorem eval_subst (T p y : Expr S) (σ : Nat → Expr S) :
    (R.eval T p y).subst σ = (R.subst σ).eval (T.subst σ) (p.subst σ) (y.subst σ) := by
  simp only [eval,DataWrapper.observe_subst,rawType_subst,toRaw_subst,subst,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false]
end ChannelCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {A B : Expr S}
/-- Data quantification using a uniform formula callback; the quantified
    annotation is still the original retained direct profile. -/
theorem all_formula_family {I : Set S} (R : QuantifierRoute L.witnesses C L.base I)
    {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ T (.sort s)) (hQ : L.Family T Q) :
    L.Formula (all R T Q) := all_formula R hT mT hs (hQ.opened hs)

theorem all_intro_future {I : Set S} (R : QuantifierRoute L.witnesses C L.base I)
    {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ T (.sort s)) (hQ : L.Family T Q)
    (h : ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
      (a : Expr S), HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a)) :
    Proves P Γ γ (all R T Q) := by
  apply all_intro R hT mT hs (hQ.opened hs)
  have hh := h _ _ (Embedding.cons hs .data) (.var 0) (HasType.var hs) (.var 0)
  have he : (Q.rename (Expr.liftRen Nat.succ)).instantiate (.var 0) = Q := by
    simp only [Expr.instantiate,Expr.subst_rename]
    have he : Expr.single (.var 0 : Expr S) ∘ Expr.liftRen Nat.succ = Expr.var := by
      funext n; cases n <;> rfl
    rw [he,Expr.subst_var]
  exact he ▸ hh

theorem all_elim_family {I : Set S} (R : QuantifierRoute L.witnesses C L.base I)
    {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ T (.sort s)) (hQ : L.Family T Q)
    {a : Expr S} (ha : HasType P Γ a T) (ma : WellModed γ a .data)
    (hp : Proves P Γ γ (all R T Q)) : Proves P Γ γ (Q.instantiate a) :=
  all_elim R hT mT hs (hQ.opened hs) ha ma (hQ.instantiate ha ma) hp
end LogicSetup

/-- The two fixed proof paths implementing a direct-domain universal. -/
structure QuantifierCode (S : Type u) where
  into : ProofWrapper S
  out : ProofWrapper S
namespace QuantifierCode
variable (K : QuantifierCode S)
def rename (ρ : Nat → Nat) : QuantifierCode S := ⟨K.into.rename ρ,K.out.rename ρ⟩
def subst (σ : Nat → Expr S) : QuantifierCode S := ⟨K.into.subst σ,K.out.subst σ⟩
def all (T Q : Expr S) := K.out.apply (.pi .dp T ((K.into.rename Nat.succ).apply Q))
theorem rename_comp (ρ τ : Nat → Nat) : (K.rename τ).rename ρ = K.rename (ρ ∘ τ) := by
  cases K; simp only [rename,ProofWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (K.rename Nat.succ).subst (Expr.single a) = K := by
  cases K; simp only [rename,subst,ProofWrapper.instantiate_raise]
theorem all_rename (T Q : Expr S) (ρ : Nat → Nat) :
    (K.all T Q).rename ρ = (K.rename ρ).all (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [all,rename,ProofWrapper.apply_rename,Expr.rename,ProofWrapper.rename_comp]
  rfl
theorem all_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (K.all T Q).subst σ = (K.subst σ).all (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [all,subst,ProofWrapper.apply_subst,Expr.subst,ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
end QuantifierCode
namespace QuantifierRoute
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {b I : Set S}
def code (R : QuantifierRoute W C b I) : QuantifierCode S := ⟨R.inCode,R.outCode⟩
theorem code_rename (R : QuantifierRoute W C b I) (e : Embedding P Γ γ Δ δ) :
    (R.rename e).code = R.code.rename e.names := rfl
end QuantifierRoute
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
theorem all_code {I : Set S} (K : QuantifierRoute L.witnesses C L.base I) (T Q : Expr S) :
    K.code.all T Q = all K T Q := rfl
end LogicSetup
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
    {C : Set (Set S)} (L : LogicSetup P Γ γ C)
theorem code_imp (A B : Expr S) : L.code.imp A B = L.imp A B := rfl
theorem code_neg (A : Expr S) : L.code.neg A = L.neg A := rfl
theorem code_bottom : L.code.bottom = L.bottom := rfl
theorem code_top : L.code.top = L.top := rfl
theorem code_conj (A B : Expr S) : L.code.conj A B = L.conj A B := rfl
theorem code_disj (A B : Expr S) : L.code.disj A B = L.disj A B := rfl
theorem code_iff (A B : Expr S) : L.code.iff A B = L.iff A B := rfl
end PureTypeSystem.Labelled.LogicSetup

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace Expr
theorem lifted_comp (ρ τ : Nat → Nat) : liftRen ρ ∘ liftRen τ = liftRen (ρ ∘ τ) := by
  funext n; cases n <;> rfl

theorem callback_rename (Q a : Expr S) (ρ τ : Nat → Nat) :
    ((Q.rename (liftRen ρ)).instantiate a).rename τ =
      (Q.rename (liftRen (τ ∘ ρ))).instantiate (a.rename τ) := by
  rw [← instantiate_rename,rename_comp,lifted_comp]
end Expr
namespace LogicCode
variable (L : LogicCode S)
def guardBody (G Q : Expr S) := (L.rename Nat.succ).imp G Q
def guardAll (K : QuantifierCode S) (T G Q : Expr S) := K.all T (L.guardBody G Q)
theorem guardBody_rename (G Q : Expr S) (ρ : Nat → Nat) :
    (L.guardBody G Q).rename (Expr.liftRen ρ) =
      (L.rename ρ).guardBody (G.rename (Expr.liftRen ρ)) (Q.rename (Expr.liftRen ρ)) := by
  simp only [guardBody,imp_rename,rename_comp]
  rfl
theorem guardBody_instantiate (G Q a : Expr S) :
    (L.guardBody G Q).instantiate a = L.imp (G.instantiate a) (Q.instantiate a) := by
  simp only [guardBody,Expr.instantiate,imp_subst,instantiate_raise]
theorem guardAll_rename (K : QuantifierCode S) (T G Q : Expr S) (ρ : Nat → Nat) :
    (L.guardAll K T G Q).rename ρ =
      (L.rename ρ).guardAll (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (Q.rename (Expr.liftRen ρ)) := by
  simp only [guardAll,QuantifierCode.all_rename,guardBody_rename]
end LogicCode
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {I : Set S} (K : QuantifierRoute L.witnesses C L.base I)
    {T G Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hG : L.Family T G) (hQ : L.Family T Q)
include hT mT hG hQ
 theorem guardAll_formula : L.Formula (L.code.guardAll K.code T G Q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.all_formula_family K hT mT (hT s hs) (hG.code_imp hQ)

 theorem guardAll_elim {a : Expr S} (ha : HasType P Γ a T) (ma : WellModed γ a .data)
    (hp : Proves P Γ γ (L.code.guardAll K.code T G Q))
    (hg : Proves P Γ γ (G.instantiate a)) : Proves P Γ γ (Q.instantiate a) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have hh := L.all_elim_family K hT mT (hT s hs) (hG.code_imp hQ) ha ma hp
  have hi : Proves P Γ γ (L.imp (G.instantiate a) (Q.instantiate a)) := by
    change Proves P Γ γ ((L.code.guardBody G Q).instantiate a) at hh
    simpa only [LogicCode.guardBody_instantiate,code_imp] using hh
  exact L.imp_elim (hG.instantiate ha ma) (hQ.instantiate ha ma) hi hg

 theorem guardAll_intro
    (h : ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
      ∀ a, HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Proves P Δ δ ((G.rename (Expr.liftRen e.names)).instantiate a) →
      Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a)) :
    Proves P Γ γ (L.code.guardAll K.code T G Q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  apply L.all_intro_future K hT mT (hT s hs) (hG.code_imp hQ)
  intro Δ δ e a ha ma
  have hg := hG _ _ e a ha ma
  have hq := hQ _ _ e a ha ma
  change Proves P Δ δ (((L.code.guardBody G Q).rename (Expr.liftRen e.names)).instantiate a)
  rw [LogicCode.guardBody_rename,LogicCode.guardBody_instantiate]
  apply (L.rename e).imp_intro_future hg hq
  intro Θ θ f hh
  have hh' : Proves P Θ θ ((G.rename (Expr.liftRen (f.names ∘ e.names))).instantiate (a.rename f.names)) := by
    simpa only [Expr.callback_rename] using hh
  have ht : HasType P Θ (a.rename f.names) (T.rename (f.names ∘ e.names)) := by
    simpa only [Expr.rename_comp] using f.typing ha
  simpa only [Expr.callback_rename,Embedding.comp] using h Θ θ (e.comp f) _ ht (f.moded ma) hh'
end LogicSetup
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} (L : LogicSetup P Γ γ C) {A B D E F : Expr S}

theorem cond_yes (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (he : Equivalent P Γ γ E (L.code.cond A B D))
    (ha : Proves P Γ γ A) : Equivalent P Γ γ E B := by
  apply L.equivalent_of_iff hE hB
  pts_pl L using [he,ha]

theorem cond_no (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (he : Equivalent P Γ γ E (L.code.cond A B D))
    (ha : Proves P Γ γ (L.neg A)) : Equivalent P Γ γ E D := by
  apply L.equivalent_of_iff hE hD
  pts_pl L using [he,ha]

theorem cond_top_yes (hA : L.Formula A) (hB : L.Formula B) (hE : L.Formula E)
    (he : Equivalent P Γ γ E (L.code.cond A L.top B))
    (ha : Proves P Γ γ A) : Proves P Γ γ E := by
  pts_pl L using [he,ha]

theorem query_positive (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (he : Equivalent P Γ γ E (L.disj (L.conj A B) D))
    (ha : Proves P Γ γ (L.neg A)) (hd : Proves P Γ γ D) : Proves P Γ γ E := by
  pts_pl L using [he,ha,hd]

theorem query_negative (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (he : Equivalent P Γ γ E (L.disj (L.conj A B) D))
    (ha : Proves P Γ γ (L.neg A)) (hd : Proves P Γ γ (L.neg D)) : Proves P Γ γ (L.neg E) := by
  pts_pl L using [he,ha,hd]

theorem query_payload (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (hF : L.Formula F)
    (he : Equivalent P Γ γ E (L.disj (L.conj A B) D))
    (ha : Proves P Γ γ A) (hd : Proves P Γ γ (L.neg D))
    (hb : Equivalent P Γ γ B F) : Equivalent P Γ γ E F := by
  apply L.equivalent_of_iff hE hF
  pts_pl L using [he,ha,hd,hb]

theorem equivalent_bottom_neg (hE : L.Formula E) (he : Equivalent P Γ γ E L.bottom) :
    Proves P Γ γ (L.neg E) := by
  pts_pl L using [he]

theorem equivalent_conj_neg (hA : L.Formula A) (hB : L.Formula B) (hE : L.Formula E)
    (he : Equivalent P Γ γ E (L.conj A B)) (hn : Proves P Γ γ (L.neg A)) :
    Proves P Γ γ (L.neg E) := by
  pts_pl L using [he,hn]

theorem equivalent_conj_yes (hA : L.Formula A) (hB : L.Formula B) (hE : L.Formula E)
    (hF : L.Formula F) (he : Equivalent P Γ γ E (L.conj A B))
    (ha : Proves P Γ γ A) (hb : Equivalent P Γ γ B F) : Equivalent P Γ γ E F := by
  apply L.equivalent_of_iff hE hF
  pts_pl L using [he,ha,hb]
end PureTypeSystem.Labelled.LogicSetup

end OAI
