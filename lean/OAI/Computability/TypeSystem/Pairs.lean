import OAI.Computability.TypeSystem.Relations

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace DataWrapper
theorem reencodeBody_subst (R R' : DataWrapper S true) (T : Expr S) (σ : Nat → Expr S) :
    (reencodeBody R R' T).subst (Expr.liftSub σ) =
      reencodeBody (R.subst σ) (R'.subst σ) (T.subst σ) := by
  simp only [reencodeBody,reencode_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
end DataWrapper
namespace Expr
theorem liftSub_succ_natural (σ : Nat → Expr S) :
    liftSub (liftSub σ) ∘ liftRen Nat.succ =
      (fun n => (liftSub σ n).rename (liftRen Nat.succ)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,liftSub,liftRen,PureTypeSystem.Expr.liftRen,rename_comp]
    rfl
end Expr
namespace ChannelCode
variable (R : ChannelCode S)
theorem pred_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (R.pred T Q).subst σ = (R.subst σ).pred (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [pred,DataWrapper.build_subst,DataWrapper.argSub,ite_true,
    Expr.compose_subst,DataWrapper.reencodeBody_subst,rawType_subst,subst]

/-- Class and edge query tags in the source's fixed seven structural tags. -/
def classTag (t : Fin 3) : Fin 7 := ⟨t.val+1,by omega⟩
def edgeTag (t : Bool) : Fin 7 := if t then 5 else 4

def isClass (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) :=
  (Q (classTag t)).instantiate (R.classPred L KP T G y)
def edge (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) :=
  L.conj (R.isClass L KP T G Q 0 y)
    (L.conj (R.isClass L KP T G Q (if t then 2 else 1) z)
      ((Q (edgeTag t)).instantiate (R.unionPred L KP T G y z)))
def formExBody (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) :=
  (L.rename Nat.succ).conj
    ((R.rename Nat.succ).edge (L.rename Nat.succ) (KP.rename Nat.succ) (T.rename Nat.succ)
      (G.rename (Expr.liftRen Nat.succ)) (fun t => (Q t).rename (Expr.liftRen Nat.succ)) false (.var 0) (z.rename Nat.succ))
    ((R.rename Nat.succ).eval (T.rename Nat.succ) (p.rename Nat.succ) (.var 0))
def pairForm (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) :=
  L.disj (L.ex KY (R.logicalType T) (R.formExBody L KP T G Q p z))
    (R.edge L KP T G Q true a z)
def pairBody (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) :=
  (R.rename Nat.succ).pairForm (L.rename Nat.succ) (KY.rename Nat.succ) (KP.rename Nat.succ)
    (T.rename Nat.succ) (G.rename (Expr.liftRen Nat.succ))
    (fun t => (Q t).rename (Expr.liftRen Nat.succ)) (p.rename Nat.succ) (a.rename Nat.succ) (.var 0)
def pairPred (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) := R.pred T (R.pairBody L KY KP T G Q p a)

theorem classBody_subst (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (σ : Nat → Expr S) :
    (R.classBody L K T G y).subst (Expr.liftSub σ) =
      (R.subst σ).classBody (L.subst σ) (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (y.subst σ) := by
  simp only [classBody,relation_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.liftSub_succ_natural,Expr.liftSub,Expr.subst]
  rfl

theorem classPred_subst (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (σ : Nat → Expr S) :
    (R.classPred L K T G y).subst σ = (R.subst σ).classPred (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) := by
  simp only [classPred,pred_subst,classBody_subst]
theorem unionBody_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.unionBody L K T G y z).subst (Expr.liftSub σ) = (R.subst σ).unionBody (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [unionBody,LogicCode.disj_subst,classBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem unionPred_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.unionPred L K T G y z).subst σ = (R.subst σ).unionPred (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [unionPred,pred_subst,unionBody_subst]

theorem isClass_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (ρ : Nat → Nat) :
    (R.isClass L KP T G Q t y).rename ρ = (R.rename ρ).isClass (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) t (y.rename ρ) := by
  simp only [isClass,← Expr.instantiate_rename,classPred_rename]
theorem isClass_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (σ : Nat → Expr S) :
    (R.isClass L KP T G Q t y).subst σ = (R.subst σ).isClass (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) := by
  simp only [isClass,← Expr.instantiate_subst,classPred_subst]
theorem edge_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (ρ : Nat → Nat) :
    (R.edge L KP T G Q t y z).rename ρ = (R.rename ρ).edge (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) t (y.rename ρ) (z.rename ρ) := by
  simp only [edge,LogicCode.conj_rename,isClass_rename,← Expr.instantiate_rename,unionPred_rename]
theorem edge_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (σ : Nat → Expr S) :
    (R.edge L KP T G Q t y z).subst σ = (R.subst σ).edge (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) (z.subst σ) := by
  simp only [edge,LogicCode.conj_subst,isClass_subst,← Expr.instantiate_subst,unionPred_subst]

theorem formExBody_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (ρ : Nat → Nat) :
    (R.formExBody L KP T G Q p z).rename (Expr.liftRen ρ) = (R.rename ρ).formExBody (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) (p.rename ρ) (z.rename ρ) := by
  simp only [formExBody,LogicCode.conj_rename,LogicCode.rename_comp,edge_rename,eval_rename,
    rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem formExBody_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (σ : Nat → Expr S) :
    (R.formExBody L KP T G Q p z).subst (Expr.liftSub σ) = (R.subst σ).formExBody (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) (p.subst σ) (z.subst σ) := by
  simp only [formExBody,LogicCode.conj_subst,edge_subst,eval_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl
theorem formExBody_instantiate (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z y : Expr S) :
    (R.formExBody L KP T G Q p z).instantiate y =
      L.conj (R.edge L KP T G Q false y z) (R.eval T p y) := by
  simp only [formExBody,Expr.instantiate,LogicCode.conj_subst,edge_subst,eval_subst,instantiate_raise,
    LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_rename,
    Expr.liftSub_single_liftRen_succ,Expr.subst,Expr.single,
    show Expr.single y ∘ Nat.succ = (Expr.var : Nat → Expr S) from rfl,Expr.subst_var]

theorem pairForm_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (ρ : Nat → Nat) :
    (R.pairForm L KY KP T G Q p a z).rename ρ = (R.rename ρ).pairForm (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) (z.rename ρ) := by
  simp only [pairForm,LogicCode.disj_rename,LogicCode.ex_rename,logicalType_rename,formExBody_rename,edge_rename]
theorem pairForm_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (σ : Nat → Expr S) :
    (R.pairForm L KY KP T G Q p a z).subst σ = (R.subst σ).pairForm (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) (z.subst σ) := by
  simp only [pairForm,LogicCode.disj_subst,LogicCode.ex_subst,logicalType_subst,formExBody_subst,edge_subst]
theorem pairBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (ρ : Nat → Nat) :
    (R.pairBody L KY KP T G Q p a).rename (Expr.liftRen ρ) = (R.rename ρ).pairBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) := by
  simp only [pairBody,pairForm_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem pairBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) :
    (R.pairBody L KY KP T G Q p a).instantiate z = R.pairForm L KY KP T G Q p a z := by
  simp only [pairBody,Expr.instantiate,pairForm_subst,instantiate_raise,
    LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_rename,
    Expr.liftSub_single_liftRen_succ,Expr.subst,Expr.single,
    show Expr.single z ∘ Nat.succ = (Expr.var : Nat → Expr S) from rfl,Expr.subst_var]
theorem pairBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairBody L KY KP T G Q p a).subst (Expr.liftSub σ) = (R.subst σ).pairBody (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairBody,pairForm_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl
theorem pairPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (ρ : Nat → Nat) :
    (R.pairPred L KY KP T G Q p a).rename ρ = (R.rename ρ).pairPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) := by
  simp only [pairPred,pred_rename,pairBody_rename]
theorem pairPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairPred L KY KP T G Q p a).subst σ = (R.subst σ).pairPred (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairPred,pred_subst,pairBody_subst]
end ChannelCode

namespace ChannelCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (KY : QuantifierRoute L.witnesses C L.base J)
    (KP : QuantifierRoute L.witnesses C L.base H)
    {T G : Expr S} {Q : Fin 7 → Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hG : L.Family (R.predicateType T) G) (hQ : ∀ t, L.Family (R.predicateType T) (Q t))
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s))
include h hT mT hG hQ hs
 theorem isClass_formula (t : Fin 3) {y : Expr S}
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Formula (R.isClass L.code KP.code T G Q t y) := by
  have hc := h.classPred_typed KP hT mT hG hy my hs
  exact (hQ (classTag t)).instantiate hc.1 hc.2
 theorem edge_formula (t : Bool) {y z : Expr S}
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Formula (R.edge L.code KP.code T G Q t y z) := by
  have hu := h.unionPred_typed KP hT mT hG hy my hz mz hs
  exact L.conj_formula (h.isClass_formula KP hT mT hG hQ hs 0 hy my)
    (L.conj_formula (h.isClass_formula KP hT mT hG hQ hs _ hz mz)
      ((hQ (edgeTag t)).instantiate hu.1 hu.2))
 theorem formExBody_family {p z : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Family (R.logicalType T) (R.formExBody L.code KP.code T G Q p z) := by
  intro Δ δ e y hy my
  rw [formExBody_rename,formExBody_instantiate]
  have ht := fun s hs => e.typing (hT s hs)
  have hz' : HasType P Δ (z.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hz
  have hy' : HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hy
  have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) (G.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hG.rename e
  have hq : ∀ t, (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) ((Q t).rename (Expr.liftRen e.names)) := by
    intro t; simpa only [predicateType_rename] using (hQ t).rename e
  have hs' : HasType P Δ ((R.rename e.names).rawType (T.rename e.names)) (.sort s) := by
    simpa only [rawType_rename,Expr.rename] using e.typing hs
  have hp' : HasType P Δ (p.rename e.names) ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using e.typing hp
  exact (L.rename e).conj_formula ((h.rename e).edge_formula (KP.rename e) ht (e.moded mT) hg hq hs' false hy' my hz' (e.moded mz))
      ((h.rename e).eval_formula ht (e.moded mT) hp' (e.moded mp) hy' my)
 theorem pairForm_formula {p a z : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Formula (R.pairForm L.code KY.code KP.code T G Q p a z) :=
  L.disj_formula (L.ex_formula KY (h.logical_sorted hT) (h.logical_mode mT)
    (h.formExBody_family KP hT mT hG hQ hs hp mp hz mz))
    (h.edge_formula KP hT mT hG hQ hs true ha ma hz mz)
 theorem pairBody_family {p a : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data) :
    L.Family (R.logicalType T) (R.pairBody L.code KY.code KP.code T G Q p a) := by
  intro Δ δ e z hz mz
  rw [pairBody_rename,pairBody_instantiate]
  have ht := fun s hs => e.typing (hT s hs)
  have ha' : HasType P Δ (a.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing ha
  have hz' : HasType P Δ z ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hz
  have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) (G.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hG.rename e
  have hq : ∀ t, (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) ((Q t).rename (Expr.liftRen e.names)) := by
    intro t; simpa only [predicateType_rename] using (hQ t).rename e
  have hs' : HasType P Δ ((R.rename e.names).rawType (T.rename e.names)) (.sort s) := by
    simpa only [rawType_rename,Expr.rename] using e.typing hs
  have hp' : HasType P Δ (p.rename e.names) ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using e.typing hp
  exact (h.rename e).pairForm_formula (KY.rename e) (KP.rename e) ht (e.moded mT) hg hq hs' hp' (e.moded mp) ha' (e.moded ma) hz' mz
 theorem pairPred_typed {p a : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data) :
    HasType P Γ (R.pairPred L.code KY.code KP.code T G Q p a) (R.predicateType T) ∧
      WellModed γ (R.pairPred L.code KY.code KP.code T G Q p a) .data :=
  h.pred_typed hT mT (h.pairBody_family KY KP hT mT hG hQ hs hp mp ha ma) hs
 theorem pairPred_evaluation {p a z : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    Equivalent P Γ γ (R.eval T (R.pairPred L.code KY.code KP.code T G Q p a) z)
      (R.pairForm L.code KY.code KP.code T G Q p a (R.round T z)) := by
  simpa only [pairPred,pairBody_instantiate] using
    h.pred_evaluation hT mT (h.pairBody_family KY KP hT mT hG hQ hs hp mp ha ma) hs hz mz
end ChannelCode.Formed

theorem queryBits_beq (q r : Fin 9) : (queryBits q == queryBits r) = (q == r) := by
  by_cases he : q = r
  · subst r; simp
  · have hn : queryBits q ≠ queryBits r := fun h => he (queryBits_injective h)
    simp only [beq_eq_false_iff_ne.mpr he,beq_eq_false_iff_ne.mpr hn]
theorem queryTag_injective : Function.Injective queryTag := by
  intro t u h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [queryTag] at he
  omega

namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h

theorem tagged_tag {T c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (q r : Fin 9) (hc : HasType P Γ c T) (mc : WellModed γ c .data) :
    Proves P Γ γ (L.code.sign (q == r)
      ((R.tagBody L.code (queryBits q) T).instantiate (R.tagged L.code r T c))) := by
  simpa only [queryBits_beq,DoubleCode.tagged] using
    h.embed_tag hT mT (queryBits q) (queryBits r) rfl hc mc

include hU

theorem encode_evaluation {T p v : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hv : HasType P Γ v (R.big T)) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (R.first.observe (R.big T) (R.encode U L.code t T p) v)
      (L.disj (L.conj
        ((R.tagBody L.code (queryBits 0) T).instantiate v)
        ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate v))
        ((R.tagBody L.code (queryBits (queryTag t)) T).instantiate v)) := by
  have he := h.first.cancellation (h.tower_sorted hT 4) (h.tower_mode mT 4)
    (h.encodeBody_family hU hT mT t hp mp) ⟨hv,mv⟩
  simpa only [DoubleCode.encode,DataWrapper.cancelFormula,ite_true,DoubleCode.encodeBody,
    Expr.instantiate,LogicCode.disj_subst,LogicCode.conj_subst,LogicCode.instantiate_raise,
    LogicSetup.code_disj,LogicSetup.code_conj,DoubleCode.big] using he

theorem encode_mark {T p c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t u : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    Proves P Γ γ (L.code.sign (t == u) (R.mark L.code u T c₀ (R.encode U L.code t T p))) := by
  have hv := h.tagged_typed hT mT (queryTag u) hc mc
  have he := h.encode_evaluation hU hT mT t hp mp hv.1 hv.2
  have h₀ := h.tagged_tag hT mT 0 (queryTag u) hc mc
  have hq := h.tagged_tag hT mT (queryTag t) (queryTag u) hc mc
  have hd := h.encode_typed hU hT mT t hp mp
  have hf := (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).2 _ _ hd.1 hd.2 ⟨hv.1,hv.2⟩
  have f₀ := (h.tagBody_family hT mT (queryBits 0)).instantiate hv.1 hv.2
  have fr := (h.recoveryBody_family hT mT 4 (hU.evalCallback_family hT mT hp mp)).instantiate hv.1 hv.2
  have fq := (h.tagBody_family hT mT (queryBits (queryTag t))).instantiate hv.1 hv.2
  have zne : (0 : Fin 9) ≠ queryTag u := (queryTag_ne_zero u).symm
  simp only [beq_eq_false_iff_ne.mpr zne,LogicCode.sign,Bool.false_eq_true,ite_false] at h₀
  by_cases htu : t = u
  · subst u
    simp only [beq_self_eq_true,LogicCode.sign,ite_true] at hq ⊢
    change Proves P Γ γ (R.first.observe _ _ _)
    pts_pl L using [he,h₀,hq]
  · have qne : queryTag t ≠ queryTag u := fun hh => htu (queryTag_injective hh)
    simp only [beq_eq_false_iff_ne.mpr htu,beq_eq_false_iff_ne.mpr qne,LogicCode.sign,Bool.false_eq_true,ite_false] at hq ⊢
    change Proves P Γ γ (L.neg (R.first.observe _ _ _))
    pts_pl L using [he,h₀,hq]

theorem encode_payload {T p c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data) :
    Equivalent P Γ γ (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code 0 T c))
      (U.observe T p c) := by
  have hv := h.tagged_typed hT mT 0 hc mc
  have he := h.encode_evaluation hU hT mT t hp mp hv.1 hv.2
  have h₀ := h.tagged_tag hT mT 0 0 hc mc
  have hq := h.tagged_tag hT mT (queryTag t) 0 hc mc
  have hrec := h.embed_recovery hT mT (queryBits 0) hc mc (hU.evalCallback_family hT mT hp mp)
  simp only [DataWrapper.evalCallback_instantiate,queryBits_length] at hrec
  change Equivalent P Γ γ ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate (R.tagged L.code 0 T c)) (U.observe T p c) at hrec
  have hd := h.encode_typed hU hT mT t hp mp
  have hf := (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).2 _ _ hd.1 hd.2 ⟨hv.1,hv.2⟩
  have f₀ := (h.tagBody_family hT mT (queryBits 0)).instantiate hv.1 hv.2
  have fr := (h.recoveryBody_family hT mT 4 (hU.evalCallback_family hT mT hp mp)).instantiate hv.1 hv.2
  have fq := (h.tagBody_family hT mT (queryBits (queryTag t))).instantiate hv.1 hv.2
  have fc := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  simp only [beq_self_eq_true,LogicCode.sign,ite_true] at h₀
  simp only [beq_eq_false_iff_ne.mpr (queryTag_ne_zero t),LogicCode.sign,Bool.false_eq_true,ite_false] at hq
  apply L.equivalent_of_iff hf fc
  pts_pl L using [he,h₀,hq,hrec]

theorem decode_encode {T p c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data) {s : S} (hs : HasType P Γ T (.sort s)) :
    Equivalent P Γ γ (U.observe T (R.decode U L.code T (R.encode U L.code t T p)) c) (U.observe T p c) := by
  have hd := h.encode_typed hU hT mT t hp mp
  have hQ := h.decoderBody_family hT mT hd.1 hd.2 hs
  have hdec := h.decode_typed hU hT mT hd.1 hd.2 hs
  have he := hU.cancellation hT mT hQ ⟨hc,mc⟩
  have he' : Equivalent P Γ γ (U.observe T (R.decode U L.code T (R.encode U L.code t T p)) c)
      (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code 0 T c)) := by
    simpa only [DataWrapper.cancelFormula,ite_true,DoubleCode.decoderBody_instantiate,DoubleCode.decode] using he
  have he₂ := h.encode_payload hU hT mT t hp mp hc mc
  have h₁ := (hU.sound hT mT).2 _ _ hdec.1 hdec.2 ⟨hc,mc⟩
  have h₂ := hQ.instantiate hc mc
  have h₃ := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  obtain ⟨r,hr⟩ := L.triple.codomain.1
  exact he'.trans he₂ (h₁.1 r hr) (by simpa only [DoubleCode.decoderBody_instantiate] using h₂.1 r hr) (h₃.1 r hr)
end DoubleCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
theorem bitBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bitBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).bitBody (L.subst σ) (T.subst σ) := by
  simp only [bitBody,bit_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl

theorem recBody_subst (L : LogicCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.recBody L T Q).subst (Expr.liftSub σ) =
      (R.subst σ).recBody (L.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [recBody,rec_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  congr 1
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,Expr.liftSub,Expr.liftRen,PureTypeSystem.Expr.liftRen,Expr.rename_comp]
    congr 1

theorem recoveryBody_subst (L : LogicCode S) (n : Nat) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.recoveryBody L n T Q).subst (Expr.liftSub σ) =
      (R.subst σ).recoveryBody (L.subst σ) n (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recoveryBody,recBody_subst,tower_subst,ih]
theorem tagBody_subst (L : LogicCode S) (bs : List Bool) (T : Expr S) (σ : Nat → Expr S) :
    (R.tagBody L bs T).subst (Expr.liftSub σ) =
      (R.subst σ).tagBody (L.subst σ) bs (T.subst σ) := by
  induction bs with
  | nil =>
    simp only [tagBody,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
    rfl
  | cons b bs ih =>
    simp only [tagBody,LogicCode.conj_subst,LogicCode.sign_subst,LogicCode.subst_rename,
      LogicCode.rename_subst,bitBody_subst,recBody_subst,tower_subst,ih]
    rfl

theorem big_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.big T).rename ρ = (R.rename ρ).big (T.rename ρ) := R.tower_rename 4 T ρ
theorem big_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.big T).subst σ = (R.subst σ).big (T.subst σ) := R.tower_subst 4 T σ
theorem bpType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.bpType T).rename ρ = (R.rename ρ).bpType (T.rename ρ) := by
  simp only [bpType,DataWrapper.apply_rename,big_rename]; rfl
theorem bpType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.bpType T).subst σ = (R.subst σ).bpType (T.subst σ) := by
  simp only [bpType,DataWrapper.apply_subst,big_subst]; rfl

theorem embedBody_subst (L : LogicCode S) (q : Fin 9) (T : Expr S) (σ : Nat → Expr S) :
    (R.embedBody L q T).subst (Expr.liftSub σ) =
      (R.subst σ).embedBody (L.subst σ) q (T.subst σ) := by
  simp only [embedBody,tagged_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl

theorem decoderBody_rename (L : LogicCode S) (T bp : Expr S) (ρ : Nat → Nat) :
    (R.decoderBody L T bp).rename (Expr.liftRen ρ) =
      (R.rename ρ).decoderBody (L.rename ρ) (T.rename ρ) (bp.rename ρ) := by
  simp only [decoderBody,Expr.compose_rename,DataWrapper.evalCallback_rename,embedBody_rename,big_rename]
  rfl

theorem decode_rename (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) (ρ : Nat → Nat) :
    (R.decode U L T bp).rename ρ =
      (R.rename ρ).decode (U.rename ρ) (L.rename ρ) (T.rename ρ) (bp.rename ρ) := by
  simp only [decode,DataWrapper.build_rename,DataWrapper.argRen,ite_true,decoderBody_rename]

theorem decoderBody_subst (L : LogicCode S) (T bp : Expr S) (σ : Nat → Expr S) :
    (R.decoderBody L T bp).subst (Expr.liftSub σ) =
      (R.subst σ).decoderBody (L.subst σ) (T.subst σ) (bp.subst σ) := by
  simp only [decoderBody,Expr.compose_subst,DataWrapper.evalCallback_subst,embedBody_subst,big_subst]
  rfl

theorem decode_subst (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) (σ : Nat → Expr S) :
    (R.decode U L T bp).subst σ =
      (R.subst σ).decode (U.subst σ) (L.subst σ) (T.subst σ) (bp.subst σ) := by
  simp only [decode,DataWrapper.build_subst,DataWrapper.argSub,ite_true,decoderBody_subst]

-- This body exposes the decoded predicate as a data map on exact BP values.
def decodeMap (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) :=
  (R.rename Nat.succ).decode (U.rename Nat.succ) (L.rename Nat.succ) (T.rename Nat.succ) (.var 0)

theorem decodeMap_instantiate (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) :
    (R.decodeMap U L T).instantiate bp = R.decode U L T bp := by
  simp only [decodeMap,Expr.instantiate,decode_subst,instantiate_raise,DataWrapper.instantiate_raise,
    LogicCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h hU
 theorem decodeMap_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    DataMap P Γ γ (R.bpType T) (U.apply T) (R.decodeMap U L.code T) := by
  let e : Embedding P Γ γ (R.bpType T :: Γ) (modeCons .data γ) := Embedding.cons hr Mode.data
  have hh := (h.rename e).decode_typed (hU.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [bpType_rename,e,Embedding.cons] using HasType.var hr) (.var 0) (e.typing hs)
  simpa only [DataMap,decodeMap,LogicSetup.code_rename,DataWrapper.apply_rename,e,Embedding.cons] using hh
end Formed

def bpBottom (L : LogicCode S) (T : Expr S) := R.first.build (R.big T) (L.bottom.rename Nat.succ)
def dummy (L : LogicCode S) (T : Expr S) := R.second.build (R.bpType T) (L.top.rename Nat.succ)
def isDummy (L : LogicCode S) (T o : Expr S) := R.second.observe (R.bpType T) o (R.bpBottom L T)
def markBody (L : LogicCode S) (t : Fin 8) (T c₀ : Expr S) :=
  R.first.contraCallback (R.big T) (R.tagged L (queryTag t) T c₀)
def pointBody (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) :=
  (L.rename Nat.succ).conj (R.markBody L 7 T c₀)
    ((U.contraCallback T c).compose (R.decodeMap U L T))
def point (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) :=
  R.second.build (R.bpType T) (R.pointBody U L T c₀ c)

theorem markBody_instantiate (L : LogicCode S) (t : Fin 8) (T c₀ bp : Expr S) :
    (R.markBody L t T c₀).instantiate bp = R.mark L t T c₀ bp := by
  simp only [markBody,DataWrapper.contraCallback_instantiate,mark]
theorem pointBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (T c₀ c bp : Expr S) :
    (R.pointBody U L T c₀ c).instantiate bp =
      L.conj (R.mark L 7 T c₀ bp) (U.observe T (R.decode U L T bp) c) := by
  simp only [pointBody,LogicCode.conj_instantiate_raise,markBody_instantiate,Expr.compose_instantiate,
    decodeMap_instantiate,DataWrapper.contraCallback_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem bpBottom_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    HasType P Γ (R.bpBottom L.code T) (R.bpType T) ∧ WellModed γ (R.bpBottom L.code T) .data :=
  (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).1 _ (.constant L.bottom_formula)
 theorem dummy_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    HasType P Γ (R.dummy L.code T) (R.paramType T) ∧ WellModed γ (R.dummy L.code T) .data :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).1 _ (.constant L.top_formula)
 theorem isDummy_formula {T o : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (ho : HasType P Γ o (R.paramType T)) (mo : WellModed γ o .data) :
    L.Formula (R.isDummy L.code T o) :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ ho mo (h.bpBottom_typed hT mT)
 theorem markBody_family {T c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    L.Family (R.bpType T) (R.markBody L.code t T c₀) := by
  have hv := h.tagged_typed hT mT (queryTag t) hc mc
  exact h.first.contraCallback_family (h.tower_sorted hT 4) (h.tower_mode mT 4) hv.1 hv.2

include hU
 theorem pointBody_family {T c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    L.Family (R.bpType T) (R.pointBody U L.code T c₀ c) :=
  (h.markBody_family hT mT 7 h₀ m₀).code_conj
    ((hU.contraCallback_family hT mT hc mc).compose (h.decodeMap_typed hU hT mT hs hr) hr)
 theorem point_typed {T c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    HasType P Γ (R.point U L.code T c₀ c) (R.paramType T) ∧
      WellModed γ (R.point U L.code T c₀ c) .data :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).1 _ (h.pointBody_family hU hT mT h₀ m₀ hc mc hs hr)
end Formed
end DoubleCode

namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem dummy_law {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    Proves P Γ γ (R.isDummy L.code T (R.dummy L.code T)) := by
  have ht := h.bpBottom_typed hT mT
  have hh := h.second.cancellation (h.bp_sorted hT) (h.bp_mode mT) (.constant L.top_formula) ht
  have he : Equivalent P Γ γ (R.isDummy L.code T (R.dummy L.code T)) L.top := by
    simpa only [DataWrapper.cancelFormula,ite_true,Expr.instantiate_raise,
      DoubleCode.isDummy,DoubleCode.dummy,LogicSetup.code_top] using hh
  exact he.2.prove L.top_intro

 theorem bottom_mark {T c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    Proves P Γ γ (L.neg (R.mark L.code t T c₀ (R.bpBottom L.code T))) := by
  have hv := h.tagged_typed hT mT (queryTag t) hc mc
  have he₀ := h.first.cancellation (h.tower_sorted hT 4) (h.tower_mode mT 4)
    (.constant L.bottom_formula) hv
  have he : Equivalent P Γ γ (R.mark L.code t T c₀ (R.bpBottom L.code T)) L.bottom := by
    simpa only [DataWrapper.cancelFormula,ite_true,Expr.instantiate_raise,
      DoubleCode.mark,DoubleCode.bpBottom,DoubleCode.big,LogicSetup.code_bottom] using he₀
  have hb := h.bpBottom_typed hT mT
  have hf := (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).2 _ _ hb.1 hb.2 hv
  pts_pl L using [he]

include hU
 theorem point_evaluation {T c₀ c bp : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data) :
    Equivalent P Γ γ (R.second.observe (R.bpType T) (R.point U L.code T c₀ c) bp)
      (L.conj (R.mark L.code 7 T c₀ bp) (U.observe T (R.decode U L.code T bp) c)) := by
  have hh := h.second.cancellation (h.bp_sorted hT) (h.bp_mode mT)
    (h.pointBody_family hU hT mT h₀ m₀ hc mc hs hr) ⟨hb,mb⟩
  simpa only [DataWrapper.cancelFormula,ite_true,DoubleCode.pointBody_instantiate,DoubleCode.point,LogicSetup.code_conj] using hh

 theorem point_not_dummy {T c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    Proves P Γ γ (L.neg (R.isDummy L.code T (R.point U L.code T c₀ c))) := by
  have hb := h.bpBottom_typed hT mT
  have he := h.point_evaluation hU hT mT h₀ m₀ hc mc hs hr hb.1 hb.2
  have hn := h.bottom_mark hT mT 7 h₀ m₀
  have hp := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have hD := h.isDummy_formula hT mT hp.1 hp.2
  have hmark₀ := (h.markBody_family hT mT 7 h₀ m₀).instantiate hb.1 hb.2
  have hmark : L.Formula (R.mark L.code 7 T c₀ (R.bpBottom L.code T)) := by
    simpa only [DoubleCode.markBody_instantiate] using hmark₀
  have hd := h.decode_typed hU hT mT hb.1 hb.2 hs
  have hobs := (hU.sound hT mT).2 _ _ hd.1 hd.2 ⟨hc,mc⟩
  change Proves P Γ γ (L.neg (R.second.observe _ _ _))
  pts_pl L using [he,hn]

 theorem point_query {T c₀ c p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Equivalent P Γ γ (R.query U L.code 7 T (R.point U L.code T c₀ c) p) (U.observe T p c) := by
  have hb := h.encode_typed hU hT mT 7 hp mp
  have he := h.point_evaluation hU hT mT h₀ m₀ hc mc hs hr hb.1 hb.2
  have hm₀ := h.encode_mark hU hT mT 7 7 hp mp h₀ m₀
  have hm : Proves P Γ γ (R.mark L.code 7 T c₀ (R.encode U L.code 7 T p)) := by
    simpa only [beq_self_eq_true,LogicCode.sign,ite_true] using hm₀
  have hd := h.decode_encode hU hT mT 7 hp mp hc mc hs
  have hpoint := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have hH := (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ hpoint.1 hpoint.2 hb
  have hE := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  have hdc := h.decode_typed hU hT mT hb.1 hb.2 hs
  have hE' := (hU.sound hT mT).2 _ _ hdc.1 hdc.2 ⟨hc,mc⟩
  have hmF₀ := (h.markBody_family hT mT 7 h₀ m₀).instantiate hb.1 hb.2
  have hmF : L.Formula (R.mark L.code 7 T c₀ (R.encode U L.code 7 T p)) := by
    simpa only [DoubleCode.markBody_instantiate] using hmF₀
  apply L.equivalent_of_iff hH hE
  pts_pl L using [he,hm,hd]
end DoubleCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
/-- Source Bundle is a fixed data term; no non-dummy proof enters its code. -/
def bundleBody (L : LogicCode S) (A d m y : Expr S) :=
  (L.rename Nat.succ).cond (R.first.contraCallback A d)
    (R.first.contraCallback A m) (R.first.contraCallback A y)
def bundle (L : LogicCode S) (A d m y : Expr S) := R.second.build (R.first.apply A) (R.bundleBody L A d m y)
/-- The outer access predicate, with the exact inner data callback `fi`. -/
def accessBody (L : LogicCode S) (A guard w fi : Expr S) :=
  (L.rename Nat.succ).cond guard (L.top.rename Nat.succ)
    ((R.second.evalCallback (R.first.apply A) w).compose fi)
def accessProbe (L : LogicCode S) (A guard w fi : Expr S) :=
  R.first.build A (R.accessBody L A guard w fi)
def access (L : LogicCode S) (A guard w fi : Expr S) :=
  R.second.observe (R.first.apply A) w (R.accessProbe L A guard w fi)

theorem bundleBody_instantiate (L : LogicCode S) (A d m y f : Expr S) :
    (R.bundleBody L A d m y).instantiate f =
      L.cond (R.first.observe A f d) (R.first.observe A f m) (R.first.observe A f y) := by
  simp only [bundleBody,Expr.instantiate,LogicCode.cond_subst,LogicCode.instantiate_raise,
    DataWrapper.contraCallback,DataWrapper.observe_subst,DataWrapper.instantiate_raise,
    Expr.subst_lift_single,DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false,Expr.subst,Expr.single]

theorem accessBody_instantiate (L : LogicCode S) (A guard w fi o : Expr S) :
    (R.accessBody L A guard w fi).instantiate o =
      L.cond (guard.instantiate o) L.top
        (R.second.observe (R.first.apply A) w (fi.instantiate o)) := by
  have he : ((L.rename Nat.succ).cond guard (L.top.rename Nat.succ)
      ((R.second.evalCallback (R.first.apply A) w).compose fi)).instantiate o =
      L.cond (guard.instantiate o) L.top
        (((R.second.evalCallback (R.first.apply A) w).compose fi).instantiate o) := by
    simp only [Expr.instantiate,LogicCode.cond_subst,LogicCode.instantiate_raise,Expr.subst_lift_single]
  exact he.trans (by rw [Expr.compose_instantiate,DataWrapper.evalCallback_instantiate])

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} (h : R.Formed L I J I)
include h
 theorem bundleBody_family {A d m y : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data) :
    L.Family (R.first.apply A) (R.bundleBody L.code A d m y) :=
  (h.first.contraCallback_family hA mA hd md).code_cond
    (h.first.contraCallback_family hA mA hm mm) (h.first.contraCallback_family hA mA hy my)
 theorem bundle_typed {A d m y : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data) :
    HasType P Γ (R.bundle L.code A d m y) (R.carrier A) ∧
      WellModed γ (R.bundle L.code A d m y) .data :=
  (h.second.sound (h.first.sorted hA) (h.first.mode mA)).1 _
    (h.bundleBody_family hA mA hd md hm mm hy my)
 theorem bundle_evaluation {A d m y f : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hf : HasType P Γ f (R.first.apply A)) (mf : WellModed γ f .data) :
    Equivalent P Γ γ (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f)
      (L.code.cond (R.first.observe A f d) (R.first.observe A f m) (R.first.observe A f y)) := by
  have hh := h.second.cancellation (h.first.sorted hA) (h.first.mode mA)
    (h.bundleBody_family hA mA hd md hm mm hy my) ⟨hf,mf⟩
  simpa only [DataWrapper.cancelFormula,ite_true,DoubleCode.bundleBody_instantiate,DoubleCode.bundle] using hh
 theorem accessBody_family {A guard w fi : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s)) :
    L.Family A (R.accessBody L.code A guard w fi) :=
  hg.code_cond (.constant L.top_formula)
    ((h.second.evalCallback_family (h.first.sorted hA) (h.first.mode mA) hw mw).compose hfi hs)
 theorem accessProbe_typed {A guard w fi : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s)) :
    HasType P Γ (R.accessProbe L.code A guard w fi) (R.first.apply A) ∧
      WellModed γ (R.accessProbe L.code A guard w fi) .data :=
  (h.first.sound hA mA).1 _ (h.accessBody_family hA mA hg hw mw hfi hs)
 theorem accessProbe_evaluation {A guard w fi o : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s))
    (ho : HasType P Γ o A) (mo : WellModed γ o .data) :
    Equivalent P Γ γ (R.first.observe A (R.accessProbe L.code A guard w fi) o)
      (L.code.cond (guard.instantiate o) L.top (R.second.observe (R.first.apply A) w (fi.instantiate o))) := by
  have hh := h.first.cancellation hA mA (h.accessBody_family hA mA hg hw mw hfi hs) ⟨ho,mo⟩
  simpa only [DataWrapper.cancelFormula,ite_true,DoubleCode.accessBody_instantiate,DoubleCode.accessProbe,LogicSetup.top,LogicCode.top,LogicCode.imp,LogicSetup.imp,LogicSetup.code] using hh
end Formed
end DoubleCode

namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} (h : R.Formed L I J I)
include h
 theorem bundle_select_true {A d m y f : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hf : HasType P Γ f (R.first.apply A)) (mf : WellModed γ f .data)
    (hg : Proves P Γ γ (R.first.observe A f d)) :
    Equivalent P Γ γ (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f)
      (R.first.observe A f m) := by
  have he := h.bundle_evaluation hA mA hd md hm mm hy my hf mf
  have hw := h.bundle_typed hA mA hd md hm mm hy my
  have hW := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 ⟨hf,mf⟩
  have hD := (h.first.sound hA mA).2 _ _ hf mf ⟨hd,md⟩
  have hM := (h.first.sound hA mA).2 _ _ hf mf ⟨hm,mm⟩
  have hY := (h.first.sound hA mA).2 _ _ hf mf ⟨hy,my⟩
  apply L.equivalent_of_iff hW hM
  pts_pl L using [he,hg]
 theorem bundle_select_false {A d m y f : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hf : HasType P Γ f (R.first.apply A)) (mf : WellModed γ f .data)
    (hg : Proves P Γ γ (L.neg (R.first.observe A f d))) :
    Equivalent P Γ γ (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f)
      (R.first.observe A f y) := by
  have he := h.bundle_evaluation hA mA hd md hm mm hy my hf mf
  have hw := h.bundle_typed hA mA hd md hm mm hy my
  have hW := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 ⟨hf,mf⟩
  have hD := (h.first.sound hA mA).2 _ _ hf mf ⟨hd,md⟩
  have hM := (h.first.sound hA mA).2 _ _ hf mf ⟨hm,mm⟩
  have hY := (h.first.sound hA mA).2 _ _ hf mf ⟨hy,my⟩
  apply L.equivalent_of_iff hW hY
  pts_pl L using [he,hg]
 theorem accessProbe_true {A guard w fi o : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s))
    (ho : HasType P Γ o A) (mo : WellModed γ o .data) (hG : Proves P Γ γ (guard.instantiate o)) :
    Proves P Γ γ (R.first.observe A (R.accessProbe L.code A guard w fi) o) := by
  have he := h.accessProbe_evaluation hA mA hg hw mw hfi hs ho mo
  have ht := h.accessProbe_typed hA mA hg hw mw hfi hs
  have hf := (h.first.sound hA mA).2 _ _ ht.1 ht.2 ⟨ho,mo⟩
  have hgf := hg.instantiate ho mo
  have hpo := hfi.apply ho mo
  have hF := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw mw hpo
  pts_pl L using [he,hG]
 theorem accessProbe_false {A guard w fi o : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s))
    (ho : HasType P Γ o A) (mo : WellModed γ o .data) (hG : Proves P Γ γ (L.neg (guard.instantiate o))) :
    Equivalent P Γ γ (R.first.observe A (R.accessProbe L.code A guard w fi) o)
      (R.second.observe (R.first.apply A) w (fi.instantiate o)) := by
  have he := h.accessProbe_evaluation hA mA hg hw mw hfi hs ho mo
  have ht := h.accessProbe_typed hA mA hg hw mw hfi hs
  have hf := (h.first.sound hA mA).2 _ _ ht.1 ht.2 ⟨ho,mo⟩
  have hgf := hg.instantiate ho mo
  have hpo := hfi.apply ho mo
  have hF := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw mw hpo
  apply L.equivalent_of_iff hf hF
  pts_pl L using [he,hG]

/-- The exact-parameter access calculation. The inner callback is raw typed data,
    not a selected term depending on the non-dummy proof. -/
 theorem access_bundle {A d m y guard fi : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hg : L.Family A guard) (hfi : DataMap P Γ γ A (R.first.apply A) fi)
    {s : S} (hs : HasType P Γ A (.sort s))
    (hgd : Proves P Γ γ (guard.instantiate d))
    (hgm : Proves P Γ γ (L.neg (guard.instantiate m)))
    (hid : Proves P Γ γ (L.neg (R.first.observe A (fi.instantiate m) d))) :
    Equivalent P Γ γ (R.access L.code A guard (R.bundle L.code A d m y) fi)
      (R.first.observe A (fi.instantiate m) y) := by
  have hw := h.bundle_typed hA mA hd md hm mm hy my
  have hf := h.accessProbe_typed hA mA hg hw.1 hw.2 hfi hs
  have ht := h.accessProbe_true hA mA hg hw.1 hw.2 hfi hs hd md hgd
  have he₁ := h.bundle_select_true hA mA hd md hm mm hy my hf.1 hf.2 ht
  have he₂ := h.accessProbe_false hA mA hg hw.1 hw.2 hfi hs hm mm hgm
  have hfm := hfi.apply hm mm
  have he₃ := h.bundle_select_false hA mA hd md hm mm hy my hfm.1 hfm.2 hid
  have h₀ := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 hf
  have h₁ := (h.first.sound hA mA).2 _ _ hf.1 hf.2 ⟨hm,mm⟩
  have h₂ := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 hfm
  have h₃ := (h.first.sound hA mA).2 _ _ hfm.1 hfm.2 ⟨hy,my⟩
  obtain ⟨r,hr⟩ := L.triple.codomain.1
  exact (he₁.trans he₂ (h₀.1 r hr) (h₁.1 r hr) (h₂.1 r hr)).trans he₃
    (h₀.1 r hr) (h₂.1 r hr) (h₃.1 r hr)
end DoubleCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
def dummyBody (L : LogicCode S) (T : Expr S) :=
  R.second.contraCallback (R.bpType T) (R.bpBottom L T)
def queryBody (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :=
  R.second.contraCallback (R.bpType T) (R.encode U L 7 T p)
def innerBody (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :=
  (L.rename Nat.succ).cond (R.dummyBody L T) (L.bottom.rename Nat.succ)
    (R.queryBody U L T p)
def innerProbe (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :=
  R.first.build (R.paramType T) (R.innerBody U L T p)

theorem dummyBody_instantiate (L : LogicCode S) (T o : Expr S) :
    (R.dummyBody L T).instantiate o = R.isDummy L T o :=
  R.second.contraCallback_instantiate _ _ _
theorem queryBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (T p o : Expr S) :
    (R.queryBody U L T p).instantiate o = R.query U L 7 T o p :=
  R.second.contraCallback_instantiate _ _ _
theorem innerBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (T p o : Expr S) :
    (R.innerBody U L T p).instantiate o =
      L.cond (R.isDummy L T o) L.bottom (R.query U L 7 T o p) := by
  simp only [innerBody,Expr.instantiate,LogicCode.cond_subst,LogicCode.instantiate_raise,
    Expr.subst_lift_single]
  change L.cond ((R.dummyBody L T).instantiate o) L.bottom
    ((R.queryBody U L T p).instantiate o) = _
  rw [dummyBody_instantiate,queryBody_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem dummyBody_family {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    L.Family (R.paramType T) (R.dummyBody L.code T) := by
  have hb := h.bpBottom_typed hT mT
  exact h.second.contraCallback_family (h.bp_sorted hT) (h.bp_mode mT) hb.1 hb.2
include hU
 theorem queryBody_family {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Family (R.paramType T) (R.queryBody U L.code T p) := by
  have he := h.encode_typed hU hT mT 7 hp mp
  exact h.second.contraCallback_family (h.bp_sorted hT) (h.bp_mode mT) he.1 he.2
 theorem innerBody_family {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Family (R.paramType T) (R.innerBody U L.code T p) :=
  (h.dummyBody_family hT mT).code_cond (.constant L.bottom_formula)
    (h.queryBody_family hU hT mT hp mp)
 theorem innerProbe_typed {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    HasType P Γ (R.innerProbe U L.code T p) (R.first.apply (R.paramType T)) ∧
      WellModed γ (R.innerProbe U L.code T p) .data :=
  (h.first.sound (h.param_sorted hT) (h.param_mode mT)).1 _ (h.innerBody_family hU hT mT hp mp)
 theorem innerProbe_evaluation {T p o : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (ho : HasType P Γ o (R.paramType T)) (mo : WellModed γ o .data) :
    Equivalent P Γ γ (R.first.observe (R.paramType T) (R.innerProbe U L.code T p) o)
      (L.code.cond (R.isDummy L.code T o) L.bottom (R.query U L.code 7 T o p)) := by
  have he := h.first.cancellation (h.param_sorted hT) (h.param_mode mT)
    (h.innerBody_family hU hT mT hp mp) ⟨ho,mo⟩
  simpa only [DataWrapper.cancelFormula,ite_true,innerBody_instantiate,LogicSetup.code_bottom,
    innerProbe] using he
 theorem innerProbe_dummy {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Proves P Γ γ (L.neg (R.first.observe (R.paramType T)
      (R.innerProbe U L.code T p) (R.dummy L.code T))) := by
  have hd := h.dummy_typed hT mT
  have he := h.innerProbe_evaluation hU hT mT hp mp hd.1 hd.2
  have hD := h.dummy_law hT mT
  have hi := h.innerProbe_typed hU hT mT hp mp
  have hf := (h.first.sound (h.param_sorted hT) (h.param_mode mT)).2 _ _ hi.1 hi.2 hd
  have hdf := h.isDummy_formula hT mT hd.1 hd.2
  have hq₀ := (h.queryBody_family hU hT mT hp mp).instantiate hd.1 hd.2
  have hq : L.Formula (R.query U L.code 7 T (R.dummy L.code T) p) := by
    simpa only [queryBody_instantiate] using hq₀
  exact L.equivalent_bottom_neg hf (L.cond_yes hdf L.bottom_formula hq hf he hD)
 theorem innerProbe_point {T c₀ c p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Equivalent P Γ γ (R.first.observe (R.paramType T) (R.innerProbe U L.code T p)
      (R.point U L.code T c₀ c)) (U.observe T p c) := by
  have ht := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have he := h.innerProbe_evaluation hU hT mT hp mp ht.1 ht.2
  have hn := h.point_not_dummy hU hT mT h₀ m₀ hc mc hs hr
  have hq := h.point_query hU hT mT h₀ m₀ hc mc hs hr hp mp
  have hi := h.innerProbe_typed hU hT mT hp mp
  have hf := (h.first.sound (h.param_sorted hT) (h.param_mode mT)).2 _ _ hi.1 hi.2 ht
  have ho := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  have hdf := h.isDummy_formula hT mT ht.1 ht.2
  have hqf₀ := (h.queryBody_family hU hT mT hp mp).instantiate ht.1 ht.2
  have hqf : L.Formula (R.query U L.code 7 T (R.point U L.code T c₀ c) p) := by
    simpa only [queryBody_instantiate] using hqf₀
  have he' := L.cond_no hdf L.bottom_formula hqf hf he hn
  obtain ⟨a,ha⟩ := L.triple.codomain.1
  exact he'.trans hq (hf.1 a ha) (hqf.1 a ha) (ho.1 a ha)
end Formed
end DoubleCode

namespace DataMap
variable {Γ : List (Expr S)} {γ : Nat → Mode} {T U V f g : Expr S} {s t : S}
theorem compose (hf : DataMap P Γ γ U V f) (hg : DataMap P Γ γ T U g)
    (hT : HasType P Γ T (.sort s)) (hU : HasType P Γ U (.sort t)) :
    DataMap P Γ γ T V (f.compose g) := by
  have hh := (hf.rename hU (Embedding.cons hT .data)).apply hg.1 hg.2
  exact hh
end DataMap
namespace LogicCode
theorem rename_bottom (L : LogicCode S) (ρ : Nat → Nat) : (L.rename ρ).bottom = L.bottom.rename ρ := rfl
theorem subst_bottom (L : LogicCode S) (σ : Nat → Expr S) : (L.subst σ).bottom = L.bottom.subst σ := rfl
end LogicCode
namespace DoubleCode

section
variable (R : DoubleCode S)
theorem rename_first (ρ : Nat → Nat) : (R.rename ρ).first = R.first.rename ρ := rfl
theorem subst_first (σ : Nat → Expr S) : (R.subst σ).first = R.first.subst σ := rfl
theorem rename_second (ρ : Nat → Nat) : (R.rename ρ).second = R.second.rename ρ := rfl
theorem subst_second (σ : Nat → Expr S) : (R.subst σ).second = R.second.subst σ := rfl
theorem bpBottom_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.bpBottom L T).rename ρ = (R.rename ρ).bpBottom (L.rename ρ) (T.rename ρ) := by
  simp only [bpBottom,DataWrapper.build_rename,big_rename,DataWrapper.argRen,ite_true,rename_first,LogicCode.rename_bottom,Expr.rename_comp]
  rfl
theorem bpBottom_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bpBottom L T).subst σ = (R.subst σ).bpBottom (L.subst σ) (T.subst σ) := by
  simp only [bpBottom,DataWrapper.build_subst,big_subst,DataWrapper.argSub,ite_true,subst_first,LogicCode.subst_bottom,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem paramType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.paramType T).rename ρ = (R.rename ρ).paramType (T.rename ρ) := by
  simp only [paramType,DataWrapper.apply_rename,bpType_rename]; rfl
theorem paramType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.paramType T).subst σ = (R.subst σ).paramType (T.subst σ) := by
  simp only [paramType,DataWrapper.apply_subst,bpType_subst]; rfl
theorem encode_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (ρ : Nat → Nat) :
    (R.encode U L t T p).rename ρ =
      (R.rename ρ).encode (U.rename ρ) (L.rename ρ) t (T.rename ρ) (p.rename ρ) := by
  simp only [encode,DataWrapper.build_rename,DataWrapper.argRen,ite_true,big_rename,encodeBody_rename]
  rfl
theorem encodeBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (σ : Nat → Expr S) :
    (R.encodeBody U L t T p).subst (Expr.liftSub σ) =
      (R.subst σ).encodeBody (U.subst σ) (L.subst σ) t (T.subst σ) (p.subst σ) := by
  simp only [encodeBody,LogicCode.disj_subst,LogicCode.conj_subst,tagBody_subst,
    recoveryBody_subst,DataWrapper.evalCallback_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem encode_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (σ : Nat → Expr S) :
    (R.encode U L t T p).subst σ =
      (R.subst σ).encode (U.subst σ) (L.subst σ) t (T.subst σ) (p.subst σ) := by
  simp only [encode,DataWrapper.build_subst,DataWrapper.argSub,ite_true,big_subst,encodeBody_subst]
  rfl
theorem dummyBody_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.dummyBody L T).rename (Expr.liftRen ρ) =
      (R.rename ρ).dummyBody (L.rename ρ) (T.rename ρ) := by
  simp only [dummyBody,DataWrapper.contraCallback_rename,bpType_rename,bpBottom_rename]; rfl
theorem dummyBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummyBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).dummyBody (L.subst σ) (T.subst σ) := by
  simp only [dummyBody,DataWrapper.contraCallback_subst,bpType_subst,bpBottom_subst]; rfl
theorem innerBody_rename (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.innerBody U L T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).innerBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [innerBody,LogicCode.cond_rename,dummyBody_rename,queryBody,
    DataWrapper.contraCallback_rename,bpType_rename,encode_rename,LogicCode.rename_comp,rename_second,LogicCode.rename_bottom,Expr.rename_comp]
  rfl
theorem innerBody_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerBody U L T p).subst (Expr.liftSub σ) =
      (R.subst σ).innerBody (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerBody,LogicCode.cond_subst,dummyBody_subst,queryBody,
    DataWrapper.contraCallback_subst,bpType_subst,encode_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,subst_second,LogicCode.subst_bottom,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem innerProbe_rename (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.innerProbe U L T p).rename ρ =
      (R.rename ρ).innerProbe (U.rename ρ) (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [innerProbe,DataWrapper.build_rename,DataWrapper.argRen,ite_true,paramType_rename,innerBody_rename]
  rfl
theorem innerProbe_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerProbe U L T p).subst σ =
      (R.subst σ).innerProbe (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerProbe,DataWrapper.build_subst,DataWrapper.argSub,ite_true,paramType_subst,innerBody_subst]
  rfl

def innerMap (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) :=
  (R.rename Nat.succ).innerProbe (U.rename Nat.succ) (L.rename Nat.succ) (T.rename Nat.succ) (.var 0)
theorem innerMap_instantiate (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :
    (R.innerMap U L T).instantiate p = R.innerProbe U L T p := by
  simp only [innerMap,Expr.instantiate,innerProbe_subst,instantiate_raise,
    DataWrapper.instantiate_raise,LogicCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h hU
 theorem innerMap_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ (U.apply T) (.sort s)) :
    DataMap P Γ γ (U.apply T) (R.first.apply (R.paramType T)) (R.innerMap U L.code T) := by
  let e : Embedding P Γ γ (U.apply T :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := (h.rename e).innerProbe_typed (hU.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [DataWrapper.apply_rename,e,Embedding.cons] using HasType.var hs) (.var 0)
  simpa only [DataMap,innerMap,LogicSetup.code_rename,DataWrapper.apply_rename,
    paramType_rename,rename_first,e,Embedding.cons] using hh
end Formed

theorem query_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (ρ : Nat → Nat) :
    (R.query U L t T m p).rename ρ =
      (R.rename ρ).query (U.rename ρ) (L.rename ρ) t (T.rename ρ) (m.rename ρ) (p.rename ρ) := by
  simp only [query,DataWrapper.observe_rename,bpType_rename,encode_rename,rename_second,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false]
theorem query_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (σ : Nat → Expr S) :
    (R.query U L t T m p).subst σ =
      (R.subst σ).query (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) (p.subst σ) := by
  simp only [query,DataWrapper.observe_subst,bpType_subst,encode_subst,subst_second,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false]
/-- The genuine predicate binder of qry_t(m,P), distinct from the parameter
binder used by Access. -/
def queryPredBody (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) :=
  (R.rename Nat.succ).query (U.rename Nat.succ) (L.rename Nat.succ) t
    (T.rename Nat.succ) (m.rename Nat.succ) (.var 0)
theorem queryPredBody_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (ρ : Nat → Nat) :
    (R.queryPredBody U L t T m).rename (Expr.liftRen ρ) =
      (R.rename ρ).queryPredBody (U.rename ρ) (L.rename ρ) t (T.rename ρ) (m.rename ρ) := by
  simp only [queryPredBody,query_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem queryPredBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (σ : Nat → Expr S) :
    (R.queryPredBody U L t T m).subst (Expr.liftSub σ) =
      (R.subst σ).queryPredBody (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) := by
  simp only [queryPredBody,query_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem queryPredBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) :
    (R.queryPredBody U L t T m).instantiate p = R.query U L t T m p := by
  simp only [queryPredBody,Expr.instantiate,query_subst,instantiate_raise,DataWrapper.instantiate_raise,
    LogicCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h hU
 theorem query_formula (t : Fin 8) {T m p : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Formula (R.query U L.code t T m p) := by
  have hb := h.encode_typed hU hT mT t hp mp
  exact (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ hm mm hb
 theorem queryPredBody_family (t : Fin 8) {T m : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data) :
    L.Family (U.apply T) (R.queryPredBody U L.code t T m) := by
  intro Δ δ e p hp mp
  rw [queryPredBody_rename,queryPredBody_instantiate]
  simpa only [← LogicSetup.code_rename] using (h.rename e).query_formula (hU.rename e) t
    (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [paramType_rename] using e.typing hm) (e.moded mm)
    (by simpa only [DataWrapper.apply_rename] using hp) mp
end Formed

def accessMap (U : DataWrapper S true) (L : LogicCode S) (T pMap : Expr S) :=
  (R.innerMap U L T).compose pMap
def recoverAccess (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) :=
  R.access L (R.paramType T) (R.dummyBody L T) w (R.accessMap U L T pMap)
theorem accessMap_instantiate (U : DataWrapper S true) (L : LogicCode S) (T pMap m : Expr S) :
    (R.accessMap U L T pMap).instantiate m = R.innerProbe U L T (pMap.instantiate m) := by
  simp only [accessMap,Expr.compose_instantiate,innerMap_instantiate]
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H) (hI : I.Nonempty) (hH : H.Nonempty)
include h hU hI hH
 theorem accessMap_typed {T pMap : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap) :
    DataMap P Γ γ (R.paramType T) (R.first.apply (R.paramType T)) (R.accessMap U L.code T pMap) := by
  obtain ⟨s,hs⟩ := hI
  obtain ⟨t,ht⟩ := hH
  exact (h.innerMap_typed hU hT mT (hU.sorted hT t ht)).compose hp
    (h.param_sorted hT s hs) (hU.sorted hT t ht)

 theorem access_recovery {T pMap m c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hnd : Proves P Γ γ (L.neg (R.isDummy L.code T m))) :
    Equivalent P Γ γ
      (R.recoverAccess U L.code T
        (R.bundle L.code (R.paramType T) (R.dummy L.code T) m (R.point U L.code T c₀ c)) pMap)
      (U.observe T (pMap.instantiate m) c) := by
  have hf := h.accessMap_typed hU hI hH hT mT hp
  have hd := h.dummy_typed hT mT
  have hy := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have hpm := hp.apply hm mm
  have hid₀ := h.innerProbe_dummy hU hT mT hpm.1 hpm.2
  have hid : Proves P Γ γ (L.neg (R.first.observe (R.paramType T)
      ((R.accessMap U L.code T pMap).instantiate m) (R.dummy L.code T))) := by
    simpa only [accessMap_instantiate] using hid₀
  obtain ⟨a,ha⟩ := hI
  have he₀ := h.access_bundle (h.param_sorted hT) (h.param_mode mT) hd.1 hd.2 hm mm hy.1 hy.2
    (h.dummyBody_family hT mT) hf (h.param_sorted hT a ha)
    (by simpa only [dummyBody_instantiate] using h.dummy_law hT mT)
    (by simpa only [dummyBody_instantiate] using hnd) hid
  have he : Equivalent P Γ γ
      (R.recoverAccess U L.code T
        (R.bundle L.code (R.paramType T) (R.dummy L.code T) m (R.point U L.code T c₀ c)) pMap)
      (R.first.observe (R.paramType T) (R.innerProbe U L.code T (pMap.instantiate m))
        (R.point U L.code T c₀ c)) := by
    simpa only [recoverAccess,accessMap_instantiate] using he₀
  have he' := h.innerProbe_point hU hT mT h₀ m₀ hc mc hs hr hpm.1 hpm.2
  have hw := h.bundle_typed (h.param_sorted hT) (h.param_mode mT) hd.1 hd.2 hm mm hy.1 hy.2
  have hfe := h.accessProbe_typed (h.param_sorted hT) (h.param_mode mT)
    (h.dummyBody_family hT mT) hw.1 hw.2 hf (h.param_sorted hT a ha)
  have hW := (h.second.sound (h.first.sorted (h.param_sorted hT)) (h.first.mode (h.param_mode mT))).2
    _ _ hw.1 hw.2 hfe
  have hfi := h.innerProbe_typed hU hT mT hpm.1 hpm.2
  have hY := (h.first.sound (h.param_sorted hT) (h.param_mode mT)).2 _ _ hfi.1 hfi.2 hy
  have hQ := (hU.sound hT mT).2 _ _ hpm.1 hpm.2 ⟨hc,mc⟩
  obtain ⟨b,hb⟩ := L.triple.codomain.1
  exact he.trans he' (hW.1 b hb) (hY.1 b hb) (hQ.1 b hb)
end Formed
end

variable (R : DoubleCode S) {A B : Expr S}
theorem carrier_converts (h : Converts A B) : Converts (R.carrier A) (R.carrier B) :=
  R.second.apply_converts (R.first.apply_converts h)
theorem tower_converts (n : Nat) (h : Converts A B) : Converts (R.tower n A) (R.tower n B) := by
  induction n with
  | zero => exact h
  | succ n ih => exact R.carrier_converts ih
theorem paramType_converts (h : Converts A B) : Converts (R.paramType A) (R.paramType B) :=
  R.second.apply_converts (R.first.apply_converts (R.tower_converts 4 h))
end DoubleCode
namespace ProbeCode

section
variable (R : ProbeCode S)
def atType (A : Expr S) := R.funPath.apply (R.funType A)
def specialize (A v : Expr S) := Expr.app .dd v (R.lifting.inject A)
def readBody (w : Expr S) := (R.tail.rename Nat.succ).read (.app .dd (.var 0) (w.rename Nat.succ))
def observe (A v w : Expr S) := R.funPath.observe (R.funType A) (R.specialize A v) (R.readBody w)

theorem atType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.atType A).rename ρ = (R.rename ρ).atType (A.rename ρ) := by
  simp only [atType,DataWrapper.apply_rename,funType_rename,rename]
theorem atType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.atType A).subst σ = (R.subst σ).atType (A.subst σ) := by
  simp only [atType,DataWrapper.apply_subst,funType_subst,subst]
theorem funType_converts {A B : Expr S} (h : Converts A B) : Converts (R.funType A) (R.funType B) :=
  .pi (R.doubled.carrier_converts (R.doubled.paramType_converts
    (R.raw.apply_converts (R.initial.apply_converts h)))) (.refl _)
theorem atType_converts {A B : Expr S} (h : Converts A B) : Converts (R.atType A) (R.atType B) :=
  R.funPath.apply_converts (R.funType_converts h)
theorem at_body_convert (A : Expr S) :
    Converts (R.body.instantiate (R.lifting.inject A)) (R.atType A) := by
  rw [body_instantiate]
  exact R.atType_converts (R.lifting.cancel A).converts

theorem readBody_instantiate (w f : Expr S) :
    (R.readBody w).instantiate f = R.tail.read (.app .dd f w) := by
  simp only [readBody,Expr.instantiate,DataTail.read_subst,DataTail.instantiate_raise,
    Expr.subst,Expr.single,Expr.subst_lift_single]

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C} {I J k p n g : Set S}
namespace Formed
variable {R} (h : R.Formed L I J k p n g)
include h

theorem at_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.atType A) J := h.funPath.sorted (h.fun_sorted ha)
theorem at_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.atType A) .data :=
  h.funPath.mode (h.fun_mode ma)
theorem at_typed {A v : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (hv : HasType P Γ v R.carrier) : HasType P Γ (R.specialize A v) (R.atType A) := by
  obtain ⟨s,hs⟩ := h.mainTriple.codomain.1
  exact (hv.application ((h.lifting.typed h.seed_sorted).1 A ha)).conversion
    (h.at_sorted ha s hs) (R.at_body_convert A)
theorem at_data {A v : Expr S} (ma : WellModed γ A .data) (mv : WellModed γ v .data) :
    WellModed γ (R.specialize A v) .data := .app mv (h.lifting.modes.2.1 A ma)

theorem readBody_family {A w : Expr S} (_ha : HasType P Γ A (.sort R.seed))
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    L.Family (R.funType A) (R.readBody w) := by
  intro Δ δ e f hf mf
  have hh := h.rename e
  have hF : HasType P Δ f ((R.rename e.names).funType (A.rename e.names)) := by
    simpa only [funType_rename] using hf
  have hW : HasType P Δ (w.rename e.names) ((R.rename e.names).singleType (A.rename e.names)) := by
    simpa only [singleType_rename] using e.typing hw
  have hr := hh.tail.read_formula (hF.apply_arrow hW) (.app mf (e.moded mw))
  convert hr using 1
  simp only [readBody,DataTail.read_rename,DataTail.rename_comp,Expr.rename,Expr.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def,Expr.instantiate,
    DataTail.read_subst,Expr.subst,Expr.single,Expr.subst_rename]
  have he : (fun x => e.names x + 1) = Nat.succ ∘ e.names := rfl
  rw [he,← DataTail.rename_comp,DataTail.instantiate_raise]
  change (R.tail.rename e.names).read (.app .dd f (w.subst (Expr.var ∘ e.names))) = _
  rw [Expr.subst_var_rename]
  rfl

theorem observe_formula {A v w : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hv : HasType P Γ v R.carrier) (mv : WellModed γ v .data)
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    L.Formula (R.observe A v w) :=
  (h.funPath.sound (h.fun_sorted ha) (h.fun_mode ma)).2 _ _ (h.at_typed ha hv)
    (h.at_data ma mv) (h.readBody_family ha hw mw)
end Formed
end

variable (R : ProbeCode S)
/-- Ordinary data abstraction on the single bundle, before even wrapping. -/
def funBuild (A Q : Expr S) : Expr S := .lam .dd (R.singleType A) ((R.tail.rename Nat.succ).send Q)
def wrappedBuild (A Q : Expr S) := R.funPath.build (R.funType A) (R.funBuild A Q)

theorem funBuild_beta (A Q w : Expr S) :
    Converts (.app .dd (R.funBuild A Q) w) (R.tail.send (Q.instantiate w)) := by
  have hh : Converts (.app .dd (R.funBuild A Q) w)
      (((R.tail.rename Nat.succ).send Q).instantiate w) :=
    .rel _ _ (Beta.head .dd _ _ _)
  simpa only [Expr.instantiate,DataTail.send_subst,DataTail.instantiate_raise] using hh

theorem funBuild_rename (A Q : Expr S) (ρ : Nat → Nat) :
    (R.funBuild A Q).rename ρ =
      (R.rename ρ).funBuild (A.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [funBuild,Expr.rename,singleType_rename,DataTail.send_rename,rename,DataTail.rename_comp]
  rfl

theorem funBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.funBuild A Q).subst σ =
      (R.subst σ).funBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [funBuild,Expr.subst,singleType_subst,DataTail.send_subst]
  simp only [subst,DataTail.subst_rename,DataTail.rename_subst]
  rfl

theorem wrappedBuild_rename (A Q : Expr S) (ρ : Nat → Nat) :
    (R.wrappedBuild A Q).rename ρ =
      (R.rename ρ).wrappedBuild (A.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [wrappedBuild,DataWrapper.build_rename,funType_rename,DataWrapper.argRen,
    Bool.false_eq_true,ite_false,funBuild_rename]
  rfl

theorem wrappedBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.wrappedBuild A Q).subst σ =
      (R.subst σ).wrappedBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [wrappedBuild,DataWrapper.build_subst,funType_subst,DataWrapper.argSub,
    Bool.false_eq_true,ite_false,funBuild_subst]
  rfl

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C} {I J k p n g : Set S}
namespace Formed
variable {R} (h : R.Formed L I J k p n g)
include h
 theorem funBuild_typed {A Q : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hQ : L.Family (R.singleType A) Q) :
    HasType P Γ (R.funBuild A Q) (R.funType A) ∧ WellModed γ (R.funBuild A Q) .data := by
  obtain ⟨r,hr⟩ := h.funTriple.product.1
  obtain ⟨s,hs,t,ht,hst⟩ := h.funTriple.output ▸ hr
  let e : Embedding P Γ γ (R.singleType A :: Γ) (modeCons .data γ) :=
    Embedding.cons (h.single_sorted ha s hs) .data
  have hsend := (h.tail.rename e).send_typed (hQ.opened (h.single_sorted ha s hs))
  refine ⟨HasType.abstraction ?_ (h.fun_sorted ha r hr), .lam (h.single_mode ma) ?_⟩
  · simpa only [DataTail.carrier_rename,e,Embedding.cons,funType,Expr.arrow] using hsend.1
  · exact hsend.2

 theorem wrappedBuild_typed {A Q : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hQ : L.Family (R.singleType A) Q) :
    HasType P Γ (R.wrappedBuild A Q) (R.atType A) ∧
      WellModed γ (R.wrappedBuild A Q) .data :=
  (h.funPath.sound (h.fun_sorted ha) (h.fun_mode ma)).1 _ (h.funBuild_typed ha ma hQ)

 theorem funBuild_evaluation {A Q w : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hQ : L.Family (R.singleType A) Q)
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (R.tail.read (.app .dd (R.funBuild A Q) w)) (Q.instantiate w) := by
  have hf := h.funBuild_typed ha ma hQ
  have hread := h.tail.read_formula (hf.1.apply_arrow hw) (.app hf.2 mw)
  have hQw := hQ.instantiate hw mw
  have hs := h.tail.send_typed hQw
  have hread' := h.tail.read_formula hs.1 hs.2
  obtain ⟨t,ht⟩ := L.triple.codomain.1
  have he : Equivalent P Γ γ (R.tail.read (.app .dd (R.funBuild A Q) w))
      (R.tail.read (R.tail.send (Q.instantiate w))) :=
    .of_conversion (hread.1 t ht) (hread'.1 t ht) (R.tail.read_converts (R.funBuild_beta A Q w))
  exact he.trans (h.tail.read_send hQw) (hread.1 t ht) (hread'.1 t ht) (hQw.1 t ht)

 theorem wrappedBuild_evaluation {A Q w : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hQ : L.Family (R.singleType A) Q)
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (R.funPath.observe (R.funType A) (R.wrappedBuild A Q) (R.readBody w))
      (Q.instantiate w) := by
  have hf := h.funBuild_typed ha ma hQ
  have hbody := h.readBody_family ha hw mw
  have he₀ := h.funPath.cancellation (h.fun_sorted ha) (h.fun_mode ma) hf hbody
  have he : Equivalent P Γ γ (R.funPath.observe (R.funType A) (R.wrappedBuild A Q) (R.readBody w))
      (R.tail.read (.app .dd (R.funBuild A Q) w)) := by
    simpa only [DataWrapper.cancelFormula,Bool.false_eq_true,ite_false,readBody_instantiate,
      wrappedBuild] using he₀
  have hwrap := h.wrappedBuild_typed ha ma hQ
  have hobs := (h.funPath.sound (h.fun_sorted ha) (h.fun_mode ma)).2 _ _ hwrap.1 hwrap.2 hbody
  have hread := h.tail.read_formula (hf.1.apply_arrow hw) (.app hf.2 mw)
  obtain ⟨t,ht⟩ := L.triple.codomain.1
  exact he.trans (h.funBuild_evaluation ha ma hQ hw mw)
    (hobs.1 t ht) (hread.1 t ht) ((hQ.instantiate hw mw).1 t ht)
end Formed
end ProbeCode
end

section
universe u
variable {S : Type u}
namespace Converts
theorem lam {l : Label} {A A' b b' : Expr S} (hA : Converts A A') (hb : Converts b b') :
    Converts (.lam l A b) (.lam l A' b') := by
  obtain ⟨D,hD,hD'⟩ := hA.join
  obtain ⟨E,hE,hE'⟩ := hb.join
  exact .trans _ _ _ (hD.lam hE).converts (.symm _ _ (hD'.lam hE').converts)
end Converts
namespace PositiveDataWrapper
theorem inject_converts (R : PositiveDataWrapper S) {a b : Expr S} (h : Converts a b) :
    Converts (R.inject a) (R.inject b) := by
  induction R with
  | identity => exact h
  | step R D e ih => exact .lam (.refl _) (ih.rename Nat.succ)
end PositiveDataWrapper
namespace DataTail
theorem send_converts (R : DataTail S) {A B : Expr S} (h : Converts A B) :
    Converts (R.send A) (R.send B) := R.positive.inject_converts (R.encode.apply_converts h)
end DataTail
namespace DataWrapper
theorem congr_build_observe {b} (R : DataWrapper S b) :
    (∀ {T T' a a'}, Converts T T' → Converts a a' → Converts (R.build T a) (R.build T' a')) ∧
    (∀ {T T' w w' a a'}, Converts T T' → Converts w w' → Converts a a' →
      Converts (R.observe T w a) (R.observe T' w' a')) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
    cases R with
    | identity =>
      constructor
      · intro T T' a a' hT ha; simpa only [build] using ha
      · intro T T' w w' a a' hT hw ha
        simp only [observe]
        exact .trans _ _ _ (ha.subst (Expr.single w)) (hw.instantiate_right a')
    | positive R D e =>
      have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
      constructor
      · intro T T' a a' hT ha
        simp only [build]
        exact .lam (.refl _) ((ih.1 hT ha).rename Nat.succ)
      · intro T T' w w' a a' hT hw ha
        simp only [observe]
        exact ih.2 hT (.app hw (.refl _)) ha
    | @negative b R U =>
      have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
      have ih' := rec R.depth (by simp only [← he,depth]; omega)
        (R.rename Nat.succ) (R.depth_rename Nat.succ)
      constructor
      · intro T T' a a' hT ha
        simp only [build]
        exact .lam (R.apply_converts hT) ((U.rename Nat.succ).send_converts
          (ih'.2 (hT.rename Nat.succ) (.refl _) (ha.rename (argRen (!b) Nat.succ))))
      · intro T T' w w' a a' hT hw ha
        simp only [observe]
        exact U.read_converts (.app hw (ih.1 hT ha))
theorem build_congr {b} (R : DataWrapper S b) {T T' a a' : Expr S}
    (hT : Converts T T') (ha : Converts a a') : Converts (R.build T a) (R.build T' a') :=
  R.congr_build_observe.1 hT ha
theorem observe_congr {b} (R : DataWrapper S b) {T T' w w' a a' : Expr S}
    (hT : Converts T T') (hw : Converts w w') (ha : Converts a a') :
    Converts (R.observe T w a) (R.observe T' w' a') := R.congr_build_observe.2 hT hw ha
end DataWrapper
namespace ProbeCode
theorem singleType_converts (R : ProbeCode S) {A B : Expr S} (h : Converts A B) :
    Converts (R.singleType A) (R.singleType B) :=
  R.doubled.carrier_converts (R.doubled.paramType_converts
    (R.raw.apply_converts (R.initial.apply_converts h)))
end ProbeCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ProbeCode
variable (R : ProbeCode S)
/-- Uniform V constructor. Q binds w:Single(z-down), then z:Z. -/
def uniform (Q : Expr S) : Expr S := .lam .dd R.domain
  ((R.rename Nat.succ).wrappedBuild ((R.lifting.rename Nat.succ).project (.var 0)) Q)

theorem uniform_specialize (A Q : Expr S) :
    Converts (R.specialize A (R.uniform Q))
      (R.wrappedBuild (R.lifting.project (R.lifting.inject A))
        (Q.subst (Expr.liftSub (Expr.single (R.lifting.inject A))))) := by
  have hh : Converts (R.specialize A (R.uniform Q))
      (((R.rename Nat.succ).wrappedBuild ((R.lifting.rename Nat.succ).project (.var 0)) Q).instantiate
        (R.lifting.inject A)) := .rel _ _ (Beta.head .dd _ _ _)
  simpa only [Expr.instantiate,wrappedBuild_subst,instantiate_raise,
    PositiveDataWrapper.project_subst,PositiveDataWrapper.instantiate_raise,Expr.subst,Expr.single] using hh

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C} {I J k p n g : Set S}
namespace Formed
variable {R} (h : R.Formed L I J k p n g)
include h
 theorem project_typed {z : Expr S} (hz : HasType P Γ z R.domain) :
    HasType P Γ (R.lifting.project z) (.sort R.seed) := (h.lifting.typed h.seed_sorted).2 _ hz
 theorem project_mode {z : Expr S} (mz : WellModed γ z .data) :
    WellModed γ (R.lifting.project z) .data := h.lifting.modes.2.2 _ mz
 theorem raised_project {s : S} (hs : HasType P Γ R.domain (.sort s)) :
    HasType P (R.domain :: Γ) ((R.lifting.rename Nat.succ).project (.var 0)) (.sort R.seed) := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  apply (h.rename e).project_typed
  simpa only [domain,PositiveDataWrapper.apply_rename,Expr.rename,ProbeCode.rename,e,Embedding.cons] using HasType.var hs
 theorem uniform_typed {Q : Expr S} {s : S} (hs : HasType P Γ R.domain (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Family
      ((R.rename Nat.succ).singleType ((R.lifting.rename Nat.succ).project (.var 0))) Q) :
    HasType P Γ (R.uniform Q) R.carrier ∧ WellModed γ (R.uniform Q) .data := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := h.rename e
  have hb := hh.wrappedBuild_typed (h.raised_project hs)
    (hh.project_mode (WellModed.var 0)) hQ
  obtain ⟨r,hr⟩ := h.mainTriple.product.1
  exact ⟨HasType.abstraction hb.1 (h.carrier_sorted r hr),.lam h.domain_mode hb.2⟩

 theorem uniform_evaluation {A Q w : Expr S}
    (ha : HasType P Γ A (.sort R.seed)) (ma : WellModed γ A .data)
    (hv : HasType P Γ (R.uniform Q) R.carrier) (mv : WellModed γ (R.uniform Q) .data)
    (hQ : L.Family (R.singleType (R.lifting.project (R.lifting.inject A)))
      (Q.subst (Expr.liftSub (Expr.single (R.lifting.inject A)))))
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    Equivalent P Γ γ (R.observe A (R.uniform Q) w)
      ((Q.subst (Expr.liftSub (Expr.single (R.lifting.inject A)))).instantiate w) := by
  let A' := R.lifting.project (R.lifting.inject A)
  let Q' := Q.subst (Expr.liftSub (Expr.single (R.lifting.inject A)))
  have ha' : HasType P Γ A' (.sort R.seed) := h.project_typed ((h.lifting.typed h.seed_sorted).1 _ ha)
  have ma' : WellModed γ A' .data := h.project_mode (h.lifting.modes.2.1 _ ma)
  have hc : Converts A' A := (R.lifting.cancel A).converts
  obtain ⟨s,hs⟩ := h.funTriple.domain.1
  have hw' : HasType P Γ w (R.singleType A') :=
    hw.conversion (h.single_sorted ha' s hs) (.symm _ _ (R.singleType_converts hc))
  have hobs := h.observe_formula ha ma hv mv hw mw
  have ht := h.wrappedBuild_typed ha' ma' hQ
  have hread := h.readBody_family ha' hw' mw
  have hobs' := (h.funPath.sound (h.fun_sorted ha') (h.fun_mode ma')).2 _ _ ht.1 ht.2 hread
  have hconv : Converts (R.observe A (R.uniform Q) w)
      (R.funPath.observe (R.funType A') (R.wrappedBuild A' Q') (R.readBody w)) :=
    R.funPath.observe_congr (R.funType_converts (.symm _ _ hc))
      (R.uniform_specialize A Q) (.refl _)
  obtain ⟨t,ht⟩ := L.triple.codomain.1
  exact (Equivalent.of_conversion (hobs.1 t ht) (hobs'.1 t ht) hconv).trans
    (h.wrappedBuild_evaluation ha' ma' hQ hw' mw)
    (hobs.1 t ht) (hobs'.1 t ht) ((hQ.instantiate hw' mw).1 t ht)
end Formed
end ProbeCode
end PureTypeSystem.Labelled

end OAI
