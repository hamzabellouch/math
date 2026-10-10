import OAI.Combinatorics.ParityLifts.ParameterBounds

namespace OAI

namespace ParityWL.Complexity

abbrev RawRole := ℕ × ℕ × ℕ

def RoleValid (t : ℕ) (r : RawRole) : Prop :=
  r.1<t ∧ r.2.1<t ∧ r.2.2<t ∧
    ((r.1=r.2.1 ∧ r.2.2=r.1) ∨
      (r.1<r.2.1 ∧ r.2.2≠r.1 ∧ r.2.2≠r.2.1))

instance (t : ℕ) (r : RawRole) : Decidable (RoleValid t r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def rawRole {t : ℕ} : TemplateVertex t → RawRole
  | .inl i => (i.val,i.val,i.val)
  | .inr h => (h.1.1.1.1.val,h.1.1.1.2.val,h.1.2.val)

lemma rawRole_valid {t : ℕ} (a : TemplateVertex t) : RoleValid t (rawRole a) := by
  cases a with
  | inl i => exact ⟨i.isLt,i.isLt,i.isLt,Or.inl ⟨rfl,rfl⟩⟩
  | inr h =>
    exact ⟨h.1.1.1.1.isLt,h.1.1.1.2.isLt,h.1.2.isLt,Or.inr ⟨h.1.1.2,
      (fun e => h.2.1 (Fin.ext e)),fun e => h.2.2 (Fin.ext e)⟩⟩

def roleDecode {t : ℕ} (r : {r : RawRole // RoleValid t r}) : TemplateVertex t :=
  if h : r.val.1=r.val.2.1 then .inl ⟨r.val.1,r.property.1⟩
  else .inr ⟨(⟨(⟨r.val.1,r.property.1⟩,⟨r.val.2.1,r.property.2.1⟩),by
    rcases r.property.2.2.2 with hh | hh
    · exact False.elim (h hh.1)
    · exact hh.1⟩,⟨r.val.2.2,r.property.2.2.1⟩),by
      rcases r.property.2.2.2 with hh | hh
      · exact False.elim (h hh.1)
      · exact ⟨fun e => hh.2.1 (congrArg Fin.val e),fun e => hh.2.2 (congrArg Fin.val e)⟩⟩

@[simp] lemma roleDecode_rawRole {t : ℕ} (a : TemplateVertex t) :
    roleDecode ⟨rawRole a,rawRole_valid a⟩=a := by
  cases a with
  | inl i => simp [roleDecode,rawRole]
  | inr h => simp [roleDecode,rawRole,ne_of_lt (show h.1.1.1.1.val<h.1.1.1.2.val from h.1.1.2)]

@[simp] lemma rawRole_roleDecode {t : ℕ} (r : {r : RawRole // RoleValid t r}) :
    rawRole (roleDecode r)=r.val := by
  unfold roleDecode
  split
  · rename_i he
    simp only [rawRole]
    rcases r.property.2.2.2 with hh | hh
    · exact Prod.ext rfl (Prod.ext hh.1 hh.2.symm)
    · exact False.elim ((ne_of_lt hh.1) he)
  · rfl

def roleEquiv (t : ℕ) : TemplateVertex t ≃ {r : RawRole // RoleValid t r} where
  toFun a := ⟨rawRole a,rawRole_valid a⟩
  invFun := roleDecode
  left_inv := roleDecode_rawRole
  right_inv r := Subtype.ext (rawRole_roleDecode r)

lemma rawRole_injective (t : ℕ) : Function.Injective (@rawRole t) := by
  intro a b he
  apply (roleEquiv t).injective
  exact Subtype.ext he

def allRoles (t : ℕ) : List RawRole :=
  ((List.range t).product ((List.range t).product (List.range t))).filter (fun r => decide (RoleValid t r))

@[simp] lemma mem_allRoles (t : ℕ) (r : RawRole) : r∈allRoles t ↔ RoleValid t r := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    apply List.mem_filter.mpr
    refine ⟨?_,decide_eq_true h⟩
    exact List.mem_product.mpr ⟨List.mem_range.mpr h.1,
      List.mem_product.mpr ⟨List.mem_range.mpr h.2.1,List.mem_range.mpr h.2.2.1⟩⟩

lemma allRoles_nodup (t : ℕ) : (allRoles t).Nodup := by
  apply List.Nodup.filter
  exact List.nodup_range.product (List.nodup_range.product List.nodup_range)

def rawAdjacent (a b : RawRole) : Bool :=
  if a.1=a.2.1 then
    if b.1=b.2.1 then decide (a.1≠b.1)
    else decide (a.1=b.1 ∨ a.1=b.2.1 ∨ a.1=b.2.2)
  else if b.1=b.2.1 then decide (b.1=a.1 ∨ b.1=a.2.1 ∨ b.1=a.2.2)
  else false

lemma rawAdjacent_iff {t : ℕ} (a b : TemplateVertex t) :
    rawAdjacent (rawRole a) (rawRole b)=true ↔ (template t).Adj a b := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      dsimp only [rawAdjacent,rawRole,template,templateAdj]
      simp only [ite_true,decide_eq_true_eq,ne_eq,Fin.val_inj]
    | inr h =>
      have hn : h.1.1.1.1.val≠h.1.1.1.2.val := ne_of_lt h.1.1.2
      dsimp only [rawAdjacent,rawRole,template,templateAdj,helperIncident]
      rw [ite_eq_right hn]
      simp only [ite_true,decide_eq_true_eq,Fin.val_inj]
  | inr h =>
    have hn : h.1.1.1.1.val≠h.1.1.1.2.val := ne_of_lt h.1.1.2
    cases b with
    | inl i =>
      dsimp only [rawAdjacent,rawRole,template,templateAdj,helperIncident]
      rw [ite_eq_right hn]
      simp only [ite_true,decide_eq_true_eq,Fin.val_inj]
    | inr g =>
      have gn : g.1.1.1.1.val≠g.1.1.1.2.val := ne_of_lt g.1.1.2
      dsimp only [rawAdjacent,rawRole,template,templateAdj]
      simp only [ite_eq_right hn,ite_eq_right gn,Bool.false_eq_true]

def rawNeighbors (t : ℕ) (a : RawRole) : List RawRole :=
  (allRoles t).filter (rawAdjacent a)

lemma mem_rawNeighbors (t : ℕ) (a b : RawRole) :
    b∈rawNeighbors t a ↔ RoleValid t b ∧ rawAdjacent a b=true := by
  simp [rawNeighbors]

lemma rawNeighbors_nodup (t : ℕ) (a : RawRole) : (rawNeighbors t a).Nodup :=
  (allRoles_nodup t).filter _

end ParityWL.Complexity

end OAI
