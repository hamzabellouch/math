import Mathlib

namespace OAI

namespace MatchingFPRAS.RealGeometry

variable {V E : Type*}

abbrev Vertex (V E : Type*) (m : ℕ) := V ⊕ (E × Fin m)

def atVertex (u v : E → V) (m : ℕ) (e : E) (i : Fin (m+2)) : Vertex V E m :=
  if h0 : i.val=0 then Sum.inl (u e)
  else if h1 : i.val=m+1 then Sum.inl (v e)
  else Sum.inr (e,⟨i.val-1,by omega⟩)

@[simp] lemma atVertex_zero (u v : E → V) (m : ℕ) (e : E) :
    atVertex u v m e 0 = Sum.inl (u e) := by simp [atVertex]

@[simp] lemma atVertex_last (u v : E → V) (m : ℕ) (e : E) :
    atVertex u v m e (Fin.last (m+1)) = Sum.inl (v e) := by simp [atVertex]

@[simp] lemma atVertex_internal (u v : E → V) (m : ℕ) (e : E) (i : Fin m) :
    atVertex u v m e i.succ.castSucc = Sum.inr (e,i) := by
  simp only [atVertex,Fin.val_castSucc,Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,
    and_false,↓reduceDIte]
  rw [dite_eq_right (by have := i.isLt; omega)]
  rfl

lemma atVertex_eq_inr_iff (u v : E → V) (m : ℕ) (e f : E)
    (i : Fin (m+2)) (j : Fin m) :
    atVertex u v m e i = Sum.inr (f,j) ↔ e=f ∧ i.val=j.val+1 := by
  unfold atVertex
  split_ifs with h0 h1
  · simp only [false_iff,not_and]
    intro h
    have := j.isLt
    omega
  · simp only [false_iff,not_and]
    intro h
    have := j.isLt
    omega
  · simp only [Sum.inr.injEq,Prod.mk.injEq,Fin.ext_iff]
    constructor
    · rintro ⟨rfl,h⟩; exact ⟨rfl,by omega⟩
    · rintro ⟨rfl,h⟩; exact ⟨rfl,by omega⟩

lemma atVertex_eq_inl_iff (u v : E → V) (m : ℕ) (e : E)
    (i : Fin (m+2)) (x : V) :
    atVertex u v m e i = Sum.inl x ↔
      (i.val=0 ∧ u e=x) ∨ (i.val=m+1 ∧ v e=x) := by
  unfold atVertex
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · simp [h0,h1]

theorem atVertex_injective (u v : E → V) (m : ℕ) (e : E) (huv : u e ≠ v e) :
    Function.Injective (atVertex u v m e) := by
  intro i j h
  by_cases hi0 : i.val=0
  · have he : atVertex u v m e i = Sum.inl (u e) := by simp [atVertex,hi0]
    have hj := (atVertex_eq_inl_iff u v m e j (u e)).mp (h.symm.trans he)
    rcases hj with hj | hj
    · apply Fin.ext; omega
    · exact False.elim (huv hj.2.symm)
  · by_cases hi1 : i.val=m+1
    · have he : atVertex u v m e i = Sum.inl (v e) := by simp [atVertex,hi1]
      have hj := (atVertex_eq_inl_iff u v m e j (v e)).mp (h.symm.trans he)
      rcases hj with hj | hj
      · exact False.elim (huv hj.2)
      · apply Fin.ext; omega
    · let k : Fin m := ⟨i.val-1,by omega⟩
      have he : atVertex u v m e i = Sum.inr (e,k) := by simp [atVertex,hi0,hi1,k]
      have hj := (atVertex_eq_inr_iff u v m e e j k).mp (h.symm.trans he)
      apply Fin.ext
      dsimp [k] at hj
      omega

theorem internal_private (u v : E → V) (m : ℕ) (e f : E) (i : Fin m)
    (j : Fin (m+2)) :
    atVertex u v m e i.succ.castSucc = atVertex u v m f j ↔
      e=f ∧ i.val+1=j.val := by
  rw [atVertex_internal,eq_comm,atVertex_eq_inr_iff]
  exact and_congr eq_comm eq_comm

def edge (u v : E → V) (m : ℕ) (e : E) (i : Fin (m+1)) : Sym2 (Vertex V E m) :=
  s(atVertex u v m e i.castSucc,atVertex u v m e i.succ)

lemma first_vertex_terminal (u v : E → V) (m : ℕ) (e : E)
    (i : Fin (m+1)) (x : V) :
    atVertex u v m e i.castSucc = Sum.inl x ↔ i.val=0 ∧ u e=x := by
  rw [atVertex_eq_inl_iff]
  have h : i.val ≠ m+1 := by omega
  simp [h]

lemma second_vertex_terminal (u v : E → V) (m : ℕ) (e : E)
    (i : Fin (m+1)) (x : V) :
    atVertex u v m e i.succ = Sum.inl x ↔ i.val=m ∧ v e=x := by
  rw [atVertex_eq_inl_iff]
  simp only [Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,and_false,false_and,false_or,
    Nat.add_right_cancel_iff]

lemma edge_ordered_injective (u v : E → V) (m : ℕ) (hm : 1 ≤ m)
    (e f : E) (i j : Fin (m+1))
    (h0 : atVertex u v m e i.castSucc = atVertex u v m f j.castSucc)
    (h1 : atVertex u v m e i.succ = atVertex u v m f j.succ) : e=f ∧ i=j := by
  by_cases hi : i.val=0
  · have hz : atVertex u v m e i.castSucc = Sum.inl (u e) := by
      apply (first_vertex_terminal _ _ _ _ _ _).mpr; exact ⟨hi,rfl⟩
    have hj : j.val=0 := ((first_vertex_terminal _ _ _ _ _ _).mp (h0.symm.trans hz)).1
    let k : Fin m := ⟨0,by omega⟩
    have hki : i.succ = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    have hkj : j.succ = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki,hkj,atVertex_internal,atVertex_internal] at h1
    have hef : e=f := congrArg Prod.fst (Sum.inr.inj h1)
    exact ⟨hef,Fin.ext (by omega)⟩
  · let k : Fin m := ⟨i.val-1,by omega⟩
    have hki : i.castSucc = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki] at h0
    have hh := (internal_private u v m e f k j.castSucc).mp h0
    refine ⟨hh.1,Fin.ext ?_⟩
    dsimp [k] at hh
    omega

lemma edge_ordered_not_reverse (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (e f : E) (i j : Fin (m+1)) :
    ¬ (atVertex u v m e i.castSucc = atVertex u v m f j.succ ∧
      atVertex u v m e i.succ = atVertex u v m f j.castSucc) := by
  rintro ⟨h0,h1⟩
  by_cases hi : i.val=0
  · have hz : atVertex u v m e i.castSucc = Sum.inl (u e) := by
      apply (first_vertex_terminal _ _ _ _ _ _).mpr; exact ⟨hi,rfl⟩
    have hj : j.val=m := ((second_vertex_terminal _ _ _ _ _ _).mp (h0.symm.trans hz)).1
    let k : Fin m := ⟨0,by omega⟩
    have hki : i.succ = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki] at h1
    have hh := (internal_private u v m e f k j.castSucc).mp h1
    dsimp [k] at hh
    omega
  · let k : Fin m := ⟨i.val-1,by omega⟩
    have hki : i.castSucc = k.succ.castSucc := by apply Fin.ext; simp only [Fin.val_succ,Fin.val_castSucc]; dsimp only [k]; omega
    rw [hki] at h0
    have hh := (internal_private u v m e f k j.succ).mp h0
    have hij : i.val=j.val+1 := by dsimp [k] at hh; omega
    by_cases him : i.val=m
    · have hz : atVertex u v m e i.succ = Sum.inl (v e) := by
        apply (second_vertex_terminal _ _ _ _ _ _).mpr; exact ⟨him,rfl⟩
      have hj : j.val=0 := ((first_vertex_terminal _ _ _ _ _ _).mp (h1.symm.trans hz)).1
      omega
    · let l : Fin m := ⟨i.val,by omega⟩
      have hli : i.succ = l.succ.castSucc := rfl
      rw [hli] at h1
      have hh' := (internal_private u v m e f l j.castSucc).mp h1
      dsimp [l] at hh'
      omega

theorem edge_injective (u v : E → V) (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (fun q : E × Fin (m+1) => edge u v m q.1 q.2) := by
  rintro ⟨e,i⟩ ⟨f,j⟩ h
  have he := Sym2.eq_iff.mp h
  rcases he with h | h
  · have hh := edge_ordered_injective u v m (by omega) e f i j h.1 h.2
    exact Prod.ext hh.1 hh.2
  · exact False.elim (edge_ordered_not_reverse u v m hm e f i j h)

noncomputable def activity [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m) : ℝ := by
  classical
  exact ∑ q : E × Fin (m+1), if edge u v m q.1 q.2 = s(x,y) then t q.1 q.2 else 0

lemma activity_symm [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m) :
    activity u v m t x y = activity u v m t y x := by
  classical
  simp only [activity,Sym2.eq_swap]

lemma activity_nonneg [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (ht : ∀ e i, 0 ≤ t e i) (x y : Vertex V E m) :
    0 ≤ activity u v m t x y := by
  classical
  unfold activity
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> simp [ht]

theorem activity_on_edge [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (e : E) (i : Fin (m+1)) :
    activity u v m t (atVertex u v m e i.castSucc) (atVertex u v m e i.succ) = t e i := by
  classical
  unfold activity
  rw [Finset.sum_eq_single (e,i)]
  · simp [edge]
  · intro q hq hne
    have hnot : edge u v m q.1 q.2 ≠ edge u v m e i := by
      intro he
      exact hne (edge_injective u v m hm he)
    exact ite_eq_right hnot
  · simp

lemma activity_eq_zero_of_not_edge [Fintype E] (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m)
    (h : ∀ e i, edge u v m e i ≠ s(x,y)) : activity u v m t x y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q hq
  exact ite_eq_right (h q.1 q.2)

theorem activity_eq_edge_or_zero [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (x y : Vertex V E m) :
    activity u v m t x y = 0 ∨
      ∃ e i, edge u v m e i = s(x,y) ∧ activity u v m t x y = t e i := by
  classical
  by_cases hex : ∃ e i, edge u v m e i = s(x,y)
  · obtain ⟨e,i,he⟩ := hex
    refine Or.inr ⟨e,i,he,?_⟩
    rcases Sym2.eq_iff.mp he with he | he
    · rw [← he.1,← he.2]
      exact activity_on_edge u v m hm t e i
    · rw [← he.2,← he.1,activity_symm]
      exact activity_on_edge u v m hm t e i
  · left
    exact activity_eq_zero_of_not_edge u v m t x y (by simpa only [not_exists] using hex)

theorem internal_incident_iff (u v : E → V) (m : ℕ) (e f : E)
    (i : Fin (m+1)) (j : Fin m) :
    Sum.inr (f,j) ∈ edge u v m e i ↔
      e=f ∧ (i.val=j.val ∨ i.val=j.val+1) := by
  rw [edge,Sym2.mem_iff]
  simp only [eq_comm (a := Sum.inr (f,j)),atVertex_eq_inr_iff,Fin.val_castSucc,Fin.val_succ]
  constructor
  · rintro (⟨he,hi⟩ | ⟨he,hi⟩)
    · exact ⟨he,Or.inr hi⟩
    · exact ⟨he,Or.inl (by omega)⟩
  · rintro ⟨he,hi | hi⟩
    · exact Or.inr ⟨he,by omega⟩
    · exact Or.inl ⟨he,hi⟩

theorem internal_activity_le [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (e : E) (j : Fin m) (T : ℝ) (hT : 0 ≤ T)
    (hleft : t e j.castSucc ≤ T) (hright : t e j.succ ≤ T) (y : Vertex V E m) :
    activity u v m t (Sum.inr (e,j)) y ≤ T := by
  rcases activity_eq_edge_or_zero u v m hm t (Sum.inr (e,j)) y with hzero | ⟨f,i,he,hw⟩
  · simpa [hzero] using hT
  · have hin : Sum.inr (e,j) ∈ edge u v m f i := by rw [he]; exact Sym2.mem_mk_left _ _
    obtain ⟨rfl,hi | hi⟩ := (internal_incident_iff u v m f e i j).mp hin
    · have hij : i=j.castSucc := Fin.ext hi
      simpa [hw,hij] using hleft
    · have hij : i=j.succ := Fin.ext hi
      simpa [hw,hij] using hright

lemma edge_not_diag (u v : E → V) (m : ℕ) (e : E) (hue : u e ≠ v e)
    (i : Fin (m+1)) : ¬ (edge u v m e i).IsDiag := by
  rw [edge,Sym2.mk_isDiag_iff]
  intro h
  have he := atVertex_injective u v m e hue h
  have hv := congrArg Fin.val he
  simp only [Fin.val_succ,Fin.val_castSucc] at hv
  omega

def realThreshold (u v : E → V) (m : ℕ) (t : E → Fin (m+1) → ℝ)
    (τ : ℝ) : SimpleGraph (Vertex V E m) where
  Adj a b := a ≠ b ∧ ∃ e i, edge u v m e i = s(a,b) ∧ τ ≤ t e i
  symm := ⟨by rintro a b ⟨hne,e,i,he,ht⟩; exact ⟨hne.symm,e,i,by simpa only [Sym2.eq_swap] using he,ht⟩⟩
  loopless := ⟨by rintro a ⟨hne,_⟩; exact hne rfl⟩

def logicalThreshold (u v : E → V) (lam : E → ℝ) (τ : ℝ) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ e, s(u e,v e)=s(a,b) ∧ τ ≤ lam e
  symm := ⟨by rintro a b ⟨hne,e,he,ht⟩; exact ⟨hne.symm,e,by simpa only [Sym2.eq_swap] using he,ht⟩⟩
  loopless := ⟨by rintro a ⟨hne,_⟩; exact hne rfl⟩

def contract (u v : E → V) (m : ℕ) (c : Fin (m+1)) : Vertex V E m → V
  | Sum.inl a => a
  | Sum.inr (e,j) => if j.val < c.val then u e else v e

@[simp] lemma contract_terminal (u v : E → V) (m : ℕ) (c : Fin (m+1)) (a : V) :
    contract u v m c (Sum.inl a) = a := rfl

lemma contract_atVertex (u v : E → V) (m : ℕ) (c : Fin (m+1)) (e : E)
    (i : Fin (m+2)) : contract u v m c (atVertex u v m e i) =
      if i.val ≤ c.val then u e else v e := by
  by_cases h0 : i.val=0
  · simp [atVertex,h0,contract]
  by_cases hlast : i.val=m+1
  · have hn : ¬ i.val ≤ c.val := by omega
    simp only [atVertex,dite_eq_right h0,dite_eq_left hlast,contract,ite_eq_right hn]
  · have he : i.val-1 < c.val ↔ i.val ≤ c.val := by omega
    simp [atVertex,h0,hlast,contract,he]

lemma contracted_edge (u v : E → V) (m : ℕ) (c : Fin (m+1)) (e : E)
    (i : Fin (m+1)) :
    contract u v m c (atVertex u v m e i.castSucc) =
      contract u v m c (atVertex u v m e i.succ) ∨
    (i=c ∧ contract u v m c (atVertex u v m e i.castSucc)=u e ∧
      contract u v m c (atVertex u v m e i.succ)=v e) := by
  rw [contract_atVertex,contract_atVertex]
  simp only [Fin.val_castSucc,Fin.val_succ]
  by_cases hi : i.val < c.val
  · left; simp [show i.val ≤ c.val by omega,show i.val+1 ≤ c.val by omega]
  by_cases hi' : c.val < i.val
  · left; simp [show ¬ i.val ≤ c.val by omega,show ¬ i.val+1 ≤ c.val by omega]
  · have hic : i=c := Fin.ext (by omega)
    right; subst i; simp

lemma reachable_of_edge_reachable {W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ a b, G.Adj a b → H.Reachable (f a) (f b))
    {a b : V} (h : G.Reachable a b) : H.Reachable (f a) (f b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h he ih =>
    exact ih.trans ((SimpleGraph.reachable_iff_reflTransGen _ _).mp (hf _ _ he))

theorem threshold_contract (u v : E → V) (m : ℕ) (c : Fin (m+1))
    (lam : E → ℝ) (t : E → Fin (m+1) → ℝ) (hc : ∀ e, t e c=lam e)
    (τ : ℝ) {a b : Vertex V E m} (h : (realThreshold u v m t τ).Reachable a b) :
    (logicalThreshold u v lam τ).Reachable (contract u v m c a) (contract u v m c b) := by
  apply reachable_of_edge_reachable (realThreshold u v m t τ)
    (logicalThreshold u v lam τ) (contract u v m c) _ h
  rintro a b ⟨hab,e,i,he,ht⟩
  rcases Sym2.eq_iff.mp he with he | he
  · rw [← he.1,← he.2]
    rcases contracted_edge u v m c e i with heq | ⟨rfl,hleft,hright⟩
    · rw [heq]
    · rw [hleft,hright]
      by_cases huv : u e=v e
      · rw [huv]
      · exact SimpleGraph.Adj.reachable ⟨huv,e,rfl,by simpa [hc e] using ht⟩
  · rw [← he.2,← he.1]
    apply SimpleGraph.Reachable.symm
    rcases contracted_edge u v m c e i with heq | ⟨rfl,hleft,hright⟩
    · rw [heq]
    · rw [hleft,hright]
      by_cases huv : u e=v e
      · rw [huv]
      · exact SimpleGraph.Adj.reachable ⟨huv,e,rfl,by simpa [hc e] using ht⟩

lemma positions_reachable (G : SimpleGraph V) (m : ℕ) (f : Fin (m+2) → V)
    (hf : ∀ i : Fin (m+1), G.Reachable (f i.castSucc) (f i.succ))
    (i : Fin (m+2)) : G.Reachable (f 0) (f i) := by
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ i ih =>
    have hi' : i < m+2 := by omega
    have hi'' : i < m+1 := by omega
    exact (ih hi').trans (hf ⟨i,hi''⟩)

theorem threshold_lift_edge (u v : E → V) (m : ℕ) (lam : E → ℝ)
    (t : E → Fin (m+1) → ℝ) (hm : ∀ e i, lam e ≤ t e i)
    (τ : ℝ) (e : E) (he : τ ≤ lam e) :
    (realThreshold u v m t τ).Reachable (Sum.inl (u e)) (Sum.inl (v e)) := by
  have h := positions_reachable (realThreshold u v m t τ) m (atVertex u v m e)
    (fun i => ?_) (Fin.last (m+1))
  · simpa using h
  by_cases hn : atVertex u v m e i.castSucc = atVertex u v m e i.succ
  · rw [hn]
  · exact SimpleGraph.Adj.reachable ⟨hn,e,i,rfl,he.trans (hm e i)⟩

theorem terminal_threshold_iff (u v : E → V) (m : ℕ) (c : Fin (m+1))
    (lam : E → ℝ) (t : E → Fin (m+1) → ℝ) (hc : ∀ e, t e c=lam e)
    (hm : ∀ e i, lam e ≤ t e i) (τ : ℝ) (a b : V) :
    (realThreshold u v m t τ).Reachable (Sum.inl a) (Sum.inl b) ↔
      (logicalThreshold u v lam τ).Reachable a b := by
  constructor
  · exact threshold_contract u v m c lam t hc τ
  · apply reachable_of_edge_reachable (logicalThreshold u v lam τ)
      (realThreshold u v m t τ) Sum.inl
    rintro a b ⟨hne,e,he,ht⟩
    rcases Sym2.eq_iff.mp he with he | he
    · rw [← he.1,← he.2]; exact threshold_lift_edge u v m lam t hm τ e ht
    · rw [← he.2,← he.1]; exact (threshold_lift_edge u v m lam t hm τ e ht).symm

lemma activity_on_eq [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (e : E) (i : Fin (m+1)) (a b : Vertex V E m)
    (he : edge u v m e i=s(a,b)) : activity u v m t a b=t e i := by
  rcases Sym2.eq_iff.mp he with he | he
  · rw [← he.1,← he.2]; exact activity_on_edge u v m hm t e i
  · rw [← he.2,← he.1,activity_symm]; exact activity_on_edge u v m hm t e i

theorem realThreshold_adj_iff [Fintype E] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (τ : ℝ) (hτ : 0 < τ) (a b : Vertex V E m) :
    (realThreshold u v m t τ).Adj a b ↔ a ≠ b ∧ τ ≤ activity u v m t a b := by
  constructor
  · rintro ⟨hne,e,i,he,ht⟩
    exact ⟨hne,by rwa [activity_on_eq u v m hm t e i a b he]⟩
  · rintro ⟨hne,ht⟩
    rcases activity_eq_edge_or_zero u v m hm t a b with hzero | ⟨e,i,he,hw⟩
    · rw [hzero] at ht; exact False.elim (not_le_of_gt hτ ht)
    · exact ⟨hne,e,i,he,by rwa [hw] at ht⟩

theorem path_interval_reachable (u v : E → V) (m : ℕ)
    (t : E → Fin (m+1) → ℝ) (τ : ℝ) (e : E)
    (i j : Fin (m+2)) (hij : i.val ≤ j.val)
    (ht : ∀ k : Fin (m+1), i.val ≤ k.val → k.val < j.val → τ ≤ t e k) :
    (realThreshold u v m t τ).Reachable (atVertex u v m e i) (atVertex u v m e j) := by
  have aux : ∀ (k : ℕ) (hk : k < m+2), i.val ≤ k →
      (∀ q : Fin (m+1), i.val ≤ q.val → q.val < k → τ ≤ t e q) →
      (realThreshold u v m t τ).Reachable (atVertex u v m e i)
        (atVertex u v m e ⟨k,hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk hik hq
      have he : i=⟨0,hk⟩ := Fin.ext (by change i.val = 0; omega)
      rw [he]
    | succ k ih =>
      intro hk hik hq
      by_cases he : i.val=k+1
      · have hei : i=⟨k+1,hk⟩ := Fin.ext he
        rw [hei]
      have hki : i.val ≤ k := by omega
      have hk' : k < m+2 := by omega
      have hk'' : k < m+1 := by omega
      have hprior := ih hk' hki (fun q hiq hqk => hq q hiq (by omega))
      apply hprior.trans
      by_cases hn : atVertex u v m e ⟨k,hk'⟩ = atVertex u v m e ⟨k+1,hk⟩
      · rw [hn]
      · exact SimpleGraph.Adj.reachable ⟨hn,e,⟨k,hk''⟩,rfl,hq ⟨k,hk''⟩ hki (Nat.lt_succ_self k)⟩
  exact aux j.val j.isLt hij ht

end MatchingFPRAS.RealGeometry

end OAI
