import Mathlib
import OAI.Combinatorics.Chromatic.Walls.Mass

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ)
noncomputable def slopeCross (d e : I → ℕ) : ℝ := mass η d*mass c e-mass c d*mass η e
@[simp] lemma slopeCross_zero_left (e : I → ℕ) : slopeCross c η 0 e=0 := by simp [slopeCross]
@[simp] lemma slopeCross_zero_right (d : I → ℕ) : slopeCross c η d 0=0 := by simp [slopeCross]
lemma slopeCross_add_left (d e b : I → ℕ) :
    slopeCross c η (d+e) b=slopeCross c η d b+slopeCross c η e b := by simp [slopeCross,mass_add]; ring
lemma slopeCross_add_right (d e b : I → ℕ) :
    slopeCross c η d (e+b)=slopeCross c η d e+slopeCross c η d b := by simp [slopeCross,mass_add]; ring
lemma slopeCross_eq (hc : ∀ i,0 < c i) (d e : I → ℕ) :
    slopeCross c η d e=(slope c η d-slope c η e)*(mass c d*mass c e) := by
  rw [slopeCross,mass_eq c η hc d,mass_eq c η hc e]
  ring
lemma slopeCross_pos_iff (hc : ∀ i,0 < c i) {d e : I → ℕ} (hd : d≠0) (he : e≠0) :
    0 < slopeCross c η d e ↔ slope c η e < slope c η d := by
  rw [slopeCross_eq c η hc,mul_pos_iff_of_pos_right (mul_pos (mass_pos c hc d hd) (mass_pos c hc e he)),sub_pos]
lemma slopeCross_nonpos_iff (hc : ∀ i,0 < c i) {d e : I → ℕ} (hd : d≠0) (he : e≠0) :
    slopeCross c η d e ≤ 0 ↔ slope c η d ≤ slope c η e := by
  rw [←not_lt, slopeCross_pos_iff c η hc hd he,not_lt]

noncomputable def polygonArea : List (I → ℕ) → ℝ
  | [] => 0
  | d::l => slopeCross c η d l.sum+polygonArea l
@[simp] lemma polygonArea_nil : polygonArea c η []=0 := rfl
@[simp] lemma polygonArea_cons (d : I → ℕ) (l : List (I → ℕ)) :
    polygonArea c η (d::l)=slopeCross c η d l.sum+polygonArea c η l := rfl
@[simp] lemma polygonArea_singleton (d : I → ℕ) : polygonArea c η [d]=0 := by simp
lemma slopeCross_list_sum (d : I → ℕ) (l : List (I → ℕ)) :
    slopeCross c η d l.sum=(l.map (slopeCross c η d)).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp [slopeCross_add_right,ih]
lemma polygonArea_append (l r : List (I → ℕ)) :
    polygonArea c η (l++r)=polygonArea c η l+polygonArea c η r+slopeCross c η l.sum r.sum := by
  induction l with
  | nil => simp
  | cons d l ih => simp [ih,slopeCross_add_right,slopeCross_add_left]; ring

def HNOrdered (l : List (I → ℕ)) : Prop :=
  (∀ d∈l,d≠0) ∧ l.Pairwise (fun d e=>slope c η e < slope c η d)

lemma polygonArea_nonneg (hc : ∀ i,0 < c i) {l : List (I → ℕ)} (hl : HNOrdered c η l) :
    0 ≤ polygonArea c η l := by
  induction l with
  | nil => exact le_refl 0
  | cons d l ih =>
    have hpair := List.pairwise_cons.mp hl.2
    have htail : HNOrdered c η l := ⟨fun e he=>hl.1 e (List.mem_cons_of_mem _ he),hpair.2⟩
    rw [polygonArea_cons,slopeCross_list_sum]
    apply add_nonneg _ (ih htail)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact ((slopeCross_pos_iff c η hc (hl.1 d (by simp)) (htail.1 e he)).mpr (hpair.1 e he)).le

lemma polygonArea_pos (hc : ∀ i,0 < c i) {l : List (I → ℕ)} (hl : HNOrdered c η l)
    (hlen : 2 ≤ l.length) : 0 < polygonArea c η l := by
  cases l with
  | nil => simp at hlen
  | cons d l =>
    cases l with
    | nil => simp at hlen
    | cons e l =>
      have hp := List.pairwise_cons.mp hl.2
      have ht : HNOrdered c η (e::l) := ⟨fun x hx=>hl.1 x (List.mem_cons_of_mem _ hx),hp.2⟩
      have hrest : 0 ≤ slopeCross c η d l.sum := by
        rw [slopeCross_list_sum]
        apply List.sum_nonneg
        intro x hx
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
        exact ((slopeCross_pos_iff c η hc (hl.1 d (by simp))
          (hl.1 y (by simp [hy]))).mpr (hp.1 y (by simp [hy]))).le
      have hde : 0 < slopeCross c η d e :=
        (slopeCross_pos_iff c η hc (hl.1 d (by simp)) (hl.1 e (by simp))).mpr (hp.1 e (by simp))
      simpa only [polygonArea_cons,List.sum_cons,slopeCross_add_right] using
        add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hde hrest) (polygonArea_nonneg c η hc ht)

lemma polygonArea_replace (l r q : List (I → ℕ)) (d e : I → ℕ) (hq : q.sum=d+e) :
    polygonArea c η (l++q++r)-polygonArea c η (l++[d,e]++r)=
      polygonArea c η q-slopeCross c η d e := by
  simp only [polygonArea_append,List.sum_append,hq,List.sum_cons,List.sum_nil,add_zero,
    polygonArea_cons,polygonArea_nil,slopeCross_zero_right]
  ring

lemma reorder_progress (hc : ∀ i,0 < c i) (l r q : List (I → ℕ)) {d e : I → ℕ}
    (hd : d≠0) (he : e≠0) (hde : slope c η d ≤ slope c η e)
    (hq : q.sum=d+e) (ho : HNOrdered c η q) :
    polygonArea c η (l++[d,e]++r) < polygonArea c η (l++q++r) ∨
    (polygonArea c η (l++[d,e]++r)=polygonArea c η (l++q++r) ∧
      (l++q++r).length < (l++[d,e]++r).length) := by
  have hdiff := polygonArea_replace c η l r q d e hq
  have hq₀ := polygonArea_nonneg c η hc ho
  have hde₀ := (slopeCross_nonpos_iff c η hc hd he).mpr hde
  by_cases hlt : polygonArea c η (l++[d,e]++r) < polygonArea c η (l++q++r)
  · exact Or.inl hlt
  right
  have heq : polygonArea c η (l++[d,e]++r)=polygonArea c η (l++q++r) := by linarith
  have hlen : q.length < 2 := by
    by_contra hh
    have := polygonArea_pos c η hc ho (by omega)
    linarith
  exact ⟨heq,by simp only [List.length_append,List.length_cons,List.length_nil]; omega⟩

end ElementaryPositivity.SlopeArithmetic

end
section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

abbrev HNComposition (d : I → ℕ) := {l : List (I → ℕ) // l.sum=d ∧ ∀ e∈l,e≠0}

def hnSize (d : I → ℕ) := ∑ i,d i
lemma hnSize_add (d e : I → ℕ) : hnSize (d+e)=hnSize d+hnSize e := Finset.sum_add_distrib
@[simp] lemma hnSize_zero : hnSize (0 : I → ℕ)=0 := by simp [hnSize]
lemma hnSize_eq_zero (d : I → ℕ) : hnSize d=0 ↔ d=0 := by
  simp only [hnSize,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies]
  exact ⟨fun h=>funext h,fun h i=>congrFun h i⟩
lemma hnSize_list_sum (l : List (I → ℕ)) : hnSize l.sum=(l.map hnSize).sum := by
  induction l with
  | nil => simp
  | cons d l ih => simp [hnSize_add,ih]
lemma HNComposition.length_le (d : I → ℕ) (l : HNComposition d) : l.val.length ≤ hnSize d := by
  have h := List.length_le_sum_of_one_le (l.val.map hnSize) (by
    intro n hn
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    have := (hnSize_eq_zero e).not.mpr (l.property.2 e he)
    omega)
  have h' : l.val.length ≤ (l.val.map hnSize).sum := by simpa only [List.length_map] using h
  exact h'.trans_eq ((hnSize_list_sum l.val).symm.trans (congrArg hnSize l.property.1))

instance (d : I → ℕ) : Finite (HNComposition d) := by
  classical
  let E := {e : I → ℕ // e ≤ d}
  let : Finite E := (Set.finite_Iic d).to_subtype
  have hs : {l : List (I → ℕ) | l.sum=d ∧ ∀ e∈l,e≠0}.Finite := by
    apply ((List.finite_length_le E (hnSize d)).image (List.map Subtype.val)).subset
    intro l hl
    let q : List E := l.attach.map (fun e=>⟨e.val,by
      have := List.le_sum_of_mem e.property
      simpa only [hl.1] using this⟩)
    refine ⟨q,?_,?_⟩
    · change q.length ≤ hnSize d
      simpa only [q,List.length_map,List.length_attach] using HNComposition.length_le d ⟨l,hl⟩
    · simp only [q,List.map_map]
      change l.attach.map (fun x=>x.val)=l
      simp
  exact hs.to_subtype

variable (c η : I → ℝ)

def HNBefore {d : I → ℕ} (l r : HNComposition d) : Prop :=
  polygonArea c η r.val < polygonArea c η l.val ∨
    (polygonArea c η r.val=polygonArea c η l.val ∧ l.val.length < r.val.length)

instance (d : I → ℕ) : IsStrictOrder (HNComposition d) (HNBefore c η) where
  irrefl l := by simp [HNBefore]
  trans l r s hl hr := by
    rcases hl with hl|⟨hl,hl'⟩ <;> rcases hr with hr|⟨hr,hr'⟩
    · exact Or.inl (lt_trans hr hl)
    · exact Or.inl (hr ▸ hl)
    · exact Or.inl (hl ▸ hr)
    · exact Or.inr ⟨hr.trans hl,lt_trans hl' hr'⟩

lemma hnBefore_wellFounded (d : I → ℕ) : WellFounded (HNBefore c η (d:=d)) :=
  Set.wellFoundedOn_univ.mp Set.finite_univ.wellFoundedOn

lemma not_hnOrdered_adjacent {l : List (I → ℕ)} (hn : ∀ d∈l,d≠0) (ho : ¬HNOrdered c η l) :
    ∃ p q d e,l=p++[d,e]++q ∧ slope c η d ≤ slope c η e := by
  have h : ¬l.IsChain (fun d e=>slope c η e<slope c η d) := by
    intro h
    exact ho ⟨hn,List.isChain_iff_pairwise.mp h⟩
  clear hn ho
  induction l with
  | nil => exact (h (by simp)).elim
  | cons d l ih =>
    cases l with
    | nil => exact (h (by simp)).elim
    | cons e l =>
      by_cases hde : slope c η e<slope c η d
      · obtain ⟨p,q,u,v,heq,huv⟩:=ih (by
          intro hh
          exact h (List.isChain_cons_cons.mpr ⟨hde,hh⟩))
        exact ⟨d::p,q,u,v,by simp only [List.cons_append,←heq],huv⟩
      · exact ⟨[],l,d,e,rfl,le_of_not_gt hde⟩

lemma hnSize_pair_lt (hc : ∀ i,0<c i) {p q : List (I → ℕ)} {d e : I → ℕ}
    (hn : ∀ b∈p++[d,e]++q,b≠0) (hde : slope c η d ≤ slope c η e)
    (ha : 0<polygonArea c η (p++[d,e]++q)) :
    hnSize (d+e)<hnSize (p++[d,e]++q).sum := by
  have hd : d≠0 := hn d (by simp)
  have he : e≠0 := hn e (by simp)
  have hpq : p≠[] ∨ q≠[] := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl,rfl⟩
    simp only [List.nil_append,List.append_nil,polygonArea_cons,List.sum_cons,List.sum_nil,
      add_zero,polygonArea_nil,slopeCross_zero_right] at ha
    exact (not_lt_of_ge ((slopeCross_nonpos_iff c η hc hd he).mpr hde)) (by simpa using ha)
  have hsz : 0<hnSize p.sum+hnSize q.sum := by
    rcases hpq with hp|hq
    · obtain ⟨b,l,rfl⟩:=List.exists_cons_of_ne_nil hp
      have hb := (hnSize_eq_zero b).not.mpr (hn b (by simp))
      simp only [List.sum_cons,hnSize_add]
      omega
    · obtain ⟨b,l,rfl⟩:=List.exists_cons_of_ne_nil hq
      have hb := (hnSize_eq_zero b).not.mpr (hn b (by simp))
      simp only [List.sum_cons,hnSize_add]
      omega
  simp only [List.sum_append,List.sum_cons,List.sum_nil,add_zero,hnSize_add]
  omega

lemma slopeCross_of_destabilizing (hc : ∀ i,0<c i) {d e : I → ℕ} (hd : d≠0)
    (h : slope c η (d+e)<slope c η d) : 0<slopeCross c η d e := by
  have hm := mass_pos c hc d hd
  have hm' := mass_pos c hc (d+e) (add_ne_zero_left d e hd)
  have h' := (div_lt_div_iff₀ hm' hm).mp h
  rw [mass_add,mass_add] at h'
  unfold slopeCross
  nlinarith

end ElementaryPositivity.SlopeArithmetic

end

end OAI
