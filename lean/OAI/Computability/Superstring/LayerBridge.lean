import OAI.Computability.Superstring.GeoCore

namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def layerWord (K : Code α) (g : ℕ) : List α := (key K g).take (period K g)
def layerExits (K : Code α) (g j : ℕ) : List ℕ :=
  (List.range (period K g)).map (fun r => rankLength K g j r)

@[fun_prop] theorem poly_layerWord : Poly (fun q : Code α × ℕ => layerWord q.1 q.2) := by
  unfold layerWord; fun_prop
@[fun_prop] theorem poly_layerExits : Poly (fun q : Code α × ℕ × ℕ => layerExits q.1 q.2.1 q.2.2) := by
  unfold layerExits
  exact BitCode.Poly.mapFn
    (f := fun q : (Code α × ℕ × ℕ) × ℕ => rankLength q.1.1 q.1.2.1 q.1.2.2 q.2)
    (by fun_prop) (by fun_prop)

omit [Coded α] in
theorem length_layerWord {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    (layerWord K g.val).length = period K g.val := by
  have hp := (period_spec h g).2
  simp only [layerWord,List.length_take,key,List.length_map,List.length_range]
  omega

omit [Coded α] in
theorem text_layerWord {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    PeriodWord.text (layerWord K g.val) = C.text g := by
  apply PeriodWord.eq_of_prefix
  · rw [length_layerWord h g]; exact (period_spec h g).1.positive
  · rw [length_layerWord h g]; exact (period_spec h g).1.periodic
  · intro i hi
    have hir : i < 2 * K.1.length := by
      rw [length_layerWord h g] at hi; have := (period_spec h g).2; omega
    have he := C.finiteKey_get g (by simpa only [Fintype.card_fin] using hir)
    have he' := key_eq h g
    have hi' : i < (key K g.val).length := by simpa only [key,List.length_map,List.length_range] using hir
    have heq : (key K g.val)[i] = C.text g (i : ℤ) := by
      rw [← he'] at he
      exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hi'] using he)
    simpa only [layerWord,List.getElem_take] using heq

theorem exit_layerExits (K : Code α) (g j : ℕ) (hp : 0 < period K g) (x : ℤ) :
    GeoCode.exit (layerExits K g j) x = exit K g j x := by
  unfold GeoCode.exit layerExits exit
  simp only [List.length_map,List.length_range]
  have hi : (x % (period K g : ℤ)).toNat < period K g := by
    have h₀ := Int.emod_nonneg x (show (period K g : ℤ) ≠ 0 by omega)
    have h₁ := Int.emod_lt_of_pos x (show (0 : ℤ) < period K g by omega)
    omega
  simp only [List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]

end Superstring.ThreadArray


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α]
abbrev GroupData (α : Type) := List α × List (List ℕ)
def turn (U : List α) (Z : List ℕ) : Walk α :=
  GeoCode.segment (PeriodWord.text U) (GeoCode.exit Z) 0 U.length
structure Represents {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (U : List α) (Z : List ℕ) (L : Layer V A p) : Prop where
  text_eq : PeriodWord.text U = A
  length_eq : U.length = p
  exit_eq : GeoCode.exit Z = L.z

theorem turn_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {U : List α} {Z : List ℕ} {L : Layer V A p} (h : Represents U Z L)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    Runs V (textWord A 0 (L.first 0)) (textWord A 0 (L.first 0)) (turn U Z) ∧
      cost (turn U Z) = p ∧ ∀ w ∈ L.Content, w ∈ turn U Z := by
  obtain ⟨P,hP,hc,hv⟩ := GeoCode.full_turn_realizes L closed hp per 0
  have he : turn U Z = WalkCode.Path.points P := by
    rw [turn,h.text_eq,h.length_eq,h.exit_eq,hP]
  rw [he]
  have hs := WalkCode.points_spec P
  refine ⟨⟨hs.1,hs.2.1,hs.2.2.1⟩,hs.2.2.2.1.trans hc,?_⟩
  rintro w ⟨x,e,hf,hl,rfl⟩
  exact (hs.2.2.2.2 _).mpr (hv x e hf hl)

variable [DecidableEq α]
def saturate (D : GroupData α) (js : List ℕ) (P : Walk α) : Walk α :=
  fill P (js.map (fun j => turn D.1 (D.2[j]?.getD [])))

theorem saturate_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {D : GroupData α} {js : List ℕ} {P : Walk α} {s t : List α}
    (L : ℕ → Layer V A p) (h : ∀ j ∈ js, Represents D.1 (D.2[j]?.getD []) (L j))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hP : Runs V s t P) (htouch : ∀ j ∈ js, ∃ w ∈ (L j).Content, w ∈ P) :
    Runs V s t (saturate D js P) ∧ cost (saturate D js P) = cost P + js.length*p ∧
      (∀ w ∈ P, w ∈ saturate D js P) ∧ ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ saturate D js P := by
  have ht (j : ℕ) (hj : j ∈ js) := turn_spec (h j hj) closed hp per
  obtain ⟨hR,hc,hv⟩ := fill_spec P (js.map (fun j => turn D.1 (D.2[j]?.getD []))) hP
    (by rintro Q hQ; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hQ; exact ⟨_,(ht j hj).1⟩)
    (by rintro Q hQ; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hQ
        obtain ⟨w,hw,hwP⟩ := htouch j hj
        exact ⟨w,hwP,(ht j hj).2.2 w hw⟩)
  refine ⟨hR,?_,fun w hw => (hv w).mpr (Or.inl hw),?_⟩
  · rw [List.map_map] at hc
    have he : (js.map (fun j => cost (turn D.1 (D.2[j]?.getD [])))).sum = js.length*p := by
      rw [List.map_congr_left (g := fun _ => p) (fun j hj => (ht j hj).2.1)]
      simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
    exact hc.trans (congrArg (cost P + ·) he)
  · intro j hj w hw
    exact (hv w).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,(ht j hj).2.2 w hw⟩)

variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_turn : Poly (fun q : List α × List ℕ => turn q.1 q.2) := by
  unfold turn
  exact GeoCode.poly_segment.comp (f := fun q : List α × List ℕ => (q.1,q.2,(0 : ℤ),q.1.length)) (by fun_prop)
omit [DecidableEq α] in
@[fun_prop] theorem poly_indexturn : Poly (fun q : GroupData α × ℕ => turn q.1.1 (q.1.2[q.2]?.getD [])) := by
  have hz : Poly (fun q : GroupData α × ℕ => q.1.2[q.2]?.getD []) :=
    (BitCode.Poly.getD ([] : List ℕ)).comp (f := fun q : GroupData α × ℕ => (q.1.2,q.2)) (by fun_prop)
  exact poly_turn.comp (f := fun q : GroupData α × ℕ => (q.1.1,q.1.2[q.2]?.getD []))
    ((show Poly (fun q : GroupData α × ℕ => q.1.1) from by fun_prop).pair hz)
@[fun_prop] theorem poly_saturate : Poly (fun q : GroupData α × List ℕ × Walk α =>
    saturate q.1 q.2.1 q.2.2) := by
  unfold saturate
  have ht : Poly (fun q : (GroupData α × List ℕ × Walk α) × ℕ =>
      turn q.1.1.1 (q.1.1.2[q.2]?.getD [])) :=
    poly_indexturn.comp (f := fun q : (GroupData α × List ℕ × Walk α) × ℕ => (q.1.1,q.2)) (by fun_prop)
  have hm : Poly (fun q : GroupData α × List ℕ × Walk α =>
      q.2.1.map (fun j => turn q.1.1 (q.1.2[j]?.getD []))) :=
    BitCode.Poly.mapFn ht (by fun_prop)
  exact WalkCode.poly_fill.comp ((show Poly (fun q : GroupData α × List ℕ × Walk α => q.2.2) from by fun_prop).pair hm)
end Superstring.LayerArray


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α]

def phaseContent (U : List α) (Z : List ℕ) (r : ℕ) : List (List α) :=
  let a := GeoCode.first Z r
  (List.range ((GeoCode.exit Z r-a).toNat+1)).map
    (fun i : ℕ => PeriodWord.window U r (a+i))
def content (U : List α) (Z : List ℕ) : List (List α) :=
  (List.range U.length).flatMap (phaseContent U Z)

theorem mem_phaseContent {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {U : List α} {Z : List ℕ} {L : Layer V A p} (h : Represents U Z L)
    (r : ℕ) (w : List α) : w ∈ phaseContent U Z r ↔
      ∃ e, L.first r ≤ e ∧ e ≤ L.last r ∧ w = textWord A r e := by
  simp only [phaseContent,GeoCode.first,h.exit_eq,PeriodWord.window_eq,h.text_eq,
    List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    refine ⟨L.first r+i,by omega,?_,rfl⟩
    have hh := L.first_le_last r
    change L.z ((r : ℤ)-1)+(i : ℤ) ≤ L.z r
    unfold Layer.first Layer.last at hh
    omega
  · rintro ⟨e,hf,hl,rfl⟩
    refine ⟨(e-L.first r).toNat,?_,?_⟩
    · unfold Layer.first Layer.last at *
      omega
    · congr 1
      change L.first r+((e-L.first r).toNat : ℤ) = e
      omega

theorem mem_content {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {U : List α} {Z : List ℕ} {L : Layer V A p} (h : Represents U Z L)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (w : List α) :
    w ∈ content U Z ↔ w ∈ L.Content := by
  simp only [content,List.mem_flatMap,List.mem_range,h.length_eq,mem_phaseContent h]
  constructor
  · rintro ⟨r,_,e,hf,hl,he⟩
    exact ⟨r,e,hf,hl,he⟩
  · rintro ⟨x,e,hf,hl,rfl⟩
    let r := x % (p : ℤ)
    let m := x / (p : ℤ)
    have hr0 : 0 ≤ r := Int.emod_nonneg x (by omega)
    have hrp : r < p := Int.emod_lt_of_pos x (by omega)
    have hrx : r+m*p = x := Int.emod_add_ediv_mul x p
    have hfr := L.first_shift_int m r
    have hlr := L.shift_int m r
    rw [hrx] at hfr hlr
    have hrn : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    refine ⟨r.toNat,by omega,e-m*p,?_,?_,?_⟩
    · rw [hrn]; omega
    · rw [hrn]
      change _ ≤ L.z r
      change e ≤ L.z x at hl
      omega
    · rw [hrn]
      have he := textWord_translate A (m*p) (per.int_mul m) r (e-m*p)
      rw [hrx,sub_add_cancel] at he
      exact he

variable [Coded α]
@[fun_prop] theorem poly_phaseContent : Poly (fun q : List α × List ℕ × ℕ =>
    phaseContent q.1 q.2.1 q.2.2) := by
  unfold phaseContent
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × List ℕ × ℕ) × ℕ =>
      PeriodWord.window q.1.1 q.1.2.2 (GeoCode.first q.1.2.1 q.1.2.2+q.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_content : Poly (fun q : List α × List ℕ => content q.1 q.2) := by
  unfold content
  exact BitCode.Poly.flatten.comp (BitCode.Poly.mapFn
    (f := fun q : (List α × List ℕ) × ℕ => phaseContent q.1.1 q.1.2 q.2)
    (by fun_prop) (by fun_prop))
end Superstring.LayerArray

end OAI
