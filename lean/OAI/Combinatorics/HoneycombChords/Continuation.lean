import OAI.Combinatorics.HoneycombChords.FluxBounds

namespace OAI

/-!
# Fresh-row continuation of honeycomb bridges

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.FiniteContinuation
open CriticalHoneycomb

/-- A fresh deterministic lattice row. Every two new centers advance one
pure-cut spacing; this construction contributes no boundary-port weight. -/
def row (i j : ℤ) : ℕ → List Center
  | 0 => []
  | n+1 => up i j::down i j::row (i+1) j n

lemma row_length (i j : ℤ) (n : ℕ) : (row i j n).length=2*n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [row,ih];omega

lemma mem_row (i j : ℤ) (n : ℕ) (v : Center) :
    v∈row i j n ↔ i≤v.1 ∧ v.1 < i + n ∧ v.2.1=j := by
  induction n generalizing i with
  | zero => simp [row];omega
  | succ n ih =>
    rcases v with ⟨x,y,t⟩
    cases t <;> simp only [row,List.mem_cons,ih,up,down,Prod.mk.injEq,Nat.cast_add,Nat.cast_one]
    all_goals constructor
    all_goals intro hv
    all_goals simp_all
    all_goals omega

lemma row_nodup (i j : ℤ) (n : ℕ) : (row i j n).Nodup := by
  induction n generalizing i with
  | zero => simp [row]
  | succ n ih =>
    simp only [row,List.nodup_cons,List.mem_cons,not_or]
    refine ⟨⟨by simp [up,down],?_⟩,⟨?_,ih _⟩⟩ <;> simp [mem_row,up,down]

lemma row_head (i j : ℤ) (n : ℕ) : (row i j (n+1)).head?=some (up i j) := rfl
lemma row_last (i j : ℤ) (n : ℕ) :
    (row i j (n+1)).getLast?=some (down (i+n) j) := by
  induction n generalizing i with
  | zero => simp [row,down]
  | succ n ih =>
    simpa [row,List.getLast?_cons_cons,ih,down,add_assoc,add_comm,add_left_comm] using ih (i+1)

lemma row_chain (i j : ℤ) (n : ℕ) : (row i j n).IsChain Adj := by
  induction n generalizing i with
  | zero => simp [row]
  | succ n ih =>
    cases n with
    | zero => simp [row,Adj,up,down]
    | succ n =>
      have hh := ih (i+1)
      simpa only [row,List.isChain_cons_cons] using
        (show Adj (up i j) (down i j) ∧ Adj (down i j) (up (i+1) j) ∧
            (row (i+1) j (n+1)).IsChain Adj from
          ⟨by simp [Adj,up,down],by simp [Adj,up,down],hh⟩)

def shift (dy : ℤ) (v : Center) : Center := (v.1,v.2.1+dy,v.2.2)
lemma shift_injective (dy : ℤ) : Function.Injective (shift dy) := by
  intro v w h
  rcases v with ⟨x,y,t⟩;rcases w with ⟨x',y',t'⟩
  simp [shift,Prod.mk.injEq] at h
  simp [h]
lemma shift_adj (dy : ℤ) (v w : Center) : Adj (shift dy v) (shift dy w) ↔ Adj v w := by
  rcases v with ⟨x,y,t⟩;rcases w with ⟨x',y',t'⟩
  cases t <;> simp only [Adj,shift,Bool.false_eq_true,ite_false,ite_true]
  all_goals constructor <;> intro h <;> rcases h with ⟨ht,h⟩ <;> refine ⟨ht,?_⟩ <;> omega
lemma shift_up (dy i j : ℤ) : shift dy (up i j)=up i (j+dy) := rfl
lemma shift_down (dy i j : ℤ) : shift dy (down i j)=down i (j+dy) := rfl
lemma shift_shift (dx dy : ℤ) (v : Center) : shift dx (shift dy v)=shift (dy+dx) v := by
  rcases v with ⟨x,y,t⟩;simp [shift,add_assoc]
lemma shift_zero (v : Center) : shift 0 v=v := by cases v;simp [shift]

/-- The same finite pure rectangle as the tensor grid, given by its literal
integer-coordinate inequalities for the geometric continuation proof. -/
def rect (W H : ℕ) : Set Center :=
  {v | 0≤v.1 ∧ v.1<(W:ℤ) ∧ 0≤v.2.1 ∧ v.2.1<(H:ℤ)}

/-- The original bottom/top chord trace, with two fresh disjoint rows. -/
def extend (W h : ℕ) (i x : Fin W) (p : List Center) : List Center :=
  row 0 0 (i.val+1)++p.map (shift 1)++row x.val (h+1) (W-x.val)

lemma extend_length (W h : ℕ) (i x : Fin W) (p : List Center) :
    (extend W h i x p).length=p.length+2*(i.val+1)+2*(W-x.val) := by
  simp [extend,row_length];omega

lemma extend_length_le (W h : ℕ) (i x : Fin W) (p : List Center) :
    (extend W h i x p).length≤p.length+4*W := by
  rw [extend_length]
  have hi := i.isLt
  have hx := x.isLt
  omega

lemma extend_mem (W h : ℕ) (i x : Fin W) (p : List Center)
    (hp : ∀ v∈p,v∈rect W h) : ∀ v∈extend W h i x p,v∈rect W (h+2) := by
  intro v hv
  simp only [extend,List.mem_append] at hv
  rcases hv with (hv|hv)|hv
  · have hm := (mem_row _ _ _ _).mp hv
    have hi := i.isLt
    simp only [rect,Set.mem_ofPred_eq]
    omega
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hu := hp u hu
    simp only [rect,Set.mem_ofPred_eq,shift] at hu ⊢
    omega
  · have hm := (mem_row _ _ _ _).mp hv
    have hx := x.isLt
    simp only [rect,Set.mem_ofPred_eq]
    omega

lemma extend_nodup (W h : ℕ) (i x : Fin W) (p : List Center)
    (hpos : 0<h) (hn : p.Nodup) (hp : ∀ v∈p,v∈rect W h) :
    (extend W h i x p).Nodup := by
  have hm : (p.map (shift 1)).Nodup := hn.map (shift_injective 1)
  have hd₁ : List.Disjoint (row 0 0 (i.val+1)) (p.map (shift 1)) := by
    intro v hv hv'
    have hr := (mem_row _ _ _ _).mp hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv'
    have hp := hp u hu
    simp only [rect,Set.mem_ofPred_eq,shift] at hp hr
    omega
  have hd₂ : List.Disjoint (row 0 0 (i.val+1)) (row x.val (h+1) (W-x.val)) := by
    intro v hv hv'
    have h₁ := (mem_row _ _ _ _).mp hv
    have h₂ := (mem_row _ _ _ _).mp hv'
    omega
  have hd₃ : List.Disjoint (p.map (shift 1)) (row x.val (h+1) (W-x.val)) := by
    intro v hv hv'
    have hr := (mem_row _ _ _ _).mp hv'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hp := hp u hu
    simp only [rect,Set.mem_ofPred_eq,shift] at hp hr
    omega
  simp only [extend,List.nodup_append]
  refine ⟨⟨row_nodup _ _ _,hm,?_⟩,row_nodup _ _ _,?_⟩
  · intro a ha b hb hab
    subst b
    exact hd₁ ha hb
  · intro a ha b hb hab
    subst b
    rcases List.mem_append.mp ha with ha|ha
    · exact hd₂ ha hb
    · exact hd₃ ha hb

/-- Symmetry is literal honeycomb adjacency, not a geometric relaxation. -/
lemma adj_symm {v w : Center} (h : Adj v w) : Adj w v := by
  rcases v with ⟨i,j,t⟩;rcases w with ⟨k,l,u⟩
  cases t <;> cases u <;> simp [Adj] at h ⊢ <;> omega

lemma reverse_chain {p : List Center} (h : p.IsChain Adj) : p.reverse.IsChain Adj := by
  rw [List.isChain_reverse]
  exact h.imp (fun _ _ h=>adj_symm h)

/-- Enter from the EAST wall on the bottom fresh row, ending immediately
below the original source. This direction matches the checked flux bound. -/
def eastRun (W : ℕ) (i : Fin W) (j : ℤ) : List Center :=
  (down i.val j::row (i.val+1) j (W-i.val-1)).reverse
/-- Leave from the original top endpoint through a new row to the WEST wall. -/
def westRun (x : ℕ) (j : ℤ) : List Center :=
  (row 0 j x++[up x j]).reverse

lemma eastRun_length (W : ℕ) (i : Fin W) (j : ℤ) :
    (eastRun W i j).length=1+2*(W-i.val-1) := by simp [eastRun,row_length];omega
lemma westRun_length (x : ℕ) (j : ℤ) : (westRun x j).length=2*x+1 := by
  simp [westRun,row_length]
lemma eastRun_last (W : ℕ) (i : Fin W) (j : ℤ) :
    (eastRun W i j).getLast?=some (down i.val j) := by simp [eastRun]
lemma westRun_head (x : ℕ) (j : ℤ) :
    (westRun x j).head?=some (up x j) := by simp [westRun]
lemma westRun_last (x : ℕ) (j : ℤ) :
    (westRun x j).getLast?=some (up 0 j) := by
  unfold westRun
  rw [List.getLast?_reverse]
  cases x <;> simp [row,up]
lemma eastRun_head (W : ℕ) (i : Fin W) (j : ℤ) :
    (eastRun W i j).head?=some (down (W-1:ℕ) j) := by
  have hi := i.isLt
  unfold eastRun
  rw [List.head?_reverse]
  cases hn : W-i.val-1 with
  | zero =>
    have he : i.val=W-1 := by omega
    simp [row,he]
  | succ n =>
    have hh := row_last (i.val+1) j n
    have he : (i.val:ℤ)+1+n=(W-1:ℕ) := by omega
    simpa [List.getLast?_cons_cons,row,he] using hh

lemma eastRun_mem (W : ℕ) (i : Fin W) (j : ℤ) {v : Center}
    (hv : v∈eastRun W i j) : 0≤v.1 ∧ v.1<(W:ℤ) ∧ v.2.1=j := by
  have hi := i.isLt
  simp only [eastRun,List.mem_reverse,List.mem_cons] at hv
  rcases hv with rfl|hv
  · simp [down]
  · have hm := (mem_row _ _ _ _).mp hv
    omega
lemma westRun_mem (x : ℕ) (j : ℤ) {v : Center}
    (hv : v∈westRun x j) : 0≤v.1 ∧ v.1≤(x:ℤ) ∧ v.2.1=j := by
  simp only [westRun,List.mem_reverse,List.mem_append,List.mem_singleton] at hv
  rcases hv with hv|rfl
  · have hm := (mem_row _ _ _ _).mp hv
    omega
  · simp [up]
lemma eastRun_nodup (W : ℕ) (i : Fin W) (j : ℤ) : (eastRun W i j).Nodup := by
  rw [eastRun,List.nodup_reverse,List.nodup_cons]
  refine ⟨?_,row_nodup _ _ _⟩
  rw [mem_row]
  simp [down]
lemma westRun_nodup (x : ℕ) (j : ℤ) : (westRun x j).Nodup := by
  rw [westRun,List.nodup_reverse,List.nodup_append]
  refine ⟨row_nodup _ _ _,by simp,?_⟩
  intro a ha b hb hab
  have he : b=up x j := by simpa using hb
  subst b;subst a
  have hm := (mem_row _ _ _ _).mp ha
  simp [up] at hm
lemma eastRun_chain (W : ℕ) (i : Fin W) (j : ℤ) : (eastRun W i j).IsChain Adj := by
  apply reverse_chain
  rw [List.isChain_cons]
  refine ⟨?_,row_chain _ _ _⟩
  cases hn : W-i.val-1 with
  | zero => simp [row]
  | succ n => simp [row,Adj,up,down]
lemma westRun_chain (x : ℕ) (j : ℤ) : (westRun x j).IsChain Adj := by
  apply reverse_chain
  apply (row_chain 0 j x).append (by simp)
  cases x with
  | zero => simp [row]
  | succ n =>
    simp only [row_last,zero_add,List.head?_singleton,Option.mem_def,Option.some.injEq]
    intro u hu v hv
    subst u;subst v
    simp [Adj,up,down]

/-- Injective continuation along fresh rows. -/
def turnedExtend (W h : ℕ) (i x : Fin W) (p : List Center) : List Center :=
  eastRun W i 0++p.map (shift 1)++westRun x.val (h+1)
lemma turnedExtend_length (W h : ℕ) (i x : Fin W) (p : List Center) :
    (turnedExtend W h i x p).length=p.length+2*(W-i.val-1)+2*x.val+2 := by
  simp [turnedExtend,eastRun_length,westRun_length];omega
lemma turnedExtend_length_le (W h : ℕ) (i x : Fin W) (p : List Center) :
    (turnedExtend W h i x p).length≤p.length+4*W := by
  rw [turnedExtend_length]
  have hi := i.isLt;have hx := x.isLt
  omega
lemma turnedExtend_mem (W h : ℕ) (i x : Fin W) (p : List Center)
    (hp : ∀ v∈p,v∈rect W h) : ∀ v∈turnedExtend W h i x p,v∈rect W (h+2) := by
  intro v hv
  simp only [turnedExtend,List.mem_append] at hv
  rcases hv with (hv|hv)|hv
  · have hm := eastRun_mem W i 0 hv
    simp only [rect,Set.mem_ofPred_eq]
    omega
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hu := hp u hu
    simp only [rect,Set.mem_ofPred_eq,shift] at hu ⊢
    omega
  · have hm := westRun_mem x.val (h+1) hv
    have hx := x.isLt
    simp only [rect,Set.mem_ofPred_eq]
    omega
lemma turnedExtend_nodup (W h : ℕ) (i x : Fin W) (p : List Center)
    (hpos : 0<h) (hn : p.Nodup) (hp : ∀ v∈p,v∈rect W h) :
    (turnedExtend W h i x p).Nodup := by
  have hm : (p.map (shift 1)).Nodup := hn.map (shift_injective 1)
  have hd₁ : List.Disjoint (eastRun W i 0) (p.map (shift 1)) := by
    intro v hv hv'
    have hr := eastRun_mem W i 0 hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv'
    have hp := hp u hu
    simp only [rect,Set.mem_ofPred_eq,shift] at hp hr
    omega
  have hd₂ : List.Disjoint (eastRun W i 0) (westRun x.val (h+1)) := by
    intro v hv hv'
    have h₁ := eastRun_mem W i 0 hv
    have h₂ := westRun_mem x.val (h+1) hv'
    omega
  have hd₃ : List.Disjoint (p.map (shift 1)) (westRun x.val (h+1)) := by
    intro v hv hv'
    have hr := westRun_mem x.val (h+1) hv'
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hp := hp u hu
    simp only [rect,Set.mem_ofPred_eq,shift] at hp hr
    omega
  simp only [turnedExtend,List.nodup_append]
  refine ⟨⟨eastRun_nodup _ _ _,hm,?_⟩,westRun_nodup _ _,?_⟩
  · intro a ha b hb hab;subst b;exact hd₁ ha hb
  · intro a ha b hb hab;subst b
    rcases List.mem_append.mp ha with ha|ha
    · exact hd₂ ha hb
    · exact hd₃ ha hb
lemma turnedExtend_chain (W h : ℕ) (i x : Fin W) (p : List Center)
    (hc : p.IsChain Adj) (hh : p.head?=some (up i.val 0))
    (hl : p.getLast?=some (down x.val ((h:ℤ)-1))) :
    (turnedExtend W h i x p).IsChain Adj := by
  have hm : (p.map (shift 1)).IsChain Adj :=
    List.isChain_map_of_isChain _ (fun _ _ h=>(shift_adj 1 _ _).mpr h) hc
  unfold turnedExtend
  apply ((eastRun_chain W i 0).append hm ?_).append (westRun_chain x.val (h+1))
  · simp only [List.getLast?_append,List.getLast?_map,hl,Option.map_some,Option.some_or,
      westRun_head,Option.mem_def,Option.some.injEq]
    intro u hu v hv
    subst u;subst v
    simp [shift,Adj,up,down]
  · simp only [eastRun_last,List.head?_map,hh,Option.map_some,Option.mem_def,Option.some.injEq]
    intro u hu v hv
    subst u;subst v
    simp [shift,Adj,up,down]

lemma turnedExtend_head (W h : ℕ) (i x : Fin W) (p : List Center) :
    (turnedExtend W h i x p).head?=some (down (W-1:ℕ) 0) := by
  simp [turnedExtend,List.head?_append,eastRun_head]
lemma turnedExtend_last (W h : ℕ) (i x : Fin W) (p : List Center) :
    (turnedExtend W h i x p).getLast?=some (up 0 (h+1)) := by
  simp [turnedExtend,List.getLast?_append,westRun_last]

def middle (h : ℕ) (v : Center) : Bool := decide (0<v.2.1 ∧ v.2.1<(h:ℤ)+1)
lemma filter_turnedExtend (W h : ℕ) (i x : Fin W) (p : List Center)
    (hp : ∀ v∈p,v∈rect W h) :
    (turnedExtend W h i x p).filter (middle h)=p.map (shift 1) := by
  have he : (eastRun W i 0).filter (middle h)=[] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    have hm := eastRun_mem W i 0 hv
    simp [middle,hm.2.2]
  have hw : (westRun x.val (h+1)).filter (middle h)=[] := by
    rw [List.filter_eq_nil_iff]
    intro v hv
    have hm := westRun_mem x.val (h+1) hv
    simp [middle,hm.2.2]
  have hm : (p.map (shift 1)).filter (middle h)=p.map (shift 1) := by
    rw [List.filter_eq_self]
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    have hp := hp u hu
    simp only [rect,Set.mem_ofPred_eq] at hp
    simp [middle,shift]
    omega
  simp only [turnedExtend,List.filter_append,he,hw,hm,List.nil_append,List.append_nil]

lemma turnedExtend_injective {W h : ℕ} {i x y : Fin W} {p q : List Center}
    (hp : ∀ v∈p,v∈rect W h) (hq : ∀ v∈q,v∈rect W h)
    (he : turnedExtend W h i x p=turnedExtend W h i y q) : p=q := by
  have hh := congrArg (List.filter (middle h)) he
  rw [filter_turnedExtend W h i x p hp,filter_turnedExtend W h i y q hq] at hh
  exact List.map_injective_iff.mpr (shift_injective 1) hh
lemma turnedExtend_height {W h k : ℕ} {i x y : Fin W} {p q : List Center}
    (he : turnedExtend W h i x p=turnedExtend W k i y q) : h=k := by
  have hh := congrArg List.getLast? he
  rw [turnedExtend_last,turnedExtend_last] at hh
  have hh : (h:ℤ)+1=(k:ℤ)+1 := by simpa [up] using hh
  omega
/-- A literal bottom-to-top bridge in width W+1 and height h+1, with
terminal position summed. No endpoint or length information is assumed. -/
def RectBridge (W h : ℕ) (i : Fin (W+1)) :=
  {p : List Center // IsTrace (rect (W+1) (h+1)) p ∧
    p.head?=some (up i.val 0) ∧
    ∃ x : Fin (W+1),p.getLast?=some (down x.val h)}
noncomputable def terminal {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) : Fin (W+1) :=
  Classical.choose γ.property.2.2
lemma terminal_last {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) :
    γ.val.getLast?=some (down (terminal γ).val h) := Classical.choose_spec γ.property.2.2
noncomputable def continuedTrace {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) : List Center :=
  (turnedExtend (W+1) (h+1) i (terminal γ) γ.val).reverse

lemma continuedTrace_trace {W h N : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i)
    (hN : h≤N) : IsTrace (rect (W+1) (N+3)) (continuedTrace γ) := by
  obtain ⟨hn,hc,hp⟩ := γ.property.1
  refine ⟨?_,?_,?_⟩
  · rw [continuedTrace,List.nodup_reverse]
    exact turnedExtend_nodup _ _ _ _ _ (by omega) hn hp
  · apply reverse_chain
    apply turnedExtend_chain _ _ _ _ _ hc γ.property.2.1
    simpa using terminal_last γ
  · intro v hv
    rw [continuedTrace,List.mem_reverse] at hv
    have hm := turnedExtend_mem _ _ _ _ _ hp v hv
    simp only [rect,Set.mem_ofPred_eq] at hm ⊢
    omega
lemma continuedTrace_head {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) :
    (continuedTrace γ).head?=some (up 0 (h+2)) := by
  simp [continuedTrace,turnedExtend_last,Nat.cast_add,Nat.cast_one,add_assoc]
lemma continuedTrace_last {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) :
    (continuedTrace γ).getLast?=some (down W 0) := by
  simp [continuedTrace,turnedExtend_head]
lemma continuedTrace_length {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) :
    (continuedTrace γ).length≤γ.val.length+4*(W+1) := by
  simpa [continuedTrace] using turnedExtend_length_le (W+1) (h+1) i (terminal γ) γ.val
lemma continuedTrace_injective {W h : ℕ} {i : Fin (W+1)} :
    Function.Injective (continuedTrace (W:=W) (h:=h) (i:=i)) := by
  intro γ δ he
  apply Subtype.ext
  have hh : turnedExtend (W+1) (h+1) i (terminal γ) γ.val=
      turnedExtend (W+1) (h+1) i (terminal δ) δ.val := by
    simpa [continuedTrace] using congrArg List.reverse he
  exact turnedExtend_injective γ.property.1.2.2 δ.property.1.2.2 hh
lemma continuedTrace_height {W h k : ℕ} {i : Fin (W+1)}
    (γ : RectBridge W h i) (δ : RectBridge W k i)
    (he : continuedTrace γ=continuedTrace δ) : h=k := by
  have hh := congrArg List.head? he
  rw [continuedTrace_head,continuedTrace_head] at hh
  have hh : (h:ℤ)+2=(k:ℤ)+2 := by simpa [up] using hh
  omega
end CriticalHoneycomb.FiniteContinuation

namespace CriticalHoneycomb.FiniteContinuation
open CriticalHoneycomb.Transfer

noncomputable def continuedChord {W h N : ℕ} {i : Fin (W+1)}
    (γ : RectBridge W h i) (hN : h≤N) :
    RasterGrid.RectChord W (N+2) ⟨h+2,by omega⟩ 0 := by
  refine ⟨continuedTrace γ,?_,?_,?_⟩
  · obtain ⟨hn,hc,hp⟩ := continuedTrace_trace γ hN
    refine ⟨hn,hc,?_⟩
    intro v hv
    apply (RasterGrid.mem_domain_iff v).mpr
    have hm := hp v hv
    simp only [rect,Set.mem_ofPred_eq] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm ⊢
    omega
  · simpa [RasterGrid.westPort,RasterGrid.cellCenter,up] using continuedTrace_head γ
  · simpa [RasterGrid.eastPort,RasterGrid.cellCenter,down] using continuedTrace_last γ

lemma continuedChord_injective {W h N : ℕ} {i : Fin (W+1)} (hN : h≤N) :
    Function.Injective (fun γ : RectBridge W h i => continuedChord γ hN) := by
  intro γ δ he
  exact continuedTrace_injective (congrArg Subtype.val he)

noncomputable instance rectBridgeFintype {W h : ℕ} {i : Fin (W+1)} :
    Fintype (RectBridge W h i) :=
  Fintype.ofInjective (fun γ : RectBridge W h i => continuedChord γ (le_refl h))
    (continuedChord_injective (le_refl h))

noncomputable def continues {W N : ℕ} {i : Fin (W+1)}
    (γ : Σ h : Fin (N+1),RectBridge W h.val i) :
    Σ j : Fin (N+3),RasterGrid.RectChord W (N+2) j 0 :=
  ⟨⟨γ.1.val+2,by have hh:=γ.1.isLt;omega⟩,
    continuedChord γ.2 (by have hh:=γ.1.isLt;omega)⟩

lemma continues_injective {W N : ℕ} {i : Fin (W+1)} :
    Function.Injective (continues (W:=W) (N:=N) (i:=i)) := by
  rintro ⟨h,γ⟩ ⟨k,δ⟩ he
  have ht : continuedTrace γ=continuedTrace δ :=
    congrArg (fun p : Σ j : Fin (N+3),RasterGrid.RectChord W (N+2) j 0 => p.2.val) he
  have hh : h=k := Fin.ext (continuedTrace_height γ δ ht)
  subst k
  have hg := continuedTrace_injective ht
  subst δ
  rfl

lemma kappa_positive : 0<kappa :=
  Real.rpow_pos_of_pos (by positivity : (0:ℝ)<2+Real.sqrt 2) _
lemma kappa_at_most_one : kappa≤1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have hh := Real.sqrt_nonneg (2:ℝ)
    linarith
  · norm_num

lemma continued_weight {W h : ℕ} {i : Fin (W+1)} (γ : RectBridge W h i) :
    kappa^(4*(W+1))*kappa^γ.val.length ≤ kappa^(continuedTrace γ).length := by
  rw [←pow_add]
  apply pow_le_pow_of_le_one kappa_positive.le kappa_at_most_one
  have hh:=continuedTrace_length γ
  omega
end CriticalHoneycomb.FiniteContinuation

namespace CriticalHoneycomb.FiniteContinuation
open CriticalHoneycomb.Transfer

noncomputable def crossingMass (W h : ℕ) (i : Fin (W+1)) : ℝ :=
  ∑ γ : RectBridge W h i,kappa^γ.val.length

lemma crossingMass_nonnegative (W h : ℕ) (i : Fin (W+1)) :
    0≤crossingMass W h i := by
  apply Finset.sum_nonneg
  intro γ hγ
  exact (pow_pos kappa_positive _).le

/-- Literal finite-height mass bound, using the injective fresh-row
continuation and the already proved finite honeycomb Ward identity. -/
theorem crossing_partial_sum (W N : ℕ) (i : Fin (W+1)) :
    kappa^(4*(W+1))*(∑ h : Fin (N+1),crossingMass W h.val i)≤1 := by
  classical
  let A := Σ h : Fin (N+1),RectBridge W h.val i
  let B := Σ j : Fin (N+3),RasterGrid.RectChord W (N+2) j 0
  let f : A → B := continues
  let g : B → ℝ := fun p => kappa^p.2.val.length
  have hfi : Function.Injective f := continues_injective
  have hb : (∑ p : B,g p)≤1 := by
    rw [Fintype.sum_sigma]
    exact FluxWard.rectangle_actual_sum_bound W (N+2) 0
  calc
    kappa^(4*(W+1))*(∑ h : Fin (N+1),crossingMass W h.val i) =
        ∑ p : A,kappa^(4*(W+1))*kappa^p.2.val.length := by
      rw [Fintype.sum_sigma]
      simp only [crossingMass,Finset.mul_sum]
    _ ≤ ∑ p : A,g (f p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact continued_weight p.2
    _ = ∑ p ∈ Finset.univ.image f,g p :=
      (Finset.sum_image hfi.injOn).symm
    _ ≤ ∑ p : B,g p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p hp hn
      exact (pow_pos kappa_positive _).le
    _ ≤ 1 := hb

/-- The actual fixed-width tall-crossing masses are summable. This is
stronger than the qualitative decay needed for the physical transfer gap,
and is a dependency only, not any of the manuscript's main theorems. -/
theorem crossing_summable (W : ℕ) (i : Fin (W+1)) :
    Summable (fun h : ℕ => crossingMass W h i) := by
  apply summable_of_sum_range_le (fun h => crossingMass_nonnegative W h i)
    (c:=1/kappa^(4*(W+1)))
  intro n
  cases n with
  | zero => simp [kappa_positive.le]
  | succ N =>
    rw [le_div_iff₀ (pow_pos kappa_positive _)]
    rw [mul_comm,←Fin.sum_univ_eq_sum_range]
    exact crossing_partial_sum W N i

/-- Uniform over the finitely many terminal sites, with the original
literal center weights and no assumed path estimates. -/
theorem crossing_tendsto_zero (W : ℕ) (i : Fin (W+1)) :
    Filter.Tendsto (fun h : ℕ => crossingMass W h i) Filter.atTop (nhds 0) :=
  (crossing_summable W i).tendsto_atTop_zero

end CriticalHoneycomb.FiniteContinuation

end OAI
