import OAI.Combinatorics.EditDistance.RowSeparation

namespace OAI

/-!
# Padded windows and insertion-deletion matching inequalities
-/

namespace EditWindow
open EditDistortion

variable {A : Type*}

def window (x : List A) (start len : ℕ) : List (Option A) :=
  List.ofFn (fun i : Fin len => x[start+i.val]?)

@[simp] lemma window_length (x : List A) (start len : ℕ) : (window x start len).length = len :=
  List.length_ofFn

lemma lookup_insert_before (p q : List A) (a : A) {r : ℕ} (hr : r < p.length) :
    (p ++ a::q)[r]? = (p ++ q)[r]? := by
  rw [List.getElem?_append_left hr,List.getElem?_append_left hr]

lemma lookup_insert_after (p q : List A) (a : A) {r : ℕ} (hr : p.length ≤ r) :
    (p ++ a::q)[r+1]? = (p ++ q)[r]? := by
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right hr]
  have he : r+1-p.length = (r-p.length)+1 := by omega
  simp only [he,List.getElem?_cons_succ]

lemma window_before (p q : List A) (a : A) {start len : ℕ} (h : start+len ≤ p.length) :
    window (p ++ a::q) start len = window (p ++ q) start len := by
  unfold window
  congr 1
  funext i
  exact lookup_insert_before p q a (by omega)

lemma window_after (p q : List A) (a : A) {start len : ℕ} (h : p.length ≤ start) :
    window (p ++ a::q) (start+1) len = window (p ++ q) start len := by
  unfold window
  congr 1
  funext i
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
    lookup_insert_after p q a (r := start+i.val) (by omega)

theorem window_insert_cost (p q : List A) (a : A) (start len : ℕ) :
    indel (window (p ++ q) start len) (window (p ++ a::q) start len) ≤ 2 := by
  by_cases hl : len = 0
  · subst len
    have hh : indel ([] : List (Option A)) [] = 0 := (cost_eq_zero_iff (s := false)).mpr rfl
    simpa only [window,List.ofFn_zero,hh] using (by norm_num : (0 : ℕ) ≤ 2)
  have hlp : 0 < len := Nat.pos_of_ne_zero hl
  let f : Fin (len-1) ↪o Fin len :=
    (Fin.castLEOrderEmb (by omega : len-1 ≤ len))
  let g₀ (i : Fin (len-1)) : Fin len :=
    ⟨if start+i.val < p.length then i.val else i.val+1,by split <;> omega⟩
  have hg : StrictMono g₀ := by
    intro i j hij
    have hij' : i.val < j.val := hij
    change (if start+i.val < p.length then i.val else i.val+1) <
      (if start+j.val < p.length then j.val else j.val+1)
    split <;> split <;> omega
  let g : Fin (len-1) ↪o Fin len := OrderEmbedding.ofStrictMono g₀ hg
  have he (i : Fin (len-1)) :
      (p ++ q)[start+(f i).val]? = (p ++ a::q)[start+(g i).val]? := by
    change (p ++ q)[start+i.val]? =
      (p ++ a::q)[start+(if start+i.val < p.length then i.val else i.val+1)]?
    split
    · rename_i hi
      exact (lookup_insert_before p q a hi).symm
    · rename_i hi
      simpa only [Nat.add_assoc] using
        (lookup_insert_after p q a (r := start+i.val) (by omega)).symm
  have hh := indel_le_of_matching (fun i : Fin len => (p ++ q)[start+i.val]?)
    (fun i : Fin len => (p ++ a::q)[start+i.val]?) f g he
  exact hh.trans (by omega)

end EditWindow

namespace EditDistortion
variable {A B : Type*}

lemma indel_cost (x y : List A) : indel x y = cost false x y := rfl

lemma step_indel_filterMap (f : A → Option B) {x y : List A} (h : Step false x y) :
    indel (x.filterMap f) (y.filterMap f) ≤ 1 := by
  cases h with
  | insert p q a =>
    cases ha : f a with
    | none => simp only [List.filterMap_append,List.filterMap_cons,ha,indel_cost,cost_refl]; omega
    | some b =>
      simpa only [List.filterMap_append,List.filterMap_cons,ha,indel_cost] using
        cost_le (Script.single (Step.insert (substitutions := false) (p.filterMap f) (q.filterMap f) b))
  | delete p q a =>
    cases ha : f a with
    | none => simp only [List.filterMap_append,List.filterMap_cons,ha,indel_cost,cost_refl]; omega
    | some b =>
      simpa only [List.filterMap_append,List.filterMap_cons,ha,indel_cost] using
        cost_le (Script.single (Step.delete (substitutions := false) (p.filterMap f) (q.filterMap f) b))
  | substitute hf => contradiction

lemma indel_filterMap_le (f : A → Option B) (x y : List A) :
    indel (x.filterMap f) (y.filterMap f) ≤ indel x y := by
  have hh {n : ℕ} {x y : List A} (h : Script false n x y) :
      indel (x.filterMap f) (y.filterMap f) ≤ n := by
    induction h with
    | nil x => exact cost_le (.nil _)
    | @cons n x y z e h ih =>
      have ht := cost_triangle (s := false) (x.filterMap f) (y.filterMap f) (z.filterMap f)
      have he := step_indel_filterMap f e
      rw [indel_cost] at he ih ⊢
      omega
  exact hh (cost_spec x y)
end EditDistortion

namespace EditWindow
open EditDistortion
variable {A : Type*}

def segment (x : ℕ → A) (start len : ℕ) : List A :=
  List.ofFn (fun i : Fin len => x (start+i.val))

@[simp] lemma segment_length (x : ℕ → A) (start len : ℕ) :
    (segment x start len).length = len := List.length_ofFn

lemma segment_sublist (x : ℕ → A) (start l k L : ℕ) (hk : k+L ≤ l) :
    (segment x (start+k) L).Sublist (segment x start l) := by
  let f : Fin L ↪o Fin l := OrderEmbedding.ofStrictMono
    (fun i => (⟨k+i.val,by omega⟩ : Fin l)) (by intro i j hij; change k+i.val < k+j.val; omega)
  have hh := sublist_ofFn_comp (fun i : Fin l => x (start+i.val)) f
  dsimp [f,OrderEmbedding.ofStrictMono] at hh
  simpa only [segment,Nat.add_assoc] using hh

lemma segment_loss (x : ℕ → A) (start l k L : ℕ) (hk : k+L ≤ l) :
    indel (segment x start l) (segment x (start+k) L) ≤ l-L := by
  simpa only [segment_length,indel_cost] using cost_le (Script.of_sublist (segment_sublist x start l k L hk))

lemma segment_cross (x y : ℕ → A) (start l s : ℕ) (hs : 1 ≤ s) (hsl : s ≤ l)
    (i j : Fin s) :
    indel (segment x start l) (segment y start l) ≤
      2*(s-1)+indel (segment x (start+i.val) (l-s+1)) (segment y (start+j.val) (l-s+1)) := by
  have hx := segment_loss x start l i.val (l-s+1) (by omega)
  have hy := segment_loss y start l j.val (l-s+1) (by omega)
  rw [indel_cost,cost_symm] at hy
  have h1 := cost_triangle (s := false) (segment x start l)
    (segment x (start+i.val) (l-s+1)) (segment y (start+j.val) (l-s+1))
  have h2 := cost_triangle (s := false) (segment x start l)
    (segment y (start+j.val) (l-s+1)) (segment y start l)
  simp only [indel_cost] at hx hy ⊢
  omega

lemma segment_append (x : ℕ → A) (start l m : ℕ) :
    segment x start (l+m) = segment x start l ++ segment x (start+l) m := by
  unfold segment
  rw [List.ofFn_add]
  congr 1
  congr 1
  funext i
  simp only [Fin.val_natAdd,Nat.add_assoc]

lemma indel_segment_blocks (x y : ℕ → A) (l b : ℕ) :
    indel (segment x 0 (b*l)) (segment y 0 (b*l)) ≤
      ∑ j ∈ Finset.range b, indel (segment x (j*l) l) (segment y (j*l) l) := by
  induction b with
  | zero => simp only [Nat.zero_mul,segment,List.ofFn_zero,Finset.sum_range_zero]; exact cost_le (.nil _)
  | succ b ih =>
    rw [Nat.succ_mul,segment_append,segment_append,Finset.sum_range_succ]
    simp only [Nat.zero_add]
    exact (cost_append_le (s := false) _ _ _ _).trans (Nat.add_le_add_right ih _)

lemma window_eq_segment (x : List A) (start len : ℕ) :
    window x start len = segment (fun k => x[k]?) start len := rfl

lemma window_padding (x : List A) (n : ℕ) (hx : x.length ≤ n) :
    window x 0 n = (x.map some) ++ List.replicate (n-x.length) none := by
  apply List.ext_getElem?
  intro i
  simp only [window,List.getElem?_ofFn,Nat.zero_add,List.getElem?_append,List.length_map,
    List.getElem?_map,List.getElem?_replicate]
  by_cases hix : i < x.length
  · have hin : i < n := lt_of_lt_of_le hix hx
    simp [hix,hin]
  · have hxn : x[i]? = none := List.getElem?_eq_none (by omega)
    have hi : i-x.length < n-x.length ↔ i < n := by omega
    simp only [ite_eq_right hix,hxn,hi]
    split <;> rfl

lemma filterMap_window (x : List A) (n : ℕ) (hx : x.length ≤ n) :
    (window x 0 n).filterMap id = x := by
  rw [window_padding x n hx]
  simp

lemma indel_le_window (x y : List A) (n : ℕ) (hx : x.length ≤ n) (hy : y.length ≤ n) :
    indel x y ≤ indel (window x 0 n) (window y 0 n) := by
  have hh := indel_filterMap_le id (window x 0 n) (window y 0 n)
  simpa only [filterMap_window x n hx,filterMap_window y n hy] using hh

end EditWindow

end OAI
