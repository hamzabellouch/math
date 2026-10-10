import Mathlib
import OAI.Combinatorics.StripMass.ScalarBridge

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.FiniteBranchTree
noncomputable section
open scoped BigOperators Classical

variable {V S : Type*} [DecidableEq V]

 

def leaves (vertex : S → V) (next : S → Bool → S) (free : Finset V) (s : S) :
    Finset (List Bool) :=
  if _h : vertex s ∈ free then
    (leaves vertex next (free.erase (vertex s)) (next s false)).image (List.cons false) ∪
      (leaves vertex next (free.erase (vertex s)) (next s true)).image (List.cons true)
  else {[]}
termination_by free.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem _h

 
def wordWeight (w : Bool → ℂ) : List Bool → ℂ
  | [] => 1
  | b::l => w b * wordWeight w l

@[simp] lemma wordWeight_nil (w : Bool → ℂ) : wordWeight w [] = 1 := rfl
@[simp] lemma wordWeight_cons (w : Bool → ℂ) (b : Bool) (l : List Bool) :
    wordWeight w (b::l) = w b * wordWeight w l := rfl

lemma prefix_disjoint (F G : Finset (List Bool)) :
    Disjoint (F.image (List.cons false)) (G.image (List.cons true)) := by
  apply Finset.disjoint_left.mpr
  intro l hl hr
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hl
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hr
  have he := ha.trans hb.symm
  simp only [List.cons.injEq, Bool.false_eq_true, false_and] at he

theorem mass_one (vertex : S → V) (next : S → Bool → S) (w : Bool → ℂ)
    (hw : w false + w true = 1) (free : Finset V) (s : S) :
    ∑ l ∈ leaves vertex next free s, wordWeight w l = 1 := by
  induction free using Finset.strongInductionOn generalizing s with
  | _ free ih =>
    rw [leaves]
    split_ifs with hs
    · rw [Finset.sum_union (prefix_disjoint _ _),
        Finset.sum_image (by intro a ha b hb h; simpa only [List.cons.injEq,true_and] using h),
        Finset.sum_image (by intro a ha b hb h; simpa only [List.cons.injEq,true_and] using h)]
      simp only [wordWeight_cons,←Finset.mul_sum]
      rw [ih _ (Finset.erase_ssubset hs),ih _ (Finset.erase_ssubset hs),mul_one,mul_one,hw]
    · simp

lemma nil_mem_iff (vertex : S → V) (next : S → Bool → S) (free : Finset V) (s : S) :
    [] ∈ leaves vertex next free s ↔ vertex s ∉ free := by
  rw [leaves]
  split_ifs <;> simp_all

lemma cons_mem_iff (vertex : S → V) (next : S → Bool → S) (free : Finset V)
    (s : S) (b : Bool) (l : List Bool) :
    b::l ∈ leaves vertex next free s ↔
      vertex s ∈ free ∧ l ∈ leaves vertex next (free.erase (vertex s)) (next s b) := by
  rw [leaves]
  split_ifs with hs
  · cases b <;> simp [hs]
  · simp [hs]

 
def visited (vertex : S → V) (next : S → Bool → S) (s : S) : List Bool → List V
  | [] => []
  | b::l => vertex s :: visited vertex next (next s b) l

 
def terminal (next : S → Bool → S) (s : S) : List Bool → S
  | [] => s
  | b::l => terminal next (next s b) l

omit [DecidableEq V] in
@[simp] lemma visited_length (vertex : S → V) (next : S → Bool → S)
    (s : S) (l : List Bool) : (visited vertex next s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp only [visited,List.length_cons,ih]

lemma visited_mem_domain (vertex : S → V) (next : S → Bool → S) {free : Finset V}
    {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    ∀ v ∈ visited vertex next s l, v ∈ free := by
  induction l generalizing free s with
  | nil => simp [visited]
  | cons b l ih =>
    obtain ⟨hs,hl⟩ := (cons_mem_iff vertex next free s b l).mp hl
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hs
    · exact Finset.mem_of_mem_erase (ih hl v hv)

lemma visited_nodup (vertex : S → V) (next : S → Bool → S) {free : Finset V}
    {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    (visited vertex next s l).Nodup := by
  induction l generalizing free s with
  | nil => simp [visited]
  | cons b l ih =>
    obtain ⟨_,hl⟩ := (cons_mem_iff vertex next free s b l).mp hl
    apply List.nodup_cons.mpr
    refine ⟨?_,ih hl⟩
    intro hv
    exact Finset.notMem_erase _ _ (visited_mem_domain vertex next hl _ hv)

lemma length_le_card (vertex : S → V) (next : S → Bool → S) {free : Finset V}
    {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    l.length ≤ free.card := by
  rw [←visited_length vertex next s l,
    ←List.toFinset_card_of_nodup (visited_nodup vertex next hl)]
  exact Finset.card_le_card (fun v hv =>
    visited_mem_domain vertex next hl v (List.mem_toFinset.mp hv))

lemma terminal_append (next : S → Bool → S) (s : S) (l m : List Bool) :
    terminal next s (l++m) = terminal next (terminal next s l) m := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => exact ih _

omit [DecidableEq V] in
lemma visited_append (vertex : S → V) (next : S → Bool → S) (s : S) (l m : List Bool) :
    visited vertex next s (l++m) =
      visited vertex next s l ++ visited vertex next (terminal next s l) m := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp only [List.cons_append,visited,ih,terminal]

omit [DecidableEq V] in
lemma visited_head (vertex : S → V) (next : S → Bool → S) (s : S) (l : List Bool)
    (hl : l ≠ []) : (visited vertex next s l).head? = some (vertex s) := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b l => rfl

 

lemma mem_leaves_iff (vertex : S → V) (next : S → Bool → S) (D : Finset V)
    (s : S) (l : List Bool) :
    l ∈ leaves vertex next D s ↔
      (visited vertex next s l).Nodup ∧
      (∀ v ∈ visited vertex next s l, v ∈ D) ∧
      (vertex (terminal next s l) ∉ D ∨
        vertex (terminal next s l) ∈ visited vertex next s l) := by
  induction l generalizing D s with
  | nil => simp [nil_mem_iff,visited,terminal]
  | cons b l ih =>
    rw [cons_mem_iff,ih]
    simp only [visited,List.nodup_cons,List.mem_cons,forall_eq_or_imp,terminal]
    constructor
    · rintro ⟨hs,hn,hm,ht⟩
      have hnot : vertex s ∉ visited vertex next (next s b) l := by
        intro hv
        exact Finset.notMem_erase _ _ (hm _ hv)
      refine ⟨⟨hnot,hn⟩,⟨hs,fun v hv => Finset.mem_of_mem_erase (hm v hv)⟩,?_⟩
      rcases ht with ht | ht
      · by_cases he : vertex (terminal next (next s b) l)=vertex s
        · exact Or.inr (Or.inl he)
        · exact Or.inl (fun hd => ht (Finset.mem_erase.mpr ⟨he,hd⟩))
      · exact Or.inr (Or.inr ht)
    · rintro ⟨⟨hnot,hn⟩,⟨hs,hm⟩,ht⟩
      refine ⟨hs,hn,fun v hv =>Finset.mem_erase.mpr ⟨?_,hm v hv⟩,?_⟩
      · exact fun he =>hnot (he ▸ hv)
      · rcases ht with ht | he | ht
        · exact Or.inl (fun hd =>ht (Finset.mem_of_mem_erase hd))
        · exact Or.inl (fun hd =>(Finset.mem_erase.mp hd).1 he)
        · exact Or.inr ht

 

lemma terminal_outside_or_collision (vertex : S → V) (next : S → Bool → S)
    {free : Finset V} {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    vertex (terminal next s l) ∉ free ∨
      vertex (terminal next s l) ∈ visited vertex next s l := by
  induction l generalizing free s with
  | nil => exact Or.inl ((nil_mem_iff vertex next free s).mp hl)
  | cons b l ih =>
    obtain ⟨hs,hl⟩ := (cons_mem_iff vertex next free s b l).mp hl
    rcases ih hl with ht | ht
    · by_cases hf : vertex (terminal next (next s b) l) ∈ free
      · right
        apply List.mem_cons.mpr
        left
        by_contra hn
        exact ht (Finset.mem_erase.mpr ⟨hn,hf⟩)
      · exact Or.inl hf
    · exact Or.inr (List.mem_cons_of_mem _ ht)

lemma terminal_mem_domain_iff_collision (vertex : S → V) (next : S → Bool → S)
    {free : Finset V} {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    vertex (terminal next s l) ∈ free ↔
      vertex (terminal next s l) ∈ visited vertex next s l := by
  refine ⟨fun h => (terminal_outside_or_collision vertex next hl).resolve_left (not_not.mpr h),
    visited_mem_domain vertex next hl _⟩

def exitMass (vertex : S → V) (next : S → Bool → S) (w : Bool → ℂ)
    (D : Finset V) (s : S) : ℂ :=
  ∑ l ∈ (leaves vertex next D s).filter (fun l => vertex (terminal next s l) ∉ D), wordWeight w l

def collisionMass (vertex : S → V) (next : S → Bool → S) (w : Bool → ℂ)
    (D : Finset V) (s : S) : ℂ :=
  ∑ l ∈ (leaves vertex next D s).filter (fun l => vertex (terminal next s l) ∈ D), wordWeight w l

 

theorem exit_add_collision (vertex : S → V) (next : S → Bool → S) (w : Bool → ℂ)
    (hw : w false + w true = 1) (D : Finset V) (s : S) :
    exitMass vertex next w D s + collisionMass vertex next w D s = 1 := by
  have h := Finset.sum_filter_add_sum_filter_not
    (leaves vertex next D s) (fun l => vertex (terminal next s l) ∉ D) (wordWeight w)
  simp only [not_not] at h
  exact h.trans (mass_one vertex next w hw D s)

end
end CriticalStrip.FiniteBranchTree

 

 

 

namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped BigOperators Classical
open FiniteBranchTree

abbrev Vertex := ℤ × ℤ × Bool
abbrev State := Vertex × Fin 3

def neighbor (v : Vertex) (p : Fin 3) : Vertex :=
  if v.2.2 then
    if p = 0 then (v.1,v.2.1-1,false)
    else if p = 1 then (v.1-1,v.2.1,false) else (v.1,v.2.1,false)
  else
    if p = 0 then (v.1,v.2.1+1,true)
    else if p = 1 then (v.1+1,v.2.1,true) else (v.1,v.2.1,true)

lemma neighbor_reverse (v : Vertex) (p : Fin 3) : neighbor (neighbor v p) p = v := by
  rcases v with ⟨i,j,b⟩
  cases b <;> fin_cases p <;> simp [neighbor]

lemma neighbor_ne (v : Vertex) (p : Fin 3) : neighbor v p ≠ v := by
  rcases v with ⟨i,j,b⟩
  cases b <;> fin_cases p <;> simp [neighbor]

lemma neighbor_injective (v : Vertex) : Function.Injective (neighbor v) := by
  rcases v with ⟨i,j,b⟩
  intro p q h
  cases b <;> fin_cases p <;> fin_cases q <;> simp_all [neighbor,Prod.mk.injEq] <;> omega

 

def outgoing (p : Fin 3) (b : Bool) : Fin 3 := if b then p+1 else p+2

def next (s : State) (b : Bool) : State :=
  let q := outgoing s.2 b
  (neighbor s.1 q,q)

lemma outgoing_ne (p : Fin 3) (b : Bool) : outgoing p b ≠ p := by
  cases b <;> fin_cases p <;> decide

lemma outgoing_injective (p : Fin 3) : Function.Injective (outgoing p) := by
  intro b c h
  cases b <;> cases c <;> fin_cases p <;> simp_all [outgoing]

lemma outgoing_exhaust (p q : Fin 3) (h : q ≠ p) : ∃! b : Bool, outgoing p b = q := by
  fin_cases p <;> fin_cases q <;> simp_all [outgoing,ExistsUnique]

lemma next_ne (s : State) (b : Bool) : (next s b).1 ≠ s.1 := neighbor_ne _ _

lemma next_back (s : State) (b : Bool) : neighbor (next s b).1 (next s b).2 = s.1 :=
  neighbor_reverse _ _

lemma next_not_back (s : State) (b : Bool) : (next s b).1 ≠ neighbor s.1 s.2 := by
  exact fun h => outgoing_ne s.2 b (neighbor_injective s.1 h)

lemma next_injective (s : State) : Function.Injective (fun b => (next s b).1) := by
  intro b c h
  exact outgoing_injective s.2 (neighbor_injective s.1 h)

 
def sign (b : Bool) : ℤ := if b then 1 else -1

def turn : List Bool → ℤ
  | [] => 0
  | b::l => sign b + turn l

def factor (b : Bool) : ℂ := (rho : ℂ) * Diagram.phase ^ sign b

lemma factor_add : factor false + factor true = 1 := by
  have hc := Diagram.phase_cosine (1:ℤ)
  simp only [zpow_one,Int.cast_one,one_mul] at hc
  change (Diagram.phase + Diagram.phase⁻¹)/2 = (C:ℂ) at hc
  have hr := congrArg (fun x : ℝ => (x : ℂ)) two_C_mul_rho
  push_cast at hr
  dsimp [factor,sign]
  simp only [zpow_one,zpow_neg_one]
  linear_combination 2 * (rho:ℂ) * hc + hr

lemma wordWeight_eq (l : List Bool) :
    wordWeight factor l = (rho : ℂ)^l.length * Diagram.phase ^ turn l := by
  induction l with
  | nil => simp [wordWeight,turn]
  | cons b l ih =>
    simp only [wordWeight_cons,ih,List.length_cons,turn,factor,pow_succ,
      zpow_add₀ Diagram.phase_ne_zero]
    ring

lemma phase_norm : ‖Diagram.phase‖ = 1 := by
  simp [Diagram.phase,Complex.norm_exp]

lemma wordWeight_norm (l : List Bool) : ‖wordWeight factor l‖ = rho^l.length := by
  rw [wordWeight_eq,norm_mul,norm_pow,norm_zpow,phase_norm,one_zpow,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos rho_pos]

 
def words (D : Finset Vertex) (s : State) : Finset (List Bool) := leaves Prod.fst next D s

theorem finite_tree_mass (D : Finset Vertex) (s : State) :
    ∑ l ∈ words D s, (rho:ℂ)^l.length * Diagram.phase^turn l = 1 := by
  simp_rw [←wordWeight_eq]
  exact mass_one Prod.fst next factor factor_add D s

theorem exit_plus_collision (D : Finset Vertex) (s : State) :
    exitMass Prod.fst next factor D s + collisionMass Prod.fst next factor D s = 1 :=
  exit_add_collision Prod.fst next factor factor_add D s

 
def embedTriangle (v : Triangle) : Vertex := (v.1,(v.2.1:ℤ),v.2.2)

lemma embedTriangle_injective : Function.Injective embedTriangle := by
  rintro ⟨i,j,b⟩ ⟨k,l,c⟩ h
  simp only [embedTriangle,Prod.mk.injEq] at h
  obtain ⟨rfl,hj,rfl⟩ := h
  congr
  exact_mod_cast hj

lemma adjacent_iff (v w : Triangle) :
    adjacent v w ↔ ∃ p : Fin 3, neighbor (embedTriangle v) p = embedTriangle w := by
  rcases v with ⟨i,j,b⟩
  rcases w with ⟨k,l,c⟩
  cases b <;> cases c <;>
    simp [adjacent,upDownAdjacent,neighbor,embedTriangle,Fin.exists_fin_succ] <;> omega

 
lemma visited_chain (s : State) (l : List Bool) :
    (visited Prod.fst next s l).IsChain (fun v w => ∃ p, neighbor v p=w) := by
  induction l generalizing s with
  | nil => simp [visited]
  | cons b l ih =>
    cases l with
    | nil => simp [visited]
    | cons c l =>
      apply List.isChain_cons_cons.mpr
      exact ⟨⟨outgoing s.2 b,rfl⟩,ih _⟩

 

def direction (s : State) : ZMod 6 := (if s.1.2.2 then 0 else 3) - 2 * s.2.val

lemma direction_next (s : State) (b : Bool) :
    direction (next s b) = direction s + (sign b : ZMod 6) := by
  rcases s with ⟨⟨i,j,c⟩,p⟩
  cases c <;> cases b <;> fin_cases p <;> norm_num [direction,next,outgoing,neighbor,sign,Fin.add_def,Fin.ext_iff] <;> decide

lemma direction_terminal (s : State) (l : List Bool) :
    direction (terminal next s l) = direction s + (turn l : ZMod 6) := by
  induction l generalizing s with
  | nil => simp [terminal,turn]
  | cons b l ih => simp only [terminal,ih,direction_next,turn,Int.cast_add,add_assoc]


 

 

 


 
def back (s : State) : State := (neighbor s.1 s.2,s.2)

@[simp] lemma back_back (s : State) : back (back s) = s := by
  simp only [back,neighbor_reverse]

@[simp] lemma back_next (s : State) (b : Bool) :
    back (next s b) = (s.1,outgoing s.2 b) := by
  simp only [back,next,neighbor_reverse]

lemma outgoing_opp (p : Fin 3) (b : Bool) : outgoing (outgoing p b) (!b) = p := by
  cases b <;> fin_cases p <;> decide

lemma next_back_next (s : State) (b : Bool) :
    next (back (next s b)) (!b) = back s := by
  rw [back_next]
  simp only [next,outgoing_opp,back]

 
def reverseTurns (l : List Bool) : List Bool := l.reverse.map Bool.not

lemma reverseTurns_involutive (l : List Bool) : reverseTurns (reverseTurns l) = l := by
  simp only [reverseTurns,←List.map_reverse,List.reverse_reverse,List.map_map]
  simp [Function.comp_def]

lemma terminal_reverseTurns (s : State) (l : List Bool) :
    terminal next (back (terminal next s l)) (reverseTurns l) = back s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    simp only [reverseTurns,List.reverse_cons,List.map_append,List.map_singleton,terminal,
      terminal_append]
    change terminal next (terminal next (back (terminal next (next s b) l))
      (reverseTurns l)) [!b] = _
    rw [ih]
    exact next_back_next s b

lemma visited_reverseTurns (s : State) (l : List Bool) :
    visited Prod.fst next (back (terminal next s l)) (reverseTurns l) =
      (visited Prod.fst next s l).reverse := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    simp only [reverseTurns,List.reverse_cons,List.map_append,List.map_singleton,terminal,
      visited_append]
    change visited Prod.fst next (back (terminal next (next s b) l)) (reverseTurns l) ++
      visited Prod.fst next (terminal next (back (terminal next (next s b) l))
        (reverseTurns l)) [!b] = _
    rw [ih,terminal_reverseTurns]
    simp only [visited,back_next,List.reverse_cons]

lemma turn_append (l m : List Bool) : turn (l++m)=turn l+turn m := by
  induction l with
  | nil => simp [turn]
  | cons b l ih => simp only [List.cons_append,turn,ih,add_assoc]

lemma sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> decide

lemma turn_reverse (l : List Bool) : turn l.reverse = turn l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.reverse_cons,turn_append,ih,turn,zero_add,add_comm]

lemma turn_map_not (l : List Bool) : turn (l.map Bool.not) = -turn l := by
  induction l with
  | nil => simp [turn]
  | cons b l ih => simp only [List.map_cons,turn,sign_not,ih,neg_add]

lemma turn_reverseTurns (l : List Bool) : turn (reverseTurns l) = -turn l := by
  rw [reverseTurns,turn_map_not,turn_reverse]

 

def reverseCycle : List Bool → List Bool
  | [] => []
  | b::l => (!b)::reverseTurns l

lemma reverseCycle_involutive (l : List Bool) : reverseCycle (reverseCycle l) = l := by
  cases l with
  | nil => rfl
  | cons b l => simp only [reverseCycle,reverseTurns_involutive,Bool.not_not]

lemma reverseCycle_length (l : List Bool) : (reverseCycle l).length=l.length := by
  cases l <;> simp [reverseCycle,reverseTurns]

lemma turn_reverseCycle (l : List Bool) : turn (reverseCycle l) = -turn l := by
  cases l with
  | nil => simp [reverseCycle,turn]
  | cons b l => simp only [reverseCycle,turn,sign_not,turn_reverseTurns,neg_add]

lemma reverseCycle_ne {l : List Bool} (hl : l ≠ []) : reverseCycle l ≠ l := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b l => cases b <;> simp [reverseCycle]

lemma third_port (p q : Fin 3) (b : Bool) (h₀ : q ≠ p) (h₁ : q ≠ outgoing p b) :
    q = outgoing p (!b) := by
  cases b <;> fin_cases p <;> fin_cases q <;> simp_all [outgoing]

lemma reverseCycle_first_step (s : State) (b : Bool) (l : List Bool)
    (hcycle : (terminal next s (b::l)).1=s.1)
    (h₀ : (terminal next s (b::l)).2 ≠ s.2)
    (h₁ : (terminal next s (b::l)).2 ≠ outgoing s.2 b) :
    next s (!b) = back (terminal next (next s b) l) := by
  have hq := third_port s.2 (terminal next s (b::l)).2 b h₀ h₁
  change next s (!b) = back (terminal next s (b::l))
  simp only [next,back,hcycle,hq]

lemma terminal_reverseCycle (s : State) (b : Bool) (l : List Bool)
    (hcycle : (terminal next s (b::l)).1=s.1)
    (h₀ : (terminal next s (b::l)).2 ≠ s.2)
    (h₁ : (terminal next s (b::l)).2 ≠ outgoing s.2 b) :
    terminal next s (reverseCycle (b::l)) = (s.1,outgoing s.2 b) := by
  simp only [reverseCycle,terminal]
  rw [reverseCycle_first_step s b l hcycle h₀ h₁,terminal_reverseTurns,back_next]

lemma visited_reverseCycle (s : State) (b : Bool) (l : List Bool)
    (hcycle : (terminal next s (b::l)).1=s.1)
    (h₀ : (terminal next s (b::l)).2 ≠ s.2)
    (h₁ : (terminal next s (b::l)).2 ≠ outgoing s.2 b) :
    visited Prod.fst next s (reverseCycle (b::l)) =
      s.1 :: (visited Prod.fst next (next s b) l).reverse := by
  simp only [reverseCycle,visited]
  rw [reverseCycle_first_step s b l hcycle h₀ h₁,visited_reverseTurns]

 

lemma visited_reverseCycle_perm (s : State) (b : Bool) (l : List Bool)
    (hcycle : (terminal next s (b::l)).1=s.1)
    (h₀ : (terminal next s (b::l)).2 ≠ s.2)
    (h₁ : (terminal next s (b::l)).2 ≠ outgoing s.2 b) :
    (visited Prod.fst next s (reverseCycle (b::l))).Perm
      (visited Prod.fst next s (b::l)) := by
  rw [visited_reverseCycle s b l hcycle h₀ h₁]
  exact (List.reverse_perm _).cons s.1

 

lemma prefix_reverseCycle_mem (D : Finset Vertex) (s : State) (stem : List Bool)
    (b : Bool) (l : List Bool) (hl : stem++b::l ∈ words D s)
    (hcycle : (terminal next s (stem++b::l)).1=(terminal next s stem).1)
    (h₀ : (terminal next s (stem++b::l)).2 ≠ (terminal next s stem).2)
    (h₁ : (terminal next s (stem++b::l)).2 ≠ outgoing (terminal next s stem).2 b) :
    stem++reverseCycle (b::l) ∈ words D s := by
  simp only [terminal_append] at hcycle h₀ h₁
  have hp := visited_reverseCycle_perm (terminal next s stem) b l hcycle h₀ h₁
  have hperm : (visited Prod.fst next s (stem++reverseCycle (b::l))).Perm
      (visited Prod.fst next s (stem++b::l)) := by
    rw [visited_append,visited_append]
    exact List.Perm.append_left _ hp
  obtain ⟨hn,hm,_⟩ := (mem_leaves_iff Prod.fst next D s (stem++b::l)).mp hl
  apply (mem_leaves_iff Prod.fst next D s _).mpr
  refine ⟨hperm.nodup_iff.mpr hn,fun v hv =>hm v (hperm.mem_iff.mp hv),?_⟩
  right
  rw [terminal_append,terminal_reverseCycle _ b l hcycle h₀ h₁,visited_append]
  apply List.mem_append_right
  simp only [visited_reverseCycle _ b l hcycle h₀ h₁,List.mem_cons,true_or]

 

lemma phase_cancel {a : ℤ} (ha : a % 8 = 4) : Diagram.phase ^ a + Diagram.phase ^ (-a) = 0 := by
  have hdecomp : a = 8*(a/8)+4 := by omega
  have h16 : Diagram.phase ^ (16:ℤ) = 1 := by
    norm_cast
    rw [show (16:ℕ)=8*2 by rfl,pow_mul,Diagram.phase_eight]
    norm_num
  have h8 : Diagram.phase ^ (8:ℤ) = -1 := by exact_mod_cast Diagram.phase_eight
  have hp : (Diagram.phase ^ a)^2 = -1 := by
    rw [←zpow_natCast,←zpow_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show a*2=16*(a/8)+8 by omega,zpow_add₀ Diagram.phase_ne_zero,
      zpow_mul,h16,one_zpow,h8,one_mul]
  rw [zpow_neg]
  have hn := zpow_ne_zero a Diagram.phase_ne_zero
  apply (mul_right_cancel₀ hn)
  rw [add_mul,zero_mul,inv_mul_cancel₀ hn,←pow_two,hp]
  exact neg_add_cancel 1

 

lemma cycle_weight_cancel (stem cycle : List Bool) (hturn : turn cycle % 8 = 4) :
    wordWeight factor (stem++cycle) + wordWeight factor (stem++reverseCycle cycle) = 0 := by
  simp only [wordWeight_eq,List.length_append,reverseCycle_length,turn_append,turn_reverseCycle]
  rw [zpow_add₀ Diagram.phase_ne_zero,zpow_add₀ Diagram.phase_ne_zero]
  have h := phase_cancel hturn
  calc
    _ = (rho:ℂ)^(stem.length+cycle.length)*Diagram.phase^turn stem *
      (Diagram.phase^turn cycle + Diagram.phase^(-turn cycle)) := by ring
    _ = 0 := by rw [h,mul_zero]

end
end CriticalStrip.HoneycombBranch

end OAI
