import OAI.Analysis.FourierLLogL.Procedure.Fork

/-! # Thin parts of a grid interval -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

def reach (i : ℕ) := 80+8*i
def gateWidth (main : Bool) (i : ℕ) := (if main then side i^2 else side i) / 128

lemma reach_pos (i : ℕ) : 1 ≤ reach i := by unfold reach; omega
lemma gate_pos (main : Bool) (i : ℕ) : 0 < gateWidth main i := by unfold gateWidth; have := side_pos i; split <;> positivity

/-- all b steps child -/
def extreme (p : Node) (b : Bool) : ℕ → Node
| 0 => p
| m+1 => (extreme p b m).child b

lemma child_depth (p : Node) (b : Bool) : (p.child b).lev=p.lev+1 := by cases b <;> rfl

lemma extreme_depth (p : Node) (b : Bool) (n : ℕ) :
    (extreme p b n).lev = p.lev+n := by
  induction n with
  | zero => simp [extreme]
  | succ n ih =>
    rw [extreme,child_depth,ih, Nat.add_assoc]

lemma extreme_length (p : Node) (b : Bool) (n : ℕ) :
    (extreme p b n).len = p.len*side n := by rw [len,extreme_depth,len,side,side,side,pow_add]

lemma extreme_below (p : Node) (b : Bool) (n : ℕ) : (extreme p b n).below p := by
  induction n with
  | zero => exact below_refl p
  | succ n ih => exact below_trans (child_below _ _) ih

lemma extreme_valid (p : Node) (hp : p.valid) (b : Bool) (n : ℕ) :
    (extreme p b n).valid := by
  induction n with
  | zero => exact hp
  | succ n ih => cases b; exact (valid_L _).mpr ih; exact (valid_R _).mpr ih

lemma extreme_left (p : Node) (n : ℕ) : (extreme p false n).a=p.a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (extreme p false n).L.a=_
    rw [a_L,ih]

lemma extreme_right (p : Node) (n : ℕ) :
    (extreme p true n).a+(extreme p true n).len=p.a+p.len := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (extreme p true n).R.a+(extreme p true n).R.len=_
    rw [a_R,len_R]; linarith

/-- strips of width 2^-l p about the two edges of both children of p; empty if the strip width
needs more bits than available. -/
def strip (p : Node) (i : ℕ) (b c : Bool) :=
    extreme (child p b) c (reach i-1)

lemma strip_depth (p : Node) (i : ℕ) (b c : Bool) :
    (strip p i b c).lev = p.lev+reach i := by rw [strip,extreme_depth,child_depth]; have := reach_pos i; omega
lemma strip_valid {p : Node} (hp : p.valid) (i : ℕ) (b c : Bool) :
    (strip p i b c).valid := by
  apply extreme_valid; cases b; exact p.valid_L.mpr hp; exact p.valid_R.mpr hp
lemma strip_below_child (p : Node) (i : ℕ) (b c : Bool) :
    (strip p i b c).below (p.child b) := extreme_below _ _ _
lemma strip_below (p : Node) (i : ℕ) (b c : Bool) :
    (strip p i b c).below p := below_trans (strip_below_child _ _ _ _) (child_below _ _)

lemma strip_length (p : Node) (i : ℕ) (b c : Bool) :
    (strip p i b c).len = p.len * side (reach i) := by rw [len,strip_depth,len,side,side,side,pow_add]

def flanked (p : Node) (i : ℕ) (x : Grid M) :=
    ∃ b c, x ∈ (strip p i b c).block M

def lanes (p : Node) (i M : ℕ) := p.lev+reach i ≤ M

def edgeW (s : Scene M) (i : ℕ) :=
    if lanes s.here i M then (∑ x, if flanked s.here i x then wt s.here s.wage s.norm x else 0)
    else 0

def hazard (s : Scene M) (main : Bool) (i : ℕ) :=
    gateWidth main i ≤ edgeW s i
def surcharge (s : Scene M) (main : Bool) (i : ℕ) :=
    if hazard s main i then edgeW s i else 0

lemma surcharge_nonneg (s : Scene M) (main : Bool) (i : ℕ) :
    0 ≤ surcharge s main i := by
  unfold surcharge; split_ifs with H
  · exact (gate_pos _ _).le.trans H
  exact le_rfl

lemma flank_in {p : Node} {i : ℕ} {x : Grid M} (hi : flanked p i x) : x∈p.block M := by
  obtain ⟨u,v,h⟩ := hi
  exact block_of_below (strip_below _ _ _ _) _ h

/-- A property measurable in depth l. Does not require l≤M. -/
def spotted (p : Grid M → Prop) (l : ℕ) :=
    ∀ v : Node, v.lev=l → ∀ x∈v.block M, ∀ y∈v.block M, p x ↔ p y

lemma flanked_at (p : Node) (i : ℕ) :
    spotted (M:=M) (flanked p i) (p.lev+reach i) := by
  intro q he x hx y hy
  unfold flanked
  have Heq (b c) : x∈(strip p i b c).block M ↔ y∈(strip p i b c).block M := by
    apply coarse_const (q:=q) _ hx hy
    rw [he,strip_depth]
  simp_rw [Heq]

lemma prob_under {p q : Node} (hp : p.ok M) (hh : q.ok M) (h : q.below p) :
    (p.dice M).prob (fun x => x∈q.block M) = q.len/p.len := by
  classical
  rw [prob_eq]
  calc
    _ = p.len⁻¹*(uniform _).prob (fun x => x∈q.block M) := by
      rw [prob_eq,Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x∈q.block M
      · simp only [hx,ite_true,dice_apply hp,ite_eq_left (block_of_below h _ hx),uniform_side,mul_comm]
      simp [hx]
    _ = q.len/p.len := by rw [prob_block hh]; ring

lemma flank_prob (p : Node) (hp : p.valid) (i : ℕ) (he : lanes p i M) :
    (p.dice M).prob (flanked p i) ≤ 4 * side (reach i) := by
  let f (b c : Bool) (x : Grid M) := if x∈(strip p i b c).block M then (1:ℝ) else 0
  let Q := p.dice M
  have HF (b c) : Q.Ex (f b c) = side (reach i) := by
    have hh : (strip p i b c).ok M := ⟨strip_valid hp _ _ _,strip_depth p _ _ _ |>.symm ▸ he⟩
    have hx := prob_under (p:=p) (q:=strip p i b c)
      (show p.ok M from ⟨hp,Nat.le_trans (Nat.le_add_right _ _) he⟩) hh (strip_below _ _ _ _)
    have hy : Q.prob (fun x => x∈(strip p i b c).block M) = Q.Ex (f b c) := by rw [prob_eq]; simp [Ex,f]
    change Q.prob _ = _ at hx
    rw [hy,strip_length] at hx; rw [hx]; field_simp [p.len_pos.ne']
  unfold prob; apply le_trans (b:=Q.Ex fun x =>
    f false false x + f false true x + f true false x + f true true x)
  · apply Ex_mono; intro x
    split_ifs with H
    · obtain ⟨a,b,H⟩ := H
      cases a <;> cases b <;> unfold f <;> split_ifs <;> norm_num
    unfold f; split_ifs <;> norm_num
  · simp_rw [Ex_add,HF]; linarith

lemma hazard_rule {s : Scene M} {main : Bool} {i : ℕ} (ha : s.here.ok M)
    (hh : 0 ≤ s.wage) (hm : 0 < s.mass) (ht : ¬ s.enter) (hx : hazard s main i) :
    lanes s.here i M ∧
      s.norm/s.mass * edgeW s i = s.actor.prob (flanked s.here i) ∧
      gateWidth main i / 2 ≤ s.actor.prob (flanked s.here i) := by
  classical
  change gateWidth main i ≤ _ at hx
  have hl : lanes s.here i M := by
    by_contra hv; rw [edgeW,ite_eq_right hv] at hx
    exact (gate_pos _ _).not_ge hx
  unfold enter at ht
  have hp : 0 < s.norm := by linarith
  have he : s.norm/s.mass * edgeW s i = s.actor.prob (flanked s.here i) := by
    rw [prob_eq,edgeW,ite_eq_left hl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x h => ?_
    split_ifs with H
    · rw [actor_def ha hh hm x]
      unfold wt; unfold mass at *
      field_simp
    exact mul_zero _
  refine ⟨hl,he,?_⟩
  rw [← he]
  apply le_trans (b:=1/2*gateWidth main i) (le_of_eq (by ring))
  apply mul_le_mul _ hx (gate_pos _ _).le (by positivity)
  apply (le_div_iff₀ hm).mpr; linarith

end FourierLLogL.Dyadic.Procedure

end OAI
