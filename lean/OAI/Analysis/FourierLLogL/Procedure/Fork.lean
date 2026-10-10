import OAI.Analysis.FourierLLogL.Procedure.Tree

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene

variable {M J j : ℕ} {s : Scene M}
open scoped Classical

namespace Scene

/-- Absolute mass in the common top grid -/
def weight (s : Scene M) := s.here.len * s.mass
def insideW (s : Scene M) (x : Grid M) : ℝ :=
    if x∈s.here.block M then s.wage x else 0
def weightE (s : Scene M) (f : Grid M → ℝ) : ℝ :=
    expU fun x => s.insideW x * f x

lemma mass_actor {s : Scene M} (hp : s.here.ok M) (hh : 0 ≤ s.wage) (x : Grid M) :
    s.mass * s.actor x = s.here.dice M x * s.wage x := by
  rcases eq_or_lt_of_le (avg_nonneg s.here (fun x _ => hh x)) with h|h
  · change 0=s.mass at h; rw [← h,zero_mul]
    unfold mass at h
    rw [avg_ex hp,Ex] at h
    have H (x) : 0 ≤ s.here.dice M x*s.wage x := mul_nonneg ((s.here.dice M).nonneg _) (hh _)
    exact (H x).antisymm (le_trans (Finset.single_le_sum (fun i _ => H i) (Finset.mem_univ _)) h.ge)
  · rw [actor_def hp hh h x,wt]; unfold mass; field_simp

lemma actor_weight {s : Scene M} (hp : s.here.ok M) (hh : 0 ≤ s.wage) (x : Grid M) :
    s.weight * s.actor x = side M * s.insideW x := by
  rw [weight,mul_assoc,mass_actor hp hh,dice_apply hp,insideW]; split_ifs
  · field_simp [s.here.len_pos.ne']
  ring

lemma Ex_weight {s : Scene M} (hp : s.here.ok M) (hh : 0 ≤ s.wage) (g : Grid M → ℝ) :
    s.weight * s.actor.Ex g = s.weightE g := by
  simp_rw [Ex,Finset.mul_sum,← mul_assoc,actor_weight hp hh,weightE,expU,smul_eq_mul,
    Finset.mul_sum,mul_assoc]

lemma weight_pos {s : Scene M} : 0 < s.weight ↔ 0 < s.mass :=
  mul_pos_iff_of_pos_left s.here.len_pos

lemma actor_reset (s : Scene M) : s.reset.actor = s.actor := rfl
lemma actor_out (s : Scene M) : s.out.actor = s.actor := rfl

end Scene

/-- Binary choices, left/right normalized. -/
structure Fork (M : ℕ) where
  src : Scene M
  dst : Bool → Scene M
  bit : Grid M → Bool

namespace Fork

def probs (s : Fork M) : Law Bool := s.src.actor.send s.bit

/-- Include balance even to a zero-mass destination. -/
structure TrueLaw (q : Fork M) : Prop where
  vertex : 0 < q.src.weight
  law : ∀ b x, (q.dst b).weight * (q.dst b).actor x =
    if q.bit x=b then q.src.weight * q.src.actor x else 0

def step (s : Scene M) : Fork M :=
  { src := s
    dst := s.smaller
    bit := fun x => decide (x ∈ s.here.R.block M) }

def toss (s : Scene M) (u : Update j M s.here) : Fork M :=
  { src := s
    dst := fun b => if b then s.win u else s.lose u
    bit := fun x => decide (u.take s.fund.mood x) }

lemma step_true {s : Scene M} (hp : s.here.valid) (he : s.here.lev < M) (hh : 0 ≤ s.wage)
    (hm : 0 < s.mass) : (step s).TrueLaw := by
  constructor
  · exact weight_pos.mpr hm
  intro b x
  have h1 := child_ok s.here hp he b
  have h2 : s.here.ok M := ⟨hp,he.le⟩
  change (s.smaller b).weight * (s.smaller b).actor x =
    if decide (x ∈ s.here.R.block M)=b then _ else 0
  rw [actor_weight (s:=s.smaller b) h1 hh, show (step s).src=s from rfl, actor_weight h2 hh]
  unfold insideW
  change (side M * if x∈(s.here.child b).block M then s.wage x else 0) =
    if decide (x ∈ s.here.R.block M) = b then _ else _
  rw [block_union s.here]
  have heq : x∈s.here.L.block M → x∈s.here.R.block M → False := fun ha hb => Set.disjoint_left.mp (s.here.block_separate M) ha hb
  cases b <;> by_cases H : x∈s.here.L.block M <;> by_cases H' : x∈s.here.R.block M <;>
    simp_all [child]

lemma toss_true {s : Scene M} (u : Update j M s.here)
    (hp : s.here.ok M) (hh : 0 ≤ s.wage) (hm : 0 < s.mass) :
    (toss s u).TrueLaw := by
  constructor
  · exact weight_pos.mpr hm
  intro b x
  have hX := split_pos u hh
  have he :
      (s.win u).weight*(s.win u).actor x = side M*(s.win u).insideW x :=
    actor_weight (s:=s.win u) hp hX.2.1 x
  have he' : (s.lose u).weight*(s.lose u).actor x = side M*(s.lose u).insideW x :=
    actor_weight (s:=s.lose u) hp hX.1.1 x
  cases b <;>
    simp only [toss,Bool.false_eq_true, ↓reduceIte,he,he',actor_weight hp hh]
  all_goals
    by_cases H : u.take s.fund.mood x <;> by_cases H' : x∈s.here.block M <;>
      simp_all [insideW, win,lose]

variable {v : Fork M}

lemma balance (h : v.TrueLaw) (b : Bool) :
    (v.dst b).weight = v.src.weight * v.probs b := by
  rw [probs,send_apply,prob_eq,Finset.mul_sum]
  calc
    _ = ∑ x, (v.dst b).weight * (v.dst b).actor x := by
      rw [← Finset.mul_sum,(v.dst b).actor.total]; simp
    _ = _ := by simp only [h.law, mul_ite,mul_zero]

lemma local_law (h : v.TrueLaw) (b : Bool) (x : Grid M) :
    v.probs b * (v.dst b).actor x = if v.bit x=b then v.src.actor x else 0 := by
  have H := h.law b x; rw [balance h b,mul_assoc] at H
  apply mul_left_cancel₀ h.vertex.ne'
  split_ifs at H ⊢ with hi <;> simpa [hi] using H

lemma expect_bit (h : v.TrueLaw) (f : Bool → Grid M → ℝ) :
    v.probs.Ex (fun b => (v.dst b).actor.Ex (f b)) =
      v.src.actor.Ex fun x => f (v.bit x) x := by
  unfold Ex
  simp_rw [Finset.mul_sum,← mul_assoc,local_law h,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma true_mass (h : v.TrueLaw) {b : Bool} :
    0 < v.probs b ↔ 0 < (v.dst b).mass := by
  rw [← weight_pos,balance h b,mul_pos_iff_of_pos_left h.vertex]

lemma branch_pos (h : v.TrueLaw) {x : Grid M} (hh : 0 < v.src.actor x) :
    0 < v.probs (v.bit x) ∧ 0 < (v.dst (v.bit x)).actor x := by
  have H := local_law h (v.bit x) x
  rw [ite_eq_left rfl] at H
  have He : 0 < v.probs (v.bit x) * (v.dst (v.bit x)).actor x := H.symm ▸ hh
  exact ⟨pos_of_mul_pos_left He ((v.dst _).actor.nonneg _),
    pos_of_mul_pos_right He (v.probs.nonneg _)⟩

lemma step_mass {s : Scene M} (h : (step s).TrueLaw) (b : Bool) :
    (s.smaller b).mass = 2*((step s).probs b)*s.mass := by
  have H := balance h b
  change (s.here.child b).len * (s.smaller b).mass = s.here.len*s.mass* _ at H
  rw [child_len] at H; nlinarith [s.here.len_pos]

lemma toss_mass {s : Scene M} {u : Update j M s.here} (h : (toss s u).TrueLaw) (b : Bool) :
    ((toss s u).dst b).mass = (toss s u).probs b*s.mass := by
  have H := balance h b
  have hh : ((toss s u).dst b).here=s.here := by cases b <;> rfl
  rw [weight,hh,weight] at H
  apply mul_left_cancel₀ s.here.len_pos.ne'
  rw [H]
  dsimp only [toss]
  ring

lemma success_prob {s : Scene M} (u : Update j M s.here) :
    (toss s u).probs true = u.chances s.actor s.fund.mood := by
  unfold probs; rw [send_apply]; simp [toss,Update.chances]

end Fork
end FourierLLogL.Dyadic.Procedure

end OAI
