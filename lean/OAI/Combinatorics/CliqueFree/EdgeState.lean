import OAI.Combinatorics.CliqueFree.FiniteEntropy
import OAI.Combinatorics.CliqueFree.WeightedGraph

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

/-- Oriented edges, the disjoint union of the neighborhood state spaces. -/
abbrev EdgeState (G : SimpleGraph V) := {e : V × V // G.Adj e.1 e.2}

noncomputable instance edgeStateFintype (G : SimpleGraph V) : Fintype (EdgeState G) :=
  Subtype.fintype _

local instance (priority := 10000) edgeStateDecEq (G : SimpleGraph V) : DecidableEq (EdgeState G) :=
  Classical.decEq _

namespace EdgeState
variable {G : SimpleGraph V}
def src (e : EdgeState G) : V := e.val.1
def dst (e : EdgeState G) : V := e.val.2
omit [Fintype V] in
@[simp] lemma adj (e : EdgeState G) : G.Adj e.src e.dst := e.property

def rev (e : EdgeState G) : EdgeState G := ⟨(e.dst, e.src), e.adj.symm⟩
omit [Fintype V] in
@[simp] lemma src_rev (e : EdgeState G) : e.rev.src = e.dst := rfl
omit [Fintype V] in
@[simp] lemma dst_rev (e : EdgeState G) : e.rev.dst = e.src := rfl
omit [Fintype V] in
@[simp] lemma rev_rev (e : EdgeState G) : e.rev.rev = e := by cases e; rfl

def revEquiv : EdgeState G ≃ EdgeState G where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

lemma sum_eq (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst) = ∑ u, ∑ v ∈ neighbors G u, f u v := by
  classical
  change (∑ e : {e : V × V // G.Adj e.1 e.2}, f e.val.1 e.val.2) = _
  rw [← Finset.sum_subtype (univ.filter fun e : V × V ↦ G.Adj e.1 e.2)
    (by simp) (fun e : V × V ↦ f e.1 e.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]

lemma sum_fiber (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if e.src = u then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  rw [sum_eq (fun a b ↦ if a = u then f b else 0)]
  simp

lemma sum_fiber' (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if u = e.src then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  simpa only [eq_comm] using sum_fiber u f

end EdgeState

lemma growth_nonneg {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) : 0 ≤ growth x s :=
  mul_nonneg hs (add_nonneg hx (le_max_left _ _))

@[simp] lemma growth_zero (x : ℝ) : growth x 0 = 0 := by simp [growth]

lemma growth_small {x s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    growth x s = s * (x - Real.log s) := by
  have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  simp [growth, Real.log_inv, max_eq_right (neg_nonneg.2 hl), sub_eq_add_neg]

lemma growth_large {x s : ℝ} (hs : 1 ≤ s) : growth x s = s * x := by
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs
  simp [growth, Real.log_inv, max_eq_left (neg_nonpos.2 hl)]

lemma growth_mono {x : ℝ} (hx : 1 ≤ x) : MonotoneOn (growth x) (Set.Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha, growth_zero]
    exact growth_nonneg (by linarith) hb
  have hb0 : 0 < b := ha.trans_le hab
  by_cases hb1 : b ≤ 1
  · rw [growth_small ha (hab.trans hb1), growth_small hb0 hb1]
    have hrel := FiniteEntropy.relTerm_nonneg ha.le hb0.le (fun _ ↦ hb0)
    rw [Real.log_div ha.ne' hb0.ne'] at hrel
    have hlog : Real.log b ≤ 0 := Real.log_nonpos hb0.le hb1
    have hmul := mul_nonneg (sub_nonneg.2 hab) (show 0 ≤ x - 1 - Real.log b by linarith)
    nlinarith
  by_cases ha1 : 1 ≤ a
  · rw [growth_large ha1, growth_large (le_of_not_ge hb1)]
    exact mul_le_mul_of_nonneg_right hab (by linarith)
  · rw [growth_small ha (le_of_not_ge ha1), growth_large (le_of_not_ge hb1)]
    have hrel := FiniteEntropy.relTerm_nonneg ha.le (by norm_num : (0:ℝ) ≤ 1)
      (fun _ ↦ by norm_num)
    simp only [div_one] at hrel
    have hamul := mul_nonneg (sub_nonneg.2 (le_of_not_ge ha1)) (show 0 ≤ x - 1 by linarith)
    have hbmul := mul_nonneg (sub_nonneg.2 (le_of_not_ge hb1)) (show 0 ≤ x by linarith)
    nlinarith

lemma growth_le_twice {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    growth x s ≤ 2 * x * (s + Real.exp (-x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hexp := Real.exp_pos (-x)
  have hi (b : ℝ) (hb : Real.exp (-x) ≤ b) : growth x b ≤ 2 * x * b := by
    have hb0 := hexp.trans_le hb
    have hl : -Real.log b ≤ x := by
      have := Real.log_le_log hexp hb
      rw [Real.log_exp] at this
      linarith
    have hmax : max 0 (-Real.log b) ≤ x := max_le hx0 hl
    simp only [growth, one_div, Real.log_inv]
    nlinarith [mul_le_mul_of_nonneg_left hmax hb0.le]
  by_cases h : Real.exp (-x) ≤ s
  · have h' := hi s h
    nlinarith [mul_nonneg hx0 hexp.le]
  · have h' := (growth_mono hx hs hexp.le (le_of_not_ge h)).trans (hi _ le_rfl)
    nlinarith [mul_nonneg hx0 hs]

omit [Fintype V] in
lemma mass_union_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A B : Finset V) :
    mass w (A ∪ B) ≤ mass w A + mass w B := by
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := w)
  have hn := mass_nonneg hw (A ∩ B)
  change 0 ≤ ∑ u ∈ A ∩ B, w u at hn
  change (∑ u ∈ A ∪ B, w u) ≤ (∑ u ∈ A, w u) + ∑ u ∈ B, w u
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI
