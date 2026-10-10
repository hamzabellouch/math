import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Score

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.SearchTree
open FiniteProduct

variable {E R : Type*}

def weightedSum (a : E → ℝ) (p : ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then a e*(1-p)+weightedSum a p r ω
      else -a e*p+weightedSum a p l ω

def quadraticCost (a : E → ℝ) : SearchTree E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => (a e)^2 + if ω e then quadraticCost a r ω else quadraticCost a l ω

def takeQuadratic (a : E → ℝ) : SearchTree E R → ℝ → SearchTree E Unit
  | .done _, _ => .done ()
  | .ask e l r, B => if (a e)^2 ≤ B then
      .ask e (takeQuadratic a l (B-(a e)^2)) (takeQuadratic a r (B-(a e)^2))
      else .done ()

lemma quadraticCost_nonneg (a : E → ℝ) (t : SearchTree E R) (ω : E → Prop) :
    0 ≤ t.quadraticCost a ω := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    simp only [quadraticCost]
    split_ifs <;> positivity

lemma takeQuadratic_valid [DecidableEq E] (a : E → ℝ) (t : SearchTree E R)
    (B : ℝ) (used : Finset E) (ht : t.Valid used) : (t.takeQuadratic a B).Valid used := by
  induction t generalizing B used with
  | done r => trivial
  | ask e l r hl hr =>
    simp only [takeQuadratic]
    split_ifs
    · exact ⟨ht.1,hl _ _ ht.2.1,hr _ _ ht.2.2⟩
    · trivial

lemma takeQuadratic_cost_le (a : E → ℝ) (t : SearchTree E R) {B : ℝ} (hB : 0≤B)
    (ω : E → Prop) : (t.takeQuadratic a B).quadraticCost a ω ≤ B := by
  induction t generalizing B with
  | done r => exact hB
  | ask e l r hl hr =>
    simp only [takeQuadratic]
    split_ifs with ha
    · have hB' : 0≤B-(a e)^2 := sub_nonneg.mpr ha
      simp only [quadraticCost]
      split_ifs
      · linarith [hr hB']
      · linarith [hl hB']
    · exact hB

lemma takeQuadratic_sum_eq (a : E → ℝ) (p : ℝ) (t : SearchTree E R)
    (B : ℝ) (ω : E → Prop) (h : t.quadraticCost a ω ≤ B) :
    (t.takeQuadratic a B).weightedSum a p ω = t.weightedSum a p ω := by
  induction t generalizing B with
  | done r => rfl
  | ask e l r hl hr =>
    have ha : (a e)^2 ≤ B := by
      simp only [quadraticCost] at h
      split_ifs at h <;> linarith [quadraticCost_nonneg a l ω,quadraticCost_nonneg a r ω]
    simp only [takeQuadratic,ite_eq_left ha,weightedSum]
    split_ifs with he
    · rw [hr]
      simp only [quadraticCost,ite_eq_left he] at h
      linarith
    · rw [hl]
      simp only [quadraticCost,ite_eq_right he] at h
      linarith

lemma fourthPotential_step (x a B δ : ℝ) (hB : a^2≤B) (hδ : δ^2≤a^2) :
    (x+δ)^4 + 7*(B-a^2)*(x+δ)^2 + 5*(B-a^2)^2 ≤
      x^4+7*B*x^2+5*B^2+(4*x^3+14*(B-a^2)*x)*δ := by
  have h4 : δ^4≤a^4 := by nlinarith [sq_nonneg (δ^2-a^2),sq_nonneg δ,sq_nonneg a]
  have hxx := mul_le_mul_of_nonneg_left hδ (sq_nonneg x)
  have hb := mul_le_mul_of_nonneg_left hδ (sub_nonneg.mpr hB)
  have hba := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hB)
  nlinarith [sq_nonneg (x*δ-2*δ^2)]

variable [Fintype E] [DecidableEq E]

lemma expected_takeQuadratic_fourth_shift (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B) (x : ℝ) :
    expect w (fun ω => (x+(t.takeQuadratic a B).weightedSum a p ω)^4) ≤
      x^4+7*B*x^2+5*B^2 := by
  induction t generalizing used w B x with
  | done r =>
    simp only [takeQuadratic,weightedSum,add_zero,expect_const w hw]
    nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg x)]
  | ask e l r hl hr =>
    by_cases ha : (a e)^2≤B
    · have hB' : 0≤B-(a e)^2 := sub_nonneg.mpr ha
      have h0 := hl _ ht.2.1 (pin w e False) (pin_normalized w hw e False)
        (pin_nonneg w hn e False) (LazyDFS.fresh_pin w p used hf e False) _ hB' (x-a e*p)
      have h1 := hr _ ht.2.2 (pin w e True) (pin_normalized w hw e True)
        (pin_nonneg w hn e True) (LazyDFS.fresh_pin w p used hf e True) _ hB' (x+a e*(1-p))
      have he := hf e ht.1
      have hp0 : 0≤1-p^2 := by nlinarith [hp.1,hp.2]
      have hp1 : 0≤1-(1-p)^2 := by nlinarith [hp.1,hp.2]
      have hδ0 : (-a e*p)^2≤(a e)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (a e)) hp0]
      have hδ1 : (a e*(1-p))^2≤(a e)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (a e)) hp1]
      have g0 := fourthPotential_step x (a e) B (-a e*p) ha hδ0
      have g1 := fourthPotential_step x (a e) B (a e*(1-p)) ha hδ1
      have heq : (fun ω => (x+((.ask e l r : SearchTree E R).takeQuadratic a B).weightedSum a p ω)^4) =
          (fun ω => if ω e then ((x+a e*(1-p))+(r.takeQuadratic a (B-(a e)^2)).weightedSum a p ω)^4
            else ((x-a e*p)+(l.takeQuadratic a (B-(a e)^2)).weightedSum a p ω)^4) := by
        funext ω
        simp only [takeQuadratic,ite_eq_left ha,weightedSum]
        split_ifs <;> congr 1 <;> ring
      rw [heq]
      erw [expect_prop_ite]
      rw [he.1,he.2]
      have h0' := mul_le_mul_of_nonneg_left (h0.trans (by simpa only [sub_eq_add_neg,neg_mul] using g0))
        (sub_nonneg.mpr hp.2)
      have h1' := mul_le_mul_of_nonneg_left (h1.trans g1) hp.1
      nlinarith
    · simp only [takeQuadratic,ite_eq_right ha,weightedSum,add_zero,expect_const w hw]
      nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg x)]

lemma expected_takeQuadratic_fourth (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B) :
    expect w (fun ω => ((t.takeQuadratic a B).weightedSum a p ω)^4) ≤ 5*B^2 := by
  simpa using expected_takeQuadratic_fourth_shift a t used ht p hp w hw hn hf B hB 0

end CriticalPercolation.SearchTree
end
end

end OAI
