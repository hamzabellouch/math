import Mathlib
import OAI.Combinatorics.UniformKServer.ConditionalLaw

namespace OAI

                                     
section

/-! Finite adaptive all-step accounting. This is the filtering telescope used
 twice in the allocation proof (primitive trackers and output-rule switching).
 No martingale assertion is conditioned on the later event being charged. -/
namespace UniformKServer.AdaptiveLedger
noncomputable section
open Finset UniformKServer.ConditionalLaw
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def expect (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω*X ω

def linear (a X : Ω → ι → ℝ) (ω : Ω) : ℝ := ∑ i, a ω i*X ω i

def post (w : Ω → ℝ) (F : Setoid Ω) (X : Ω → ι → ℝ) (ω : Ω) (i : ι) : ℝ :=
  posterior w F (fun v => X v i) ω

def increment (w : Ω → ℝ) (F G : Setoid Ω) (a X : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, a ω i*(post w G X ω i-post w F X ω i)

def drift (w : Ω → ℝ) (F : Setoid Ω) (a X Y : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, a ω i*(post w F Y ω i-post w F X ω i)

theorem expect_add (w : Ω → ℝ) (X Y : Ω → ℝ) :
    expect w (fun ω => X ω+Y ω)=expect w X+expect w Y := by
  simp only [expect,mul_add,sum_add_distrib]

theorem expect_sub (w : Ω → ℝ) (X Y : Ω → ℝ) :
    expect w (fun ω => X ω-Y ω)=expect w X-expect w Y := by
  simp only [expect,mul_sub,sum_sub_distrib]

theorem expect_const (w : Ω → ℝ) (C : ℝ) (hw : ∑ ω, w ω=1) :
    expect w (fun _ => C)=C := by rw [expect,←sum_mul,hw,one_mul]

theorem expect_mono {w X Y : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hXY : ∀ ω, X ω ≤ Y ω) : expect w X ≤ expect w Y :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hXY ω) (hw ω)

/-- Expected filtering vanishes for old-history coefficients even if the
 subsequent domains, stopping events and output rules are chosen adaptively. -/
theorem filtering_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F G : Setoid Ω)
    (hGF : ∀ ω v, G.r ω v → F.r ω v) (a X : Ω → ι → ℝ)
    (ha : ∀ i, measurable F (fun ω => a ω i)) :
    expect w (increment w F G a X)=0 := by
  simp only [expect,increment,mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro i _
  simpa only [post,mul_assoc] using filtering hw F G hGF (fun ω => a ω i) (fun ω => X ω i) (ha i)

/-- Hidden drift is evaluated at the new information, while old coefficient
 bounds alone suffice. The L1 contraction has coefficient one. -/
theorem drift_bound {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (F : Setoid Ω)
    (a X Y : Ω → ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ ω i, |a ω i| ≤ C) :
    expect w (drift w F a X Y) ≤ C*expect w (fun ω => ∑ i, |Y ω i-X ω i|) := by
  have hp (ω : Ω) : drift w F a X Y ω ≤ C*(∑ i, |post w F Y ω i-post w F X ω i|) := by
    unfold drift
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha ω i) (abs_nonneg _))
  refine (expect_mono hw hp).trans ?_
  have hex : expect w (fun ω => ∑ i, |post w F Y ω i-post w F X ω i|) ≤
      expect w (fun ω => ∑ i, |Y ω i-X ω i|) := by
    simp only [expect,mul_sum]
    rw [sum_comm,sum_comm (s := univ) (t := univ) (f := fun ω i => w ω*|Y ω i-X ω i|)]
    apply sum_le_sum
    intro i _
    exact expected_contraction hw F (fun ω => Y ω i) (fun ω => X ω i)
  have he (Z : Ω → ℝ) : expect w (fun ω => C*Z ω)=C*expect w Z := by
    simp only [expect,mul_sum]
    apply sum_congr rfl
    intro ω _
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hex hC

/-- Generic ledger with genuine filtering increments and hidden L1 drift.
 One-step inequalities are deterministic algorithmic obligations, not a
 substitute for an assumed competitive bound. The conclusion sums all steps. -/
theorem telescope {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (F : ℕ → Setoid Ω) (hF : ∀ t ω v, (F (t+1)).r ω v → (F t).r ω v)
    (a X : ℕ → Ω → ι → ℝ) (P M Q : ℕ → Ω → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ t ω i, |a t ω i| ≤ C)
    (hmeas : ∀ t i, measurable (F t) (fun ω => a t ω i))
    (hstep : ∀ t ω, M t ω ≤ P t ω-P (t+1) ω+
      increment w (F t) (F (t+1)) (a t) (X t) ω+
      drift w (F (t+1)) (a t) (X t) (X (t+1)) ω+Q t ω) (H : ℕ) :
    (∑ t ∈ range H, expect w (M t)) ≤ expect w (P 0)-expect w (P H)+
      C*(∑ t ∈ range H, expect w (fun ω => ∑ i, |X (t+1) ω i-X t ω i|))+
      ∑ t ∈ range H, expect w (Q t) := by
  have hs (t : ℕ) : expect w (M t) ≤ expect w (P t)-expect w (P (t+1))+
      C*expect w (fun ω => ∑ i, |X (t+1) ω i-X t ω i|)+expect w (Q t) := by
    have h := expect_mono hw (hstep t)
    rw [expect_add,expect_add,expect_add,expect_sub,filtering_zero hw _ _ (hF t) _ _ (hmeas t),add_zero] at h
    have hd := drift_bound hw (F (t+1)) (a t) (X t) (X (t+1)) hC (ha t)
    linarith
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ,sum_range_succ,sum_range_succ]
    have h := hs H
    linarith

end
end UniformKServer.AdaptiveLedger

end

end OAI
