import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferTree

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma buffer_log_recurrence {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (A D : ℝ)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -D) ≤ R (n+1)) (n : ℕ) :
    Real.log (R n)+(if ω ∈ B n then A else -D) ≤ Real.log (R (n+1)) := by
  have hp : 0 < R n * Real.exp (if ω ∈ B n then A else -D) := mul_pos (hR n) (Real.exp_pos _)
  have hh := Real.log_le_log hp (hstep n)
  rwa [Real.log_mul (hR n).ne' (Real.exp_pos _).ne',Real.log_exp] at hh

lemma buffer_log_sum {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (A D : ℝ)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -D) ≤ R (n+1)) (n : ℕ) :
    Real.log (R 0) + successes B n ω*(A+D) - (n:ℝ)*D ≤ Real.log (R n) := by
  induction n with
  | zero => simp [successes]
  | succ n ih =>
    have hh := buffer_log_recurrence B ω R hR A D hstep n
    rw [successes_succ,Nat.cast_add,Nat.cast_one]
    by_cases hb : ω ∈ B n
    · simp only [ite_eq_left hb] at hh ⊢
      nlinarith
    · simp only [ite_eq_right hb] at hh ⊢
      nlinarith

lemma buffer_log_growth {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) {A s W : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -(s*A/8)) ≤ R (n+1))
    (hexcess : ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W) (n : ℕ) :
    Real.log (R 0) + (s*A/8)*(n:ℝ) - W*(A+s*A/8) ≤ Real.log (R n) := by
  have hh := buffer_log_sum B ω R hR A (s*A/8) hstep n
  have hAD : 0 ≤ A+s*A/8 := by positivity
  have hc := mul_le_mul_of_nonneg_right (hexcess n) hAD
  have hn : 0 ≤ s*s*A*(n:ℝ) := by positivity
  nlinarith

lemma buffer_stage_count {Ω : Type*} (B : ℕ → Set Ω) (ω : Ω)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) {A s W C : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hstep : ∀ n, R n * Real.exp (if ω ∈ B n then A else -(s*A/8)) ≤ R (n+1))
    (hexcess : ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W)
    (hR0 : 1 ≤ R 0) (hC : 0 < C) (n H : ℕ) (hheight : R n ≤ C*(H+1)) :
    (s*A/8)*(n:ℝ) ≤ Real.log C + Real.log ((H:ℝ)+1) + W*(A+s*A/8) := by
  have hl := buffer_log_growth B ω R hR hA hs hstep hexcess n
  have hu := Real.log_le_log (hR n) hheight
  have hH : 0 < (H:ℝ)+1 := by positivity
  rw [Real.log_mul hC.ne' hH.ne'] at hu
  have h0 := Real.log_nonneg hR0
  linarith

lemma buffer_contraction_choice {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
    0 < ε ∧ ε < 1 ∧ Real.exp (Real.log (1+α))=1+α ∧
      Real.exp (-(s*Real.log (1+α)/8))=1-ε := by
  have hA : 0 < Real.log (1+α) := Real.log_pos (by linarith)
  have hd : 0 < s*Real.log (1+α)/8 := by positivity
  have he := Real.exp_lt_one_iff.mpr (show -(s*Real.log (1+α)/8)<0 by linarith)
  have hep := Real.exp_pos (-(s*Real.log (1+α)/8))
  dsimp only
  refine ⟨by linarith,by linarith,Real.exp_log (by linarith),by ring⟩
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferCurrentNode {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (n : ℕ) : AdaptedBufferNode e :=
  bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root (bufferHistory e f hef R₀ z₀ ε α g κ H hH root ω n)

lemma bufferCurrentNode_succ {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (n : ℕ) :
    let N := bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n
    let p := bufferNodeDecision e f z₀ ε α g H N ω
    bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω (n+1) =
      bufferChildNode e f hef R₀ z₀ ε α g κ N (H N.radius) (hH N.radius) p.1 p.2 := rfl

lemma bufferNextRadius_exponential_step (R₀ r ε α A D : ℝ)
    (hα : Real.exp A=1+α) (hε : Real.exp (-D)=1-ε) (b : Bool) :
    r*Real.exp (if b then A else -D) ≤ bufferNextRadius R₀ r ε α b := by
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,bufferNextRadius,hα,hε]
  · simpa only [mul_comm] using (le_max_right R₀ ((1-ε)*r))
  · simpa only [mul_comm] using (le_max_right R₀ ((1+α)*r))

lemma bufferCurrentNode_exponential_step {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g A D : ℝ) (hα : Real.exp A=1+α) (hε : Real.exp (-D)=1-ε)
    (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (ω : Environment d) (hr : ω ∈ root.active) (n : ℕ) :
    (bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n).radius *
      Real.exp (if ω ∈ bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root n then A else -D) ≤
      (bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω (n+1)).radius := by
  rw [bufferCurrentNode_succ]
  have hb := bufferTreeSuccess_iff_decision e f hef R₀ z₀ ε α g κ H hH root ω hr n
  rw [hb]
  let N := bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n
  have he := bufferNextRadius_exponential_step R₀ N.radius ε α A D hα hε
    (bufferNodeDecision e f z₀ ε α g H N ω).2
  convert he using 1
  · congr 2
    exact congrArg (fun h : Decidable ((bufferNodeDecision e f z₀ ε α g H N ω).2=true) =>
      @ite ℝ _ h A (-D)) (Subsingleton.elim _ _)
  · rfl

lemma bufferCurrentNode_log_growth {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R₀ α s : ℝ} (hR₀ : 0 < R₀) (hα : 0 < α) (hs : 0 < s)
    (z₀ g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (hroot : root.radius=R₀) (ω : Environment d) (hr : ω ∈ root.active)
    (W : ℝ)
    (hexcess : ∀ n : ℕ, s/4*(n:ℝ)-successes
      (bufferTreeSuccess e f hef R₀ z₀ (1-Real.exp (-(s*Real.log (1+α)/8))) α g κ H hH root) n ω ≤ W)
    (n : ℕ) :
    Real.log R₀+(s*Real.log (1+α)/8)*(n:ℝ)-W*(Real.log (1+α)+s*Real.log (1+α)/8) ≤
      Real.log (bufferCurrentNode e f hef R₀ z₀ (1-Real.exp (-(s*Real.log (1+α)/8))) α g κ H hH root ω n).radius := by
  let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
  let R := fun n => (bufferCurrentNode e f hef R₀ z₀ ε α g κ H hH root ω n).radius
  have hp (n : ℕ) : 0 < R n := hR₀.trans_le
    (bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hroot.ge _)
  have hc := buffer_contraction_choice hα hs
  have he := bufferCurrentNode_exponential_step e f hef R₀ z₀ ε α g
    (Real.log (1+α)) (s*Real.log (1+α)/8) hc.2.2.1 hc.2.2.2 κ H hH root ω hr
  have hA : 0 ≤ Real.log (1+α) := (Real.log_pos (by linarith)).le
  have hh := buffer_log_growth
    (bufferTreeSuccess e f hef R₀ z₀ ε α g κ H hH root) ω R hp hA hs.le he hexcess n
  have hr0 : R 0=R₀ := hroot
  rw [hr0] at hh
  exact hh
end DirectionalTransience

end

end

end OAI
