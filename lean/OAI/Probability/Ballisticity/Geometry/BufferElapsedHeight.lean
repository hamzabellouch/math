import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferTree

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferWordHeight : List (ℕ × Bool) → ℕ
  | [] => 0
  | p::l => p.1+1+bufferWordHeight l

lemma bufferNodeAt_level {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ z₀ ε α g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (root : AdaptedBufferNode e) (l : List (ℕ × Bool)) :
    (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).level = root.level+bufferWordHeight l := by
  induction l with
  | nil => simp [bufferNodeAt,bufferWordHeight]
  | cons p l ih =>
    change (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).level+p.1+1 = _
    rw [ih,bufferWordHeight,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    ring

lemma bufferNodeAt_radius_elapsed {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R₀ ε α M C : ℝ} (hR₀ : 0 < R₀) (hε : 0 ≤ ε) (hα : 0 ≤ α) (_ : 0 < M)
    (hC0 : R₀ ≤ C) (hC : (1+α)*M ≤ C)
    (z₀ g : ℝ) (κ : ℝ≥0) (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (hplan : ∀ r : ℝ, R₀ ≤ r → r ≤ M*(H r+1))
    (root : AdaptedBufferNode e) (hr : root.radius=R₀) (ω : Environment d)
    (l : List (ℕ × Bool))
    (ha : ω ∈ (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).active) :
    (bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l).radius ≤ C*(bufferWordHeight l+1) := by
  have hCpos : 0 < C := hR₀.trans_le hC0
  induction l with
  | nil => simpa [bufferNodeAt,bufferWordHeight,hr] using hC0
  | cons p l ih =>
    let N := bufferNodeAt e f hef R₀ z₀ ε α g κ H hH root l
    have hpa : ω ∈ N.active := ha.1
    have hb : BufferStageEvent (realPosition (step e)) f (H N.radius) z₀ N.radius ε α g (N.law ω).val ω ↔ p.2=true := ha.2.2
    have hk : bufferFirstFailure (realPosition (step e)) f N.level (z₀+(1-ε)*N.radius) g N.law (H N.radius) ω=p.1 := ha.2.1
    have hNr : R₀ ≤ N.radius := bufferNodeAt_radius e f hef R₀ z₀ ε α g κ H hH root hr.ge l
    have hn : 0 ≤ N.radius := hR₀.le.trans hNr
    have ih' := ih hpa
    change bufferNextRadius R₀ N.radius ε α p.2 ≤ C*((bufferWordHeight (p::l):ℕ)+1)
    unfold bufferNextRadius
    apply max_le
    · apply hC0.trans
      have hh : (1:ℝ) ≤ (bufferWordHeight (p::l):ℝ)+1 := by
        have := Nat.cast_nonneg (α := ℝ) (bufferWordHeight (p::l)); linarith
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hCpos.le
    · cases hp : p.2
      · simp only [Bool.false_eq_true,↓reduceIte]
        have hdec : (1-ε)*N.radius ≤ N.radius := by nlinarith
        apply hdec.trans (ih'.trans _)
        apply mul_le_mul_of_nonneg_left _ hCpos.le
        simp only [bufferWordHeight,Nat.cast_add,Nat.cast_one]
        have ht := Nat.cast_nonneg (α := ℝ) (bufferWordHeight l)
        have hk := Nat.cast_nonneg (α := ℝ) p.1
        linarith
      · simp only [↓reduceIte]
        have hE := hb.mpr hp
        have htop := (bufferStageEvent_iff_last_tests (realPosition (step e)) f N.level z₀
          N.radius ε α g N.law (hH N.radius) ω).mp hE |>.1
        have hj := bufferFirstFailure_eq_top_of_pass (realPosition (step e)) f N.level
          (z₀+(1-ε)*N.radius) g N.law (hH N.radius) ω htop
        have hkH : p.1=H N.radius := hk.symm.trans hj
        have hh := mul_le_mul_of_nonneg_left (hplan N.radius hNr) (show 0 ≤ 1+α by linarith)
        rw [←mul_assoc] at hh
        apply hh.trans
        rw [←hkH]
        have hmul := mul_le_mul_of_nonneg_right hC (show 0 ≤ (p.1:ℝ)+1 by positivity)
        apply hmul.trans
        apply mul_le_mul_of_nonneg_left _ hCpos.le
        simp only [bufferWordHeight,Nat.cast_add,Nat.cast_one]
        have ht := Nat.cast_nonneg (α := ℝ) (bufferWordHeight l)
        have hk := Nat.cast_nonneg (α := ℝ) p.1
        linarith
end DirectionalTransience

end

end

end OAI
