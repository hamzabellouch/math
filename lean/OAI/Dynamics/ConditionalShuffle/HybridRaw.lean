import OAI.Dynamics.ConditionalShuffle.CycleEnergy

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional.Hybrid

def publicHistory {d t : ℕ} (s : Fin t → Bool) (ω : History d t) : Fin t → Option (Coins d) :=
  fun i => if s i then none else some (ω i)

def raw (d : ℕ) (v : RawState (d+1)) :
    (t : ℕ) → (Fin t → Bool) → History (d+1) t → RawState (d+1)
  | 0, _, _ => v
  | t+1, s, ω =>
      let u := raw d v t (Fin.init s) (Fin.init ω)
      if s (Fin.last t) then rawNext d u (ω (Fin.last t))
      else rawPermute u (step (d+1) (ω (Fin.last t)))

lemma publicHistory_snoc {d t : ℕ} (s : Fin t → Bool) (b : Bool)
    (ω : History d t) (c : Coins d) :
    publicHistory (Fin.snoc s b) (Fin.snoc ω c) =
      Fin.snoc (publicHistory s ω) (if b then none else some c) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [publicHistory]

lemma raw_snoc (d : ℕ) (v : RawState (d+1)) (t : ℕ) (s : Fin t → Bool) (b : Bool)
    (ω : History (d+1) t) (c : Coins (d+1)) :
    raw d v (t+1) (Fin.snoc s b) (Fin.snoc ω c) =
      if b then rawNext d (raw d v t s ω) c else rawPermute (raw d v t s ω) (step (d+1) c) := by
  simp only [raw, Fin.init_snoc, Fin.snoc_last]

lemma raw_free (d : ℕ) (v : RawState (d+1)) (t : ℕ) (s : Fin t → Bool)
    (ω : History (d+1) t) (y) :
    (raw d v t s ω).free y = v.free ((run (d+1) t ω).symm y) := by
  induction t generalizing y with
  | zero => rfl
  | succ t ih =>
      rw [raw]; split_ifs
      · change (raw d v t (Fin.init s) (Fin.init ω)).free
          ((step (d+1) (ω (Fin.last t))).symm y) = _
        rw [ih, run_succ]
        rfl
      · change (raw d v t (Fin.init s) (Fin.init ω)).free
          ((step (d+1) (ω (Fin.last t))).symm y) = _
        rw [ih, run_succ]
        rfl

lemma raw_energy_le (d : ℕ) (v : RawState (d+1)) (t : ℕ) (s : Fin t → Bool)
    (ω : History (d+1) t) : rawEnergy (raw d v t s ω) ≤ rawEnergy v := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
      rw [raw]; split_ifs
      · exact (physicalFlow_energy_le d _ _ _).trans (ih _ _)
      · rw [rawPermute_energy]; exact ih _ _

lemma permute_test {d : ℕ} (v : RawState d) (g : State d) (f : Position d → ℝ) :
    (∑ y, (rawPermute v g).weight y * f y) = ∑ x, v.weight x * f (g x) := by
  change (∑ y, v.weight (g.symm y) * f y) = _
  have h := Equiv.sum_comp g (fun y => v.weight (g.symm y) * f y)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem flow_joint {ι : Type*} (d : ℕ) (v : RawState (d+1))
    (e : ι → Position (d+1)) (he : ∀ i, v.free (e i) = false)
    (t : ℕ) (s : Fin t → Bool)
    (f : (Fin t → Option (Coins (d+1))) → (Fin (t+1) → ι → Position (d+1)) → Position (d+1) → ℝ) :
    mean (fun ω : History (d+1) t => ∑ x, v.weight x *
      f (publicHistory s ω) (exposedPath (d+1) e t ω) (run (d+1) t ω x)) =
    mean (fun ω : History (d+1) t => ∑ y, (raw d v t s ω).weight y *
      f (publicHistory s ω) (exposedPath (d+1) e t ω) y) := by
  induction t with
  | zero => simp only [run_zero, raw]; rfl
  | succ t ih =>
      let b := s (Fin.last t)
      let s₀ := Fin.init s
      have hs : s = Fin.snoc s₀ b := (Fin.snoc_init_self s).symm
      rw [hs]
      let F (q : Fin t → Option (Coins (d+1))) (p : Fin (t+1) → ι → Position (d+1)) (x : Position (d+1)) :=
        mean (fun c : Coins (d+1) => f (Fin.snoc q (if b then none else some c))
          (Fin.snoc p (step (d+1) c ∘ p (Fin.last t))) (step (d+1) c x))
      have hl : mean (fun ω : History (d+1) (t+1) => ∑ x, v.weight x *
          f (publicHistory (Fin.snoc s₀ b) ω) (exposedPath (d+1) e (t+1) ω) (run (d+1) (t+1) ω x)) =
          mean (fun ω : History (d+1) t => ∑ x, v.weight x *
            F (publicHistory s₀ ω) (exposedPath (d+1) e t ω) (run (d+1) t ω x)) := by
        rw [mean_history_succ]
        apply mean_congr; intro ω
        simp only [publicHistory_snoc, exposedPath_snoc, run_snoc]
        rw [mean_sum]
        simp_rw [mean_const_mul]
        simp only [F, exposedPath_last]
        rfl
      have hr : mean (fun ω : History (d+1) (t+1) => ∑ y,
          (raw d v (t+1) (Fin.snoc s₀ b) ω).weight y *
          f (publicHistory (Fin.snoc s₀ b) ω) (exposedPath (d+1) e (t+1) ω) y) =
          mean (fun ω : History (d+1) t => ∑ y, (raw d v t s₀ ω).weight y *
            F (publicHistory s₀ ω) (exposedPath (d+1) e t ω) y) := by
        rw [mean_history_succ]
        apply mean_congr; intro ω
        simp only [raw_snoc, publicHistory_snoc, exposedPath_snoc]
        cases hb : b
        · simp only [Bool.false_eq_true, ite_false]
          simp_rw [permute_test]
          rw [mean_sum]
          simp_rw [mean_const_mul]
          simp only [F, hb, Bool.false_eq_true, ite_false, exposedPath_last]
          rfl
        · simp only [ite_true]
          change mean (fun c : Position d → Bool => ∑ y,
            physicalFlow d (raw d v t s₀ ω).free (raw d v t s₀ ω).weight c y *
            f (Fin.snoc (publicHistory s₀ ω) none)
              (Fin.snoc (exposedPath (d+1) e t ω) ((step (d+1) c) ∘ ((run (d+1) t ω) ∘ e))) y) = _
          rw [physicalFlow_joint d (raw d v t s₀ ω).free (raw d v t s₀ ω).weight
            ((run (d+1) t ω) ∘ e) (by
              intro i
              simp only [Function.comp_apply, raw_free, Equiv.symm_apply_apply]
              exact he i)
            (fun e' y => f (Fin.snoc (publicHistory s₀ ω) none)
              (Fin.snoc (exposedPath (d+1) e t ω) e') y)]
          rw [mean_sum]
          simp_rw [mean_const_mul]
          simp only [F, hb, ite_true, exposedPath_last]
          rfl
      exact hl.trans ((ih s₀ F).trans hr.symm)

end Thorp.Conditional.Hybrid

end

end OAI
