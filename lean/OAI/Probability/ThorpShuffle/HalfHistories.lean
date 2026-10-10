import OAI.Probability.ThorpShuffle.FreshCoins

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

structure RawState (d : ℕ) where
  free : Position d → Bool
  weight : Position d → ℝ

def rawNext (d : ℕ) (v : RawState (d + 1)) (c : Coins (d + 1)) : RawState (d + 1) where
  free := physicalFree d v.free c
  weight := physicalFlow d v.free v.weight c

def rawIterate (d : ℕ) (v : RawState (d + 1)) :
    (t : ℕ) → History (d + 1) t → RawState (d + 1)
  | 0, _ => v
  | t + 1, ω => rawNext d (rawIterate d v t (fun i => ω i.castSucc)) (ω (Fin.last t))

def CenteredState.raw {d : ℕ} (v : CenteredState d) : RawState d := ⟨v.free, v.weight⟩

theorem iterateState_raw (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) :
    (iterateState d v t ω).raw = rawIterate d v.raw t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change rawNext d (iterateState d v t (fun i => ω i.castSucc)).raw (ω (Fin.last t)) = _
    rw [ih]
    rfl

theorem rawIterate_free (d : ℕ) (v : RawState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) (x : Position (d + 1)) :
    (rawIterate d v t ω).free x = v.free ((run (d + 1) t ω).symm x) := by
  induction t generalizing x with
  | zero => simp only [rawIterate, run_zero]; rfl
  | succ t ih =>
    change (rawIterate d v t (fun i => ω i.castSucc)).free
      ((step (d + 1) (ω (Fin.last t))).symm x) = _
    rw [ih, run_succ]
    rfl

theorem mean_bool (f : Bool → ℝ) : mean f = (f false + f true) / 2 := by
  simp [mean, add_comm]

theorem pairUpdate_mean_fst (u v : Bool) (a b : ℝ) :
    mean (fun c : Bool => (pairUpdate u v a b c).1) = (a + b) / 2 := by
  cases u <;> cases v <;> simp [mean_bool, pairUpdate]

theorem pairUpdate_mean_snd (u v : Bool) (a b : ℝ) :
    mean (fun c : Bool => (pairUpdate u v a b c).2) = (a + b) / 2 := by
  cases u <;> cases v <;> simp [mean_bool, pairUpdate]
  all_goals ring

theorem mean_sign {α : Type uα} [Fintype α] [DecidableEq α] (i : α) :
    mean (fun c : α → Bool => sign (c i)) = 0 := by
  simp [mean, sum_sign]

theorem mean_coin_eval {α : Type uα} [Fintype α] [DecidableEq α]
    (i : α) (f : Bool → ℝ) : mean (fun c : α → Bool => f (c i)) = mean f := by
  have hfun (b : Bool) : f b = (f false + f true) / 2 +
      sign b * ((f false - f true) / 2) := by
    cases b <;> simp [sign] <;> ring
  calc
    _ = mean (fun c : α → Bool => (f false + f true) / 2 +
        sign (c i) * ((f false - f true) / 2)) := mean_congr (fun c => hfun (c i))
    _ = mean f := by
      rw [mean_add, mean_const, mean_mul_const]
      simp only [mean_sign, zero_mul, add_zero, mean_bool]

theorem mean_physicalFlow_snoc (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (x : Position d) (b : Bool) :
    mean (fun c : Coins (d + 1) => physicalFlow d B w c (Fin.snoc x b)) =
      (w (Fin.cons false x) + w (Fin.cons true x)) / 2 := by
  rw [← scatterPosition_eq_snoc]
  simp only [physicalFlow_scatter]
  cases b
  · change mean (fun c : Position d → Bool =>
      (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).1) = _
    rw [mean_coin_eval x (fun c => (pairUpdate (B (Fin.cons false x))
      (B (Fin.cons true x)) (w (Fin.cons false x)) (w (Fin.cons true x)) c).1),
      pairUpdate_mean_fst]
  · change mean (fun c : Position d → Bool =>
      (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).2) = _
    rw [mean_coin_eval x (fun c => (pairUpdate (B (Fin.cons false x))
      (B (Fin.cons true x)) (w (Fin.cons false x)) (w (Fin.cons true x)) c).2),
      pairUpdate_mean_snd]

end Conditional

namespace Conditional

def firstMean (d : ℕ) (w : Position (d + 1) → ℝ) (x : Position d) : ℝ :=
  mean (fun b : Bool => w (Fin.cons b x))

def meanLayer : (d : ℕ) → (Position d → ℝ) → Position d → ℝ
  | 0, w => w
  | d + 1, w => fun x => firstMean d w (Fin.init x)

theorem mean_physicalFlow (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (x : Position (d + 1)) :
    mean (fun c : Coins (d + 1) => physicalFlow d B w c x) =
      meanLayer (d + 1) w x := by
  conv_lhs => rw [← Fin.snoc_init_self x]
  rw [mean_physicalFlow_snoc]
  change _ = mean (fun b : Bool => w (Fin.cons b (Fin.init x)))
  exact (mean_bool (fun b : Bool => w (Fin.cons b (Fin.init x)))).symm

theorem init_cons (d : ℕ) (b : Bool) (x : Position (d + 1)) :
    (Fin.init (Fin.cons b x : Position (d + 2)) : Position (d + 1)) =
      (Fin.cons b (Fin.init x) : Position (d + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem meanLayer_lift (d : ℕ) (w : Position d → ℝ) :
    meanLayer (d + 1) (fun x => w (Fin.init x)) =
      fun x => meanLayer d w (Fin.init x) := by
  funext x
  cases d with
  | zero =>
    have hall (b : Bool) : Fin.init (Fin.cons b (Fin.init x) : Position 1) = Fin.init x :=
      Subsingleton.elim _ _
    simp only [meanLayer, firstMean, hall, mean_const]
  | succ d =>
    simp only [meanLayer, firstMean, init_cons]

theorem mean_iterations_dimension (d t : ℕ) (w : Position (d + 1) → ℝ)
    (x : Position (d + 1)) :
    (meanLayer (d + 1))^[t + 1] w x =
      (meanLayer d)^[t] (firstMean d w) (Fin.init x) := by
  have hs : Function.Semiconj (fun w : Position d → ℝ => fun x : Position (d + 1) => w (Fin.init x))
      (meanLayer d) (meanLayer (d + 1)) := fun w => (meanLayer_lift d w).symm
  rw [Function.iterate_succ_apply]
  exact (congrFun (hs.iterate_right t (firstMean d w)) x).symm

theorem mean_firstMean (d : ℕ) (w : Position (d + 1) → ℝ) :
    mean (firstMean d w) = mean w := by
  have h := mean_equiv (splitPosition d).symm w
  rw [mean_prod] at h
  rw [← h, mean_comm]
  rfl

theorem mean_iterations_sweep (d : ℕ) (w : Position d → ℝ) (x : Position d) :
    (meanLayer d)^[d] w x = mean w := by
  induction d with
  | zero =>
    change w x = mean w
    have hw : w = fun _ => w x := funext (fun y => congrArg w (Subsingleton.elim y x))
    rw [hw, mean_const]
  | succ d ih =>
    rw [mean_iterations_dimension, ih, mean_firstMean]

theorem mean_rawIterate_weight (d : ℕ) (v : RawState (d + 1)) (t : ℕ)
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) t => (rawIterate d v t ω).weight x) =
      (meanLayer (d + 1))^[t] v.weight x := by
  induction t generalizing x with
  | zero => simp [rawIterate, mean_const]
  | succ t ih =>
    rw [mean_history_succ]
    have hi (ω : History (d + 1) t) :
        mean (fun c : Coins (d + 1) =>
          (rawIterate d v (t + 1) (Fin.snoc ω c)).weight x) =
            meanLayer (d + 1) (rawIterate d v t ω).weight x := by
      simp only [rawIterate, Fin.snoc_castSucc, Fin.snoc_last, rawNext]
      exact mean_physicalFlow _ _ _ _
    simp_rw [hi]
    change mean (fun ω : History (d + 1) t =>
      mean (fun b : Bool => (rawIterate d v t ω).weight (Fin.cons b (Fin.init x)))) = _
    rw [mean_comm]
    simp_rw [ih]
    rw [Function.iterate_succ_apply']
    rfl

theorem mean_rawIterate_sweep (d : ℕ) (v : RawState (d + 1))
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) (d + 1) => (rawIterate d v (d + 1) ω).weight x) =
      mean v.weight := by
  rw [mean_rawIterate_weight, mean_iterations_sweep]

theorem rawIterate_indicator (d : ℕ) (B : Position (d + 1) → Bool) (t : ℕ)
    (ω : History (d + 1) t) (x : Position (d + 1)) :
    (rawIterate d ⟨B, fun y => if B y then 1 else 0⟩ t ω).weight x =
      if (rawIterate d ⟨B, fun y => if B y then 1 else 0⟩ t ω).free x then 1 else 0 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    change physicalFlow d _ (rawIterate d _ t (fun i => ω i.castSucc)).weight
      (ω (Fin.last t)) x = _
    rw [funext (ih (fun i => ω i.castSucc))]
    exact physicalFlow_uniform _ _ _ _ _

theorem mean_free_after_sweep (d : ℕ) (B : Position (d + 1) → Bool)
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) (d + 1) =>
      if B ((run (d + 1) (d + 1) ω).symm x) then (1 : ℝ) else 0) =
        (freeCount B : ℝ) / Fintype.card (Position (d + 1)) := by
  let v : RawState (d + 1) := ⟨B, fun y => if B y then 1 else 0⟩
  have h (ω : History (d + 1) (d + 1)) :
      (if B ((run (d + 1) (d + 1) ω).symm x) then (1 : ℝ) else 0) =
        (rawIterate d v (d + 1) ω).weight x := by
    rw [rawIterate_indicator, rawIterate_free]
  simp_rw [h]
  rw [mean_rawIterate_sweep]
  change (∑ y, if B y then (1 : ℝ) else 0) / _ = _
  rw [sum_free_indicator]

end Conditional

end Thorp

end

end OAI
