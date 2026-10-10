import Mathlib
import OAI.Computability.VertexCover.Sampling.Basic
import OAI.Computability.VertexCover.Sampling.FiniteTrials

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) («c» : ℝ) :
    traceAverage w n (fun _ => «c») = «c» := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

end

end UniqueGames.Foundations.CorrelatedSampling

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
