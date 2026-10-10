import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodegreeNoiseExit

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def historyCompensator {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ)
    (ω : History α T) : ℝ :=
  historyCounter (fun k a => pmfMean (K k a) (f (k+1))-f k a) T j ω

theorem history_noise_compensator {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : ℕ → α → ℝ) (T j : ℕ) (hj : j ≤ T)
    (ω : History α T) :
    f j (ω (historyIndex T j)) = f 0 (ω (historyIndex T 0))+
      historyNoise K f T j ω+historyCompensator K f T j ω := by
  unfold historyCompensator historyCounter historyNoise historyIncrement
  simp only [Nat.min_eq_left hj]
  rw [add_assoc,← Finset.sum_add_distrib]
  have he : (∑ k ∈ Finset.range j,
      (f (k+1) (ω (historyIndex T (k+1)))-pmfMean (K k (ω (historyIndex T k))) (f (k+1))+
        (pmfMean (K k (ω (historyIndex T k))) (f (k+1))-f k (ω (historyIndex T k))))) =
      f j (ω (historyIndex T j))-f 0 (ω (historyIndex T 0)) := by
    calc
      _ = ∑ k ∈ Finset.range j,
          (f (k+1) (ω (historyIndex T (k+1)))-f k (ω (historyIndex T k))) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := Finset.sum_range_sub (fun k => f k (ω (historyIndex T k))) j
  rw [he]
  ring

noncomputable def prefixNormalizedCodegree {n : ℕ} (u v : Fin n)
    (k : ℕ) (G : Graph n) : ℝ :=
  (currentCodegree G u v : ℝ)/earlyTemplateScale 1 2 n k

noncomputable def prefixCodegreePredictableError {n : ℕ} (u v : Fin n)
    (j : ℕ) (ω : History (Graph n) (prefixTime n)) : ℝ :=
  prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1+
    historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω

def PrefixCodegreeDriftExit {n : ℕ} (u v : Fin n)
    (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∃ j ≤ prefixTime n,
    (∀ k < j, |prefixNormalizedCodegree u v k (ω (historyIndex (prefixTime n) k))-1| <
      2*codegreeNoiseRadius n) ∧
    codegreeNoiseRadius n ≤ |prefixCodegreePredictableError u v j ω|

theorem codegree_first_exit_noise_or_drift {n : ℕ} (u v : Fin n)
    (hs : ∀ k ≤ prefixTime n, 0 < earlyTemplateScale 1 2 n k)
    (hr : codegreeNoiseRadius n ≤ 1/2)
    (ω : History (Graph n) (prefixTime n))
    (hex : ∃ j ≤ prefixTime n,
      2*codegreeNoiseRadius n ≤
        |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1|) :
    PrefixCodegreeNoiseExit u v ω ∨ PrefixCodegreeDriftExit u v ω := by
  classical
  let P : ℕ → Prop := fun j => j ≤ prefixTime n ∧ 2*codegreeNoiseRadius n ≤
      |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1|
  have hex' : ∃ j, P j := hex
  let j := Nat.find hex'
  have hj : j ≤ prefixTime n := (Nat.find_spec hex').1
  have hcross := (Nat.find_spec hex').2
  have hbefore : ∀ k < j, |prefixNormalizedCodegree u v k (ω (historyIndex (prefixTime n) k))-1| <
      2*codegreeNoiseRadius n := by
    intro k hk
    have hh := Nat.find_min' hex' (m := k)
    by_contra hn
    have hp : P k := ⟨by omega,le_of_not_gt hn⟩
    have := hh hp
    omega
  have hcount : ∀ k < j,
      (currentCodegree (ω (historyIndex (prefixTime n) k)) u v : ℝ) ≤
        2*earlyTemplateScale 1 2 n k := by
    intro k hk
    have hh := (le_abs_self (prefixNormalizedCodegree u v k
      (ω (historyIndex (prefixTime n) k))-1)).trans (hbefore k hk).le
    have hq : prefixNormalizedCodegree u v k (ω (historyIndex (prefixTime n) k)) ≤ 2 := by linarith
    exact (div_le_iff₀ (hs k (by omega))).mp hq
  let noise := historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω
  by_cases hm : codegreeNoiseRadius n ≤ |noise|
  · exact Or.inl ⟨j,hj,hcount,hm⟩
  · apply Or.inr
    refine ⟨j,hj,hbefore,?_⟩
    have hid := history_noise_compensator (fun _ => step) (prefixNormalizedCodegree u v)
      (prefixTime n) j hj ω
    have he : prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1 =
        noise+prefixCodegreePredictableError u v j ω := by
      unfold noise prefixCodegreePredictableError
      linarith only [hid]
    have htriangle := abs_add_le noise (prefixCodegreePredictableError u v j ω)
    change 2*codegreeNoiseRadius n ≤
      |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1| at hcross
    rw [he] at hcross
    linarith only [hcross,htriangle,lt_of_not_ge hm]

end SharpTerminalLeave

end

end OAI
