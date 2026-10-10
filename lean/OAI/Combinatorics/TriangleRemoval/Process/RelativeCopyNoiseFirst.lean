import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeScaleBudget

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

theorem relativeCopyNoise_first_crossing {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hL : ∀ k < T, 0 ≤ L k) (hjump : ∀ k < T, 3*L k/s (k+1) ≤ c)
    (r : ℝ) (hr : 0 < r) (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure G) (fun _ => step) T T).support)
    (j : ℕ) (hj : j ≤ T) (hloads : pastRelativeCopyLoadsSafe required L T j ω)
    (hcounts : ∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k)
    (hcross : r ≤ |historyNoise (fun _ => step)
      (fun k H => copyCount required H/s k) T j ω|) :
    ∃ m ≤ T, pastRelativeCopyLoadsSafe required L T m ω ∧
      r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T m ω| ∧
      historyCounter (relativeCopyVarianceRate required L s) T m ω ≤
        c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c) := by
  classical
  let f := fun k H => copyCount required H/s k
  let P : ℕ → Prop := fun m => r ≤ |historyNoise (fun _ => step) f T m ω|
  have hex : ∃ m, P m := ⟨j,hcross⟩
  let m := Nat.find hex
  have hmj : m ≤ j := Nat.find_min' hex hcross
  have hmT : m ≤ T := hmj.trans hj
  have hm : P m := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    have : r ≤ (0 : ℝ) := by simpa [P,he] using hm
    linarith
  obtain ⟨k,he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hkm : k < m := by omega
  have hkT : k < T := hkm.trans_le hmT
  have hprev : |historyNoise (fun _ => step) f T k ω| < r := by
    exact lt_of_not_ge (Nat.find_min hex hkm)
  have hsafe : pastRelativeCopyLoadsSafe required L T m ω := by
    intro a ha
    apply hloads a
    exact lt_of_lt_of_le ha (min_le_min_right T hmj)
  obtain ⟨hinit,hpath⟩ := historyLaw_path_support (PMF.pure G) (fun _ => step) T T le_rfl ω hω
  have hG : ω (historyIndex T 0) = G := by
    simpa only [PMF.mem_support_pure_iff] using hinit
  have hload : copyLoadSafe required (L k) (ω (historyIndex T k)) := by
    apply hsafe k
    simpa [Nat.min_eq_left hmT] using hkm
  have hinc : |historyIncrement (fun _ => step) f T k ω| ≤ c := by
    unfold historyIncrement
    simp only [f,div_eq_mul_inv,pmfMean_mul_const,← sub_mul,abs_mul,
      abs_of_pos (inv_pos.mpr (hs (k+1) (by omega)))]
    have hh := pmf_centered_of_loss_range (step (ω (historyIndex T k))) (copyCount required)
      (copyCount required (ω (historyIndex T k))) (3*L k)
      (fun H hH => copyCount_step_loss_range required _ H (L k) (hL k hkT) hload hH)
      _ (hpath k hkT)
    exact (mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (hs (k+1) (by omega)).le)).trans
      (by simpa only [div_eq_mul_inv] using hjump k hkT)
  have hM : historyNoise (fun _ => step) f T m ω ≤ r+c := by
    rw [he,historyNoise_succ_same _ _ T k hkT]
    have hp := le_abs_self (historyNoise (fun _ => step) f T k ω)
    have hi := le_abs_self (historyIncrement (fun _ => step) f T k ω)
    linarith
  refine ⟨m,hmT,hsafe,hm,?_⟩
  have hv := relativeCopyCounter_le required T m hmT L s c B hc.le hB hs hdec hjump ω
    (fun a ha => hcounts a (ha.trans_le hmj))
  rw [hG] at hv
  exact hv.trans (mul_le_mul_of_nonneg_left (by dsimp [f] at hM; linarith) hc.le)

open Classical in

theorem triangle_relative_template_self_bounded_tail {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (G : Graph n) (T : ℕ) (L s : ℕ → ℝ)
    (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hL : ∀ k < T, 0 ≤ L k) (hjump : ∀ k < T, 3*L k/s (k+1) ≤ c)
    (r : ℝ) (hr : 0 < r) :
    pmfMean (historyLaw (PMF.pure G) (fun _ => step) T T)
      (fun ω => if ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
        (∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) ∧
        r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω|
        then 1 else 0) ≤
      2*(T+1 : ℝ)*Real.exp
        (-r^2/(4*(c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c)+c*r))) := by
  have hs' : ∀ k < T, 0 < s (k+1) := fun k hk => hs (k+1) (by omega)
  have hV : 0 ≤ c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c) := by
    have hz := hs 0 (Nat.zero_le T)
    have hn := copyCount_nonneg required G
    have hb := relativeScaleBudget_nonneg s T hs hdec
    positivity
  apply le_trans _ (triangle_relative_template_before_load_exit required G T L s c hc hs' hL
    hjump r (c*(copyCount required G/s 0+B*relativeScaleBudget s T+r+c)) hr hV)
  apply pmfMean_mono
  intro ω hω
  by_cases hex : ∃ j ≤ T, pastRelativeCopyLoadsSafe required L T j ω ∧
      (∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) ∧
      r ≤ |historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω|
  · obtain ⟨j,hj,hloads,hcounts,hcross⟩ := hex
    have hh := relativeCopyNoise_first_crossing required G T L s c B hc hB hs hdec hL hjump
      r hr ω hω j hj hloads hcounts hcross
    rw [ite_eq_left ⟨j,hj,hloads,hcounts,hcross⟩,ite_eq_left hh]
  · rw [ite_eq_right hex]
    split <;> norm_num

end SharpTerminalLeave

end

end OAI
