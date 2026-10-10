import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Problem336
namespace FiniteTiltLimit

variable {S : Type*} [Fintype S]

def partition (p w : S → ℝ) : ℝ := ∑ s, p s * w s

def mean (p w f : S → ℝ) : ℝ :=
  (∑ s, p s * w s * f s) / partition p w

theorem partition_pos {p w : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp_sum : ∑ s, p s = 1) (hw : ∀ s, 0 < w s) :
    0 < partition p w := by
  have hex : ∃ s, 0 < p s := by
    by_contra h
    push Not at h
    have hz : ∀ s, p s = 0 := fun s => le_antisymm (h s) (hp s)
    simp [hz] at hp_sum
  obtain ⟨s, hs⟩ := hex
  exact Finset.sum_pos' (fun t _ => mul_nonneg (hp t) (hw t).le)
    ⟨s, Finset.mem_univ s, mul_pos hs (hw s)⟩

theorem mean_mem_Icc {p w f : S → ℝ} (hp : ∀ s, 0 ≤ p s)
    (hp_sum : ∑ s, p s = 1) (hw : ∀ s, 0 < w s)
    (hf : ∀ s, f s ∈ Set.Icc (0 : ℝ) 1) :
    mean p w f ∈ Set.Icc (0 : ℝ) 1 := by
  have hz := partition_pos hp hp_sum hw
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun s _ =>
      mul_nonneg (mul_nonneg (hp s) (hw s).le) (hf s).1) hz.le
  · apply (div_le_one hz).mpr
    exact Finset.sum_le_sum fun s _ =>
      mul_le_of_le_one_right (mul_nonneg (hp s) (hw s).le) (hf s).2

theorem tendsto_partition {p : ℕ → S → ℝ} {q w : S → ℝ}
    (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s))) :
    Tendsto (fun n => partition (p n) w) atTop (nhds (partition q w)) := by
  exact tendsto_finsetSum _ fun s _ => (hp s).mul tendsto_const_nhds

theorem tendsto_mean {p : ℕ → S → ℝ} {q w f : S → ℝ}
    (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hq : partition q w ≠ 0) :
    Tendsto (fun n => mean (p n) w f) atTop (nhds (mean q w f)) := by
  apply Tendsto.div _ (tendsto_partition hp) hq
  exact tendsto_finsetSum _ fun s _ =>
    ((hp s).mul tendsto_const_nhds).mul tendsto_const_nhds

theorem tendsto_mean_of_probability {p : ℕ → S → ℝ} {q w f : S → ℝ}
    (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hq : ∀ s, 0 ≤ q s) (hq_sum : ∑ s, q s = 1)
    (hw : ∀ s, 0 < w s) :
    Tendsto (fun n => mean (p n) w f) atTop (nhds (mean q w f)) :=
  tendsto_mean hp (ne_of_gt (partition_pos hq hq_sum hw))

theorem response_le_of_eventually {p : ℕ → S → ℝ} {q w w' f : S → ℝ}
    {d : ℝ} (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hw : partition q w ≠ 0) (hw' : partition q w' ≠ 0)
    (hresponse : ∀ᶠ n in atTop, |mean (p n) w f - mean (p n) w' f| ≤ d) :
    |mean q w f - mean q w' f| ≤ d := by
  exact le_of_tendsto
    (((tendsto_mean hp hw).sub (tendsto_mean hp hw')).abs) hresponse

theorem response_le_of_tendsto {p : ℕ → S → ℝ} {q w w' f : S → ℝ}
    {d : ℝ} (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hw : partition q w ≠ 0) (hw' : partition q w' ≠ 0)
    (hresponse : ∀ n, |mean (p n) w f - mean (p n) w' f| ≤ d) :
    |mean q w f - mean q w' f| ≤ d := by
  exact le_of_tendsto
    (((tendsto_mean hp hw).sub (tendsto_mean hp hw')).abs)
    (Eventually.of_forall hresponse)

theorem probability_of_tendsto {p : ℕ → S → ℝ} {q : S → ℝ}
    (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hp_nonneg : ∀ n s, 0 ≤ p n s) (hp_sum : ∀ n, ∑ s, p n s = 1) :
    (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1 := by
  constructor
  · intro s
    exact ge_of_tendsto (hp s) (Eventually.of_forall fun n => hp_nonneg n s)
  · have hsum : Tendsto (fun n => ∑ s, p n s) atTop (nhds (∑ s, q s)) :=
      tendsto_finsetSum _ fun s _ => hp s
    have hone : Tendsto (fun n => ∑ s, p n s) atTop (nhds (1 : ℝ)) := by
      simpa only [hp_sum] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    exact tendsto_nhds_unique hsum hone

theorem tendsto_exponential_mean {p : ℕ → S → ℝ} {q f g : S → ℝ}
    (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hq : ∀ s, 0 ≤ q s) (hq_sum : ∑ s, q s = 1) :
    Tendsto (fun n => mean (p n) (fun s => Real.exp (g s)) f)
      atTop (nhds (mean q (fun s => Real.exp (g s)) f)) :=
  tendsto_mean_of_probability hp hq hq_sum (fun s => Real.exp_pos (g s))

theorem exponential_response_le {p : ℕ → S → ℝ} {q f g g' : S → ℝ}
    {d : ℝ} (hp : ∀ s, Tendsto (fun n => p n s) atTop (nhds (q s)))
    (hq : ∀ s, 0 ≤ q s) (hq_sum : ∑ s, q s = 1)
    (hresponse : ∀ n,
      |mean (p n) (fun s => Real.exp (g s)) f -
        mean (p n) (fun s => Real.exp (g' s)) f| ≤ d) :
    |mean q (fun s => Real.exp (g s)) f -
      mean q (fun s => Real.exp (g' s)) f| ≤ d :=
  response_le_of_tendsto hp
    (ne_of_gt (partition_pos hq hq_sum (fun s => Real.exp_pos (g s))))
    (ne_of_gt (partition_pos hq hq_sum (fun s => Real.exp_pos (g' s)))) hresponse

end FiniteTiltLimit
end Problem336

end

end OAI
