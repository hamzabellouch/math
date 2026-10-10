import OAI.MeasureTheory.Falconer.Estimates.DyadicSecantError

namespace OAI

/-! Length and endpoint accounting for ordered profile intervals. -/
namespace Falconer
open Set

 theorem ordered_interval_length_le {S : List (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    (S.map Prod.snd).sum ≤ b-a := by
  induction S generalizing a with
  | nil => simpa using sub_nonneg.mpr hab
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have hs := ih (a := c.1+c.2) hc.2.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,(hb d (by simp [hd])).2⟩)
    simp only [List.map_cons,List.sum_cons]
    linarith

 theorem ordered_interval_count_bound {S : List (ℝ × ℝ)} {a b τ : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2)
    (hτ : ∀ c ∈ S, τ ≤ c.2) :
    τ*(S.length : ℝ) ≤ b-a := by
  have hsum : τ*(S.length : ℝ) ≤ (S.map Prod.snd).sum := by
    induction S with
    | nil => simp
    | cons c S ih =>
      have ht : ∀ d ∈ S, τ ≤ d.2 := fun d hd => hτ d (by simp [hd])
      have hi := ih (by simpa using hord.of_cons) (fun d hd => hb d (by simp [hd])) ht
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.map_cons,List.sum_cons]
      linarith [hτ c (by simp)]
  exact hsum.trans (ordered_interval_length_le hab hord hb)

 theorem ordered_profile_increment_lower {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {S : List (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    f b-f a-2*((b-a)-(S.map Prod.snd).sum) ≤
      (S.map (fun c => f (c.1+c.2)-f c.1)).sum := by
  have hinc {u v : ℝ} (huv : u ≤ v) : f v-f u ≤ 2*(v-u) := by
    have hd := hf.dist_le_mul v u
    simp only [Real.dist_eq,NNReal.coe_ofNat,abs_of_nonneg (sub_nonneg.mpr huv)] at hd
    exact (le_abs_self _).trans hd
  induction S generalizing a with
  | nil => simpa using sub_nonpos.mpr (hinc hab)
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have hs := ih (a := c.1+c.2) hc.2.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,(hb d (by simp [hd])).2⟩)
    simp only [List.map_cons,List.sum_cons]
    linarith [hinc hc.1]

end Falconer

end OAI
