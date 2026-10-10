import OAI.Probability.InvariantIsing.Core.TailOrder

namespace OAI

/-! Contact inequalities at trial-partition endpoints imply the full upper
 tail order. Monotone quantile tails lie above their interval chords. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

lemma pathTail_chord (p : OverlapPath) {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    (b - s) * pathTail p a + (s - a) * pathTail p b ≤ (b - a) * pathTail p s := by
  have hleft : (∫ u in a..s, p u) ≤ ∫ _u in a..s, p s :=
    intervalIntegral.integral_mono_on has p.monotone.intervalIntegrable
    intervalIntegrable_const (fun u hu => p.monotone hu.2)
  have hright : (∫ _u in s..b, p s) ≤ ∫ u in s..b, p u :=
    intervalIntegral.integral_mono_on hsb intervalIntegrable_const
    p.monotone.intervalIntegrable (fun u hu => p.monotone hu.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hleft hright
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (p.monotone.intervalIntegrable (μ := volume) (a := a) (b := s))
    (p.monotone.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (p.monotone.intervalIntegrable (μ := volume) (a := s) (b := b))
    (p.monotone.intervalIntegrable (μ := volume) (a := b) (b := 1))
  have hL := mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hsb)
  have hR := mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr has)
  unfold pathTail
  nlinarith

lemma pathTail_chord_eq_of_const (q : OverlapPath) {a s b c : ℝ}
    (has : a ≤ s) (hsb : s ≤ b) (hc : ∀ u ∈ Ioo a b, q u = c) :
    (b - s) * pathTail q a + (s - a) * pathTail q b = (b - a) * pathTail q s := by
  have hleft : (∫ u in a..s, q u) = (s - a) * c := by
    calc
      _ = ∫ _u in a..s, c := intervalIntegral.integral_congr_Ioo_of_le has
        (fun u hu => hc u ⟨hu.1, hu.2.trans_le hsb⟩)
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hright : (∫ u in s..b, q u) = (b - s) * c := by
    calc
      _ = ∫ _u in s..b, c := intervalIntegral.integral_congr_Ioo_of_le hsb
        (fun u hu => hc u ⟨has.trans_lt hu.1, hu.2⟩)
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (q.monotone.intervalIntegrable (μ := volume) (a := a) (b := s))
    (q.monotone.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (q.monotone.intervalIntegrable (μ := volume) (a := s) (b := b))
    (q.monotone.intervalIntegrable (μ := volume) (a := b) (b := 1))
  rw [hleft] at h1
  rw [hright] at h2
  unfold pathTail
  nlinarith

lemma pathTail_le_of_interval_endpoints (p q : OverlapPath) {a s b c : ℝ}
    (hab : a < b) (has : a ≤ s) (hsb : s ≤ b) (hc : ∀ u ∈ Ioo a b, q u = c)
    (ha : pathTail q a ≤ pathTail p a) (hb : pathTail q b ≤ pathTail p b) :
    pathTail q s ≤ pathTail p s := by
  have hp := pathTail_chord p has hsb
  have hq := pathTail_chord_eq_of_const q has hsb hc
  have h1 := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hsb)
  have h2 := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr has)
  nlinarith

lemma finite_cut_bracket {n : ℕ} (cut : Fin (n + 2) → ℝ)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin (n + 1), cut i.castSucc ≤ s ∧ s ≤ cut i.succ := by
  classical
  let S := Finset.univ.filter (fun i : Fin (n + 1) => cut i.castSucc ≤ s)
  have hS : S.Nonempty := ⟨0, by simp only [S, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.castSucc_zero, hfirst]; exact hs.1⟩
  let i := S.max' hS
  have hiS : i ∈ S := Finset.max'_mem _ _
  have hi : cut i.castSucc ≤ s := (Finset.mem_filter.mp hiS).2
  refine ⟨i, hi, ?_⟩
  by_cases hin : i.val = n
  · have he : i.succ = Fin.last (n + 1) := by ext; simp only [Fin.val_succ, Fin.val_last]; omega
    rw [he, hlast]
    exact hs.2
  · by_contra hsb
    let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have he : j.castSucc = i.succ := by ext; rfl
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [he]; exact (lt_of_not_ge hsb).le⟩
    have hji : j ≤ i := Finset.le_max' S j hjS
    change j.val ≤ i.val at hji
    dsimp only [j] at hji
    omega

 theorem pathTail_order_of_finite_partition (p q : OverlapPath) {n : ℕ}
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (v : Fin (n + 1) → ℝ)
    (hq : ∀ i u, u ∈ Ioo (cut i.castSucc) (cut i.succ) → q u = v i)
    (hend : ∀ i, pathTail q (cut i) ≤ pathTail p (cut i)) :
    ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s := by
  intro s hs
  obtain ⟨i, has, hsb⟩ := finite_cut_bracket cut hfirst hlast hs
  exact pathTail_le_of_interval_endpoints p q
    (hcut (by exact_mod_cast (show i.val < i.val + 1 by omega))) has hsb (hq i)
    (hend i.castSucc) (hend i.succ)

end InvariantIsing

end

end OAI
