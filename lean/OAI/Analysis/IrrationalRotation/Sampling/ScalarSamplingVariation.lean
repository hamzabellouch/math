import OAI.Analysis.IrrationalRotation.Sampling.ScalarSampling
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

namespace OAI

open Set

namespace Invariant233.ScalarSampling

lemma antitone_variation_Icc_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (f a - f b) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (f (u i) - f (u (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [edist_comm, edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg.mpr (hf (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (f (u i) - f (u (i + 1)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg.mpr (hf (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (f (u 0) - f (u n)) := by
      congr 1
      exact Finset.sum_range_sub' (fun i => f (u i)) n
    _ ≤ ENNReal.ofReal (f a - f b) := by
      apply ENNReal.ofReal_le_ofReal
      have hab : a ≤ b := (hus 0).1.trans (hus 0).2
      exact sub_le_sub (hf ⟨le_rfl, hab⟩ (hus 0) (hus 0).1)
        (hf (hus n) ⟨hab, le_rfl⟩ (hus n).2)

theorem interval_indicator_variation_le {L C : ℝ}
    (hL : 0 < L) (hLone : L ≤ 1) (hC : 0 ≤ C) :
    eVariationOn ((Ioo 0 L).indicator (fun _ => C)) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * C) := by
  let f : ℝ → ℝ := (Ioo 0 L).indicator (fun _ => C)
  have hhalf : 0 < L / 2 := by linarith
  have hhalfL : L / 2 < L := by linarith
  have hhalfOne : L / 2 ≤ 1 := by linarith
  have hnonneg (x : ℝ) : 0 ≤ f x := Set.indicator_nonneg (fun _ _ => hC) x
  have hleft : MonotoneOn f (Icc 0 (L / 2)) := by
    intro x hx y hy hxy
    by_cases hx0 : 0 < x
    · have hy0 : 0 < y := hx0.trans_le hxy
      have hxL : x < L := hx.2.trans_lt hhalfL
      have hyL : y < L := hy.2.trans_lt hhalfL
      simp [f, hx0, hy0, hxL, hyL]
    · have hfx : f x = 0 := Set.indicator_of_notMem (by simp [hx0]) _
      rw [hfx]
      exact hnonneg y
  have hright : AntitoneOn f (Icc (L / 2) 1) := by
    intro x hx y hy hxy
    by_cases hyL : y < L
    · have hxL : x < L := hxy.trans_lt hyL
      have hx0 : 0 < x := hhalf.trans_le hx.1
      have hy0 : 0 < y := hhalf.trans_le hy.1
      simp [f, hx0, hy0, hxL, hyL]
    · have hfy : f y = 0 := Set.indicator_of_notMem (by simp [hyL]) _
      rw [hfy]
      exact hnonneg x
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by simp [f, not_lt.mpr hLone]
  have hfc : f (L / 2) = C := by simp [f, hhalf, hhalfL]
  have hleftBound : eVariationOn f (Icc 0 (L / 2)) ≤ ENNReal.ofReal C := by
    simpa only [inter_self, hf0, hfc, sub_zero] using
      (hleft.eVariationOn_eq ⟨le_rfl, hhalf.le⟩ ⟨hhalf.le, le_rfl⟩).le
  have hrightBound : eVariationOn f (Icc (L / 2) 1) ≤ ENNReal.ofReal C := by
    simpa only [hfc, hf1, sub_zero] using antitone_variation_Icc_le hright
  change eVariationOn f (Icc 0 1) ≤ ENNReal.ofReal (2 * C)
  calc
    eVariationOn f (Icc 0 1) =
        eVariationOn f (Icc 0 (L / 2)) + eVariationOn f (Icc (L / 2) 1) := by
      simpa only [univ_inter] using
        (eVariationOn.Icc_add_Icc f hhalf.le hhalfOne (mem_univ (L / 2))).symm
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add hleftBound hrightBound
    _ = ENNReal.ofReal (2 * C) := by rw [← ENNReal.ofReal_add hC hC]; congr 1; ring

theorem rawKernel_le_height {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s t : ℝ) :
    rawKernel h α s t ≤ (h * α)⁻¹ := by
  unfold rawKernel
  split_ifs with hs
  · by_cases ht : t ∈ Ioo 0 (h * delta s)
    · rw [Set.indicator_of_mem ht]
      simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hs hh.le)
    · rw [Set.indicator_of_notMem ht]
      positivity
  · positivity

theorem rawKernel_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    eVariationOn (rawKernel h α s) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (h * α)⁻¹) := by
  by_cases hs : α ≤ delta s
  · have hdelta : 0 < delta s := hα.trans_le hs
    have hL : 0 < h * delta s := mul_pos hh hdelta
    have hLone : h * delta s ≤ 1 := by
      calc
        h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone hdelta.le
        _ ≤ 1 := by nlinarith [delta_le_half s]
    have hi : (h * delta s)⁻¹ ≤ (h * α)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hs hh.le)
    have hfun : rawKernel h α s = (Ioo 0 (h * delta s)).indicator
        (fun _ => (h * delta s)⁻¹) := by
      funext t
      simp only [rawKernel, ite_eq_left hs]
    rw [hfun]
    exact (interval_indicator_variation_le hL hLone (inv_nonneg.mpr hL.le)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hi (by norm_num)))
  · simp [rawKernel, hs, eVariationOn]

theorem rawKernel_boundedVariation {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) : BoundedVariationOn (rawKernel h α s) (Icc (0 : ℝ) 1) := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rawKernel_variation_le hh hhone hα s)

theorem rawKernel_height_add_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s t : ℝ) :
    rawKernel h α s t + (eVariationOn (rawKernel h α s) (Icc (0 : ℝ) 1)).toReal ≤
      3 * (h * α)⁻¹ := by
  have hv := ENNReal.toReal_le_of_le_ofReal (by positivity) (rawKernel_variation_le hh hhone hα s)
  have hf := rawKernel_le_height hh hα s t
  linarith

lemma rawKernel_zero (h α s : ℝ) : rawKernel h α s 0 = 0 := by
  unfold rawKernel
  split_ifs <;> simp

lemma rawKernel_one {h α s : ℝ} (hhone : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    rawKernel h α s 1 = 0 := by
  have hLone : h * delta s ≤ 1 := by
    calc
      h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone (delta_nonneg hs)
      _ ≤ 1 := by nlinarith [delta_le_half s]
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro ht
    exact (not_lt.mpr hLone) ht.2
  · rfl

lemma circleKernel_eq_raw_on_unit {h α : ℝ} (hhone : h ≤ 1) (z : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    circleKernel h α z v = rawKernel h α (Int.fract z) v := by
  rcases lt_or_eq_of_le hv.2 with hlt | heq
  · simp only [circleKernel, Int.fract_eq_self.mpr ⟨hv.1, hlt⟩]
  · subst v
    simp only [circleKernel, Int.fract_one, rawKernel_zero]
    exact (rawKernel_one hhone ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩).symm

theorem circleKernel_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (z : ℝ) :
    eVariationOn (circleKernel h α z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (h * α)⁻¹) := by
  rw [eVariationOn.congr (fun _ hv => circleKernel_eq_raw_on_unit hhone z hv)]
  exact rawKernel_variation_le hh hhone hα (Int.fract z)

lemma manuscript_reciprocal_height {m : ℕ} (hm : 200 ≤ m) :
    ((m : ℝ) ^ (-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ = (m : ℝ) ^ (13 / 5 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have htwo : 1 / (m : ℝ)^2 = (m : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hmpos.le, Real.rpow_two]
    simp only [one_div]
  rw [htwo, ← Real.rpow_add hmpos, ← Real.rpow_neg hmpos.le]
  congr 1
  norm_num

theorem manuscriptKernel_variation_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (m : ℝ) ^ (13 / 5 : ℝ)) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  change eVariationOn (circleKernel _ _ z) _ ≤ _
  simpa only [manuscript_reciprocal_height hm] using circleKernel_variation_le hh hhone hα z

theorem manuscriptKernel_le_height {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    manuscriptKernel m z v ≤ (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, circleKernel, manuscript_reciprocal_height hm] using
    rawKernel_le_height hh hα (Int.fract z) (Int.fract v)

theorem manuscriptKernel_height_add_variation_le {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    manuscriptKernel m z v + (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      3 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  have hv := ENNReal.toReal_le_of_le_ofReal
    (by positivity) (manuscriptKernel_variation_le hm z)
  have hf := manuscriptKernel_le_height hm z v
  linarith

theorem manuscriptKernel_sup_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) ≤
      (m : ℝ) ^ (13 / 5 : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have hh := (manuscript_parameters hm).1
  have hnonneg : 0 ≤ manuscriptKernel m z v :=
    rawKernel_nonneg hh.le ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
  dsimp only
  rw [abs_of_nonneg hnonneg]
  exact manuscriptKernel_le_height hm z v

theorem manuscriptKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    BoundedVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) +
          (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
        3 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (manuscriptKernel_variation_le hm z)
  · have hv := ENNReal.toReal_le_of_le_ofReal
      (by positivity) (manuscriptKernel_variation_le hm z)
    have hf := manuscriptKernel_sup_le hm z
    linarith

theorem manuscriptKernel_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) +
        (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      3 * (m : ℝ)^10 := by
  calc
    _ ≤ 3 * (m : ℝ) ^ (13 / 5 : ℝ) := (manuscriptKernel_BV_bound hm z).2
    _ ≤ 3 * (m : ℝ)^10 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
        (by norm_num)

end Invariant233.ScalarSampling

end OAI
