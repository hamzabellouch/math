import OAI.Probability.InvariantIsing.Core.Variational

namespace OAI

/-! The upper-tail order used in the finite-spectrum upper comparison. -/

noncomputable section

open MeasureTheory Set

namespace InvariantIsing

def pathTail (p : OverlapPath) (s : ℝ) : ℝ := ∫ u in s..1, p u

lemma posPart_integral_eq_interval (p : OverlapPath) (r : ℝ) :
    (∫ u, max (p u - r) 0 ∂pathMeasure) = ∫ u in 0..1, max (p u - r) 0 := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

lemma pathTail_sub_le_posPart (p : OverlapPath) (r : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    pathTail p s - (1 - s) * r ≤ ∫ u, max (p u - r) 0 ∂pathMeasure := by
  let g : ℝ → ℝ := fun u => max (p u - r) 0
  have hg : Monotone g := fun _ _ huv =>
    max_le_max (sub_le_sub_right (p.monotone huv) r) le_rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := 0) (b := s))
    (hg.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have hlo : 0 ≤ ∫ u in 0..s, g u :=
    intervalIntegral.integral_nonneg_of_forall hs.1 (fun _ => le_max_right _ _)
  have hhi : (∫ u in s..1, p u - r) ≤ ∫ u in s..1, g u :=
    intervalIntegral.integral_mono hs.2
      (p.monotone.intervalIntegrable.sub intervalIntegrable_const) hg.intervalIntegrable
      (fun _ => le_max_left _ _)
  rw [intervalIntegral.integral_sub p.monotone.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hhi
  rw [posPart_integral_eq_interval]
  change (∫ u in s..1, p u) - (1 - s) * r ≤ ∫ u in 0..1, g u
  linarith

/-- A monotone quantile crosses any horizontal level at a cutoff, allowing a
jump or a nontrivial atom at that level. Endpoint values play no role. -/
lemma exists_path_level_cutoff (p : OverlapPath) (r : ℝ) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∀ u ∈ Ioo 0 s, p u ≤ r) ∧ (∀ u ∈ Ioo s 1, r ≤ p u) := by
  let A : Set ℝ := {u | u ∈ Icc (0 : ℝ) 1 ∧ r < p u} ∪ {1}
  have hne : A.Nonempty := ⟨1, Or.inr rfl⟩
  have hb : BddBelow A := by
    refine ⟨0, ?_⟩
    intro u hu
    rcases hu with hu | hu
    · exact hu.1.1
    · rw [Set.mem_singleton_iff.mp hu]; norm_num
  have hs0 : 0 ≤ sInf A := le_csInf hne (by
    intro u hu
    rcases hu with hu | hu
    · exact hu.1.1
    · rw [Set.mem_singleton_iff.mp hu]; norm_num)
  have hs1 : sInf A ≤ 1 := csInf_le hb (Or.inr rfl)
  refine ⟨sInf A, ⟨hs0, hs1⟩, ?_, ?_⟩
  · intro u hu
    by_contra h
    have humem : u ∈ A := Or.inl ⟨⟨hu.1.le, hu.2.le.trans hs1⟩, lt_of_not_ge h⟩
    exact (not_le_of_gt hu.2) (csInf_le hb humem)
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := exists_lt_of_csInf_lt hne hu.1
    rcases hv with hv | hv
    · exact (hv.2.trans_le (p.monotone hvu.le)).le
    · rw [Set.mem_singleton_iff.mp hv] at hvu
      exact False.elim ((not_lt_of_ge hu.2.le) hvu)

/-- The positive-part integral is attained by a tail of the quantile. -/
lemma exists_posPart_eq_pathTail (p : OverlapPath) (r : ℝ) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      (∫ u, max (p u - r) 0 ∂pathMeasure) = pathTail p s - (1 - s) * r := by
  obtain ⟨s, hs, hlo, hhi⟩ := exists_path_level_cutoff p r
  let g : ℝ → ℝ := fun u => max (p u - r) 0
  have hg : Monotone g := fun _ _ huv =>
    max_le_max (sub_le_sub_right (p.monotone huv) r) le_rfl
  have hlow : (∫ u in 0..s, g u) = 0 := by
    calc
      _ = ∫ _ in 0..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.1
        intro u hu
        exact max_eq_right (sub_nonpos.mpr (hlo u hu))
      _ = 0 := by simp
  have hhigh : (∫ u in s..1, g u) = pathTail p s - (1 - s) * r := by
    calc
      _ = ∫ u in s..1, p u - r := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.2
        intro u hu
        exact max_eq_left (sub_nonneg.mpr (hhi u hu))
      _ = _ := by
        rw [intervalIntegral.integral_sub p.monotone.intervalIntegrable intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := 0) (b := s))
    (hg.intervalIntegrable (μ := volume) (a := s) (b := 1))
  refine ⟨s, hs, ?_⟩
  rw [posPart_integral_eq_interval]
  simpa only [hlow, hhigh, zero_add] using hsum.symm

/-- Manuscript `up:tail-order`: ordering every upper tail reverses the entire
deficit function, including at jumps and atoms of either overlap quantile. -/
theorem deficit_le_of_pathTail_le (p q : OverlapPath)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, pathTail q s ≤ pathTail p s) (r : ℝ) :
    deficit p r ≤ deficit q r := by
  obtain ⟨s, hs, he⟩ := exists_posPart_eq_pathTail q r
  have hpos : (∫ u, max (q u - r) 0 ∂pathMeasure) ≤
      ∫ u, max (p u - r) 0 ∂pathMeasure := by
    rw [he]
    exact (sub_le_sub_right (htail s hs) _).trans (pathTail_sub_le_posPart p r hs)
  unfold deficit
  linarith

end InvariantIsing

end

end OAI
