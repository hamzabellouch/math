import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def saddleSum (lam : ι → ℝ) (a z : ℝ) : ℝ := ∑ i, (z - a * lam i)⁻¹

lemma saddleSum_strictAnti (lam : ι → ℝ) (a x y : ℝ)
    (hx : ∀ i, 0 < x - a * lam i) (hxy : x < y) :
    saddleSum lam a y < saddleSum lam a x := by
  classical
  have hi : ∀ i, (y - a * lam i)⁻¹ < (x - a * lam i)⁻¹ := by
    intro i
    simpa only [one_div] using
      one_div_lt_one_div_of_lt (hx i) (show x - a * lam i < y - a * lam i by linarith)
  apply Finset.sum_lt_sum
  · intro i _
    exact (hi i).le
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Finset.mem_univ i, hi i⟩

theorem spherical_saddle_existsUnique (lam : ι → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (top : ι) (htop : ∀ i, lam i ≤ lam top) :
    ∃! z : ℝ, (∀ i, 0 < z - a * lam i) ∧
      saddleSum lam a z = Fintype.card ι := by
  classical
  let N : ℝ := Fintype.card ι
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hNge : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card ι))
  have hNinv : 0 < N⁻¹ := inv_pos.mpr hNpos
  have hNinv_le : N⁻¹ ≤ 1 := (inv_le_one₀ hNpos).mpr hNge
  let l : ℝ := a * lam top + N⁻¹
  let u : ℝ := a * lam top + 1
  have hgap : ∀ z ∈ Set.Icc l u, ∀ i, 0 < z - a * lam i := by
    intro z hz i
    have hm := mul_le_mul_of_nonneg_left (htop i) ha
    have hzlo : a * lam top + N⁻¹ ≤ z := hz.1
    linarith
  have hlu : l ≤ u := by dsimp [l, u]; linarith
  have hcont : ContinuousOn (saddleSum lam a) (Set.Icc l u) := by
    unfold saddleSum
    apply continuousOn_finsetSum
    intro i _
    exact (continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => ne_of_gt (hgap z hz i))
  have hl : N ≤ saddleSum lam a l := by
    calc
      N = (l - a * lam top)⁻¹ := by simp [l]
      _ ≤ ∑ i, (l - a * lam i)⁻¹ := by
        apply Finset.single_le_sum (f := fun i : ι => (l - a * lam i)⁻¹)
        · intro i _
          exact inv_nonneg.mpr (le_of_lt (hgap l ⟨le_rfl, hlu⟩ i))
        · exact Finset.mem_univ top
  have hu : saddleSum lam a u ≤ N := by
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hden : 1 ≤ u - a * lam i := by
          have hm := mul_le_mul_of_nonneg_left (htop i) ha
          dsimp [u]
          linarith
        exact (inv_le_one₀ (by linarith : 0 < u - a * lam i)).mpr hden
      _ = N := by simp [N]
  obtain ⟨z, hz, hroot⟩ := intermediate_value_Icc' hlu hcont ⟨hu, hl⟩
  refine ⟨z, ⟨hgap z hz, hroot⟩, ?_⟩
  intro y hy
  rcases lt_trichotomy y z with h | h | h
  · have := saddleSum_strictAnti lam a y z hy.1 h
    rw [hy.2, hroot] at this
    exact False.elim (lt_irrefl N this)
  · exact h
  · have := saddleSum_strictAnti lam a z y (hgap z hz) h
    rw [hy.2, hroot] at this
    exact False.elim (lt_irrefl N this)

def sphericalObjective (lam : ι → ℝ) (a z : ℝ) : ℝ :=
  (z - 1) / 2 - (∑ i, Real.log (z - a * lam i)) / (2 * Fintype.card ι)

lemma log_tangent_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h
  convert h using 1
  field_simp

lemma log_tangent_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≠ x) :
    Real.log y - Real.log x < (y - x) / x := by
  have hh : y / x ≠ 1 := by
    intro h
    exact hxy ((div_eq_one_iff_eq (ne_of_gt hx)).mp h)
  have h := Real.log_lt_sub_one_of_pos (div_pos hy hx) hh
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h
  convert h using 1
  field_simp

theorem spherical_saddle_strict_min (lam : ι → ℝ) (a z : ℝ)
    (hz : ∀ i, 0 < z - a * lam i)
    (hroot : saddleSum lam a z = Fintype.card ι)
    (y : ℝ) (hy : ∀ i, 0 < y - a * lam i) (hyz : y ≠ z) :
    sphericalObjective lam a z < sphericalObjective lam a y := by
  classical
  have hlog : ∀ i, Real.log (y - a * lam i) - Real.log (z - a * lam i) <
      (y - z) * (z - a * lam i)⁻¹ := by
    intro i
    have hne : y - a * lam i ≠ z - a * lam i := by
      intro h
      exact hyz (by linarith)
    convert log_tangent_strict (hz i) (hy i) hne using 1; ring
  have hsum : (∑ i, Real.log (y - a * lam i)) -
      (∑ i, Real.log (z - a * lam i)) < (y - z) * Fintype.card ι := by
    rw [← Finset.sum_sub_distrib, ← hroot]
    unfold saddleSum
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro i _
      exact (hlog i).le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i, Finset.mem_univ i, hlog i⟩
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  unfold sphericalObjective
  have h := (div_lt_div_iff_of_pos_right (show 0 < 2 * (Fintype.card ι : ℝ) by positivity)).mpr hsum
  have heq : ((y - z) * (Fintype.card ι : ℝ)) / (2 * Fintype.card ι) = (y - z) / 2 := by
    field_simp
  rw [heq, sub_div] at h
  linarith

lemma spherical_saddle_min (lam : ι → ℝ) (a z : ℝ)
    (hz : ∀ i, 0 < z - a * lam i)
    (hroot : saddleSum lam a z = Fintype.card ι)
    (y : ℝ) (hy : ∀ i, 0 < y - a * lam i) :
    sphericalObjective lam a z ≤ sphericalObjective lam a y := by
  by_cases h : y = z
  · subst y
    exact le_rfl
  · exact (spherical_saddle_strict_min lam a z hz hroot y hy h).le

omit [Nonempty ι] in
lemma spherical_saddle_upper (lam : ι → ℝ) (a z : ℝ) (ha : 0 ≤ a)
    (top : ι) (htop : ∀ i, lam i ≤ lam top)
    (hroot : saddleSum lam a z = Fintype.card ι) :
    z ≤ 1 + a * lam top := by
  classical
  by_contra! h
  have hi : ∀ i, (z - a * lam i)⁻¹ < 1 := by
    intro i
    have hm := mul_le_mul_of_nonneg_left (htop i) ha
    have hden : 1 < z - a * lam i := by linarith
    simpa using one_div_lt_one_div_of_lt zero_lt_one hden
  have hs : saddleSum lam a z < ∑ _i : ι, (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hi i).le
    · exact ⟨top, Finset.mem_univ top, hi top⟩
  simp [hroot] at hs

omit [Nonempty ι] in
lemma spherical_saddle_lower (lam : ι → ℝ) (a z : ℝ) (ha : 0 ≤ a)
    (bot : ι) (hbot : ∀ i, lam bot ≤ lam i)
    (hz : ∀ i, 0 < z - a * lam i)
    (hroot : saddleSum lam a z = Fintype.card ι) :
    1 + a * lam bot ≤ z := by
  classical
  by_contra! h
  have hi : ∀ i, 1 < (z - a * lam i)⁻¹ := by
    intro i
    have hm := mul_le_mul_of_nonneg_left (hbot i) ha
    have hden : z - a * lam i < 1 := by linarith
    simpa using one_div_lt_one_div_of_lt (hz i) hden
  have hs : (∑ _i : ι, (1 : ℝ)) < saddleSum lam a z := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hi i).le
    · exact ⟨bot, Finset.mem_univ bot, hi bot⟩
  simp [hroot] at hs

omit [Nonempty ι] in
theorem spherical_saddle_variance_bounds (lam : ι → ℝ) (a z : ℝ)
    (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (top : ι) (htop : ∀ i, lam i ≤ lam top)
    (hbounded : ∀ i, |lam i| ≤ 3)
    (hz : ∀ i, 0 < z - a * lam i)
    (hroot : saddleSum lam a z = Fintype.card ι) :
    ∀ i, (1 / 13 : ℝ) ≤ (z - a * lam i)⁻¹ ∧
      (z - a * lam i)⁻¹ ≤ Fintype.card ι := by
  classical
  have hupper := spherical_saddle_upper lam a z ha top htop hroot
  intro i
  constructor
  · have hltop : lam top ≤ 3 := (abs_le.mp (hbounded top)).2
    have hli : -3 ≤ lam i := (abs_le.mp (hbounded i)).1
    have hm := mul_le_mul_of_nonneg_left (show lam top - lam i ≤ 6 by linarith) ha
    have hden : z - a * lam i ≤ 13 := by nlinarith
    simpa only [one_div] using one_div_le_one_div_of_le (hz i) hden
  · rw [← hroot]
    exact Finset.single_le_sum
      (fun j _ => inv_nonneg.mpr (hz j).le) (Finset.mem_univ i)

end CriticalSK

end

end OAI
