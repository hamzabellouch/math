import Mathlib
import OAI.Combinatorics.KMedian.Process.Taper

namespace OAI

section
section
namespace MetricKMedian.Taper
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_data (Δ : ℕ) {g P : ℝ} (d : I → ℝ) (own : Finset I)
    (hg : 0 < g) (hunit : g*(Δ : ℝ)=1)
    (hP : 0 < P) (hP1 : P ≤ 1/2) (hd : ∀ i, 0 ≤ d i)
    (htotal : 1 ≤ ∑ _i : I, g)
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    ∃ (N : ℝ) (q : I → ℝ), 0 ≤ N ∧
      (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧
      (∀ i ∈ own, q i=1) ∧
      (∀ i, q i < 1 → N*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ N*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P d (1/R) → N ≤ R) := by
  by_cases hc : colocatedMass g d < 1
  · obtain ⟨r, hr, heq, hmin⟩ := exists_minimal_radius d hg hP hP1 hd htotal hc
    let q := fun i => marginal P (d i) r
    have hsum : ∑ i, q i=Δ := by
      apply (mul_left_cancel₀ (ne_of_gt hg))
      rw [Finset.mul_sum, hunit]
      exact heq
    refine ⟨1/r, q, (one_div_pos.mpr hr).le,
      fun _ => marginal_nonneg hP, fun i => marginal_le_one P (d i) r,
      heq, hsum, ?_, ?_, ?_, ?_⟩
    · intro i hi
      dsimp only [q]
      rw [hown i hi]
      exact marginal_at_zero_distance hP (by linarith only [hP1])
    · intro i hi
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hr).mpr
      have hh := lower_comparison hP hi
      nlinarith only [hh]
    · intro i hi
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ hr).mpr
      have hh := upper_comparison hP hi
      nlinarith only [hh]
    · intro R hR hmass
      apply (div_le_iff₀ hr).mpr
      have hh := (div_le_iff₀ hR).mp (hmin (1/R) hmass)
      nlinarith only [hh]
  · have hc1 : 1 ≤ colocatedMass g d := le_of_not_gt hc
    let Z := Finset.univ.filter (fun i => d i=0)
    have hz : (Z.card : ℝ)*g=colocatedMass g d := by
      simp only [Z, colocatedMass, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hzcard : Δ ≤ Z.card := by
      have hh : (Δ : ℝ) ≤ Z.card := by nlinarith only [hc1, hz, hunit, hg]
      exact_mod_cast hh
    have hsub : own ⊆ Z := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hown i hi⟩
    obtain ⟨S, hownS, hSZ, hScard⟩ := Finset.exists_subsuperset_card_eq hsub howncard hzcard
    let q := fun i => if i ∈ S then (1:ℝ) else 0
    have hq0 : ∀ i, 0 ≤ q i := by intro i; dsimp only [q]; split_ifs <;> norm_num
    have hq1 : ∀ i, q i ≤ 1 := by intro i; dsimp only [q]; split_ifs <;> norm_num
    have hsum : ∑ i, q i=Δ := by
      simp only [q, ← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const,
        nsmul_eq_mul, mul_one, hScard]
    refine ⟨0, q, le_refl 0, hq0, hq1, ?_, hsum, ?_, ?_, ?_, ?_⟩
    · rw [← Finset.mul_sum, hsum, hunit]
    · intro i hi
      exact ite_eq_left (hownS hi)
    · intro i _
      simpa only [zero_mul] using hd i
    · intro i hi
      have hiS : i ∈ S := by
        by_contra hn
        simp only [q, ite_eq_right hn] at hi
        exact lt_irrefl _ hi
      have hid := (Finset.mem_filter.mp (hSZ hiS)).2
      simp only [zero_mul, hid, le_refl]
    · intro R hR _
      exact hR.le

omit [DecidableEq I] in

theorem mass_from_near_unit {g P D : ℝ} (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P < 1) (hD : 0 < D)
    (hunit : (S.card : ℝ)*g=1) (hnear : ∀ i ∈ S, d i ≤ D) :
    1 ≤ mass g P d ((1-P)/D) := by
  have hq : ∀ i ∈ S, marginal P (d i) ((1-P)/D)=1 := by
    intro i hi
    apply marginal_one hP
    have hh := mul_le_mul_of_nonneg_left (hnear i hi)
      (div_nonneg (sub_nonneg.mpr hP1.le) hD.le)
    rw [div_mul_cancel₀ _ (ne_of_gt hD)] at hh
    exact hh
  have hs : (∑ i ∈ S, g*marginal P (d i) ((1-P)/D))=1 := by
    calc
      _ = ∑ _i ∈ S, g := Finset.sum_congr rfl (fun i hi => by rw [hq i hi, mul_one])
      _ = 1 := by rw [Finset.sum_const, nsmul_eq_mul, hunit]
  calc
    1 = ∑ i ∈ S, g*marginal P (d i) ((1-P)/D) := hs.symm
    _ ≤ mass g P d ((1-P)/D) :=
      Finset.sum_le_univ_sum_of_nonneg (fun i => mul_nonneg hg (marginal_nonneg hP))

end MetricKMedian.Taper
end
end

end OAI
