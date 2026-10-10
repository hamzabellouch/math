import OAI.Analysis.FreeEntropy.OptionSeries

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
variable {α : Type} [Fintype α]

theorem cumulants_norm_le {M : Series α} (hM : M [] = 1) {A : ℝ} (hA : 0 < A)
    (h : ∀ n, 0 < n → degreeNorm M n ≤ A^n) (n : ℕ) :
    degreeNorm (cumulants M) n ≤ (32*A)^n := by
  let B := 4*A
  have hB : 0 < B := by dsimp [B]; positivity
  let r := B⁻¹
  have hr : 0 < r := inv_pos.mpr hB
  have hrA : r*A = 1/4 := by dsimp [r, B]; field_simp
  have hw (N : ℕ) : seriesWeight (M-unit) r N ≤ 1/3 := by
    have hz : (M-unit : Series α) [] = 0 := by simp [hM]
    have hb (m : ℕ) (hm : 0 < m) : degreeNorm (M-unit) m ≤ A^m := by
      rw [degreeNorm_sub_unit_pos M hm]
      exact h m hm
    have hh := weight_le_geom hz hA.le hr.le (by rw [hrA]; norm_num) hb N
    norm_num [hrA] at hh ⊢
    exact hh
  have hwB (N : ℕ) : seriesWeight (boolean M) r N ≤ 1/2 := by
    have he : boolean M = -(inverse M-unit) := by unfold boolean; abel
    rw [he, seriesWeight_neg]
    have hh := inverse_tail_weight hM hr.le (by norm_num : (0:ℝ) ≤ 1/3)
      (by norm_num : (1:ℝ)/3 < 1) N (hw N)
    norm_num at hh ⊢
    exact hh
  have hBn (m : ℕ) : degreeNorm (boolean M) m ≤ B^m := by
    have hh := degreeNorm_le_of_weight hr (fun N => (hwB N).trans (by norm_num)) m
    simpa [r] using hh
  let t := (8*B)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have htB : (2*t)*B = 1/4 := by dsimp [t]; field_simp ; ring
  have hneg : (-boolean M) [] = 0 := by simp
  have hnegW (N : ℕ) : seriesWeight (-boolean M) (2*t) N ≤ 1/3 := by
    have hh := weight_le_geom hneg hB.le (by positivity : 0 ≤ 2*t)
      (by rw [htB]; norm_num) (fun m _ => by simpa using hBn m) N
    norm_num [htB] at hh ⊢
    exact hh
  have hJ (N : ℕ) : seriesWeight (moments (-boolean M)-unit) t N ≤ 1/3 :=
    moments_tail_weight hneg ht.le (by norm_num) (by norm_num) hnegW N
  have hR (N : ℕ) : seriesWeight (cumulants M) t N ≤ 1 := by
    have hh := inverse_tail_weight (moments_nil (-boolean M)) ht.le
      (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num : (1:ℝ)/3 < 1) N (hJ N)
    change seriesWeight (cumulants M) t N ≤ _ at hh
    norm_num at hh
    exact hh.trans (by norm_num)
  have hh := degreeNorm_le_of_weight ht hR n
  norm_num [t, B, ← mul_assoc] at hh
  exact hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
