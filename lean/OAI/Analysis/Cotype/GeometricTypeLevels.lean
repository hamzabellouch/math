import OAI.Analysis.Cotype.TypeExtrapolationParameters
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
theorem norm_le_one_of_lp_ball {N : ℕ} {p : ℝ} (hp : 0 < p)
    (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1) (i : Fin N) : ‖x i‖ ≤ 1 := by
  have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Real.rpow_nonneg (norm_nonneg (x j)) p)
    (Finset.mem_univ i)
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by norm_num) hp).mp
  simpa only [Real.one_rpow] using hs.trans hx

omit [NormedSpace ℝ X] in

theorem exists_geometric_levels {N : ℕ} {r : ℝ} (hr : 1 < r)
    (x : Fin N → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ l : Fin N → ℕ, ∀ i, ‖x i‖ ≤ (r⁻¹)^(l i) ∧
      (x i ≠ 0 → (r⁻¹)^(l i+1) < ‖x i‖) := by
  classical
  have hr0 : 0 < r := by linarith
  have hq : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have hq0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have heach i : ∃ k : ℕ, ‖x i‖ ≤ (r⁻¹)^k ∧ (x i ≠ 0 → (r⁻¹)^(k+1) < ‖x i‖) := by
    by_cases hz : x i = 0
    · exact ⟨0,by simpa using hx i,fun hh => (hh hz).elim⟩
    have hex : ∃ k : ℕ, (r⁻¹)^(k+1) < ‖x i‖ := by
      obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hz) hq
      exact ⟨k,(by calc
        (r⁻¹)^(k+1) = (r⁻¹)^k*r⁻¹ := pow_succ _ _
        _ ≤ (r⁻¹)^k := mul_le_of_le_one_right (pow_nonneg hq0.le _) hq.le
        _ < _ := hk)⟩
    let k := Nat.find hex
    refine ⟨k,?_,fun _ => Nat.find_spec hex⟩
    by_cases hk : k = 0
    · simpa only [hk,pow_zero] using hx i
    have hmin : ¬ (r⁻¹)^((k-1)+1) < ‖x i‖ :=
      Nat.find_min hex (show k-1 < k by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hmin
    exact le_of_not_gt hmin
  choose l hl using heach
  exact ⟨l,hl⟩

theorem real_pow_rpow_comm (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (p : ℝ) :
    (a^k)^p = (a^p)^k := by
  rw [← Real.rpow_natCast_mul ha,← Real.rpow_mul_natCast ha]
  congr 1
  ring

omit [NormedSpace ℝ X] in

theorem geometric_level_card_le {N n k : ℕ} (hn : 0 < n) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hrp : r^p = n)
    (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1)
    (s : Finset (Fin N)) (hs : ∀ i ∈ s, (r⁻¹)^(k+1) ≤ ‖x i‖) :
    s.card ≤ n^(k+1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : ((r⁻¹)^(k+1))^p = ((n : ℝ)^(k+1))⁻¹ := by
    rw [real_pow_rpow_comm _ (inv_nonneg.mpr hr.le),Real.inv_rpow hr.le,hrp,inv_pow]
  have hlo : (s.card : ℝ)*((n : ℝ)^(k+1))⁻¹ ≤ ∑ i ∈ s, ‖x i‖^p := by
    rw [← he]
    calc
      _ = ∑ _i ∈ s, ((r⁻¹)^(k+1))^p := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi => Real.rpow_le_rpow (by positivity) (hs i hi) hp.le)
  have hhi : (∑ i ∈ s, ‖x i‖^p) ≤ 1 := by
    apply le_trans _ hx
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hh := (mul_inv_le_iff₀ (pow_pos hn0 (k+1))).mp (hlo.trans hhi)
  have hh' : (s.card : ℝ) ≤ (n : ℝ)^(k+1) := by simpa using hh
  exact_mod_cast hh'

theorem geometric_block_bound {N n k : ℕ} {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r)
    (h : QuadraticTypeBound X (n^(k+1)) (A^(k+1)))
    (s : Finset (Fin N)) (hs : s.card ≤ n^(k+1))
    (x : Fin N → X) (hx0 : ∀ i, i ∉ s → x i = 0)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ (r⁻¹)^k) :
    cubeL2 X (rademacherSum X x) ≤
      Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by
  classical
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hAn : 0 ≤ A*n := mul_nonneg hA hn
  have hmass : (∑ i, ‖x i‖^2) ≤ (n : ℝ)^(k+1)*((r⁻¹)^k)^2 := by
    calc
      _ = ∑ i ∈ s, ‖x i‖^2 := (Finset.sum_subset (Finset.subset_univ _)
        (fun i _ hi => by rw [hx0 i hi,norm_zero]; norm_num)).symm
      _ ≤ ∑ _i ∈ s, ((r⁻¹)^k)^2 := Finset.sum_le_sum (fun i hi =>
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hx i hi))
      _ = (s.card : ℝ)*((r⁻¹)^k)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
  have hb := (h.support s hs x hx0).trans (mul_le_mul_of_nonneg_left hmass (pow_nonneg hA _))
  let C := Real.sqrt (A*n)
  have hC : C^2 = A*n := Real.sq_sqrt hAn
  have hCk : (C^k)^2 = (A*n)^k := by rw [← pow_mul,mul_comm k 2,pow_mul,hC]
  have he : (C*(C*r⁻¹)^k)^2 = A^(k+1)*(n : ℝ)^(k+1)*((r⁻¹)^k)^2 := by
    rw [mul_pow,mul_pow,mul_pow,hC,hCk]
    simp only [mul_pow,pow_succ]
    ring
  apply (sq_le_sq₀ (cubeL2_nonneg _) (by positivity)).mp
  rw [he]
  simpa only [mul_assoc] using hb

end Cotype

end

end OAI
