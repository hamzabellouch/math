import Mathlib

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace SlopeRational

theorem eventually_lt_of_quadratic_expansion {C : ℝ → ℝ} {A B : ℝ}
    (hB : B < 0)
    (hrem : IsLittleO (𝓝[>] (0 : ℝ))
      (fun ε => C ε - (A + B * ε ^ 2)) (fun ε => ε ^ 2)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), C ε < A := by
  have hb := hrem.bound (show 0 < -B / 2 by linarith)
  filter_upwards [hb, self_mem_nhdsWithin] with ε hε heps
  have he : 0 < ε := heps
  have hh : |C ε - (A + B * ε ^ 2)| ≤ (-B / 2) * ε ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_sq] using hε
  have hupper := (abs_le.mp hh).2
  have hneg : B * ε ^ 2 < 0 := mul_neg_of_neg_of_pos hB (sq_pos_of_pos he)
  linarith

theorem fourth_order_implies_quadratic_littleO {f : ℝ → ℝ}
    (hf : IsBigO (𝓝[>] (0 : ℝ)) f (fun ε => ε ^ 4)) :
    IsLittleO (𝓝[>] (0 : ℝ)) f (fun ε => ε ^ 2) := by
  exact hf.trans_isLittleO ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 4 by norm_num)).mono
    nhdsWithin_le_nhds)

theorem rpow_littleO_rpow_zero {r s : ℝ} (hrs : r < s) :
    IsLittleO (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ε ^ s) (fun ε : ℝ => ε ^ r) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with ε he
    have hepos : 0 < ε := he
    intro hz
    exact False.elim ((Real.rpow_pos_of_pos hepos r).ne' hz)
  · have hcont := (Real.continuous_rpow_const (sub_nonneg.mpr hrs.le)).continuousAt
      (x := (0 : ℝ))
    have ht : Tendsto (fun ε : ℝ => ε ^ (s - r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa [Real.zero_rpow (sub_ne_zero.mpr hrs.ne')] using
        hcont.tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε he
    exact Real.rpow_sub he s r

theorem vanishing_padding_conditions :
    (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ^ (5 / 2 : ℝ)) ∧
    IsBigO (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ε ^ (5 / 2 : ℝ)) (fun ε => ε ^ 2) ∧
    IsLittleO (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ε ^ 3)
      (fun ε : ℝ => ε ^ (5 / 2 : ℝ)) ∧
    IsLittleO (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ε ^ (5 / 2 : ℝ))
      (fun ε => ε ^ 2) := by
  have hsmall : IsLittleO (𝓝[>] (0 : ℝ))
      (fun ε : ℝ => ε ^ (5 / 2 : ℝ)) (fun ε => ε ^ 2) := by
    convert rpow_littleO_rpow_zero (show (2 : ℝ) < 5 / 2 by norm_num) using 1
    simp only [Real.rpow_ofNat]
  refine ⟨?_, hsmall.isBigO, ?_, hsmall⟩
  · filter_upwards [self_mem_nhdsWithin] with ε he
    exact Real.rpow_pos_of_pos he _
  · convert rpow_littleO_rpow_zero (show (5 / 2 : ℝ) < 3 by norm_num) using 1
    simp only [Real.rpow_ofNat]

theorem quadratic_padding_conditions {η : ℝ} (hη : 0 < η) :
    (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < η * ε ^ 2) ∧
    IsBigO (𝓝[>] (0 : ℝ)) (fun ε : ℝ => η * ε ^ 2) (fun ε => ε ^ 2) ∧
    IsLittleO (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ε ^ 3) (fun ε => η * ε ^ 2) := by
  refine ⟨?_, (isBigO_refl (fun ε : ℝ => ε ^ 2) _).const_mul_left η, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε he
    exact mul_pos hη (sq_pos_of_pos he)
  · apply IsLittleO.const_mul_right hη.ne'
    exact (isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).mono nhdsWithin_le_nhds

theorem quadratic_padding_cost_lt {C : ℝ → ℝ} {A J I η : ℝ}
    (hgap : J - I + η / 2 < 0)
    (hrem : IsBigO (𝓝[>] (0 : ℝ))
      (fun ε => C ε - (A + ε ^ 2 * (J - I) + (η * ε ^ 2) / 2))
      (fun ε => ε ^ 4)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), C ε < A := by
  apply eventually_lt_of_quadratic_expansion hgap
  exact (fourth_order_implies_quadratic_littleO hrem).congr_left (fun ε => by ring)

theorem vanishing_padding_cost_lt {C : ℝ → ℝ} {A J I : ℝ}
    (hgap : J < I)
    (hrem : IsBigO (𝓝[>] (0 : ℝ))
      (fun ε => C ε - (A + ε ^ 2 * (J - I) + (ε ^ (5 / 2 : ℝ)) / 2))
      (fun ε => ε ^ 4)) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), C ε < A := by
  apply eventually_lt_of_quadratic_expansion (show J - I < 0 by linarith)
  have hp := vanishing_padding_conditions.2.2.2.const_mul_left (1 / 2 : ℝ)
  exact ((fourth_order_implies_quadratic_littleO hrem).add hp).congr_left
    (fun ε => by ring)

theorem exists_positive_regularization_gap {J I : ℝ → ℝ} {j i : ℝ}
    (hJ : Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 j))
    (hI : Tendsto I (𝓝[>] (0 : ℝ)) (𝓝 i)) (hgap : j < i) :
    ∃ d : ℝ, 0 < d ∧ J d < I d := by
  have hg := hJ.eventually_lt hI hgap
  have he : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d ∧ J d < I d := by
    filter_upwards [self_mem_nhdsWithin, hg] with d hd hdi
    exact ⟨hd, hdi⟩
  exact he.exists

end SlopeRational

end

end OAI
