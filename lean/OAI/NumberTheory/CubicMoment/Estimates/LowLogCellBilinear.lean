import OAI.NumberTheory.CubicMoment.Estimates.LogCellMajorant
import OAI.NumberTheory.CubicMoment.Estimates.LowThinBilinear

namespace OAI

/-! The published-input dispersion bound on the actual disjoint log cells.
Restricting either finite coefficient sequence is performed explicitly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem low_logCell_bilinear_height_square
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ d : ℕ, ∀ q : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J : ℝ), 8 ≤ J → ∀ (P S : Finset Eisenstein)
        (α β : Eisenstein → ℂ) (Z A B T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ a ∈ P, primary a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      ∀ i ∈ P.image (logNormCell J A), ∀ j : ℤ,
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ logNormCellSupport P J A i,
          ∑ b ∈ logNormCellSupport S J B j,
            α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖^2) T ≤
        K*((A/J)*(∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2)+
          J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q)*
          (∑ a ∈ logNormCellSupport P J A i, ‖α a‖^2) := by
  obtain ⟨d,hfamily⟩ := low_thinCell_bilinear_height_square hpnt hMV hC hHuxley
  refine ⟨d,?_⟩
  intro q
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily q
  refine ⟨16*K,Ct,by positivity,?_⟩
  intro J hJ P S α β Z A B T M u hZ hA hT hM hP hS hβ i hi j
  have hJp : 0 < J := by linarith
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hAp : 0 < A := lt_of_lt_of_le (by positivity : 0 < 2*Z^(3/2:ℝ)) hA
  obtain ⟨a,ha,hai⟩ := Finset.mem_image.mp hi
  have hai' : logNormCell J A a = i := hai
  have hscale := logCellScale_bounds hJ hAp (hP a ha).1 (hP a ha).2
  rw [hai'] at hscale
  have hAi : 0 < logCellScale J A i := logCellScale_pos hJp hAp i
  have hAiZ : Z^(3/2:ℝ) ≤ logCellScale J A i := by linarith [hscale.1]
  have hPa : ∀ a ∈ logNormCellSupport P J A i, primary a ∧
      1+1/(4*(J/8)) ≤ norm a/logCellScale J A i ∧
        norm a/logCellScale J A i ≤ 1+3/(4*(J/8)) := by
    intro a ha
    obtain ⟨ha,hai⟩ := Finset.mem_filter.mp ha
    refine ⟨(hP a ha).1,?_⟩
    have hb := log_cell_plateau (norm_pos_of_ne_zero (primary_ne_zero (hP a ha).1))
      hAp hJ (logNormCell J A a) (logNormCell_bounds J A a)
    rwa [hai] at hb
  have hSb : ∀ b ∈ logNormCellSupport S J B j,
      primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z :=
    fun b hb => hS b (Finset.mem_filter.mp hb).1
  have hh := hbound (J/8) (by linarith) (logNormCellSupport P J A i)
    (logNormCellSupport S J B j) α β Z (logCellScale J A i) T M u hZ hAiZ hT hM hPa hSb
    (fun b hb => hβ b (Finset.mem_filter.mp hb).1)
  have hm : logCellScale J A i/(J/8) ≤ 16*(A/J) := by
    calc
      _ ≤ (2*A)/(J/8) := div_le_div_of_nonneg_right hscale.2 (by positivity)
      _ = _ := by field_simp; ring
  have hp : (J/8)^d ≤ J^d := pow_le_pow_left₀ (by positivity) (by linarith) d
  have hpow : (logCellScale J A i)^(2/3:ℝ) ≤ 2*A^(2/3:ℝ) := by
    have ht : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (2/3:ℝ) ≤ 1)
    calc
      _ ≤ (2*A)^(2/3:ℝ) := Real.rpow_le_rpow hAi.le hscale.2 (by norm_num)
      _ = (2:ℝ)^(2/3:ℝ)*A^(2/3:ℝ) := Real.mul_rpow (by norm_num) hAp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (by positivity)
  have hrem : (J/8)^d*M^2*(logCellScale J A i)^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q ≤
      2*(J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q) := by
    have hm := mul_le_mul hp hpow (by positivity) (by positivity)
    have hm' := mul_le_mul_of_nonneg_right hm
      (show 0 ≤ M^2*Z^(5/3:ℝ)/(1+Real.log Z)^q by positivity)
    convert hm' using 1 <;> ring
  let Eb := ∑ b ∈ logNormCellSupport S J B j, ‖β b‖^2
  have hEb : 0 ≤ Eb := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : (logCellScale J A i/(J/8))*Eb+
      (J/8)^d*M^2*(logCellScale J A i)^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q ≤
      16*((A/J)*Eb+J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q) := by
    have hm' := mul_le_mul_of_nonneg_right hm hEb
    nlinarith [show 0 ≤ J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^q by positivity]
  apply hh.trans
  have he := mul_le_mul_of_nonneg_left hb hK.le
  have he' := mul_le_mul_of_nonneg_right he
    (Finset.sum_nonneg (fun a (_ : a ∈ logNormCellSupport P J A i) => sq_nonneg ‖α a‖))
  convert he' using 1
  ring

end CubicFirstMoment

end

end OAI
