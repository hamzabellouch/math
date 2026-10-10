import OAI.Dynamics.StandardMap.BridgeLinear

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma geometric_Ico_bound (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1/2) (l B : ℕ) :
    ∑ i ∈ Finset.Ico l B, q^i ≤ 2*q^l := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add,mul_comm (q^l)]
  rw [← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range (B-l), q^i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (B-l), (1/2:ℝ)^i := by gcongr
      _ ≤ 2 := sum_geometric_two_le (B-l)
  exact mul_le_mul_of_nonneg_right hs (pow_nonneg hq _)
lemma stable_error_sum (M c : ℝ) (D : ℕ → ℝ) (l B : ℕ) (hM : 1 < M)
    (_hc : 0 < c) (hq : M ^ (-2*c) ≤ 1/2) (_hl : 1 ≤ l) (_hlB : l ≤ B)
    (hD : ∀ i, l ≤ i → i ≤ B → M^(c*(i:ℝ)) ≤ D i) :
    ∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) ≤ 2*M^(1-c-2*c*(l:ℝ)) := by
  have hpos : 0 < M := by linarith
  have hqpos : 0 ≤ M ^ (-2*c) := Real.rpow_nonneg hpos.le _
  have hpoint (i : ℕ) (hi : i ∈ Finset.Ico l B) :
      M/(D i*D (i+1)) ≤ M^(1-c)*(M^(-2*c))^i := by
    obtain ⟨hli,hiB⟩:=Finset.mem_Ico.mp hi
    have hDi := hD i hli (by omega)
    have hDi' := hD (i+1) (by omega) (by omega)
    have hi0 : 0 < D i := (Real.rpow_pos_of_pos hpos _).trans_le hDi
    have hi1 : 0 < D (i+1) := (Real.rpow_pos_of_pos hpos _).trans_le hDi'
    calc
      _ ≤ M/(M^(c*(i:ℝ))*M^(c*((i+1:ℕ):ℝ))) := by
        apply div_le_div_of_nonneg_left hpos.le (by positivity)
        exact mul_le_mul hDi hDi' (Real.rpow_nonneg hpos.le _) hi0.le
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one M]
        rw [← Real.rpow_add hpos,← Real.rpow_sub hpos,← Real.rpow_mul_natCast,← Real.rpow_add hpos]
        · congr 1
          push_cast
          ring
        · exact hpos.le
  calc
    _ ≤ ∑ i ∈ Finset.Ico l B, M^(1-c)*(M^(-2*c))^i := Finset.sum_le_sum hpoint
    _ = M^(1-c)*∑ i ∈ Finset.Ico l B, (M^(-2*c))^i := by rw [Finset.mul_sum]
    _ ≤ M^(1-c)*(2*(M^(-2*c))^l) :=
      mul_le_mul_of_nonneg_left (geometric_Ico_bound _ hqpos hq l B) (Real.rpow_nonneg hpos.le _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hpos.le]
      have hh:=Real.rpow_add hpos (1-c) ((-2*c)*(l:ℝ))
      rw [show 1-c-2*c*(l:ℝ)=1-c+(-2*c)*(l:ℝ) by ring,hh]
      ring
lemma stable_prefix_power_bound (M : ℝ) (D : ℕ → ℝ) (l B : ℕ)
    (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2) (hl : 1 ≤ l) (hlB : l ≤ B)
    (hD : ∀ i, l ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ D i)
    (hu : D l ≤ M^(l:ℝ)) :
    (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)) := by
  have hp : 0 < M := by linarith
  have hlR : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hsum:=stable_error_sum M (49/50) D l B hM (by norm_num) (by convert hq using 1 ; norm_num) hl hlB hD
  have hDl :=hD l le_rfl hlB
  have hDpos : 0 < D l := (Real.rpow_pos_of_pos hp _).trans_le hDl
  have hinv : (D l)⁻¹ ≤ M^(-(49/50:ℝ)*(l:ℝ)) := by
    rw [neg_mul,Real.rpow_neg hp.le]
    exact inv_le_inv₀ hDpos (Real.rpow_pos_of_pos hp _) |>.mpr hDl
  have hi : M^(-(49/50:ℝ)*(l:ℝ)) ≤ M^(-(47/50:ℝ)*(l:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hM.le (by nlinarith)
  have hmul : D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1))) ≤ 2*M^(-(47/50:ℝ)*(l:ℝ)) := by
    calc
      _ ≤ M^(l:ℝ)*(2*M^(1-49/50-2*(49/50)*(l:ℝ))) :=
        mul_le_mul hu hsum (Finset.sum_nonneg fun i hi => by
          have hi':=Finset.mem_Ico.mp hi
          have h0 := (Real.rpow_pos_of_pos hp _).trans_le (hD i hi'.1 (by omega))
          have h1 := (Real.rpow_pos_of_pos hp _).trans_le (hD (i+1) (by omega) (by omega))
          positivity) (Real.rpow_nonneg hp.le _)
      _ = 2*M^((l:ℝ)+(1-49/50-2*(49/50)*(l:ℝ))) := by rw [Real.rpow_add hp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le (by linarith)) (by norm_num)
  nlinarith
end StandardMapEntropy

end OAI
