import OAI.Geometry.Kahler.BaseChartSeries

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma chartScale_nonneg (k : ℕ) (δ : ℝ) : 0 ≤ chartScale k δ := by
  unfold chartScale
  split <;> positivity

lemma chartScale_le_inverse {k : ℕ} {δ : ℝ} (hkδ : 0 < (k:ℝ)*δ) :
    chartScale k δ ≤ 16/((k:ℝ)*δ) := by
  unfold chartScale
  split_ifs with h
  · have hs := Real.sqrt_le_one.mpr h
    have hi : 1 ≤ 16/((k:ℝ)*δ) := (le_div_iff₀ hkδ).mpr (by linarith)
    exact hs.trans hi
  · have hpos : 0 < (k:ℝ)*δ/16 := by positivity
    have he : (k:ℝ)*δ/16 ≤ Real.exp ((k:ℝ)*δ/16) := by linarith [Real.add_one_le_exp ((k:ℝ)*δ/16)]
    have hh := one_div_le_one_div_of_le hpos he
    rw [one_div, ← Real.exp_neg] at hh
    calc Real.exp (-(k:ℝ)*δ/16) = Real.exp (-((k:ℝ)*δ/16)) := congrArg Real.exp (by ring)
         _ ≤ 1/((k:ℝ)*δ/16) := hh
         _ = 16/((k:ℝ)*δ) := by field_simp

lemma chartScale_summable {Q : ℕ} (hQ : 2 ≤ Q) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun j => chartScale (Q^(j+1)) δ) := by
  have hQ0 : 0 < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hi : (Q:ℝ)⁻¹ < 1 := (inv_lt_one₀ hQ0).mpr (by exact_mod_cast hQ)
  have hs := (summable_geometric_of_lt_one (inv_nonneg.mpr hQ0.le) hi).mul_left (16/δ*(Q:ℝ)⁻¹)
  apply Summable.of_nonneg_of_le (fun j => chartScale_nonneg _ _) _ hs
  intro j
  apply (chartScale_le_inverse (by rw [Nat.cast_pow]; positivity : 0 < ((Q^(j+1):ℕ):ℝ)*δ)).trans_eq
  rw [Nat.cast_pow,pow_succ,inv_pow]
  field_simp

lemma chartScale_sum_uniform {Q : ℕ} (hQ : 2 ≤ Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → (∑' j, chartScale (Q^(j+1)) δ) ≤ B := by
  have hQ1 : 1 < (Q:ℝ) := by exact_mod_cast (show 1 < Q by omega)
  have hQ0 : 0 < (Q:ℝ) := by linarith
  let s := Real.sqrt (Q:ℝ)
  have hs : 1 < s := by
    dsimp [s]
    exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hQ1)
  have hsPow (n : ℕ) : Real.sqrt ((Q:ℝ)^n) = s^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hQ0.le _), ih, pow_succ]
  have hspos : 0 < s-1 := by linarith
  have hi : (Q:ℝ)⁻¹ < 1 := (inv_lt_one₀ hQ0).mpr hQ1
  let B := s/(s-1)+16/(1-(Q:ℝ)⁻¹)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro δ hδ
  have hex : ∃ J : ℕ, 1 < (Q:ℝ)^(J+1)*δ := by
    obtain ⟨J,hJ⟩ := exists_nat_gt (1/δ)
    have hd := (div_lt_iff₀ hδ).mp hJ
    have hg : (J+1:ℝ) ≤ (Q:ℝ)^(J+1) := by exact_mod_cast lacunary_degree_ge hQ J
    refine ⟨J,?_⟩
    nlinarith
  let J := Nat.find hex
  have hJ : 1 < (Q:ℝ)^(J+1)*δ := Nat.find_spec hex
  have hlow (j : ℕ) (hj : j < J) : (Q:ℝ)^(j+1)*δ ≤ 1 := le_of_not_gt (Nat.find_min hex hj)
  have hpow : J=0 ∨ (Q:ℝ)^J*δ ≤ 1 := by
    by_cases hzero : J=0
    · exact Or.inl hzero
    · right
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hh := hlow m (by omega)
      simpa [hm,Nat.succ_eq_add_one] using hh
  have hlo : (∑ j ∈ Finset.range J, chartScale (Q^(j+1)) δ) ≤ s/(s-1) := by
    by_cases hzero : J=0
    · simp only [hzero,Finset.range_zero,Finset.sum_empty]
      exact div_nonneg (by linarith) hspos.le
    have hp : (Q:ℝ)^J*δ ≤ 1 := hpow.resolve_left hzero
    have hsδ : s^J*Real.sqrt δ ≤ 1 := by
      have hh := Real.sqrt_le_one.mpr hp
      simpa only [Real.sqrt_mul (pow_nonneg hQ0.le _),hsPow] using hh
    have heach (j : ℕ) (hj : j ∈ Finset.range J) : chartScale (Q^(j+1)) δ = s*Real.sqrt δ*s^j := by
      rw [chartScale,ite_eq_left (by rw [Nat.cast_pow]; exact hlow j (Finset.mem_range.mp hj)),Nat.cast_pow,
        Real.sqrt_mul (pow_nonneg hQ0.le _),hsPow,pow_succ]
      dsimp [s]
      ring
    rw [Finset.sum_congr rfl heach,← Finset.mul_sum]
    apply (le_div_iff₀ hspos).mpr
    have hg := geom_sum_mul s J
    have heq : (s*Real.sqrt δ*∑ j ∈ Finset.range J, s^j)*(s-1)=s*Real.sqrt δ*(s^J-1) := by
      rw [mul_assoc,geom_sum_mul]
    rw [heq]
    have hsq := Real.sqrt_nonneg δ
    nlinarith
  have htail : (∑' m, chartScale (Q^(m+J+1)) δ) ≤ 16/(1-(Q:ℝ)⁻¹) := by
    have hsum := summable_geometric_of_lt_one (inv_nonneg.mpr hQ0.le) hi
    have ht : Summable (fun m => chartScale (Q^(m+J+1)) δ) :=
      (chartScale_summable hQ hδ).comp_injective (fun m n h => Nat.add_right_cancel h)
    have hh := ht.tsum_le_tsum (g := fun m => 16*((Q:ℝ)⁻¹)^m) (fun m => ?_) (hsum.mul_left 16)
    · rw [tsum_mul_left,tsum_geometric_of_lt_one (inv_nonneg.mpr hQ0.le) hi] at hh
      exact hh.trans_eq (by ring)
    apply (chartScale_le_inverse (by rw [Nat.cast_pow]; positivity : 0 < ((Q^(m+J+1):ℕ):ℝ)*δ)).trans
    have heq : 16/(((Q^(m+J+1):ℕ):ℝ)*δ) = (16/((Q:ℝ)^(J+1)*δ))*((Q:ℝ)⁻¹)^m := by
      rw [Nat.cast_pow,show m+J+1=(J+1)+m by omega,pow_add,inv_pow]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity : 0 < (Q:ℝ)^(J+1)*δ)).mpr (by linarith)) (by positivity)
  rw [← (chartScale_summable hQ hδ).sum_add_tsum_nat_add J]
  exact add_le_add hlo htail

end PinchedHartogs.BaseConstruction

end

end OAI
