import OAI.NumberTheory.TotientAsymptotic.PrefixCoordinates
import OAI.NumberTheory.TotientAsymptotic.RenewalRatios
import OAI.NumberTheory.TotientAsymptotic.SimplexVolume

namespace OAI

/-! The bounded weights expressing each prefix coordinate in standard-simplex variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def prefixSimplexMap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  (weightedScale N).comp (prefixLinear N)

def prefixWeight (N : ℕ) (i j : Fin N) : ℝ :=
  if i ≤ j then g (j.val-i.val)/(rho^(i.val+1)*g (j.val+1)) else 0

lemma prefixSimplexMap_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i/rho^(i.val+1) = ∑ j, prefixWeight N i j*prefixSimplexMap N u j := by
  conv_lhs => rw [prefixLinear_coordinate N u i]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [prefixWeight, prefixSimplexMap, LinearMap.comp_apply, weightedScale_apply]
  split_ifs
  · field_simp [(g_pos (j.val+1)).ne']
  · simp

lemma sum_suffix_weights (N : ℕ) (i : Fin N) (f : ℕ → ℝ) :
    (∑ j : Fin N, if i ≤ j then f (j.val-i.val) else 0) =
      ∑ k ∈ Finset.range (N-i.val), f k := by
  change (∑ j : Fin N, if i.val ≤ j.val then f (j.val-i.val) else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => if i.val ≤ j then f (j-i.val) else 0)]
  have hs := Finset.sum_range_add (fun j => if i.val ≤ j then f (j-i.val) else 0)
    i.val (N-i.val)
  rw [Nat.add_sub_of_le (Nat.le_of_lt i.isLt)] at hs
  rw [hs]
  have hz : (∑ j ∈ Finset.range i.val, if i.val ≤ j then f (j-i.val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma prefixWeight_nonneg (N : ℕ) (i j : Fin N) : 0 ≤ prefixWeight N i j := by
  unfold prefixWeight
  split_ifs
  · exact div_nonneg (g_pos _).le (mul_pos (pow_pos rho_pos _) (g_pos _)).le
  · rfl

lemma prefixWeight_error {C : ℝ}
    (hC : ∀ i k : ℕ, |g k/(rho^i*g (i+k))-1| ≤ C*rho^k)
    (N : ℕ) (i j : Fin N) (hij : i ≤ j) :
    |prefixWeight N i j-1| ≤ C*rho^(j.val-i.val) := by
  have hh := hC (i.val+1) (j.val-i.val)
  have he : i.val+1+(j.val-i.val) = j.val+1 := by
    have : i.val ≤ j.val := hij
    omega
  simpa only [he, prefixWeight, ite_eq_left hij] using hh

/-- Uniform first- and second-moment bounds; the error is independent of dimension. -/
theorem prefixWeight_bounds : ∃ M K : ℝ, 1 ≤ M ∧ 0 < K ∧
    ∀ (N : ℕ) (i : Fin N),
      (∀ j, 0 ≤ prefixWeight N i j ∧ prefixWeight N i j ≤ M) ∧
      |(∑ j, prefixWeight N i j)-(N-i.val:ℕ)| ≤ K ∧
      (∑ j, (prefixWeight N i j)^2) ≤ M*((N-i.val:ℕ)+K) := by
  obtain ⟨C,hC,he⟩ := renewal_ratio_error
  let M := C+1
  let K := C/(1-rho)
  have hK : 0 < K := div_pos hC (sub_pos.mpr rho_lt_one)
  refine ⟨M,K,by dsimp [M]; linarith,hK,?_⟩
  intro N i
  have hpoint (j : Fin N) : |prefixWeight N i j-(if i ≤ j then 1 else 0)| ≤
      if i ≤ j then C*rho^(j.val-i.val) else 0 := by
    by_cases hij : i ≤ j
    · simpa only [ite_eq_left hij] using prefixWeight_error he N i j hij
    · simp [prefixWeight, hij]
  have hupper (j : Fin N) : prefixWeight N i j ≤ M := by
    by_cases hij : i ≤ j
    · have hh := (abs_le.mp (prefixWeight_error he N i j hij)).2
      have hp := pow_le_one₀ rho_pos.le rho_lt_one.le (n := j.val-i.val)
      dsimp [M]
      nlinarith
    · simp only [prefixWeight, ite_eq_right hij]
      dsimp [M]
      linarith
  have herror : |(∑ j, prefixWeight N i j)-(N-i.val:ℕ)| ≤ K := by
    have hone : (∑ j : Fin N, if i ≤ j then (1:ℝ) else 0) = (N-i.val:ℕ) := by
      rw [sum_suffix_weights N i (fun _ => 1)]
      simp
    rw [← hone, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |prefixWeight N i j-(if i ≤ j then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin N, if i ≤ j then C*rho^(j.val-i.val) else 0 := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = C*∑ k ∈ Finset.range (N-i.val), rho^k := by rw [sum_suffix_weights N i (fun k => C*rho^k), Finset.mul_sum]
      _ ≤ K := by
        have hg := (hasSum_geometric_of_lt_one rho_pos.le rho_lt_one).summable.sum_le_tsum
          (Finset.range (N-i.val)) (fun k _ => (pow_pos rho_pos k).le)
        rw [tsum_geometric_of_lt_one rho_pos.le rho_lt_one] at hg
        exact mul_le_mul_of_nonneg_left hg hC.le
  refine ⟨fun j => ⟨prefixWeight_nonneg N i j,hupper j⟩,herror,?_⟩
  calc
    _ ≤ M*(∑ j, prefixWeight N i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hn := prefixWeight_nonneg N i j
      have hu := hupper j
      nlinarith
    _ ≤ M*((N-i.val:ℕ)+K) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [M]; positivity)
      have hh := (abs_le.mp herror).2
      linarith

end TotientAsymptotic

end

end OAI
