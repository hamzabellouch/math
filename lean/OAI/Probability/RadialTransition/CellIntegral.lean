import OAI.Probability.RadialTransition.StarIntegral

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma cluster_rate_le {h α : ℝ} (h1 : h ≤ α) (h4 : 4*h-9 ≤ α)
    {n : ℕ} (hn : n ≤ 3) : h*(n+1)-3*n ≤ α := by
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn3 : (n:ℝ) ≤ 3 := by exact_mod_cast hn
  by_cases hh : h ≤ 3
  · nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hh)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hn3) (sub_nonneg.mpr (le_of_not_ge hh))]

lemma core_cluster_coefficient_bound {t h α : ℝ} (ht : 0 ≤ t)
    (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) {n : ℕ} (hn : n ≤ 3) :
    Real.exp (t*h*(n+1))/(n+1).factorial * Real.exp (-t*α) *
      ((n+1)*((2*((1+(1:ℝ)/1000)*microLength t))^3)^n) ≤ 3000 := by
  have hl := (microLength_pos t).le
  have hfac : (1:ℝ) ≤ (n+1).factorial := by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (n+1)))
  have he : Real.exp (t*h*(n+1))*Real.exp (-t*α)*
      (((2*((1+(1:ℝ)/1000)*microLength t))^3)^n) =
      Real.exp (t*(h*(n+1)-3*n-α))*((2*(1+(1:ℝ)/1000))^3)^n := by
    have hbase : 2*((1+(1:ℝ)/1000)*microLength t) = (2*(1+(1:ℝ)/1000))*microLength t := by ring
    rw [hbase, mul_pow, mul_pow]
    have hexp : (microLength t^3)^n = Real.exp ((n:ℝ)*(3*(-t))) := by
      simp only [microLength, ← Real.exp_nat_mul, Nat.cast_ofNat]
    rw [hexp]
    calc
      _ = (Real.exp (t*h*(n+1))*Real.exp (-t*α)*Real.exp ((n:ℝ)*(3*(-t))))*
          ((2*(1+(1:ℝ)/1000))^3)^n := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have hrate : Real.exp (t*(h*(n+1)-3*n-α)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr (cluster_rate_le h1 h4 hn))
  have hpow : (n+1:ℝ)*((2*(1+(1:ℝ)/1000))^3)^n ≤ 3000 := by
    interval_cases n <;> norm_num
  calc
    _ ≤ Real.exp (t*h*(n+1))*Real.exp (-t*α)*
        (((2*((1+(1:ℝ)/1000)*microLength t))^3)^n)*(n+1) := by
      have hc : Real.exp (t*h*(n+1))/(n+1).factorial ≤ Real.exp (t*h*(n+1)) :=
        div_le_self (Real.exp_pos _).le hfac
      nlinarith [mul_le_mul_of_nonneg_right hc
        (mul_nonneg (Real.exp_pos (-t*α)).le
          (mul_nonneg (show (0:ℝ) ≤ n+1 by positivity) (by positivity : 0 ≤ ((2*((1+(1:ℝ)/1000)*microLength t))^3)^n)))]
    _ = Real.exp (t*(h*(n+1)-3*n-α))*(((2*(1+(1:ℝ)/1000))^3)^n)*(n+1) := by rw [he]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right hrate
        (mul_nonneg (by positivity : 0 ≤ ((2*(1+(1:ℝ)/1000))^3)^n) (show (0:ℝ) ≤ n+1 by positivity))]

lemma lintegral_cellClusterWeight_sector {t α r : ℝ} (hr : 0 ≤ r) (k : Cell)
    {n : ℕ} (hn : n ≤ 3) :
    (∫⁻ x : Fin (n+1) → Position, cellClusterWeight t α r k (configurationMultiset x)
      ∂Measure.pi (fun _ => volume)) =
    ENNReal.ofReal (Real.exp (-t*α))*((n+1 : ℕ)*(volume (gridRegion k)*(ENNReal.ofReal (2*r)^3)^n)) := by
  have hn4 : n+1 ≤ 4 := by omega
  simp only [cellClusterWeight, emptyWeight, configurationMultiset_card, Fintype.card_fin,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, ite_eq_left hn4, zero_add]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_starWeight _ (measurableSet_gridRegion _) hr]

lemma particleBase_cellClusterWeight_le {t h α : ℝ} (ht : 0 ≤ t)
    (h1 : h ≤ α) (h4 : 4*h-9 ≤ α) (k : Cell) :
    (∫⁻ x, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (particleMultiset x)
      ∂particleBase volume (t*h)) ≤ 15001 := by
  have hl := (microLength_pos t).le
  have hm := measurable_particleObservable _ (measurable_cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k) 0
  simp only [zero_add] at hm
  rw [lintegral_particleBase _ _ hm]
  have hz (n : ℕ) (hn : n ∉ Finset.range 5) :
      ENNReal.ofReal (Real.exp (t*h*n)/n.factorial)*
      (∫⁻ x : Fin n → Position, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (particleMultiset ⟨n,x⟩)
        ∂Measure.pi (fun _ => volume)) = 0 := by
    have hn4 : ¬n ≤ 4 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    have hn0 : n ≠ 0 := by omega
    simp [particleMultiset, cellClusterWeight, emptyWeight, configurationMultiset_card, hn4, hn0]
  rw [tsum_eq_sum hz]
  have hterm (n : ℕ) (hn : n ∈ Finset.range 5) :
      ENNReal.ofReal (Real.exp (t*h*n)/n.factorial)*
      (∫⁻ x : Fin n → Position, cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (particleMultiset ⟨n,x⟩)
        ∂Measure.pi (fun _ => volume)) ≤ 3000 := by
    rcases n with _|n
    · norm_num [particleMultiset, cellClusterWeight, emptyWeight, starWeight, configurationMultiset, Finset.univ_eq_empty]
    have hn3 : n ≤ 3 := by have := Finset.mem_range.mp hn; omega
    change ENNReal.ofReal _ * (∫⁻ x : Fin (n+1) → Position,
      cellClusterWeight t α ((1+(1:ℝ)/1000)*microLength t) k (configurationMultiset x) ∂Measure.pi (fun _ => volume)) ≤ _
    rw [lintegral_cellClusterWeight_sector (by positivity) k hn3]
    have hv : volume (gridRegion k) ≤ (1:ℝ≥0∞) :=
      (volume_gridRegion_le k).trans (by norm_num)
    apply le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hv le_rfl)) ))
    simp only [one_mul]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*((1+(1:ℝ)/1000)*microLength t)),
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ (2*((1+(1:ℝ)/1000)*microLength t))^3)]
    have hnat : ((n+1:ℕ):ℝ≥0∞) = ENNReal.ofReal ((n+1:ℕ):ℝ) := by norm_cast
    rw [hnat, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have hb := ENNReal.ofReal_le_ofReal (core_cluster_coefficient_bound ht h1 h4 hn3)
    norm_num only [ENNReal.ofReal_ofNat, Nat.cast_add, Nat.cast_one] at hb ⊢
    convert hb using 1
    congr 1
    ring
  calc
    _ ≤ ∑ _n ∈ Finset.range 5, (3000:ℝ≥0∞) := Finset.sum_le_sum hterm
    _ ≤ 15001 := by norm_num

end RadialTransition
end

end OAI
