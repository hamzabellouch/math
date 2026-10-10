import OAI.Dynamics.StandardMap.SliceCancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma pattern_power_bound (n : ℕ) (hn : 1000 ≤ n) :
    (4:ℝ)^(n+2)*(((1/4:ℝ)^400)^(n/100-1)*3) ≤ (1/4:ℝ)^n := by
  have hexp : 2*n+4 ≤ 400*(n/100-1) := by omega
  rw [← pow_mul]
  calc
    _ ≤ (4:ℝ)^(n+2)*((1/4:ℝ)^(2*n+4)*3) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by norm_num)) (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
    _ = (1/4:ℝ)^n*(3/16) := by
      have he : 2*n+4= n+(n+4) := by omega
      rw [he,pow_add,pow_add,pow_add]
      simp only [one_div_pow]
      field_simp
      ; ring
    _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) n]
lemma pattern_ennreal_bound (n : ℕ) (hn : 1000 ≤ n) :
    (4^(n+2):ℝ≥0∞)*(ENNReal.ofReal ((1/4:ℝ)^400)^(n/100-1)*3) ≤
      ENNReal.ofReal ((1/4:ℝ)^n) := by
  have hh := ENNReal.ofReal_le_ofReal (pattern_power_bound n hn)
  simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4^(n+2)),
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((1/4:ℝ)^400)^(n/100-1)),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
    ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (1/4:ℝ)^400),ENNReal.ofReal_ofNat] using hh

theorem eventually_small_endpoints_slice :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
      ∀ q : ℝ, ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
      volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
        pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
          3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
        pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
          3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))} ≤ ENNReal.ofReal ((1/4:ℝ)^n) := by
  let η : ℝ := (1/4:ℝ)^400/5
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨η',hη',Mη,hscarce⟩:=local_scarcity η hη
  have hlim : Tendsto (fun M : ℝ => M^(-goodExponent)/5) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop goodExponent_pos).div_const 5
  obtain ⟨MM,hMM⟩:=eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη'))
  refine ⟨max 6 (max Mη MM),?_⟩
  intro k hk hM q n Np Nm hn hNp hNm
  have hm6 : 6 ≤ growthBase k := (le_max_left _ _).trans hM
  have hmη : Mη ≤ growthBase k := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hmmm : MM ≤ growthBase k := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hs :=small_endpoints_slice_bound k q η η' n Np Nm hn hNp hNm hk.le hm6 hη.le
    (hMM _ hmmm) (fun jm jp b hgood hmatch => hscarce k hk hmη q b jm jp hgood hmatch)
  have he : 5*η=(1/4:ℝ)^400 := by dsimp only [η]; exact mul_div_cancel₀ _ (by norm_num : (5:ℝ) ≠ 0)
  rw [he] at hs
  exact hs.trans (pattern_ennreal_bound n (by omega))
end StandardMapEntropy

end OAI
