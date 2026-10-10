import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogHeightDecomposition
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! A fixed smooth product envelope equals one on the full sharp dyadic
interval. Thus the exact prime cutoff can be retained in the height integral
while every factorized row has a smooth product weight. -/
noncomputable section
open Set Filter
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def primeProductBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def primeProductEnvelope (x : ℝ) : ℂ := (primeProductBump x : ℝ)

lemma primeProductEnvelope_tsupport :
    tsupport primeProductEnvelope = tsupport primeProductBump := by
  apply congrArg closure
  ext x
  simp [Function.support,primeProductEnvelope]

lemma primeProductEnvelope_compact : HasCompactSupport primeProductEnvelope := by
  change IsCompact (tsupport primeProductEnvelope)
  rw [primeProductEnvelope_tsupport]
  exact primeProductBump.hasCompactSupport

lemma primeProductEnvelope_positive : tsupport primeProductEnvelope ⊆ Ioi 0 := by
  rw [primeProductEnvelope_tsupport,primeProductBump.tsupport_eq]
  intro x hx
  have hx' : |x-3/2| ≤ 1 := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,primeProductBump] using hx
  have h := (abs_le.mp hx').1
  change 0 < x
  linarith

lemma primeProductEnvelope_smooth : ContDiff ℝ ∞ primeProductEnvelope :=
  Complex.ofRealCLM.contDiff.comp primeProductBump.contDiff

def primeProductWeights : UniformLogWeights (fun _ : Unit => primeProductEnvelope) :=
  uniformLogWeights_constant primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth

lemma primeProductEnvelope_norm_le (x : ℝ) : ‖primeProductEnvelope x‖ ≤ 1 := by
  rw [primeProductEnvelope,Complex.norm_real,Real.norm_of_nonneg primeProductBump.nonneg]
  exact primeProductBump.le_one

lemma primeProductEnvelope_one {x : ℝ} (hx : x ∈ Icc 1 2) :
    primeProductEnvelope x = 1 := by
  have h : primeProductBump x = 1 := by
    apply primeProductBump.one_of_mem_closedBall
    change |x-3/2| ≤ 1/2
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  simp only [primeProductEnvelope,h,Complex.ofReal_one]

lemma primeProductEnvelope_zero {x : ℝ} (hx : 3 ≤ x) : primeProductEnvelope x = 0 := by
  have h : primeProductBump x = 0 := by
    apply primeProductBump.zero_of_le_dist
    change 1 ≤ |x-3/2|
    exact (by linarith : (1:ℝ) ≤ x-3/2).trans (le_abs_self _)
  simp only [primeProductEnvelope,h,Complex.ofReal_zero]

lemma primeProductEnvelope_sharp {X n : ℝ} (hX : 0 < X) :
    primeProductEnvelope (n/X)*(intervalStep X (2*X) n : ℝ) =
      (intervalStep X (2*X) n : ℝ) := by
  by_cases hn : n ∈ Icc X (2*X)
  · have he : primeProductEnvelope (n/X) = 1 := primeProductEnvelope_one
      ⟨(le_div_iff₀ hX).mpr (by simpa using hn.1),
        (div_le_iff₀ hX).mpr hn.2⟩
    simp only [he,one_mul]
  · simp only [intervalStep,ite_eq_right hn,Complex.ofReal_zero,mul_zero]

lemma sharpDyadicPrimeComparison_envelope (ℓ : ℤ) {X : ℝ} (hX : 0 < X) :
    sharpDyadicPrimeComparison ℓ X =
      ∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*
          (intervalStep X (2*X) (norm p) : ℝ) := by
  unfold sharpDyadicPrimeComparison
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_comm (primeProductEnvelope _) _,mul_assoc,primeProductEnvelope_sharp hX]

lemma primeProductComparison_bound (ℓ : ℤ) {p : Eisenstein} (hp : primaryPrime p)
    (X : ℝ) :
    ‖primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p‖ ≤ 1+cStar := by
  rw [norm_mul]
  exact (mul_le_mul (primeProductEnvelope_norm_le _) (primeComparisonCoefficient_bound ℓ hp)
    (_root_.norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)

end CubicFirstMoment

end

end OAI
