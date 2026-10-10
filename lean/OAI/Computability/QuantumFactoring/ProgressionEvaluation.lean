import Mathlib
import OAI.Computability.QuantumFactoring.Exactness

namespace OAI

section
open scoped BigOperators


/-! Constant-length exact evaluation of the selected arithmetic progression.
The exponentially many progression points are replaced by seven truncated
arithmetic sums. This is the explicit arithmetic behind source Lemma 4.1. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Five fixed terms, of which only the constant and linear ones are nonzero. -/
def linearSum (a b : ℚ) (lo hi : ℕ) : ℚ :=
  fiveTermSum (fun q => if q=0 then a else if q=1 then b else 0) lo hi

lemma linearSum_correct (a b : ℚ) (lo hi : ℕ) :
    linearSum a b lo hi = ∑ i ∈ Finset.Ico lo hi, (a+b*i) := by
  rw [linearSum,fiveTermSum_correct]
  apply Finset.sum_congr rfl
  intro i _
  norm_num [Finset.sum_range_succ]

/-- A ramp can change sign only once along an arithmetic progression. -/
def rampSum (a b : ℚ) (M : ℕ) : ℚ :=
  if 0 < b then linearSum a b (Int.ceil (-a/b)).toNat M
  else if b < 0 then linearSum a b 0 (min M (Int.ceil (-a/b)).toNat)
  else M*max 0 a

lemma sum_ramp_filter_nonneg (a b : ℚ) (M : ℕ) :
    (∑ i ∈ Finset.range M, max 0 (a+b*i)) =
      ∑ i ∈ (Finset.range M).filter (fun i : ℕ => 0 ≤ a+b*(i:ℚ)), (a+b*i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ a+b*i
  · rw [ite_eq_left h,max_eq_right h]
  · rw [ite_eq_right h,max_eq_left (le_of_not_ge h)]

lemma sum_ramp_filter_pos (a b : ℚ) (M : ℕ) :
    (∑ i ∈ Finset.range M, max 0 (a+b*i)) =
      ∑ i ∈ (Finset.range M).filter (fun i : ℕ => 0 < a+b*(i:ℚ)), (a+b*i) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < a+b*i
  · rw [ite_eq_left h,max_eq_right h.le]
  · rw [ite_eq_right h,max_eq_left (le_of_not_gt h)]

lemma rampSum_correct (a b : ℚ) (M : ℕ) :
    rampSum a b M = ∑ i ∈ Finset.range M, max 0 (a+b*i) := by
  unfold rampSum
  split_ifs with hp hn
  · rw [linearSum_correct,sum_ramp_filter_nonneg]
    congr 1
    ext i
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range,
      Int.toNat_le,Int.ceil_le,Int.cast_natCast,div_le_iff₀ hp]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · rw [linearSum_correct,sum_ramp_filter_pos]
    congr 1
    ext i
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range,
      zero_le, true_and,lt_min_iff,Int.lt_toNat,Int.lt_ceil,Int.cast_natCast,
      lt_div_iff_of_neg hn]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  · have hb : b=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    simp [hb]

/-- The real coordinate of the seven-ramp spline derivative summed exactly. -/
def phaseSumRe (a b : ℚ) (M : ℕ) : ℚ :=
  -(M:ℚ)+4*linearSum (a+1/2) b 0 M-8*rampSum a b M+
    8*rampSum (a-1/2) b M-8*rampSum (a-1) b M

def phaseSumIm (a b : ℚ) (M : ℕ) : ℚ :=
  4*linearSum (a+1/2) b 0 M-8*rampSum (a+1/4) b M+
    8*rampSum (a-1/4) b M-8*rampSum (a-3/4) b M+
    8*rampSum (a-5/4) b M

lemma phaseSumRe_correct (a b : ℚ) (M : ℕ) :
    (phaseSumRe a b M : ℝ) =
      ∑ i ∈ Finset.range M, splineReDeriv ((a:ℝ)+(b:ℝ)*i) := by
  simp only [phaseSumRe,linearSum_correct,rampSum_correct,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_neg,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Nat.Ico_zero_eq_range,splineReDeriv,sub_add_eq_add_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_neg_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

lemma phaseSumIm_correct (a b : ℚ) (M : ℕ) :
    (phaseSumIm a b M : ℝ) =
      ∑ i ∈ Finset.range M, splineImDeriv ((a:ℝ)+(b:ℝ)*i) := by
  have hh' (i : ℕ) : (a:ℝ)+1/4+(b:ℝ)*i = (a:ℝ)+(b:ℝ)*i+1/4 := by ring
  simp only [phaseSumIm,linearSum_correct,rampSum_correct,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one,Rat.cast_sum,Rat.cast_max,Rat.cast_zero,
    Nat.Ico_zero_eq_range,splineImDeriv,hh',sub_add_eq_add_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

lemma phaseSum_correct (a b : ℚ) (M : ℕ)
    (h : ∀ i < M, -(1/2:ℝ) ≤ (a:ℝ)+(b:ℝ)*i ∧ (a:ℝ)+(b:ℝ)*i ≤ 3/2) :
    ((phaseSumRe a b M : ℚ):ℂ)+((phaseSumIm a b M : ℚ):ℂ)*Complex.I =
      ∑ i ∈ Finset.range M, phase ((a:ℝ)+(b:ℝ)*i) := by
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ratCast_re,Complex.ratCast_im,mul_zero,zero_mul,sub_self,add_zero,
      Complex.re_sum,phase]
    rw [phaseSumRe_correct]
    apply Finset.sum_congr rfl
    intro i hi
    exact splineReDeriv_eq (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ratCast_re,Complex.ratCast_im,mul_zero,mul_one,add_zero,zero_add,
      Complex.im_sum,phase]
    rw [phaseSumIm_correct]
    apply Finset.sum_congr rfl
    intro i hi
    exact splineImDeriv_eq (h i (Finset.mem_range.mp hi)).1 (h i (Finset.mem_range.mp hi)).2

/-- Offset and slope are rational values of polynomial bit length, evaluated
using the arithmetic nearest-bin rule rather than any transcendental oracle. -/
def sampleOffset (Q d j t : ℕ) : ℚ :=
  (((j*t)%d:ℕ):ℚ)/d+binErrorRat Q d j*t/Q

def sampleSlope (Q d j : ℕ) : ℚ := binErrorRat Q d j*d/Q

lemma sampleLine_cast (Q d j t i : ℕ) :
    (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i =
      ((j*t)%d:ℕ)/(d:ℝ)+binError Q d j*((t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q)) := by
  simp only [sampleOffset,sampleSlope,Rat.cast_add,Rat.cast_div,Rat.cast_mul,
    Rat.cast_natCast,binErrorRat_cast]
  ring

lemma sampleLine_bounds {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j i : ℕ) (hi : i < sampleCount Q d t) :
    -(1/2:ℝ) ≤ (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i ∧
      (sampleOffset Q d j t:ℝ)+(sampleSlope Q d j:ℝ)*i ≤ 3/2 := by
  rw [sampleLine_cast]
  have hQ : (0:ℝ) < Q := by exact_mod_cast lt_of_lt_of_le hd hdQ
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hu : (0:ℝ) ≤ ((j*t)%d:ℕ)/(d:ℝ) := by positivity
  have hu' : ((j*t)%d:ℕ)/(d:ℝ) < 1 := by
    rw [div_lt_one hd']
    exact_mod_cast Nat.mod_lt (j*t) hd
  have hv : (0:ℝ) ≤ (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) := by positivity
  have hv' : (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) ≤ 1 := by
    have h := (lt_sampleCount_iff hd hdQ ht).mp hi
    have h' : (t:ℝ)+i*d ≤ Q := by exact_mod_cast h.le
    have he : (t:ℝ)/Q+(i:ℝ)*((d:ℝ)/Q) = ((t:ℝ)+i*d)/Q := by ring
    rw [he,div_le_one hQ]
    exact h'
  rcases abs_le.mp (binError_bound (Q:=Q) (j:=j) hd) with ⟨he₀,he₁⟩
  have hm₀ := mul_le_mul_of_nonneg_right he₀ hv
  have hm₁ := mul_le_mul_of_nonneg_right he₁ hv
  constructor <;> nlinarith

/-- Constant-piece rational P: seven ramp sums, hence no loop of length Q or d. -/
def fastResidueProbability (Q d j t : ℕ) : ℚ :=
  let a := sampleOffset Q d j t
  let b := sampleSlope Q d j
  let M := sampleCount Q d t
  (phaseSumRe a b M ^ 2 + phaseSumIm a b M ^ 2)/(Q:ℚ)^2

lemma residueAmplitude_fast {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    residueAmplitude Q d j t = (Q:ℂ)⁻¹ *
      ((phaseSumRe (sampleOffset Q d j t) (sampleSlope Q d j) (sampleCount Q d t):ℂ)+
        (phaseSumIm (sampleOffset Q d j t) (sampleSlope Q d j) (sampleCount Q d t):ℂ)*Complex.I) := by
  rw [phaseSum_correct _ _ _ (fun i hi => sampleLine_bounds hd hdQ ht j i hi),
    residueAmplitude_samples hd hdQ ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sampleLine_cast]

lemma fastResidueProbability_correct {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    (fastResidueProbability Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability,residueAmplitude_fast hd hdQ ht]
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_mul,Complex.normSq_inv]
  simp [fastResidueProbability,Complex.normSq_apply,div_eq_mul_inv,pow_two]
  ring

lemma fastResidueProbability_eq {Q d t : ℕ} (hd : 0 < d) (hdQ : d ≤ Q)
    (ht : t < d) (j : ℕ) :
    fastResidueProbability Q d j t = residueProbabilityRat Q d j t := by
  apply Rat.cast_injective (α:=ℝ)
  rw [fastResidueProbability_correct hd hdQ ht,
    residueProbabilityRat_cast (lt_of_lt_of_le hd hdQ)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
