import Mathlib
import OAI.Probability.SKGap.Localization.TAPVectorTaylor
import OAI.Probability.SKGap.Entropy.ConditionalBadSet

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma quadraticForm_le_mulvec_bound {n : ℕ} {K : ℝ} (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (x : Field n) :
    quadraticForm J x ≤ K*vectorSqNorm x := by
  have he : quadraticForm J x=∑ i,x i*(J*ᵥx) i := by
    simp only [quadraticForm,mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  rw [he]
  calc
    _ ≤ |∑ i,x i*(J*ᵥx) i| := le_abs_self _
    _ ≤ vectorNorm x*vectorNorm (J*ᵥx) := vector_dot_abs_le _ _
    _ ≤ vectorNorm x*(K*vectorNorm x) := mul_le_mul_of_nonneg_left (hJ x) (vectorNorm_nonneg _)
    _ = _ := by rw [← vectorNorm_sq];ring

lemma badField_small_overlap_impossible {n : ℕ} (hn : 0 < n) {j A K q₀ ε c : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hK : 0 ≤ K-j)
    (hmargin : c < 1-A*(K-j+6*j*q₀))
    (W : Matrix (Fin n) (Fin n) ℝ) (y : Field n)
    (hJ : ∀ z : Field n,vectorNorm (plantedInteraction j W*ᵥz) ≤ K*vectorNorm z)
    (hy : (W,y)∈badFieldSet n j A ε c) : 2*q₀ < overlap y := by
  by_contra! hq
  obtain ⟨a,ha,_hclose,x,hx,hquad⟩ := hy
  have hv : vectorSqNorm x.ofLp=1 := by
    rw [← vectorNorm_sq]
    change ‖WithLp.toLp 2 x.ofLp‖^2=1
    simp only [WithLp.toLp_ofLp,hx,one_pow]
  have hcoef : 0 ≤ K-j+3*j*overlap y := add_nonneg hK (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hj) (overlap_nonneg y))
  have hh := hessian_lower_bound hn hj y a (fun i=>(ha i).1) (fun i=>(ha i).2)
    (quadraticForm_le_mulvec_bound _ hJ) hcoef x.ofLp
  rw [hv,mul_one] at hh
  have hc := mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hj) hA)
  nlinarith only [hh,hquad,hmargin,hc]

lemma overlap_neighborhood {n : ℕ} (hn : 0 < n) {q₀ r : ℝ} (hr : 2*r ≤ q₀)
    (y d : Field n) (hy : 2*q₀ < overlap y) (hd : vectorNorm d ≤ r*sqrt (n:ℝ)) :
    q₀ ≤ overlap (y+d) := by
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hh := varianceAverage_difference hn y d
  have hb := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2/sqrt (n:ℝ))
  have he : 2/sqrt (n:ℝ)*(r*sqrt (n:ℝ))=2*r := by field_simp
  rw [he] at hb
  unfold varianceAverage at hh
  linarith [le_abs_self ((1-overlap (y+d))-(1-overlap y))]

lemma high_temperature_small_margin {j : ℝ} (hj : 0 < j) (hj1 : j < 1) :
    ∃ A K q₀ c : ℝ,1 < A ∧ 2*sqrt j < K ∧ 0 < q₀ ∧ 0 < c ∧
      sqrt j*A < 1 ∧ 0 ≤ K-j ∧ c < 1-A*(K-j+6*j*q₀) := by
  have hs : 0 < sqrt j := sqrt_pos.mpr hj
  have hs1 : sqrt j < 1 := by simpa using sqrt_lt_sqrt hj.le hj1
  have hjroot : j < 2*sqrt j := by nlinarith [sq_sqrt hj.le]
  let f : ℝ → ℝ := fun δ=>1-(1+δ)*(2*sqrt j+2*δ-j+6*j*δ)
  let g : ℝ → ℝ := fun δ=>sqrt j*(1+δ)
  have hf0 : 0 < f 0 := by dsimp [f];nlinarith [sq_sqrt hj.le,sq_pos_of_pos (sub_pos.mpr hs1)]
  have hc : ContinuousAt f 0 := by dsimp [f];fun_prop
  have hg : ContinuousAt g 0 := by dsimp [g];fun_prop
  have he : ∀ᶠ δ in nhds (0:ℝ),0 < f δ ∧ g δ < 1 :=
    (hc.tendsto.eventually_const_lt hf0).and (hg.tendsto.eventually_lt_const (by simpa [g] using hs1))
  obtain ⟨r,hr,hrgood⟩ := Metric.eventually_nhds_iff.mp he
  have hd : dist (r/2) (0:ℝ) < r := by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)];linarith
  obtain ⟨hf,hg⟩ := hrgood hd
  refine ⟨1+r/2,2*sqrt j+2*(r/2),r/2,f (r/2)/2,by linarith,by linarith,
    half_pos hr,half_pos hf,hg,by linarith,?_⟩
  change f (r/2)/2 < f (r/2)
  linarith
end SKGap
end
end

end OAI
