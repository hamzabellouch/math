import Mathlib
import OAI.Probability.SKGap.Localization.EmpiricalGramBound
import OAI.Probability.SKGap.Localization.CompactTube

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma conditionalSize_bounds {j : ℝ} {p : ScalarPoint} {r L : ℝ}
    (hq : 0 < scalarQMoment p.1) (hs : 0 < scalarS j p)
    (hB : 0 < j*scalarBMoment p.1+r) (hsize : conditionalScalarSize j p r < L) :
    (1+|scalarD j p|)/scalarS j p < L ∧ 1/scalarQMoment p.1 < L ∧
    1/scalarS j p < L ∧ 1/(j*scalarBMoment p.1+r) < L ∧
    j*scalarBMoment p.1+r < L ∧ ‖conditionalScalarData j p‖ < L := by
  have h1 : 0 ≤ (1+|scalarD j p|)/scalarS j p := by positivity
  have h2 : 0 ≤ 1/scalarQMoment p.1 := by positivity
  have h3 : 0 ≤ 1/scalarS j p := by positivity
  have h4 : 0 ≤ 1/(j*scalarBMoment p.1+r) := by positivity
  have h5 := norm_nonneg (conditionalScalarData j p)
  unfold conditionalScalarSize at hsize
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

lemma empiricalGramColumns_norm {n : ℕ} (hn : 0 < n) (y : Fin n → ℝ)
    {d s L R : ℝ} (hs : 0 < s) (hL : 1 ≤ L) (hR : 0 ≤ R)
    (hd : (1+|d|)/s ≤ L) (hy : ∑ i,y i^2 ≤ R^2*(n:ℝ)) (r : Fin 3) :
    ‖empiricalGramColumns y d s r‖ ≤ 2*L*(R+1) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hb (i : Fin n) : (gramCoordinates d s (y i) r)^2 ≤ 2*L^2*(1+y i^2) := by
    simpa only [← sq,abs_pow, sq_abs] using gramCoordinates_product_bound hs hL hd (y i) r r
  have hsq : ‖empiricalGramColumns y d s r‖^2 ≤ 2*L^2*(1+R^2) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [empiricalGramColumns,PiLp.toLp_apply,div_pow,Real.sq_sqrt hnR.le]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hnR).mpr
    calc
      _ ≤ ∑ i,2*L^2*(1+y i^2) := Finset.sum_le_sum (fun i _=>hb i)
      _ = 2*L^2*((n:ℝ)+∑ i,y i^2) := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; simp
      _ ≤ 2*L^2*((n:ℝ)+R^2*(n:ℝ)) := mul_le_mul_of_nonneg_left (add_le_add_right hy _) (by positivity)
      _ = _ := by ring
  have hcmp : 2*L^2*(1+R^2) ≤ (2*L*(R+1))^2 := by
    nlinarith [mul_nonneg (sq_nonneg L) hR, sq_nonneg (L*R)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hsq.trans hcmp)

def empiricalUnit {n : ℕ} (y : Fin n → ℝ) (q : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i=>tanh (y i)/sqrt ((n:ℝ)*q))

lemma empiricalUnit_unit {n : ℕ} [NeZero n] (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp=1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hsum : ∑ i,tanh (y i)^2=(n:ℝ)*scalarQMoment (empiricalLaw y) := by
    simpa only [scalarQMoment,Fintype.card_fin] using (card_mul_integral_empiricalLaw y (fun x=>tanh x^2)).symm
  simp only [empiricalUnit,WithLp.ofLp_toLp,dotProduct,← sq,div_pow,Real.sq_sqrt (mul_nonneg hn.le hq.le)]
  rw [← Finset.sum_div,hsum,div_self (mul_pos hn hq).ne']

lemma empiricalUnit_norm {n : ℕ} [NeZero n] (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    ‖empiricalUnit y (scalarQMoment (empiricalLaw y))‖=1 := by
  have hh := empiricalUnit_unit y hq
  have he : ‖empiricalUnit y (scalarQMoment (empiricalLaw y))‖^2=1 := by
    simpa only [EuclideanSpace.real_norm_sq_eq,dotProduct,← sq] using hh
  nlinarith [norm_nonneg (empiricalUnit y (scalarQMoment (empiricalLaw y)))]

lemma normalized_average_l2 {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hd : ∑ i,d i^2 ≤ ε^2*(n:ℝ)) :
    |(n:ℝ)⁻¹*∑ i,d i| ≤ ε := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : sqrt (∑ i,d i^2) ≤ ε*sqrt (n:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    simpa only [mul_pow,Real.sq_sqrt hnR.le] using hd
  have hh := (Finset.abs_sum_le_sum_abs d Finset.univ).trans (sum_abs_le_sqrt_card_l2 d)
  simp only [Fintype.card_fin] at hh
  have hh' : |∑ i,d i| ≤ ε*(n:ℝ) := by
    apply hh.trans
    apply (mul_le_mul_of_nonneg_left hs (sqrt_nonneg _)).trans_eq
    calc
      _ = ε*(sqrt (n:ℝ))^2 := by ring
      _ = _ := by rw [sq_sqrt hnR.le]
  rw [abs_mul,abs_of_pos (inv_pos.mpr hnR)]
  have hp := mul_le_mul_of_nonneg_left hh' (inv_nonneg.mpr hnR.le)
  convert hp using 1; first | rfl | field_simp

lemma empirical_mass_close {n : ℕ} [NeZero n] (a y : Fin n → ℝ) {j ε : ℝ}
    (hj : 0 ≤ j) (hε : 0 ≤ ε)
    (hd : ∑ i,(a i-(1-tanh (y i)^2))^2 ≤ ε^2*(n:ℝ)) :
    |j/(n:ℝ)*∑ i,a i-j*scalarBMoment (empiricalLaw y)| ≤ j*ε := by
  have hb : scalarBMoment (empiricalLaw y)=(n:ℝ)⁻¹*∑ i,(1-tanh (y i)^2) := by
    rw [scalarBMoment_integral]
    simpa only [scalarGramVariance,Fintype.card_fin] using integral_empiricalLaw y (fun x=>1-tanh x^2)
  rw [hb]
  have he : j/(n:ℝ)*∑ i,a i-j*((n:ℝ)⁻¹*∑ i,(1-tanh (y i)^2))=
      j*((n:ℝ)⁻¹*∑ i,(a i-(1-tanh (y i)^2))) := by simp only [Finset.sum_sub_distrib]; ring
  rw [he,abs_mul,abs_of_nonneg hj]
  exact mul_le_mul_of_nonneg_left (normalized_average_l2 (NeZero.pos n) _ hε hd) hj
end SKGap
end
end

end OAI
