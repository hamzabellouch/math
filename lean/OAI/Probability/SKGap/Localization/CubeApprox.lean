import Mathlib
import OAI.Probability.SKGap.Matrix.RegularizedLogDet
import OAI.Probability.SKGap.Brownian.LogDetPath

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def coordAverage (a : ι → ℝ) : ℝ := (∑ i,a i)/(Fintype.card ι:ℝ)

omit [DecidableEq ι] in
lemma coordAverage_bounds {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    0 ≤ coordAverage a ∧ coordAverage a ≤ 1 := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) hn.le
  · apply (div_le_iff₀ hn).mpr
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha1 i)

omit [DecidableEq ι] in
lemma coordAverage_sub_le {a b : ι → ℝ} {δ : ℝ} (hab : ∀ i, |a i-b i| ≤ δ) :
    |coordAverage a-coordAverage b| ≤ δ := by
  have hn : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  unfold coordAverage
  rw [← sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  exact ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => hab i))).trans_eq (by simp [mul_comm])

omit [DecidableEq ι] in
lemma coordAverage_sq_sub_le {j δ : ℝ} (hj : 0 ≤ j) {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i,a i ≤ 1) (hb : ∀ i,0 ≤ b i) (hb1 : ∀ i,b i ≤ 1)
    (hab : ∀ i, |a i-b i| ≤ δ) :
    |j*(coordAverage a)^2-j*(coordAverage b)^2| ≤ 2*j*δ := by
  have haa := coordAverage_bounds ha ha1
  have hbb := coordAverage_bounds hb hb1
  have hd := coordAverage_sub_le hab
  have hh := mul_le_mul_of_nonneg_left hd hj
  have he : j*(coordAverage a)^2-j*(coordAverage b)^2=
    (j*(coordAverage a-coordAverage b))*(coordAverage a+coordAverage b) := by ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg hj,abs_of_nonneg (by linarith : 0 ≤ coordAverage a+coordAverage b)]
  calc
    _ ≤ (j*δ)*2 := mul_le_mul hh (by linarith) (by linarith : 0 ≤ coordAverage a+coordAverage b) (by nlinarith [abs_nonneg (coordAverage a-coordAverage b)])
    _ = _ := by ring

lemma logPath_cube_difference {j δ R : ℝ} (hj : 0 ≤ j) (hδ : 0 ≤ δ) (_hR : 0 ≤ R)
    {a b : ι → ℝ} (ha : ∀ i,0 ≤ a i) (ha1 : ∀ i,a i ≤ 1)
    (hb : ∀ i,0 ≤ b i) (hb1 : ∀ i,b i ≤ 1) (hab : ∀ i,|a i-b i| ≤ δ)
    {M : Matrix ι ι ℝ} (hM : opNorm M ≤ R) :
    ‖logPath (j*coordAverage a) a M 1-logPath (j*coordAverage b) b M 1‖ ≤
      sqrt (Fintype.card ι:ℝ)*(2*j+R)*δ := by
  have haa := coordAverage_bounds ha ha1
  have hd := coordAverage_sub_le hab
  have hDa : opNorm (diagonal a-diagonal b) ≤ δ := by
    rw [diagonal_sub]
    exact opNorm_diagonal_le hδ hab
  have hDb : opNorm (diagonal b) ≤ 1 := opNorm_diagonal_le (by norm_num)
    (fun i => by rw [abs_of_nonneg (hb i)]; exact hb1 i)
  have hF₁ := (LogDet.frobenius_le_sqrt_card_opNorm (diagonal a-diagonal b)).trans
    (mul_le_mul_of_nonneg_left hDa (sqrt_nonneg _))
  have hF₂ := (LogDet.frobenius_le_sqrt_card_opNorm (diagonal b)).trans
    (mul_le_mul_of_nonneg_left hDb (sqrt_nonneg _))
  simp only [mul_one] at hF₂
  have hq : |j*coordAverage a| ≤ j := by rw [abs_of_nonneg (mul_nonneg hj haa.1)]; nlinarith
  have hq' : |j*coordAverage a-j*coordAverage b| ≤ j*δ := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hj]; exact mul_le_mul_of_nonneg_left hd hj
  have he : logPath (j*coordAverage a) a M 1-logPath (j*coordAverage b) b M 1=
      (j*coordAverage a) • (diagonal a-diagonal b)+
      (j*coordAverage a-j*coordAverage b) • diagonal b-(diagonal a-diagonal b)*M := by
    simp only [logPath,one_pow,one_mul,one_smul,smul_sub,sub_smul,Matrix.sub_mul]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (frobenius_mul_le_opNorm_right _ _)).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
  have hf₁ := mul_le_mul hq hF₁ (norm_nonneg _) hj
  have hf₂ := mul_le_mul hq' hF₂ (norm_nonneg _) (mul_nonneg hj hδ)
  have hf₃ := mul_le_mul hF₁ hM (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) hδ)
  nlinarith

lemma scalar_cube_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset ℝ, (∀ x ∈ s, x ∈ Icc (0:ℝ) 1) ∧
      ∀ x ∈ Icc (0:ℝ) 1, ∃ y ∈ s, |x-y| ≤ δ := by
  classical
  obtain ⟨s,hs,hsfin,hcover⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).finite_cover_balls hδ
  refine ⟨hsfin.toFinset,fun x hx => hs (hsfin.mem_toFinset.mp hx),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  exact ⟨y,hsfin.mem_toFinset.mpr hy,(show |x-y| < δ from Metric.mem_ball.mp hxy).le⟩
end SKGap
end
end

end OAI
