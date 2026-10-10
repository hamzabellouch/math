import OAI.Probability.SLE.Angle.AngleSpectralBounds

namespace OAI

/-! An explicit large-time uniformly positive polynomial spectral kernel.
Identification with the actual stopped-angle transition is separate. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def angleSpectralMixingTime (κ : ℝ) : ℝ :=
  (8/κ)*(4+Real.log (4*(κ+4)/κ))+2

lemma angleSpectralMixingTime_pos {κ : ℝ} (hκ : 0<κ) :
    0<angleSpectralMixingTime κ := by
  have hb : 1≤4*(κ+4)/κ := (le_div_iff₀ hκ).mpr (by linarith)
  have hl := Real.log_nonneg hb
  unfold angleSpectralMixingTime
  positivity

lemma angleSpectralTerm_bound {κ u : ℝ} (hκ : 0<κ) (hu : angleSpectralMixingTime κ≤u)
    {n : ℕ} (hn : 1≤n) {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1) :
    |Real.exp (-u*anglePolynomialEigenvalue κ n)*angleSpectralFactor κ n x y|≤
      (1/3:ℝ)^n := by
  let C := 4+Real.log (4*(κ+4)/κ)
  have hb : 1≤4*(κ+4)/κ := (le_div_iff₀ hκ).mpr (by linarith)
  have hC : 0≤C := by dsimp [C]; linarith [Real.log_nonneg hb]
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have heig : 0≤anglePolynomialEigenvalue κ n := by unfold anglePolynomialEigenvalue; positivity
  have he : angleSpectralMixingTime κ*anglePolynomialEigenvalue κ n =
      C*(n:ℝ)^2+2*(n:ℝ)+(8/κ)*C*(n:ℝ)+(κ/4)*(n:ℝ)^2 := by
    unfold angleSpectralMixingTime anglePolynomialEigenvalue
    dsimp [C]
    field_simp
    ring
  have hexp : -u*anglePolynomialEigenvalue κ n+C*(n:ℝ)^2≤-2*(n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hu heig
    rw [he] at hh
    have hz : 0≤(8/κ)*C*(n:ℝ)+(κ/4)*(n:ℝ)^2 := by positivity
    linarith
  have he2 : Real.exp (-2)≤(1/3:ℝ) := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 2)).mpr (by nlinarith [Real.add_one_le_exp (2:ℝ)])
  calc
    _ = Real.exp (-u*anglePolynomialEigenvalue κ n)*|angleSpectralFactor κ n x y| := by
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-u*anglePolynomialEigenvalue κ n)*Real.exp (C*(n:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (angleSpectralFactor_exp_bound hκ hn hx hy) (Real.exp_pos _).le
    _ = Real.exp (-u*anglePolynomialEigenvalue κ n+C*(n:ℝ)^2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-2*(n:ℝ)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-2)^n := by rw [mul_comm,Real.exp_nat_mul]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he2 n

def angleSpectralKernel (κ u θ φ : ℝ) : ℝ :=
  1+∑' n : ℕ, Real.exp (-u*anglePolynomialEigenvalue κ (n+1))*
    angleSpectralFactor κ (n+1) (Real.cos θ) (Real.cos φ)

lemma angleSpectralKernel_summable {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ φ : ℝ) :
    Summable (fun n : ℕ => Real.exp (-u*anglePolynomialEigenvalue κ (n+1))*
      angleSpectralFactor κ (n+1) (Real.cos θ) (Real.cos φ)) := by
  have hs : Summable (fun n : ℕ => (1/3:ℝ)^(n+1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)<1)).mul_right (1/3)
  apply hs.of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs] using angleSpectralTerm_bound hκ hu (by omega : 1≤n+1)
    (Real.abs_cos_le_one θ) (Real.abs_cos_le_one φ)

lemma angleSpectralKernel_bounds {κ u : ℝ} (hκ : 0<κ)
    (hu : angleSpectralMixingTime κ≤u) (θ φ : ℝ) :
    1/2≤angleSpectralKernel κ u θ φ ∧ angleSpectralKernel κ u θ φ≤2 := by
  have hs : Summable (fun n : ℕ => (1/3:ℝ)^(n+1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)<1)).mul_right (1/3)
  have hsum : (∑' n : ℕ, (1/3:ℝ)^(n+1))=1/2 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/3)
      (by norm_num : (1/3:ℝ)<1)]
    norm_num
  have he : |∑' n : ℕ, Real.exp (-u*anglePolynomialEigenvalue κ (n+1))*
      angleSpectralFactor κ (n+1) (Real.cos θ) (Real.cos φ)|≤1/2 := by
    rw [← hsum]
    have hbnd (n : ℕ) : ‖Real.exp (-u*anglePolynomialEigenvalue κ (n+1))*
        angleSpectralFactor κ (n+1) (Real.cos θ) (Real.cos φ)‖≤(1/3:ℝ)^(n+1) := by
      simpa only [Real.norm_eq_abs] using angleSpectralTerm_bound hκ hu (by omega : 1≤n+1)
        (Real.abs_cos_le_one θ) (Real.abs_cos_le_one φ)
    have hsn := hs.of_nonneg_of_le (fun n => norm_nonneg _) hbnd
    exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbnd hs)
  unfold angleSpectralKernel
  constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2]

end SLEExactGauge

end

end OAI
