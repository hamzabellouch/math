import OAI.Analysis.AncientFlat.Weighted.WeightedCharts

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def radius (z : V) : ℝ := Real.sqrt (‖z‖^2+1)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma one_le_radius (z : V) : 1≤radius z := by
  rw [radius,Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [sq_nonneg ‖z‖]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma radius_pos (z : V) : 0<radius z := lt_of_lt_of_le (by norm_num) (one_le_radius z)
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma norm_le_radius (z : V) : ‖z‖≤radius z := by
  rw [radius,Real.le_sqrt (norm_nonneg _) (by positivity)]
  linarith
omit [FiniteDimensional ℝ V] in
lemma sigma_scale (r : ℝ) (hr : 0<r) (z : V) : sigma (r•z,-r^4)=r*radius z := by
  have h4 : r^4=(r^2)^2 := by ring
  simp only [sigma,norm_smul,Real.norm_eq_abs,abs_of_pos hr,neg_neg,h4,Real.sqrt_sq (sq_nonneg r)]
  rw [show (r*‖z‖)^2+r^2=r^2*(‖z‖^2+1) by ring,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
  rfl
def scaledSource (w r : ℝ) (f : V × ℝ → ℂ) (z : V) : ℂ :=
  r^(-(w-4)) • f (r•z,-r^4)
lemma scaledSource_eq_pullback (w r : ℝ) (hr : 0<r) (f : V × ℝ → ℂ) (z : V) :
    scaledSource w r f z=radius z^(w-4) • pullback (w-4) (r•z,-r^4) f 0 := by
  simp only [scaledSource,pullback,chart_zero,sigma_scale r hr z,
    Real.mul_rpow hr.le (radius_pos z).le,smul_smul]
  rw [mul_left_comm,Real.rpow_neg (radius_pos z).le,mul_inv_cancel₀ (Real.rpow_pos_of_pos (radius_pos z) _).ne',mul_one]
lemma YBound.scaled_pointwise {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (ha : 0<a) (r : ℝ) (hr : 0<r) (z : V) :
    ‖scaledSource w r f z‖≤M*radius z^(w-4) := by
  rw [scaledSource_eq_pullback w r hr,norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (radius_pos z) _)]
  exact (mul_le_mul_of_nonneg_left ((h _ (by dsimp; exact neg_neg_of_pos (pow_pos hr _))).1
    0 (zero_localDomain a ha _ (by dsimp; exact neg_neg_of_pos (pow_pos hr _))))
    (Real.rpow_pos_of_pos (radius_pos z) _).le).trans_eq (mul_comm _ _)
omit [FiniteDimensional ℝ V] in
lemma normalizedSource_eq_scaled (γ : ℝ) (f : V × ℝ → ℂ) (τ : ℝ) (z : V) :
    normalizedSource γ f τ z=scaledSource (-2+4*γ) (Real.exp (-τ/4)) f z := by
  have hpow : Real.exp (-τ/4)^4=Real.exp (-τ) := by
    rw [←Real.exp_nat_mul]; congr 1; ring
  simp only [normalizedSource,scaledSource,hpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  congr 2
  ring
end FlatWeighted

end

end OAI
