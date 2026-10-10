import OAI.Analysis.AncientFlat.Weighted.WeightedRescaling

namespace OAI
noncomputable section
open Set Filter Topology
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
lemma chart_spatial_scale (r : ℝ) (hr : 0<r) (x y : V) :
    chart (r•x,-r^4) ((radius x)⁻¹ • (y-x),0)=(r•y,-r^4) := by
  simp only [chart,sigma_scale r hr x,smul_smul,mul_assoc,
    mul_inv_cancel₀ (radius_pos x).ne',mul_one,mul_zero,add_zero,Prod.mk.injEq,and_true]
  rw [smul_sub]; module
omit [FiniteDimensional ℝ V] in
lemma scaledSource_at (w r : ℝ) (hr : 0<r) (f : V × ℝ → ℂ) (x y : V) :
    scaledSource w r f y=radius x^(w-4) •
      pullback (w-4) (r•x,-r^4) f ((radius x)⁻¹ • (y-x),0) := by
  simp only [scaledSource,pullback,chart_spatial_scale r hr,sigma_scale r hr x,
    Real.mul_rpow hr.le (radius_pos x).le,smul_smul]
  rw [mul_left_comm,Real.rpow_neg (radius_pos x).le,
    mul_inv_cancel₀ (Real.rpow_pos_of_pos (radius_pos x) _).ne',mul_one]
omit [FiniteDimensional ℝ V] in
lemma spatial_chart_norm (x y : V) : ‖(radius x)⁻¹ • (y-x)‖≤‖x-y‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 (radius_pos x)),norm_sub_rev]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (one_le_radius x))
lemma YBound.scaled_spatial_near {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (hα : 0≤α) (hw : w≤4) (ha : 0<a) (hM : 0≤M)
    (r : ℝ) (hr : 0<r) (x y : V) (hxy : ‖x-y‖<a) :
    ‖scaledSource w r f x-scaledSource w r f y‖≤M*‖x-y‖^α := by
  let p : V × ℝ := (r•x,-r^4)
  let q : V × ℝ := ((radius x)⁻¹ • (y-x),0)
  have hp : p.2<0 := neg_neg_of_pos (pow_pos hr _)
  have hq : q∈localDomain a p := by
    refine ⟨(spatial_chart_norm x y).trans_lt hxy,?_,?_,?_⟩
    · exact neg_neg_of_pos (pow_pos ha _)
    · exact pow_pos ha _
    · dsimp only [q,p]
      rw [chart_spatial_scale r hr]
      exact hp
  have hb := (h p hp).2 0 (zero_localDomain a ha p hp) q hq
  have hpd : pdist (0:V × ℝ) q=‖(radius x)⁻¹ • (y-x)‖ := by simp [pdist,q]
  rw [hpd] at hb
  rw [scaledSource_eq_pullback w r hr f x,scaledSource_at w r hr f x y,←smul_sub,
    norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (radius_pos x) _)]
  calc
    _ ≤ radius x^(w-4)*(M*‖(radius x)⁻¹ • (y-x)‖^α) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos (radius_pos x) _).le
    _ ≤ 1*(M*‖x-y‖^α) := mul_le_mul
      (Real.rpow_le_one_of_one_le_of_nonpos (one_le_radius x) (by linarith))
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
        (spatial_chart_norm x y) hα) hM) (by positivity) (by norm_num)
    _ = _ := one_mul _
lemma YBound.scaled_spatial {α w a M : ℝ} {f : V × ℝ → ℂ}
    (h : YBound α w a M f) (hα : 0≤α) (hw : w≤4) (ha : 0<a) (hM : 0≤M)
    (r : ℝ) (hr : 0<r) (x y : V) :
    ‖scaledSource w r f x-scaledSource w r f y‖≤(1+2/a^α)*M*‖x-y‖^α := by
  have hpow : 0<a^α := Real.rpow_pos_of_pos ha _
  have hC : 1≤1+2/a^α := le_add_of_nonneg_right (by positivity)
  by_cases hxy : ‖x-y‖<a
  · exact (h.scaled_spatial_near hα hw ha hM r hr x y hxy).trans
      (by nlinarith [mul_nonneg hM (Real.rpow_nonneg (norm_nonneg (x-y)) α)])
  · have hb (z : V) : ‖scaledSource w r f z‖≤M := (h.scaled_pointwise ha r hr z).trans
      (mul_le_of_le_one_right hM (Real.rpow_le_one_of_one_le_of_nonpos (one_le_radius z) (by linarith)))
    have hab : a^α≤‖x-y‖^α := Real.rpow_le_rpow ha.le (not_lt.mp hxy) hα
    have hratio : 2≤(2/a^α)*‖x-y‖^α := by
      have he : (2/a^α)*a^α=2 := div_mul_cancel₀ _ hpow.ne'
      have hi := mul_le_mul_of_nonneg_left hab (show 0≤2/a^α by positivity)
      linarith
    calc
      _ ≤ ‖scaledSource w r f x‖+‖scaledSource w r f y‖ := norm_sub_le _ _
      _ ≤ M+M := add_le_add (hb x) (hb y)
      _ ≤ (1+2/a^α)*M*‖x-y‖^α := by
        nlinarith [mul_le_mul_of_nonneg_left hratio hM,
          mul_nonneg hM (Real.rpow_nonneg (norm_nonneg (x-y)) α)]
end FlatWeighted

end

end OAI
