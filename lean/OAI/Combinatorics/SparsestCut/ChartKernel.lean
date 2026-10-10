import OAI.Combinatorics.SparsestCut.MetricKernel

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartKernel
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def residual (J : E →L[ℝ] F) (B : F →L[ℝ] E) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F-J.comp B

def alpha (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    (q k ε : ℝ) (s : Fin S) (x : F) (j : Fin S × Fin N) : ℝ :=
  if j.1=s then k/ε*(x j.2-inner ℝ (g j.1 j.2) (B s x)/q) else 0

lemma norm_linear_le_l1 (B : F →L[ℝ] E) {V : ℝ} (_hV : 0 ≤ V)
    (hB : ∀ i, ‖B (EuclideanSpace.single i 1)‖ ≤ V) (x : F) :
    ‖B x‖ ≤ V*∑ i, |x i| := by
  have he : x = ∑ i : Fin N, x i • EuclideanSpace.single i 1 := by
    apply PiLp.ext
    intro j
    simp [ Pi.single_apply]
  conv_lhs => rw [he, map_sum]
  calc
    _ ≤ ∑ i : Fin N, ‖B (x i • EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, |x i| * V := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg _)
    _ = V*∑ i : Fin N, |x i| := by rw [← Finset.sum_mul]; ring

lemma alpha_linear (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    (q k ε : ℝ) (s : Fin S) (x h : F) (t : ℝ) :
    alpha g B q k ε s (x+t • h) = fun j => alpha g B q k ε s x j+t*alpha g B q k ε s h j := by
  funext j
  simp only [alpha, map_add, map_smul, inner_add_right, real_inner_smul_right,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hj : j.1=s <;> simp only [hj, ite_true,ite_false] <;> ring

lemma alpha_norm_bound (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    {q k ε R : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) (s : Fin S) (x : F)
    (hx : ‖residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x‖ ≤ R)
    (j : Fin S × Fin N) : |alpha g B q k ε s x j| ≤ k/ε*R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  by_cases hj : j.1=s
  · simp only [alpha,hj,ite_true,abs_mul,abs_of_nonneg (div_nonneg hk hε.le)]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hk hε.le)
    have hc := PiLp.norm_apply_le (p := (2:ENNReal))
      (residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x) j.2
    have he : residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x j.2 =
        x j.2-inner ℝ (g s j.2) (B s x)/q := by
      simp [residual,FrameCharts.chart_apply,real_inner_smul_left,div_eq_inv_mul]
    simpa only [he,Real.norm_eq_abs] using hc.trans hx
  · simp only [alpha,hj,ite_false,abs_zero]
    positivity

lemma alpha_derivative_bound (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    {q k ε H : ℝ} (hq : 0 < q) (hk : 0 ≤ k) (hk1 : k ≤ 1) (hε : 0 < ε)
    (s : Fin S) (h : F) (hH : ∑ i, |h i| ≤ H)
    (hg : ∀ i, ‖g s i‖ ≤ 2*q) (hB : ∀ i, ‖B s (EuclideanSpace.single i 1)‖ ≤ 4*k)
    (j : Fin S × Fin N) : |alpha g B q k ε s h j| ≤ (9*k/ε)*H := by
  have hv := norm_linear_le_l1 (B s) (by positivity : 0 ≤ 4*k) hB h
  have hv' : ‖B s h‖ ≤ 4*k*H := hv.trans (mul_le_mul_of_nonneg_left hH (by positivity))
  have hH0 : 0 ≤ H := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans hH
  have hh (i : Fin N) : |h i| ≤ H := (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans hH
  by_cases hj : j.1=s
  · simp only [alpha,hj,ite_true,abs_mul,abs_of_nonneg (div_nonneg hk hε.le)]
    have hip : |inner ℝ (g s j.2) (B s h)/q| ≤ 8*k*H := by
      rw [abs_div,abs_of_pos hq]
      apply (div_le_iff₀ hq).mpr
      calc
        _ ≤ ‖g s j.2‖*‖B s h‖ := abs_real_inner_le_norm _ _
        _ ≤ (2*q)*(4*k*H) := mul_le_mul (hg _) hv' (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hb : |h j.2-inner ℝ (g s j.2) (B s h)/q| ≤ 9*H := by
      refine (abs_sub _ _).trans ?_
      have := mul_le_mul_of_nonneg_right hk1 hH0
      linarith [hh j.2,hip]
    calc
      _ ≤ (k/ε)*(9*H) := mul_le_mul_of_nonneg_left hb (div_nonneg hk hε.le)
      _ = _ := by ring
  · simp only [alpha,hj,ite_false,abs_zero]
    positivity

end UniformSparsestCut.ChartKernel

end

end OAI
