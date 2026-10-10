import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace InvariantProjection.UniformRotationAverage

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev Circle := AddCircle (1 : ℝ)
abbrev CSpace := C(Circle, ℂ)

def translate (a : Circle) : C(Circle, Circle) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

def translateL (a : Circle) : CSpace →L[ℂ] CSpace :=
  ContinuousMap.compCLM ℂ ℂ (translate a)

def averageL (a : Circle) (n : ℕ) : CSpace →L[ℂ] CSpace :=
  (n : ℂ)⁻¹ • ∑ k ∈ range n, translateL (k • a)

@[simp] lemma averageL_apply (a : Circle) (n : ℕ) (f : CSpace) (x : Circle) :
    averageL a n f x = (n : ℂ)⁻¹ * ∑ k ∈ range n, f (x + k • a) := by
  simp [averageL, translateL, translate]

lemma norm_averageL_apply_le (a : Circle) (n : ℕ) (f : CSpace) :
    ‖averageL a n f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  rw [averageL_apply, norm_mul, norm_inv]
  have hsum : ‖∑ k ∈ range n, f (x + k • a)‖ ≤ n * ‖f‖ := by
    calc
      _ ≤ ∑ k ∈ range n, ‖f (x + k • a)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range n, ‖f‖ := sum_le_sum fun k _ => f.norm_coe_le_norm _
      _ = n * ‖f‖ := by simp
  have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hcast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (n * ‖f‖) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ ‖f‖ := by
      by_cases hn : n = 0
      · simp [hn]
      · rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

lemma averageL_lipschitz (a : Circle) (n : ℕ) : LipschitzWith 1 (averageL a n) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
    norm_averageL_apply_le a n (f - g)

def meanL : CSpace →L[ℂ] CSpace :=
  (ContinuousLinearMap.const ℂ Circle).comp
    ((MeasureTheory.L1.integralCLM' ℂ).comp
      (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ))

@[simp] lemma meanL_apply (f : CSpace) :
    meanL f = ContinuousMap.const Circle (∫ x, f x ∂AddCircle.haarAddCircle) := by
  apply ContinuousMap.ext
  intro x
  change (MeasureTheory.L1.integralCLM' ℂ)
    (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ f) = _
  rw [← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle f)

def convergentSubmodule (a : Circle) : Submodule ℂ CSpace where
  carrier := {f | Tendsto (fun n => averageL a n f) atTop (𝓝 (meanL f))}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun n => averageL a n (f + g)) atTop (𝓝 (meanL (f + g)))
    simpa only [map_add] using hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (fun n => averageL a n (c • f)) atTop (𝓝 (meanL (c • f)))
    simpa only [map_smul] using hf.const_smul c

lemma isClosed_convergentSubmodule (a : Circle) :
    IsClosed (convergentSubmodule a : Set CSpace) := by
  exact (LipschitzWith.uniformEquicontinuous (fun n => averageL a n) 1
    (averageL_lipschitz a)).equicontinuous.isClosed_setOfPred_tendsto meanL.continuous

lemma fourier_translate (m : ℤ) (a x : Circle) (k : ℕ) :
    fourier m (x + k • a) = fourier m x * (fourier m a) ^ k := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]
  rw [smul_comm m k a, AddCircle.toCircle_nsmul, _root_.Circle.coe_pow]

lemma averageL_fourier (a : Circle) (n : ℕ) (m : ℤ) :
    averageL a n (fourier m) =
      ((n : ℂ)⁻¹ * ∑ k ∈ range n, (fourier m a) ^ k) • fourier m := by
  apply ContinuousMap.ext
  intro x
  simp only [averageL_apply, fourier_translate, ← mul_sum,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

lemma norm_geometric_sum_le {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

lemma tendsto_averageL_fourier_zero {a : Circle} {m : ℤ}
    (hne : fourier m a ≠ 1) :
    Tendsto (fun n => averageL a n (fourier m)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ => (n : ℝ)⁻¹ * (2 / ‖fourier m a - 1‖))
  · intro n
    rw [averageL_fourier, norm_smul, fourier_norm, mul_one, norm_mul, norm_inv]
    have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    rw [hcast]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
    exact norm_geometric_sum_le (_root_.Circle.norm_coe _) hne n
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (2 / ‖fourier m a - 1‖)

lemma fourier_ne_one_of_irrational {θ : ℝ} (hθ : Irrational θ)
    {m : ℤ} (hm : m ≠ 0) : fourier m (θ : Circle) ≠ 1 := by
  intro h
  have hc : AddCircle.toCircle (m • (θ : Circle)) = AddCircle.toCircle (0 : Circle) := by
    apply Subtype.ext
    simpa only [fourier_apply, AddCircle.toCircle_zero, _root_.Circle.coe_one] using h
  have hz := AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hc
  rw [← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  have hi : Irrational ((m : ℝ) * θ) := irrational_intCast_mul_iff.mpr ⟨hm, hθ⟩
  apply hi.ne_int k
  simpa only [zsmul_eq_mul, mul_one] using hk.symm

lemma meanL_fourier_of_ne_zero {m : ℤ} (hm : m ≠ 0) :
    meanL (fourier m) = 0 := by
  rw [meanL_apply]
  have hi : (∫ x : Circle, fourier m x ∂AddCircle.haarAddCircle) = 0 :=
    integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hm (by norm_num))
  rw [hi]
  rfl

lemma fourier_mem_convergentSubmodule {θ : ℝ} (hθ : Irrational θ) (m : ℤ) :
    fourier m ∈ convergentSubmodule (θ : Circle) := by
  change Tendsto (fun n => averageL (θ : Circle) n (fourier m)) atTop
    (𝓝 (meanL (fourier m)))
  by_cases hm : m = 0
  · subst m
    have hm : meanL (fourier (T := (1 : ℝ)) 0) = 1 := by
      rw [meanL_apply]
      simp only [fourier_zero, integral_const, probReal_univ, one_smul]
      exact ContinuousMap.const_one
    rw [hm]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    apply ContinuousMap.ext
    intro x
    simp [averageL_apply, hn]
  · rw [meanL_fourier_of_ne_zero hm]
    exact tendsto_averageL_fourier_zero (fourier_ne_one_of_irrational hθ hm)

theorem tendsto_averageL {θ : ℝ} (hθ : Irrational θ) (f : CSpace) :
    Tendsto (fun n => averageL (θ : Circle) n f) atTop (𝓝 (meanL f)) := by
  have hs : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤
      convergentSubmodule (θ : Circle) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact fourier_mem_convergentSubmodule hθ m
  have hc := Submodule.topologicalClosure_minimal
    (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))))
    hs (isClosed_convergentSubmodule (θ : Circle))
  rw [span_fourier_closure_eq_top] at hc
  exact hc (Submodule.mem_top)

theorem tendstoUniformly_complex {θ : ℝ} (hθ : Irrational θ) (f : CSpace) :
    TendstoUniformly
      (fun (n : ℕ) x => (n : ℂ)⁻¹ * ∑ k ∈ range n, f (x + k • (θ : Circle)))
      (fun _ => ∫ x, f x ∂AddCircle.haarAddCircle) atTop := by
  have h := ContinuousMap.tendsto_iff_tendstoUniformly.mp (tendsto_averageL hθ f)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp h) ε hε] with n hn
  intro x
  simpa only [averageL_apply, meanL_apply, ContinuousMap.const_apply] using hn x

theorem tendstoUniformly_real {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) :
    TendstoUniformly
      (fun n x => birkhoffAverage ℝ (fun y : Circle => y + (θ : Circle)) f n x)
      (fun _ => ∫ x, f x ∂AddCircle.haarAddCircle) atTop := by
  let fC : CSpace := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc := Complex.uniformContinuous_re.comp_tendstoUniformly
    (tendstoUniformly_complex hθ fC)
  simp only [Function.comp_def] at hc
  have heq : (fun (n : ℕ) (x : Circle) =>
      ((n : ℂ)⁻¹ * ∑ k ∈ range n, fC (x + k • (θ : Circle))).re) =
      (fun n x => birkhoffAverage ℝ (fun y : Circle => y + (θ : Circle)) f n x) := by
    funext n x
    simp only [fC, ContinuousMap.coe_mk, birkhoffAverage, birkhoffSum,
      add_right_iterate, smul_eq_mul]
    norm_cast
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [heq] at hc
  simpa only [fC, ContinuousMap.coe_mk, integral_complex_ofReal, Complex.ofReal_re] using hc

end InvariantProjection.UniformRotationAverage

end

end OAI
