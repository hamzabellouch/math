import Mathlib

namespace OAI

/-!
# Local fractional-density integrability

Simple normal-crossing densities with coefficients strictly less than one are locally integrable.
Rational fractional coefficients admit a common exponent `a > 1`, giving the local `L^a` input
to Hölder's inequality in the weight-integral bounds. Supporting results cover interpolation and
floor arithmetic, logarithmic comparison weights, contraction, and fixed-space weak convergence
and class vanishing.

This local coordinate result omits the bounded geometric factor, coordinate gluing, regularized
metric bounds, and the uniform integral estimate. It establishes neither a geometric adjoint-metric
theorem nor injectivity of the natural coherent-cohomology inclusion.
`NefAdjoint.SNC.LelongSNCDivergenceGoal` remains a goal proposition, not a proved theorem.
-/


noncomputable section
open MeasureTheory Set Metric
open scoped Topology
namespace NefAdjoint.SNC

def euclideanNorm {n : ℕ} (z : Fin n → ℂ) : ℝ := ‖WithLp.toLp 2 z‖
def boundaryWeight {n : ℕ} (β : Fin n → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∑ i, β i * Real.log (‖z i‖^2)
def density {n : ℕ} (β : Fin n → ℝ) (z : Fin n → ℂ) : ℝ :=
  Real.exp (-boundaryWeight β z)

def SNCDensityGoal : Prop :=
  ∀ (n : ℕ) (β : Fin n → ℝ), (∀ i, β i < 1) → LocallyIntegrable (density β) volume

def LelongSNCDivergenceGoal : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (β : Fin n → ℝ), (∀ i, β i < 1) →
  ∀ (α c R : ℝ), 0 < α → 0 < c → 0 < R →
  (n : ℝ) ≤ c*α + ∑ i, β i →
  ∀ (φ : (Fin n → ℂ) → ℝ) (K : ℝ),
    (∀ z, 0 < euclideanNorm z → euclideanNorm z < R →
      φ z ≤ α * Real.log (euclideanNorm z ^ 2) + K) →
    ¬ IntegrableOn (fun z => Real.exp (-c*φ z-boundaryWeight β z))
      {z | euclideanNorm z < R} volume
end NefAdjoint.SNC

end


noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace NefAdjoint.SNC

def powerDensity {n : ℕ} (β : Fin n → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∏ i, ‖z i‖ ^ (-2*β i)

lemma powerDensity_nonneg {n : ℕ} (β : Fin n → ℝ) (z : Fin n → ℂ) :
    0 ≤ powerDensity β z := Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

lemma density_eq_power {n : ℕ} (β : Fin n → ℝ) {z : Fin n → ℂ}
    (hz : ∀ i, z i ≠ 0) : density β z = powerDensity β z := by
  simp only [density, boundaryWeight, ← Finset.sum_neg_distrib, Real.exp_sum, powerDensity]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (hz i)),Real.log_pow]
  congr 1
  ring

lemma density_ae_power {n : ℕ} (β : Fin n → ℝ) : density β =ᵐ[volume] powerDensity β := by
  have hn : ∀ᵐ z : Fin n → ℂ, ∀ i, z i ≠ 0 :=
    ae_all_iff.mpr fun i => Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℂ)) i 0
  exact hn.mono fun _ hz => density_eq_power β hz

lemma planar_power_integrable {β : ℝ} (hβ : β < 1) (R : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖^(-2*β)) (ball 0 R) volume := by
  refine integrableOn_ball_of_norm_le_rpow (by norm_num : 1 ≤ Module.finrank ℝ ℂ)
    (C := 1) (α := 2*β) ?_ ?_ ?_
  · simpa using hβ
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
      simp only [one_mul,neg_mul]
      exact le_rfl
  · exact (by fun_prop : Measurable (fun z : ℂ => ‖z‖^(-2*β))).aestronglyMeasurable

lemma powerDensity_integrable_polydisc {n : ℕ} {β : Fin n → ℝ}
    (hβ : ∀ i, β i < 1) (R : ℝ) :
    IntegrableOn (powerDensity β) (Set.univ.pi (fun _ => ball (0 : ℂ) R)) volume := by
  change Integrable (powerDensity β)
    ((Measure.pi (fun _ : Fin n => (volume : Measure ℂ))).restrict _)
  rw [Measure.restrict_pi_pi]
  exact Integrable.fintype_prod fun i => planar_power_integrable (hβ i) R

lemma powerDensity_locallyIntegrable {n : ℕ} {β : Fin n → ℝ} (hβ : ∀ i, β i < 1) :
    LocallyIntegrable (powerDensity β) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_lt
  apply (powerDensity_integrable_polydisc hβ R).mono_set
  intro z hz i hi
  exact mem_ball_zero_iff.mpr ((norm_le_pi_norm z i).trans_lt (hKR z hz))

theorem snc_density : SNCDensityGoal := by
  intro n β hβ
  exact (powerDensity_locallyIntegrable hβ).congr (density_ae_power β).symm

end NefAdjoint.SNC

end

noncomputable section

namespace NefAdjoint.InteriorBoundary

def interpolate {ι : Type*} (C₀ C₂ : ι → ℚ) (t : ℚ) : ι → ℚ :=
  fun i => (1 - t) * C₀ i + t * C₂ i

def floorDifference {ι : Type*} (C₀ C₂ : ι → ℚ) (t : ℚ) : ι → ℤ :=
  fun i => ⌊interpolate C₀ C₂ t i⌋ - ⌊C₀ i⌋

lemma interpolate_between {ι : Type*} {C₀ C₂ : ι → ℚ} {t : ℚ}
    (hC : ∀ i, C₀ i ≤ C₂ i) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : ι) :
    C₀ i ≤ interpolate C₀ C₂ t i ∧ interpolate C₀ C₂ t i ≤ C₂ i := by
  have ha := mul_nonneg ht₀ (sub_nonneg.mpr (hC i))
  have hb := mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr (hC i))
  dsimp [interpolate]
  constructor <;> nlinarith

lemma floorDifference_nonneg {ι : Type*} {C₀ C₂ : ι → ℚ} {t : ℚ}
    (hC : ∀ i, C₀ i ≤ C₂ i) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : ι) :
    0 ≤ floorDifference C₀ C₂ t i := by
  exact sub_nonneg.mpr (Int.floor_mono (interpolate_between hC ht₀ ht₁ i).1)

lemma adjoint_difference {ι : Type*} (L : ι → ℤ) (C₀ C₂ : ι → ℚ)
    (t : ℚ) (i : ι) :
    (L i - ⌊interpolate C₀ C₂ t i⌋) + floorDifference C₀ C₂ t i =
      L i - ⌊C₀ i⌋ := by
  dsimp [floorDifference]
  omega

lemma interpolate_ne_zero_iff {ι : Type*} {C₀ C₂ : ι → ℚ} {t : ℚ}
    (h₀ : ∀ i, 0 ≤ C₀ i) (hC : ∀ i, C₀ i ≤ C₂ i)
    (ht₀ : 0 < t) (ht₁ : t < 1) (i : ι) :
    interpolate C₀ C₂ t i ≠ 0 ↔ C₂ i ≠ 0 := by
  have h₂ : 0 ≤ C₂ i := le_trans (h₀ i) (hC i)
  constructor
  · intro h hz
    have hc₀ : C₀ i = 0 := le_antisymm (hz ▸ hC i) (h₀ i)
    apply h
    simp [interpolate, hc₀, hz]
  · intro h
    have hpos : 0 < C₂ i := lt_of_le_of_ne h₂ (Ne.symm h)
    have hl := mul_pos ht₀ hpos
    have hr := mul_nonneg (sub_nonneg.mpr ht₁.le) (h₀ i)
    dsimp [interpolate]
    exact ne_of_gt (add_pos_of_nonneg_of_pos hr hl)

lemma exists_common_exponent {ι : Type*} [Finite ι] (β : ι → ℝ)
    (hβ : ∀ i, β i < 1) : ∃ a : ℝ, 1 < a ∧ ∀ i, a * β i < 1 := by
  have hnear : ∀ᶠ a : ℝ in nhds 1, ∀ i, a * β i < 1 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun a : ℝ => a * β i) 1 := by fun_prop
    exact hc (IsOpen.mem_nhds isOpen_Iio (by simpa using hβ i))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨1 + r / 2, by linarith, hball ?_⟩
  rw [Real.dist_eq, show 1 + r / 2 - 1 = r / 2 by ring, abs_of_pos (half_pos hr)]
  linarith

lemma fractional_coefficients (c : ℚ) :
    0 ≤ (c : ℝ) - (⌊c⌋ : ℝ) ∧ (c : ℝ) - (⌊c⌋ : ℝ) < 1 := by
  have h₀ := Int.floor_le c
  have h₁ := Int.lt_floor_add_one c
  constructor
  · exact_mod_cast (sub_nonneg.mpr h₀ : (0 : ℚ) ≤ c - ⌊c⌋)
  · exact_mod_cast (by linarith : c - (⌊c⌋ : ℚ) < 1)

end NefAdjoint.InteriorBoundary

namespace NefAdjoint.SNC

lemma density_rpow {n : ℕ} (β : Fin n → ℝ) (a : ℝ) (z : Fin n → ℂ) :
    density β z ^ a = density (fun j => a * β j) z := by
  simp only [density, ← Real.exp_mul, boundaryWeight]
  congr 1
  simp only [← Finset.mul_sum, mul_assoc]
  ring

theorem exists_locallyIntegrable_power {n : ℕ} (β : Fin n → ℝ)
    (hβ : ∀ j, β j < 1) :
    ∃ a : ℝ, 1 < a ∧ MeasureTheory.LocallyIntegrable
      (fun z => density β z ^ a) MeasureTheory.volume := by
  obtain ⟨a, ha, hab⟩ := InteriorBoundary.exists_common_exponent β hβ
  refine ⟨a, ha, ?_⟩
  simpa only [density_rpow] using snc_density n (fun j => a * β j) hab

lemma fractional_density_power {n : ℕ} (C : Fin n → ℚ) :
    ∃ a : ℝ, 1 < a ∧ MeasureTheory.LocallyIntegrable
      (fun z => density (fun j => (C j : ℝ) - (⌊C j⌋ : ℝ)) z ^ a)
      MeasureTheory.volume :=
  exists_locallyIntegrable_power _ fun j => (InteriorBoundary.fractional_coefficients (C j)).2

end NefAdjoint.SNC

namespace NefAdjoint.ComparisonWeights

def logSum (x y : ℝ) : ℝ := Real.log (Real.exp x + Real.exp y)

lemma le_logSum_left (x y : ℝ) : x ≤ logSum x y := by
  calc
    x = Real.log (Real.exp x) := (Real.log_exp x).symm
    _ ≤ logSum x y := Real.log_le_log (Real.exp_pos x)
      (le_add_of_nonneg_right (Real.exp_pos y).le)

lemma le_logSum_right (x y : ℝ) : y ≤ logSum x y := by
  rw [logSum, add_comm]
  exact le_logSum_left y x

lemma logSum_add (x y r : ℝ) : logSum (x + r) (y + r) = logSum x y + r := by
  have hx : Real.exp x + Real.exp y ≠ 0 := ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  simp only [logSum, Real.exp_add, ← add_mul]
  rw [Real.log_mul hx (ne_of_gt (Real.exp_pos r)), Real.log_exp]

lemma logSum_le_of_le {x y x' y' : ℝ} (hx : x ≤ x') (hy : y ≤ y') :
    logSum x y ≤ logSum x' y' := by
  apply Real.log_le_log (add_pos (Real.exp_pos _) (Real.exp_pos _))
  exact add_le_add (Real.exp_le_exp.mpr hx) (Real.exp_le_exp.mpr hy)

lemma raised_exponential_le (x y b : ℝ) (hb : 0 ≤ b) :
    Real.exp (-b * logSum x y) ≤ Real.exp (-b * x) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (le_logSum_left x y) (neg_nonpos.mpr hb)

lemma integral_weight_contraction (x y c₀ c₂ f₀ f₁ t : ℝ) (ht : 0 ≤ t) :
    let Φ₀ := logSum x (y + c₂ - c₀) + c₀
    let Φ₂ := y + c₂
    let h₀ := Φ₀ - f₀
    let h₁ := (1-t) * Φ₀ + t * Φ₂ - f₁
    Real.exp ((f₁-f₀) - h₀) ≤ Real.exp (-h₁) := by
  dsimp only
  have hraised := le_logSum_right x (y + c₂ - c₀)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hraised)]

end NefAdjoint.ComparisonWeights

namespace NefAdjoint.FixedSpace

open Filter
open scoped Topology

theorem tendsto_pairings_of_dense
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {S : Set E} (hS : Dense S) (u : ℕ → E) (M : ℝ)
    (hbound : ∀ k, ‖u k‖ ≤ M)
    (htest : ∀ v ∈ S, Tendsto (fun k => inner 𝕜 v (u k)) atTop (𝓝 0))
    (v : E) : Tendsto (fun k => inner 𝕜 v (u k)) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hbound 0)
  have hMp : 0 < M + 1 := by linarith
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε / (2 * (M + 1)) := div_pos hε (mul_pos (by norm_num) hMp)
  obtain ⟨w, hwS, hvw⟩ := Metric.mem_closure_iff.mp (hS v) _ hδ
  rw [dist_eq_norm] at hvw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (htest w hwS) (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  have htail : ‖inner 𝕜 (v-w) (u k)‖ < ε / 2 := by
    calc
      ‖inner 𝕜 (v-w) (u k)‖ ≤ ‖v-w‖ * ‖u k‖ := norm_inner_le_norm _ _
      _ ≤ ‖v-w‖ * M := mul_le_mul_of_nonneg_left (hbound k) (norm_nonneg _)
      _ ≤ ‖v-w‖ * (M+1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < (ε / (2 * (M+1))) * (M+1) := mul_lt_mul_of_pos_right hvw hMp
      _ = ε / 2 := by field_simp
  have hhead : ‖inner 𝕜 w (u k)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN k hk
  rw [dist_zero_right]
  calc
    ‖inner 𝕜 v (u k)‖ = ‖inner 𝕜 (v-w) (u k) + inner 𝕜 w (u k)‖ := by
      rw [inner_sub_left, sub_add_cancel]
    _ ≤ ‖inner 𝕜 (v-w) (u k)‖ + ‖inner 𝕜 w (u k)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add htail hhead
    _ = ε := by ring

theorem tendsto_duals_of_dense
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] {S : Set E} (hS : Dense S) (u : ℕ → E) (M : ℝ)
    (hbound : ∀ k, ‖u k‖ ≤ M)
    (htest : ∀ v ∈ S, Tendsto (fun k => inner 𝕜 v (u k)) atTop (𝓝 0))
    (f : E →L[𝕜] 𝕜) : Tendsto (fun k => f (u k)) atTop (𝓝 0) := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    tendsto_pairings_of_dense hS u M hbound htest ((InnerProductSpace.toDual 𝕜 E).symm f)

theorem constant_class_vanishes
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (q : E →L[𝕜] F) (u : ℕ → E) (c : F)
    (hweak : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun k => f (u k)) atTop (𝓝 0))
    (hclass : ∀ k, q (u k) = c) : c = 0 := by
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜)
  intro f
  have hlim : Tendsto (fun _ : ℕ => f c) atTop (𝓝 0) := by
    simpa only [ContinuousLinearMap.comp_apply, hclass] using hweak (f.comp q)
  exact tendsto_nhds_unique tendsto_const_nhds hlim

theorem class_vanishes_of_weakly_null_differences
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (q : E →L[𝕜] F) (u : ℕ → E) (γ : E)
    (hweak : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun k => f (u k)) atTop (𝓝 0))
    (hdiff : ∀ k, q (γ - u k) = 0) : q γ = 0 := by
  apply constant_class_vanishes q u (q γ) hweak
  intro k
  have hz : q γ - q (u k) = 0 := by simpa only [map_sub] using hdiff k
  exact (sub_eq_zero.mp hz).symm

theorem class_vanishes_of_closure_differences
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (q : E →L[𝕜] F) (S : Set E) (hS : ∀ z ∈ S, q z = 0)
    (u : ℕ → E) (γ : E)
    (hweak : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun k => f (u k)) atTop (𝓝 0))
    (hdiff : ∀ k, γ - u k ∈ closure S) : q γ = 0 := by
  have hclosure : closure S ⊆ {z : E | q z = 0} :=
    closure_minimal hS (isClosed_eq q.continuous continuous_const)
  exact class_vanishes_of_weakly_null_differences q u γ hweak
    (fun k => hclosure (hdiff k))

end NefAdjoint.FixedSpace

end

end OAI
