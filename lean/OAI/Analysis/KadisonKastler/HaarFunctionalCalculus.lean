import OAI.Analysis.KadisonKastler.FreeHaarClosure
import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

/-! # The continuous Haar trace formula

An explicit continuous functional calculus is determined here by its
values on Fourier monomials. Fourier density and the integer Haar
moments identify its trace with normalized angular Haar integration.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

universe u

abbrev HaarCircle := AddCircle (2 * Real.pi)

local instance haarFunctionalPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Integration of continuous functions against probability Haar measure. -/
def haarCircleIntegral : C(HaarCircle, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM' ℂ).comp
    (ContinuousMap.toLp 1 (AddCircle.haarAddCircle (T := 2 * Real.pi)) ℂ)

@[simp]
theorem haarCircleIntegral_apply (g : C(HaarCircle, ℂ)) :
    haarCircleIntegral g = ∫ t, g t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
  change MeasureTheory.L1.integralCLM' ℂ
      (ContinuousMap.toLp 1 (AddCircle.haarAddCircle (T := 2 * Real.pi)) ℂ g) = _
  rw [← MeasureTheory.L1.integral_eq', MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp
    (AddCircle.haarAddCircle (T := 2 * Real.pi)) g)

theorem haarCircleIntegral_fourier (n : ℤ) :
    haarCircleIntegral (fourier (T := 2 * Real.pi) n) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) n) 0
  rw [haarCircleIntegral_apply]
  by_cases hn : n = 0
  · subst n
    simp
  · simpa [fourierCoeff, hn, Ne.symm hn] using h

variable {B : Type u} [CStarAlgebra B]

private def traceCLM (τ : FaithfulTracialState B) : B →L[ℂ] ℂ :=
  τ.toLinearMap.mkContinuous 1 (fun x => by
    simpa only [one_mul] using τ.norm_apply_le_norm x)

/-- Matching the Fourier monomials with Haar powers determines the trace
of every continuous function. -/
theorem haar_functional_trace (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (g : C(HaarCircle, ℂ)) :
    τ.toLinearMap (Φ g) = ∫ t, g t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
  let L : C(HaarCircle, ℂ) →L[ℂ] ℂ := (traceCLM τ).comp (starAlgHomToContinuousLinearMap Φ)
  let D := L - haarCircleIntegral
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi))) ≤ D.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change τ.toLinearMap (Φ (fourier n)) - haarCircleIntegral (fourier n) = 0
    rw [hΦ n, haarCircleIntegral_fourier]
    by_cases hn : n = 0
    · simp [hn, τ.map_one]
    · simp [hn, hhaar n hn]
  have hclose := Submodule.topologicalClosure_minimal _ hspan D.isClosed_ker
  have hg : g ∈ (Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  have hzero : D g = 0 := hclose hg
  change τ.toLinearMap (Φ g) - haarCircleIntegral g = 0 at hzero
  rw [haarCircleIntegral_apply] at hzero
  exact sub_eq_zero.mp hzero

theorem FreeHaarMoments.functional_trace {τ : FaithfulTracialState B}
    {A : StarSubalgebra ℂ B} {v : unitary B} (h : FreeHaarMoments τ A v)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (g : C(HaarCircle, ℂ)) :
    τ.toLinearMap (Φ g) = ∫ t, g t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) :=
  haar_functional_trace τ v h.haar_moment Φ hΦ g

/-- The continuous calculus preserves the scalar Haar square integral. -/
theorem haar_functional_trace_square (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (g : C(HaarCircle, ℂ)) :
    τ.toLinearMap (star (Φ g) * Φ g) =
      ((∫ t, ‖g t‖ ^ 2 ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) : ℝ) := by
  rw [← map_star, ← map_mul, haar_functional_trace τ v hhaar Φ hΦ]
  calc
    _ = ∫ t, ((‖g t‖ ^ 2 : ℝ) : ℂ) ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      change star (g t) * g t = _
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    _ = _ := integral_complex_ofReal

/-- In particular, its tracial two-norm is the scalar Haar `L²` norm. -/
theorem traceTwoNorm_haar_functional (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (g : C(HaarCircle, ℂ)) :
    traceTwoNorm τ (Φ g) =
      Real.sqrt (∫ t, ‖g t‖ ^ 2 ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) := by
  rw [traceTwoNorm, haar_functional_trace_square τ v hhaar Φ hΦ]
  rfl

theorem map_fourierSpan_mem_haarLaurentSpan (v : unitary B)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) {g : C(HaarCircle, ℂ)}
    (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))) :
    Φ g ∈ haarLaurentSpan v := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    rw [hΦ]
    exact haarPower_mem_haarLaurentSpan v n
  | zero => simpa only [map_zero] using (haarLaurentSpan v).zero_mem
  | add f g hf hg hfΦ hgΦ =>
    simpa only [map_add] using (haarLaurentSpan v).add_mem hfΦ hgΦ
  | smul c g hg hgΦ =>
    simpa only [map_smul] using (haarLaurentSpan v).smul_mem c hgΦ

/-- Fourier density supplies actual Laurent approximants to every
continuous function of the Haar unitary. -/
theorem exists_haarLaurent_approx_of_functional (τ : FaithfulTracialState B)
    (v : unitary B) (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (g : C(HaarCircle, ℂ)) :
    ∃ c : ℕ → B, (∀ n, c n ∈ haarLaurentSpan v) ∧
      Tendsto (fun n => traceTwoNorm τ (c n - Φ g)) atTop (𝓝 0) := by
  have hg : g ∈ closure (Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi))) :
      Set C(HaarCircle, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp hg
  refine ⟨fun n => Φ (q n), fun n => map_fourierSpan_mem_haarLaurentSpan v Φ hΦ (hq n), ?_⟩
  have hmap : Tendsto (fun n => Φ (q n)) atTop (𝓝 (Φ g)) :=
    (starAlgHomToContinuousLinearMap Φ).continuous.tendsto _ |>.comp hlim
  have hn : Tendsto (fun n => ‖Φ (q n) - Φ g‖) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => Φ g) atTop (𝓝 (Φ g)) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hmap.sub hconst).norm
  exact squeeze_zero (fun n => traceTwoNorm_nonneg τ _) (fun n => traceTwoNorm_le_norm τ _) hn

end

end KadisonKastler

end OAI
