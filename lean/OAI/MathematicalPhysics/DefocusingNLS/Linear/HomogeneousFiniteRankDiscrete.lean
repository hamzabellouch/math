import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankFactor
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Order.Interval.Set.Infinite

namespace OAI

/-! # Finitely many exceptional spectral values outside a larger disk

The finite-dimensional determinant is nonzero near infinity. The identity
principle on the exterior disk makes its zeros discrete, and compactness
of the ambient spectrum makes every outer portion finite.
-/

open Set Filter Topology Bornology

namespace DefocusingNLS

private theorem complex_norm_exterior_preconnected (q : ℝ) (hq : 0 ≤ q) :
    IsPreconnected {z : ℂ | q < ‖z‖} := by
  let f : ℝ × ℂ → ℂ := fun p => p.1 • p.2
  have hi : f '' (Ioi q ×ˢ Metric.sphere (0 : ℂ) 1) = {z : ℂ | q < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      have hr0 : 0 < r := hq.trans_lt hr
      have hu1 : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
      change q < ‖r • u‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hu1, mul_one]
      exact hr
    · intro hz
      have hz0 : 0 < ‖z‖ := hq.trans_lt hz
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hz0, inv_mul_cancel₀ hz0.ne']
      · dsimp only [f]
        rw [smul_smul, mul_inv_cancel₀ hz0.ne', one_smul]
  rw [← hi]
  apply (isPreconnected_Ioi.prod
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) 1)).image
  fun_prop

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem exterior_mem_resolvent (B : E →L[ℂ] E) {z : ℂ} (hz : ‖B‖ < ‖z‖) :
    z ∈ resolventSet ℂ B := by
  apply spectrum.mem_resolventSet_of_norm_lt_mul
  exact (mul_le_of_le_one_right (norm_nonneg B)
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E))).trans_lt hz

theorem finiteRankSchurDet_codiscrete (B K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap)) :
    {z : ℂ | finiteRankSchurDet B K z ≠ 0} ∈
      codiscreteWithin {z : ℂ | ‖B‖ < ‖z‖} := by
  have hf : AnalyticOnNhd ℂ (finiteRankSchurDet B K) {z : ℂ | ‖B‖ < ‖z‖} :=
    fun z hz => finiteRankSchurDet_analyticAt B K hK z (exterior_mem_resolvent B hz)
  have hnonzero := (finiteRankSchurDet_tendsto_one B K).eventually
    (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  have hlarge : ∀ᶠ z : ℂ in cobounded ℂ, ‖B‖ < ‖z‖ :=
    tendsto_norm_cobounded_atTop.eventually_gt_atTop ‖B‖
  obtain ⟨w, hw, hw0⟩ := (hlarge.and hnonzero).exists
  exact (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
    (complex_norm_exterior_preconnected ‖B‖ (norm_nonneg B))).resolve_left
      (fun hzero => hw0 (hzero hw))

theorem finiteRank_spectrum_outer_finite (B K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (r : ℝ) (hr : ‖B‖ < r) :
    {z : ℂ | z ∈ spectrum ℂ (B + K) ∧ r ≤ ‖z‖}.Finite := by
  let C := spectrum ℂ (B + K) ∩ {z : ℂ | r ≤ ‖z‖}
  have hc : IsCompact C :=
    (spectrum.isCompact (B + K)).inter_right (isClosed_le continuous_const continuous_norm)
  have hsub : C ⊆ {z : ℂ | ‖B‖ < ‖z‖} := fun z hz => hr.trans_le hz.2
  have hfinite := hc.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono hsub) (finiteRankSchurDet_codiscrete B K hK))
  have heq : C \ {z : ℂ | finiteRankSchurDet B K z ≠ 0} = C := by
    apply Subset.antisymm sdiff_subset
    intro z hz
    refine ⟨hz, ?_⟩
    exact fun hne => hne ((finiteRankSchurDet_spectrum_iff B K hK z
      (exterior_mem_resolvent B (hsub hz))).mp hz.1)
  rw [heq] at hfinite
  exact hfinite

/-- A contracting remainder admits a spectral contour strictly inside the unit circle. -/
theorem finiteRank_exists_resolvent_circle (B K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (hB : ‖B‖ < 1) (η : ℝ) (hη : η < 1) :
    ∃ r : ℝ, ‖B‖ < r ∧ η < r ∧ r < 1 ∧
      ∀ z : ℂ, ‖z‖ = r → z ∈ resolventSet ℂ (B + K) := by
  let a := (max ‖B‖ η + 1) / 2
  have hmax : max ‖B‖ η < 1 := max_lt hB hη
  have hBa : ‖B‖ < a := by
    have hle := le_max_left ‖B‖ η
    dsimp only [a]
    linarith
  have hηa : η < a := by
    have hle := le_max_right ‖B‖ η
    dsimp only [a]
    linarith
  have ha1 : a < 1 := by dsimp only [a]; linarith
  have hf := (finiteRank_spectrum_outer_finite B K hK a hBa).image
    (fun z : ℂ => ‖z‖)
  obtain ⟨r, hr, hnot⟩ := (Set.Ioo_infinite ha1).exists_notMem_finite hf
  refine ⟨r, hBa.trans hr.1, hηa.trans hr.1, hr.2, ?_⟩
  intro z hz
  by_contra hres
  have hs : z ∈ spectrum ℂ (B + K) := hres
  apply hnot
  exact ⟨z, ⟨hs, by simpa only [hz] using hr.1.le⟩, hz⟩

end

end DefocusingNLS

end OAI
