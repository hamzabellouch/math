import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralHaarFunctionalCalculus
import OAI.Analysis.KadisonSimilarity.Representation.SpectralSupportLimit

namespace OAI

/-! Continuous functions approximating the open arc spectral projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology
open Filter

/-- The positive resolvent approximation to the open cut `(c,∞)`. -/
def spectralCutFunction (c ε t : ℝ) : ℝ := (t - c)⁺ / ((t - c)⁺ + ε)

theorem spectralCutFunction_continuous (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (spectralCutFunction c ε) := by
  unfold spectralCutFunction
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  exact ne_of_gt (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε)

theorem spectralCutFunction_nonneg (c t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ spectralCutFunction c ε t :=
  div_nonneg (posPart_nonneg _) (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε).le

theorem spectralCutFunction_le_one (c t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    spectralCutFunction c ε t ≤ 1 := by
  apply (div_le_one (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε)).mpr
  linarith

theorem spectralCutFunction_tendsto (c t : ℝ) (ε : ℕ → ℝ)
    (_hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => spectralCutFunction c (ε n) t) atTop
      (𝓝 (if c < t then 1 else 0)) := by
  by_cases hct : c < t
  · simp only [ite_eq_left hct]
    have ht : 0 < (t - c)⁺ := by rw [posPart_eq_self.mpr (sub_pos.mpr hct).le]; linarith
    have hc : Tendsto (fun _ : ℕ => (t - c)⁺) atTop (𝓝 ((t - c)⁺)) := tendsto_const_nhds
    have h := hc.div (hlim.const_add ((t - c)⁺)) (by simpa only [add_zero] using ht.ne')
    change Tendsto (fun n => (t - c)⁺ / ((t - c)⁺ + ε n)) atTop
      (𝓝 ((t - c)⁺ / ((t - c)⁺ + 0))) at h
    simpa only [spectralCutFunction, Pi.div_apply, add_zero, div_self ht.ne'] using h
  · have ht : (t - c)⁺ = 0 := posPart_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hct))
    simpa only [spectralCutFunction, ht, zero_div, ite_eq_right hct] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveShift_cfc (a : H →L[ℂ] H) (ha : IsSelfAdjoint a) (c : ℝ) :
    cfc (fun t : ℝ => (t - c)⁺) a = (a - c • 1)⁺ := by
  have hs : cfc (fun t : ℝ => t - c) a = a - c • 1 := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => c) a continuousOn_id continuousOn_const,
      cfc_id' ℝ a ha, cfc_const c a ha, Algebra.algebraMap_eq_smul_one]
  rw [CFC.posPart_def, cfcₙ_eq_cfc, ← hs]
  exact cfc_comp' (fun t : ℝ => t⁺) (fun t => t - c) a
    (by fun_prop) (by fun_prop) ha

/-- The actual operators in the strong support approximation are evaluations
of the scalar continuous cut functions. -/
theorem supportResolvent_positiveShift_eq_cfc (a : H →L[ℂ] H)
    (ha : IsSelfAdjoint a) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    supportResolvent (a - c • 1)⁺ ε = cfc (spectralCutFunction c ε) a := by
  let B := (a - c • 1)⁺
  have hB : 0 ≤ B := CFC.posPart_nonneg _
  have hres : supportResolvent B ε = cfc (fun t : ℝ => t / (t + ε)) B := by
    rw [supportResolvent, positiveShiftReciprocal]
    conv_lhs => arg 1; rw [← cfc_id' ℝ B hB.isSelfAdjoint]
    rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) B
      continuousOn_id (positiveShiftReciprocal_continuous B hB hε)]
    rfl
  rw [hres]
  change cfc (fun t : ℝ => t / (t + ε)) (a - c • 1)⁺ = _
  rw [← positiveShift_cfc a ha c]
  exact (cfc_comp' (fun t : ℝ => t / (t + ε)) (fun t : ℝ => (t - c)⁺) a
    (by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      obtain ⟨x, _, rfl⟩ := ht
      exact ne_of_gt (add_pos_of_nonneg_of_pos (posPart_nonneg _) hε))
    (by fun_prop) ha).symm

end KadisonSimilarity

end

end OAI
