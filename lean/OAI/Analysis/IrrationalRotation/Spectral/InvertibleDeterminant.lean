import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal CStarAlgebra
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem vectorTrace_re_mono (ξ : H) {A B : H →L[ℂ] H} (h : A ≤ B) :
    (vectorTrace ξ A).re ≤ (vectorTrace ξ B).re := by
  have hp := ContinuousLinearMap.le_def.mp h
  have hv := hp.re_inner_nonneg_right ξ
  change 0 ≤ (inner ℂ ξ ((B - A) ξ)).re at hv
  simpa only [sub_apply, inner_sub_right, Complex.sub_re,
    sub_nonneg, vectorTrace] using hv

theorem log_le_log_add_smul_one {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (hA : IsStrictlyPositive a)
    (ε : ℝ) (hε : 0 ≤ ε) :
    CFC.log a ≤ CFC.log (a + ε • (1 : A)) := by
  have hsa : IsSelfAdjoint a := hA.isSelfAdjoint
  have hshift : cfc (fun x : ℝ => x + ε) a = a + ε • (1 : A) := by
    rw [cfc_add_const ε (fun x : ℝ => x) a (by fun_prop) hsa,
      cfc_id' (R := ℝ) a hsa]
    rw [Algebra.algebraMap_eq_smul_one]
  have hc : ContinuousOn Real.log ((fun x : ℝ => x + ε) '' spectrum ℝ a) := by
    apply Real.continuousOn_log.mono
    rintro x ⟨y, hy, rfl⟩
    exact ne_of_gt (lt_of_lt_of_le (hA.spectrum_pos hy) (le_add_of_nonneg_right hε))
  rw [CFC.log, CFC.log, ← hshift, ← cfc_comp Real.log (fun x : ℝ => x + ε) a hsa hc]
  apply cfc_mono
  · intro x hx
    exact Real.log_le_log (hA.spectrum_pos hx) (le_add_of_nonneg_right hε)
  · exact Real.continuousOn_log.mono (fun x hx => (hA.spectrum_pos hx).ne')
  · exact hc.comp (by fun_prop) (fun x hx => ⟨x, hx, rfl⟩)

theorem tendsto_log_add_one_div {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (hA : IsStrictlyPositive a) :
    Tendsto (fun n : ℕ => CFC.log (a + (1 / ((n : ℝ) + 1)) • (1 : A)))
      atTop (𝓝 (CFC.log a)) := by
  have hscalar : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => a + (1 / ((n : ℝ) + 1)) • (1 : A))
      atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add
      (hscalar.smul (tendsto_const_nhds (x := (1 : A))))
  apply (CFC.continuousOn_log a ⟨hA.isSelfAdjoint, hA.isUnit⟩).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hlim, Filter.Eventually.of_forall fun n => ?_⟩
  have hp : IsStrictlyPositive (a + (1 / ((n : ℝ) + 1)) • (1 : A)) :=
    hA.add_nonneg (smul_nonneg (by positivity) zero_le_one)
  exact ⟨hp.isSelfAdjoint, hp.isUnit⟩

theorem vectorFugledeKadisonDeterminant_of_isUnit (ξ : H) (T : H →L[ℂ] H)
    (hT : IsUnit T) :
    vectorFugledeKadisonDeterminant ξ T =
      ENNReal.ofReal (Real.exp ((vectorTrace ξ (CFC.log (star T * T))).re / 2)) := by
  have hA : IsStrictlyPositive (star T * T) :=
    ⟨star_mul_self_nonneg T, hT.star.mul hT⟩
  have hcont : Continuous (fun B : H →L[ℂ] H =>
      ENNReal.ofReal (Real.exp ((vectorTrace ξ B).re / 2))) := by
    apply ENNReal.continuous_ofReal.comp
    unfold vectorTrace
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp (tendsto_log_add_one_div (star T * T) hA)
  unfold vectorFugledeKadisonDeterminant
  apply le_antisymm
  · apply ge_of_tendsto' hlim
    intro n
    exact iInf_le _ (⟨1 / ((n : ℝ) + 1), by positivity⟩ : {r : ℝ // 0 < r})
  · apply le_iInf
    intro ε
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact vectorTrace_re_mono ξ (log_le_log_add_smul_one (star T * T) hA ε.val ε.property.le)

theorem vectorFugledeKadisonDeterminant_pos_of_isUnit (ξ : H) (T : H →L[ℂ] H)
    (hT : IsUnit T) : 0 < vectorFugledeKadisonDeterminant ξ T := by
  rw [vectorFugledeKadisonDeterminant_of_isUnit ξ T hT]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem zero_mem_spectrum_of_vectorDeterminant_zero (ξ : H) (T : H →L[ℂ] H)
    (hT : vectorFugledeKadisonDeterminant ξ T = 0) : 0 ∈ spectrum ℂ T := by
  apply (spectrum.zero_mem_iff ℂ).mpr
  intro hu
  have hp := vectorFugledeKadisonDeterminant_pos_of_isUnit ξ T hu
  rw [hT] at hp
  exact (lt_irrefl (0 : ℝ≥0∞)) hp

theorem vectorFugledeKadisonDeterminant_sub_scalar_of_spectrum_subset_zero
    (ξ : H) (T : H →L[ℂ] H) (hσ : spectrum ℂ T ⊆ {0})
    (z : ℂ) (hz : z ≠ 0) :
    vectorFugledeKadisonDeterminant ξ (T - z • (1 : H →L[ℂ] H)) =
      ENNReal.ofReal (Real.exp ((vectorTrace ξ (CFC.log
        (star (T - z • (1 : H →L[ℂ] H)) * (T - z • (1 : H →L[ℂ] H))))).re / 2)) := by
  apply vectorFugledeKadisonDeterminant_of_isUnit
  have hnot : z ∉ spectrum ℂ T := fun h => hz (hσ h)
  have hu := (spectrum.notMem_iff.mp hnot).neg
  simpa only [neg_sub, Algebra.algebraMap_eq_smul_one] using hu

end Invariant233

end

end OAI
