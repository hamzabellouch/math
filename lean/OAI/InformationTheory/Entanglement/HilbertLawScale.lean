import OAI.InformationTheory.Entanglement.HilbertLawAlgebra

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}
lemma hilbertENorm_real_smul (b : HilbertBasis ι ℂ H) (c : ℝ) (hc : 0≤c) (A : H→L[ℂ]H) :
    hilbertENorm b ((c : ℂ) • A)=ENNReal.ofReal c*hilbertENorm b A := by
  have he : CFC.abs ((c : ℂ) • A)=(c : ℂ) • CFC.abs A := by
    rw [CFC.abs_smul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
    ext x
    simp
  simp only [hilbertENorm,he,_root_.smul_apply,inner_smul_right,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,ENNReal.ofReal_mul hc]
  exact ENNReal.tsum_mul_left
lemma hilbertVariation_real_smul (b : HilbertBasis ι ℂ H) (c : ℝ) (hc : 0≤c)
    (F : Set T→H→L[ℂ]H) :
    hilbertVariation b (fun s => (c : ℂ) • F s)=ENNReal.ofReal c*hilbertVariation b F := by
  simp only [hilbertVariation,hilbertENorm_real_smul b c hc,← Finset.mul_sum,← ENNReal.mul_iSup]
lemma hermitianTraceClass_scaled_difference (b : HilbertBasis ι ℂ H) (c : ℝ) (hc : 0≤c)
    {A B : H→L[ℂ]H} (hA : HasFinitePositiveTrace b A) (hB : HasFinitePositiveTrace b B) :
    HermitianTraceClass b ((c : ℂ) • (A-B)) := by
  rw [smul_sub]
  exact (positive_difference_traceClass b (finitePositiveTrace_real_smul b c hc hA)
    (finitePositiveTrace_real_smul b c hc hB)).1

theorem hilbertClassical_mixture_bound {a : Type*} [Fintype a]
    (b : HilbertBasis ι ℂ H) (δ : ℝ) (hδ0 : 0≤δ) (hδ1 : δ≤1)
    (W ok bad γ : a→PositiveHilbertMeasure T H b)
    (hW : ∀ i s, MeasurableSet s →
      (W i).value s=((1-δ : ℝ) : ℂ) • (ok i).value s+(δ : ℂ) • (bad i).value s)
    (hbad : ∑ i, (bad i).traceMeasure Set.univ=1)
    (hγ : ∑ i, (γ i).traceMeasure Set.univ=1) :
    hilbertClassicalDistance b W γ≤
      ENNReal.ofReal (1-δ)*hilbertClassicalDistance b ok γ+2*ENNReal.ofReal δ := by
  have hc : 0≤1-δ := sub_nonneg.mpr hδ1
  have hb := hilbertClassicalDistance_le_two b bad γ hbad hγ
  calc
    _ ≤ ENNReal.ofReal (1-δ)*hilbertClassicalDistance b ok γ+
          ENNReal.ofReal δ*hilbertClassicalDistance b bad γ := by
      unfold hilbertClassicalDistance
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have he := hilbertVariation_congr b (fun s hs => show
          (W i).value s-(γ i).value s=
          ((1-δ : ℝ) : ℂ) • ((ok i).value s-(γ i).value s)+
            (δ : ℂ) • ((bad i).value s-(γ i).value s) from by
          rw [hW i s hs]
          push_cast
          module)
      rw [he,← hilbertVariation_real_smul b (1-δ) hc,← hilbertVariation_real_smul b δ hδ0]
      exact hilbertVariation_add_le b _ _
        (fun s hs => hermitianTraceClass_scaled_difference b (1-δ) hc ((ok i).positive s hs) ((γ i).positive s hs))
        (fun s hs => hermitianTraceClass_scaled_difference b δ hδ0 ((bad i).positive s hs) ((γ i).positive s hs))
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [mul_comm] using mul_le_mul (show ENNReal.ofReal δ ≤ ENNReal.ofReal δ from le_rfl) hb (bot_le) (bot_le)

end SecretKey

end

end OAI
