import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma defect_tendstoInMeasure_of_small_exceptions
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) (E : ℕ → Lp V 2 μ) (r : ℕ → X → V)
    (η : ℕ → ℝ) (hη : ∀ n, 0 ≤ η n) (hηt : Tendsto η atTop (𝓝 0))
    (B : ℕ → Set X) (hB : Tendsto (fun n => μ (B n)) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (hEC : ∀ n, ‖E n‖ ≤ C)
    (hdef : ∀ n, ∀ᵐ x ∂μ, x ∉ B n → ‖r n x‖ ≤ η n * ‖E n x‖) :
    TendstoInMeasure μ r atTop (fun _ => 0) := by
  let Z : ℕ → Lp V 2 μ := fun n => η n • E n
  have hZ : Tendsto Z atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa using hηt.mul_const C)
    intro n
    change ‖η n • E n‖ ≤ η n * C
    rw [norm_smul, Real.norm_of_nonneg (hη n)]
    simpa only [mul_comm] using mul_le_mul (hEC n) le_rfl (hη n) hC
  have hZI : TendstoInMeasure μ (fun n x => Z n x) atTop (fun _ => 0) := by
    have hh := tendstoInMeasure_of_tendsto_Lp hZ
    apply hh.congr_right
    filter_upwards [Lp.coeFn_zero (E := V) (p := 2) (μ := μ)] with x hx
    exact hx
  rw [tendstoInMeasure_iff_norm] at hZI ⊢
  intro ε hε
  simp only [sub_zero] at hZI ⊢
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hB.add (hZI ε hε))
  · exact Eventually.of_forall (fun _ => bot_le)
  · apply Eventually.of_forall
    intro n
    have hs : ∀ᵐ x ∂μ, x ∈ {x | ε ≤ ‖r n x‖} → x ∈ B n ∪ {x | ε ≤ ‖Z n x‖} := by
      filter_upwards [hdef n, Lp.coeFn_smul (η n) (E n)] with x hx hz
      intro hr
      by_cases hb : x ∈ B n
      · exact Or.inl hb
      · right
        have he : ‖Z n x‖ = η n * ‖E n x‖ := by
          change ‖(η n • E n : Lp V 2 μ) x‖ = _
          rw [hz, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (hη n)]
        exact (hr.trans (hx hb)).trans_eq he.symm
    exact (measure_mono_ae hs).trans (measure_union_le _ _)

end ScalarConductivity

end
end

end OAI
