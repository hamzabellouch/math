import OAI.Analysis.StructuralCrouzeix.SharedDensity

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def analyticRangeMaximum {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) : ℝ :=
  sSup ((fun z => ‖v z‖) '' closure D.domain)

lemma analyticRangeMaximum_bddAbove {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    BddAbove ((fun z => ‖v z‖) '' closure D.domain) := by
  exact (D.compact_closure.image_of_continuousOn hv.continuousOn.norm).bddAbove

theorem analyticRangeMaximum_attained {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    ∃ z ∈ closure D.domain, D.analyticRangeMaximum v = ‖v z‖ := by
  have hne : (closure D.domain).Nonempty := ⟨D.base, subset_closure D.base_mem⟩
  obtain ⟨z, hz, hmax⟩ := D.compact_closure.exists_isMaxOn hne hv.continuousOn.norm
  refine ⟨z, hz, ?_⟩
  change sSup ((fun w => ‖v w‖) '' closure D.domain) = ‖v z‖
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro r ⟨w, hw, rfl⟩
    exact hmax hw
  · exact le_csSup (D.analyticRangeMaximum_bddAbove v hv) ⟨z, hz, rfl⟩

lemma analyticRangeMaximum_nonneg {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    0 ≤ D.analyticRangeMaximum v := by
  obtain ⟨z, hz, he⟩ := D.analyticRangeMaximum_attained v hv
  rw [he]
  exact norm_nonneg _

lemma norm_le_analyticRangeMaximum {m : Type*} [Fintype m] [DecidableEq m]
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain))
    {z : ℂ} (hz : z ∈ closure D.domain) : ‖v z‖ ≤ D.analyticRangeMaximum v := by
  exact le_csSup (D.analyticRangeMaximum_bddAbove v hv) ⟨z, hz, rfl⟩

theorem common_positiveDensity_maximum_for_metric
    {n : ℕ} [Nonempty (Fin n)]
    (A H : Matrix (Fin n) (Fin n) ℂ) {τ : ℝ}
    (hW : numericalRange A ⊆ D.domain)
    (hf : MetricFeasible (matrixAnalyticEval A D.interior.toDisk) τ H) :
    ∃ Λ : C(UnitAddCircle, Matrix (Fin n) (Fin n) ℂ),
      (∀ t, 0 ≤ Λ t) ∧
      (∫ t, Λ t ∂AddCircle.haarAddCircle) = 1 ∧
      ∀ (m : ℕ), 0 < m →
      ∀ (v : ℂ → Matrix (Fin m) (Fin m) ℂ)
        (_ : AnalyticOnNhd ℂ v (closure D.domain)),
        completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
          ∫ t, Λ t ⊗ₖ v (D.G t.toCircle) ∂AddCircle.haarAddCircle ∧
        ‖completeAnalyticEval A v‖ ≤
          (‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖) * D.analyticRangeMaximum v := by
  obtain ⟨Λ, hpos, hmass, hrep⟩ := D.common_positiveDensity_for_metric A H hW hf
  refine ⟨Λ, hpos, hmass, ?_⟩
  intro m hm v hv
  obtain ⟨he, hb⟩ := hrep m v hv
  exact ⟨he, hb (D.analyticRangeMaximum v) (D.analyticRangeMaximum_nonneg v hv)
    (fun z hz => D.norm_le_analyticRangeMaximum v hv hz)⟩

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
