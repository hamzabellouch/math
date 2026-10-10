import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LogarithmicBoxScale

namespace OAI

/-! # Logarithmic ambient length for the full root ideal -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- A fixed word basis measures the logarithm of every nilpotent-factor
element. The metric estimate is derived from the actual generator paths. -/
theorem exists_cartan_n_log_metric_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (β : M.Bases) (D : ℝ), 0 ≤ D ∧ ∀ v : cartanRootIdeal H,
      dist 1 (F.inclusionN (F.ExpN (F.N.equiv v))) ≤
        D * Real.log (2 + ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖) := by
  let s : Fin M.letterCount → ℝ := fun _ => 1
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (fun w => bracketWordExponent s w)
  obtain ⟨lo, hi, hlo, _, hcost⟩ := exists_positive_wordExponent_bounds s
    (fun _ => zero_lt_one) M.wordList
  obtain ⟨C, hC, hm⟩ := exists_cartan_n_chart_metric_bound T M F hExpG realize haarN dynkinN
    b₀ 1 zero_le_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨β, C * (1 / Real.log 2 + 1 / lo), by positivity, ?_⟩
  intro v
  let b := WordBasisSelections.basis M.letter M.wordList β
  let R := ‖b.equivFun v‖
  let r := Real.log (2 + R) / lo
  have hR : 0 ≤ R := norm_nonneg _
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg (by linarith)) hlo.le
  have hv := norm_box_at_logarithmic_scale_le_one b
    (fun j => bracketWordExponent s (β.val j)) hlo (fun j => (hcost (β.val j)).1) v
  have hdist := hm s (fun _ => le_rfl) β hβ r hr v hv
  have hlog : Real.log 2 ≤ Real.log (2 + R) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hone : 1 ≤ Real.log (2 + R) / Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by simpa using hlog)
  calc
    _ ≤ C * (1 + r) := hdist
    _ ≤ C * (Real.log (2 + R) / Real.log 2 + Real.log (2 + R) / lo) :=
      mul_le_mul_of_nonneg_left (by dsimp [r]; linarith [hone]) hC
    _ = _ := by dsimp [R, b]; ring

end PolycyclicRecognition

end

end OAI
