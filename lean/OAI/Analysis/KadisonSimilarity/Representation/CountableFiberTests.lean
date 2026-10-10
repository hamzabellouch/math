import OAI.Analysis.KadisonSimilarity.Representation.WeakOperatorCompactness
import Mathlib.MeasureTheory.Measure.AEMeasurable

namespace OAI

/-! # One conull set for the scalar fiber estimates

A countable family of contraction tests gives a common conull set. Weak
operator density then extends the bound to every contraction in each fiber.
This is the countability step in the central-decomposition argument; the
existence and density of the measurable sections remain explicit data.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMapWOT MeasureTheory Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A commutator bound extends from a set of operators to its weak closure. -/
theorem commutator_bound_of_weak_closure (Y T : H →L[ℂ] H)
    (S : Set (H →L[ℂ] H)) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ X ∈ S, ‖commutator Y X‖ ≤ c)
    (hT : ofCLM T ∈ closure (ofCLM '' S)) : ‖commutator Y T‖ ≤ c := by
  have hclosed : IsClosed {X : H →WOT[ℂ] H | ‖commutator Y (toCLM X)‖ ≤ c} := by
    exact (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_const_mul (ofCLM Y)).sub (continuous_mul_const (ofCLM Y)))
  apply closure_minimal _ hclosed hT
  rintro X ⟨X, hX, rfl⟩
  exact hbound X hX

/-- Weakly dense contraction tests control the full scalar commutator norm. -/
theorem scalarCommutatorNorm_le_of_weak_dense_tests
    (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (test : ℕ → H →L[ℂ] H)
    (hdense : ∀ X : H →L[ℂ] H, X ∈ P → ‖X‖ ≤ 1 →
      ofCLM X ∈ closure (Set.range fun n => ofCLM (test n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ n, ‖commutator Y (test n)‖ ≤ c) :
    scalarCommutatorNorm P Y ≤ c := by
  let : SeminormedAddCommGroup P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  let : NormedSpace ℂ P.toStarSubalgebra.toSubalgebra.toSubmodule := inferInstance
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hc
  intro x hx
  change ‖commutator Y (x : H →L[ℂ] H)‖ ≤ c
  apply commutator_bound_of_weak_closure Y x (Set.range test) hc
  · rintro _ ⟨n, rfl⟩
    exact hbound n
  · simpa only [Set.range_comp'] using hdense x x.property (le_of_eq hx)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ a, NormedAddCommGroup (K a)]
  [∀ a, InnerProductSpace ℂ (K a)] [∀ a, CompleteSpace (K a)]

/-- Countably many almost-everywhere test inequalities hold simultaneously.
Density on each remaining fiber gives its full scalar commutator bound. -/
theorem ae_scalarCommutatorNorm_le_of_countable_tests
    (P : ∀ a, VonNeumannAlgebra (K a))
    (Y : ∀ a, K a →L[ℂ] K a) (test : ∀ a, ℕ → K a →L[ℂ] K a)
    (hdense : ∀ᵐ a ∂μ, ∀ X : K a →L[ℂ] K a, X ∈ P a → ‖X‖ ≤ 1 →
      ofCLM X ∈ closure (Set.range fun n => ofCLM (test a n)))
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ n, ∀ᵐ a ∂μ, ‖commutator (Y a) (test a n)‖ ≤ c) :
    ∀ᵐ a ∂μ, scalarCommutatorNorm (P a) (Y a) ≤ c := by
  have hall : ∀ᵐ a ∂μ, ∀ n, ‖commutator (Y a) (test a n)‖ ≤ c :=
    eventually_countable_forall.mpr hbound
  filter_upwards [hdense, hall] with a ha hb
  exact scalarCommutatorNorm_le_of_weak_dense_tests (P a) (Y a) (test a) ha hc hb

end KadisonSimilarity

end

end OAI
