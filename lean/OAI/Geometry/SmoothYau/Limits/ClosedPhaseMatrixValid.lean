import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RealPhaseLinear

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {X : Type*} [TopologicalSpace X]

lemma isClosed_phaseMatrixValid (H : X → RealForm PhaseSpace) (z : X → Fin 3 → ℂ)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (hz : Continuous z)
    (κ C : ℝ) :
    IsClosed {p : X × ComplexPhaseMatrix | PhaseMatrixValid (H p.1) (z p.1) κ C p.2} := by
  have hs : IsClosed {p : X × ComplexPhaseMatrix | p.2ᵀ = p.2} :=
    isClosed_eq (by fun_prop) continuous_snd
  have ha : IsClosed {p : X × ComplexPhaseMatrix | p.2 *ᵥ z p.1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hb : IsClosed {p : X × ComplexPhaseMatrix | ‖p.2‖ ≤ C} :=
    isClosed_le continuous_snd.norm continuous_const
  have hg : IsClosed {p : X × ComplexPhaseMatrix | ∀ v,
      4*κ*squareSum v ≤ realQuadratic (phaseFormMatrix (H p.1)-p.2.map Complex.re) v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold realQuadratic
    have hM : Continuous (fun p : X × ComplexPhaseMatrix => phaseFormMatrix (H p.1)) :=
      hH.comp continuous_fst
    fun_prop
  exact hs.inter (ha.inter (hb.inter hg))

def boundedPhaseSet (H : X → RealForm PhaseSpace) (B κ C : ℝ) :
    Set ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) :=
  {p | ‖p.1.2‖ ≤ B ∧ (∑ i, p.1.2 i * p.1.2 i = -1) ∧
    PhaseMatrixValid (H p.1.1) p.1.2 κ C p.2}

theorem boundedPhaseSet_isCompact [CompactSpace X]
    (H : X → RealForm PhaseSpace) (hH : Continuous (fun x => phaseFormMatrix (H x)))
    (B κ C : ℝ) : IsCompact (boundedPhaseSet H B κ C) := by
  have hz : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) | ‖p.1.2‖ ≤ B} :=
    isClosed_le (continuous_snd.comp continuous_fst).norm continuous_const
  have hn : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) |
      ∑ i, p.1.2 i * p.1.2 i = -1} := isClosed_eq (by fun_prop) continuous_const
  have hv := isClosed_phaseMatrixValid (fun p : X × (Fin 3 → ℂ) => H p.1)
    (fun p => p.2) (hH.comp continuous_fst) continuous_snd κ C
  have hclosed : IsClosed (boundedPhaseSet H B κ C) := hz.inter (hn.inter hv)
  apply ((isCompact_univ.prod (isCompact_closedBall (0 : Fin 3 → ℂ) B)).prod
    (isCompact_closedBall (0 : ComplexPhaseMatrix) C)).of_isClosed_subset hclosed
  intro p hp
  exact ⟨⟨mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1⟩,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.2.2.2.1⟩

end YauCounterexamples

end

end OAI
