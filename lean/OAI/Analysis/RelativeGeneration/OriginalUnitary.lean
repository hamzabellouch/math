import OAI.Analysis.FactorGeneration.NormalTrace
import OAI.Analysis.FactorGeneration.TraceTransport
import OAI.Analysis.FactorGeneration.UnitaryMetric
import OAI.Analysis.RelativeGeneration.Topology

namespace OAI

noncomputable section

/- Normalized trace-two topology on actual unitaries of the original factor.
   The wrapper avoids Mathlib's existing operator-norm topology on unitary S. -/
open scoped Topology
namespace Generator
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}

abbrev factorVonNeumann (hS : IsII1Factor S) : VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS.weaklyClosed

theorem IsII1Factor.factor_smul (hS : IsII1Factor S) :
    ∀ c : (factorVonNeumann hS).toStarSubalgebra,
      (∀ a : (factorVonNeumann hS).toStarSubalgebra, a*c=c*a) →
      ∃ z : ℂ,c=z • (1 : (factorVonNeumann hS).toStarSubalgebra) := by
  intro c hc
  obtain ⟨z,hz⟩ := hS.factor c hc
  exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩

theorem IsII1Factor.one_ne_zero (hS : IsII1Factor S) :
    (1 : (factorVonNeumann hS).toStarSubalgebra) ≠ 0 := by
  intro h
  exact hS.nonzero (congrArg Subtype.val h).symm

open Tracial
variable (S) (hS : IsII1Factor S)
local notation "hf" => hS.factor_smul
local notation "hu" => hS.one_ne_zero
local notation "K" => TraceFreeHilbert hf hS.diffuse hS.finite hu
local notation "R" => traceFreeHilbertClosure hf hS.diffuse hS.finite hu
local notation "σ" => traceFreeHilbertClosureTrace hf hS.diffuse hS.finite hu
local notation "e" => traceFreeHilbertEquiv hf hS.diffuse hS.finite hu
local notation "π" => traceFreeHilbertAction hf hS.diffuse hS.finite hu
local notation "Ω" => traceFreeHilbertVector hf hS.diffuse hS.finite hu

/- Supply the already constructed Hilbert instances explicitly: inference does
   not reconstruct the original von Neumann algebra from its subtype here. -/
local instance factorTracePreNormed :
    NormedAddCommGroup (TraceFreePreHilbert hf hS.diffuse hS.finite hu) :=
  traceFreePreHilbertNormedAddCommGroup hf hS.diffuse hS.finite hu
local instance factorTracePreInner :
    InnerProductSpace ℂ (TraceFreePreHilbert hf hS.diffuse hS.finite hu) :=
  traceFreePreHilbertInnerProductSpace hf hS.diffuse hS.finite hu

/-- The constructed faithful normalized trace on the original factor. -/
def normalizedFactorTrace : S →L[ℂ] ℂ := traceFreeTrace hf hS.diffuse hS.finite hu

/-- The trace constructed from the factor hypotheses is faithful, normal, and normalized. -/
theorem normalizedFactorTrace_isNormalizedTrace :
    RelativeGeneration.IsNormalizedTrace S (normalizedFactorTrace S hS) := by
  let : CompleteSpace (factorVonNeumann hS).toStarSubalgebra :=
    baseCompleteSpace (factorVonNeumann hS)
  let : CStarAlgebra (factorVonNeumann hS).toStarSubalgebra := {}
  let : PartialOrder (factorVonNeumann hS).toStarSubalgebra :=
    CStarAlgebra.spectralOrder _
  let : StarOrderedRing (factorVonNeumann hS).toStarSubalgebra :=
    CStarAlgebra.spectralOrderedRing _
  obtain ⟨_, normalized, positive, star_preserving, tracial⟩ :=
    traceFreeTrace_spec (M := factorVonNeumann hS) hf hS.diffuse hS.finite hu
  refine
    { normalized := normalized
      positive := fun element => positive (star element * element) (star_mul_self_nonneg element)
      star_preserving := star_preserving
      tracial := tracial
      faithful := ?_
      normal := traceFreeTrace_normal (M := factorVonNeumann hS) hf hS.diffuse hS.finite hu }
  intro element trace_zero
  apply (CStarRing.star_mul_self_eq_zero_iff element).mp
  exact (traceFreeTrace_faithful (M := factorVonNeumann hS) hf hS.diffuse hS.finite hu
    (star element * element) (star_mul_self_nonneg element)).mp trace_zero

/-- Same unitaries, with trace topology rather than the operator-norm topology. -/
structure FactorTraceUnitary (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_hS : IsII1Factor S) where
  toUnitary : unitary S

namespace FactorTraceUnitary

def algebra (u : FactorTraceUnitary S hS) : S := u.toUnitary

/-- Forgetting the metric wrapper preserves every genuine unitary of the original factor. -/
def unitaryEquiv : FactorTraceUnitary S hS ≃ unitary S where
  toFun := toUnitary
  invFun element := ⟨element⟩
  left_inv element := by cases element; rfl
  right_inv element := rfl

def represented (u : FactorTraceUnitary S hS) : TraceUnitary σ :=
  ⟨⟨e (u.algebra S hS),Unitary.map_mem e u.toUnitary.property⟩⟩

def representedEquiv : FactorTraceUnitary S hS ≃ TraceUnitary σ where
  toFun := represented S hS
  invFun v := ⟨⟨(e).symm (v.algebra σ),Unitary.map_mem (e).symm v.toUnitary.property⟩⟩
  left_inv u := by
    cases u
    simp only [represented,algebra,TraceUnitary.algebra,StarAlgEquiv.symm_apply_apply]
  right_inv v := by
    cases v
    simp only [represented,algebra,TraceUnitary.algebra,StarAlgEquiv.apply_symm_apply]

instance : MetricSpace (FactorTraceUnitary S hS) :=
  MetricSpace.induced (represented S hS) (representedEquiv S hS).injective inferInstance

def representedIsometryEquiv : FactorTraceUnitary S hS ≃ᵢ TraceUnitary σ :=
  { representedEquiv S hS with isometry_toFun := fun _ _ => rfl }

def representedHomeomorph : FactorTraceUnitary S hS ≃ₜ TraceUnitary σ :=
  (representedIsometryEquiv S hS).toHomeomorph

/-- The metric is literally the normalized trace two-norm of the difference. -/
theorem dist_eq_trace (u v : FactorTraceUnitary S hS) :
    dist u v = Real.sqrt ((normalizedFactorTrace S hS)
      (star (u.algebra S hS-v.algebra S hS)*(u.algebra S hS-v.algebra S hS))).re := by
  change dist (represented S hS u) (represented S hS v) = _
  rw [TraceUnitary.dist_eq]
  change ‖(π (u.algebra S hS)-π (v.algebra S hS)) Ω‖ = _
  rw [← map_sub,traceFreeHilbertAction_vector,LinearIsometry.norm_map]
  rw [normalizedFactorTrace,← traceFreeCopy_norm_sq hf hS.diffuse hS.finite hu,Real.sqrt_sq (norm_nonneg _)]

/-- The transported metric topology agrees with the trace-ball topology on genuine unitaries. -/
def traceHomeomorph :
    @Homeomorph (FactorTraceUnitary S hS) (unitary S) inferInstance
      (RelativeGeneration.traceTopology S (normalizedFactorTrace S hS)) :=
  RelativeGeneration.traceUnitaryHomeomorph S (normalizedFactorTrace S hS)
    (unitaryEquiv S hS) (fun left right => dist_eq_trace S hS left right)

/-- Filter convergence, and hence the topology, is exactly normalized trace-2 convergence. -/
theorem tendsto_iff {I : Type*} (l : Filter I) (u : I → FactorTraceUnitary S hS)
    (v : FactorTraceUnitary S hS) :
    Filter.Tendsto u l (𝓝 v) ↔ Filter.Tendsto (fun i => Real.sqrt
      ((normalizedFactorTrace S hS)
        (star ((u i).algebra S hS-v.algebra S hS)*((u i).algebra S hS-v.algebra S hS))).re)
      l (𝓝 0) := by
  simpa only [dist_eq_trace] using (tendsto_iff_dist_tendsto_zero (f := u) (a := v) (x := l))

end FactorTraceUnitary
end Generator

end

end OAI
