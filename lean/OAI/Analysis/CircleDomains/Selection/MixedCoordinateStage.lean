import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateStage
import OAI.Analysis.CircleDomains.Sobolev.ModelRealEnergy
import OAI.Analysis.CircleDomains.Transfer.RealTransferStage

namespace OAI

/-! A mixed stage retains both its period data and a real stage with the
same map, inverse, metric, terminals and core. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MixedCoordinateStage {S : Type*} {n m : ℕ} {G U : Set Sphere}
    {π : Sphere → Sphere} {σ : S → Sphere} (C : Fin n → MaskedCoordinateData G U π σ)
    (ι : Fin m → Fin n) (r : Fin m → (ℝ × ℝ) → ℝ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε ρ : ℝ) (k₀ : ℕ)
    extends MaskedCoordinateStage C Flag O K₀ ε ρ k₀ where
  real : ModelRealSubfamily model ι r
  real_excess : ∀ j, Real.sqrt (∑' s : indices,
    max (terminalOscillation (terminals.H s) (real.functions j) -
      ((C (ι j)).upper s - (C (ι j)).lower s)) 0 ^ 2) < ε

variable {S : Type*} {n m : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {C : Fin n → MaskedCoordinateData G U π σ} {ι : Fin m → Fin n} {r : Fin m → (ℝ × ℝ) → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}

def MixedCoordinateStage.realStage
    (T : MixedCoordinateStage C ι r Flag O K₀ ε ρ k₀)
    (hG : IsOpen G) (hRM : ∀ j, (C (ι j)).mask = univ)
    (hr : ∀ j, ContDiffOn ℝ ∞ (r j) (realChartDomain G))
    (hr2 : ∀ j, MemLp (planarGradient (r j)) 2 (volume.restrict (realChartDomain G)))
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = (C (ι j)).physical x) :
    RealTransferStage G π σ r (fun j => (C (ι j)).lower) (fun j => (C (ι j)).upper)
      Flag O K₀ ε := by
  classical
  letI : Fintype T.indices := T.indices_finite.fintype
  refine {
    indices := T.indices
    finite_indices := T.indices_finite
    flags := T.flags
    terminals := T.terminals
    core := T.core
    core_closed := T.core_closed
    core_contains := T.core_contains
    core_source := T.core_source
    core_cocompact := T.core_cocompact
    core_model := T.core_model
    functions := T.real.functions
    extension := realChartDomain G ∪ ⋃ i, realJordanInterior (T.filling i)
    extension_open := (isOpen_realChartDomain hG).union
      (isOpen_iUnion fun i => (realJordanInterior_geometry (T.filling i)).1)
    extension_contains := T.real.extension_contains
    functions_smooth := T.real.filled.1
    retained := T.real.retained
    radius := T.model.radius
    radius_pos := T.model.radius_pos
    metric := T.model.metric
    metric_smooth := T.model.metric_smooth
    metric_pos := T.model.metric_pos
    metric_core := T.model.metric_core
    metric_far := T.model.metric_far
    source_energy := fun j E hE hEK => T.real.source_energy (isOpen_realChartDomain hG)
      (fun j => by simp only [hRM, physicalMask, preimage_univ, realChartDomain]) hr hrproj j hE hEK
    excess := T.real_excess
    oscillation := ?_
    domain := T.model.domain
    forward := T.model.forward
    inverse := T.model.inverse
    circle_domain := T.model.circle_domain
    equivalence := T.model.equivalence
    conformal_core := T.model.conformal_core
    principal := T.model.principal
    metric_conformal := T.real.metric_conformal
    integrable := ?_
    transported_smooth := fun j => (T.real.transported j).1 }
  · intro j
    rw [tsum_fintype]
    apply (CircleDomainRigidity.sqrt_sum_sq_le_band_add_excess
      (fun s : T.indices => terminalOscillation (T.terminals.H s) (T.real.functions j))
      (fun s : T.indices => (C (ι j)).upper s - (C (ι j)).lower s)
      (fun _ => Metric.diam_nonneg) (fun s => (C (ι j)).width_nonneg s)).trans_lt
    apply add_lt_add_of_le_of_lt
    · exact CircleDomainRigidity.finite_label_band_norm_le (fun s : T.indices => (s : S))
        Subtype.val_injective (fun s => (C (ι j)).upper s - (C (ι j)).lower s)
        (C (ι j)).width_summable
    · simpa only [tsum_fintype] using T.real_excess j
  · intro j
    exact integrableOn_gradientEnergy_with_cofinite_core
      ((isOpen_realChartDomain hG).union (isOpen_iUnion fun i =>
        (realJordanInterior_geometry (T.filling i)).1))
      (isClosed_real_completedRegion T.terminals.H) T.real.extension_contains
      T.core_closed T.core_cocompact T.core_source (T.real.filled.1 j)
      (integrable_gradientEnergy_spherical_of_memLp (hr2 j))
      (T.real.retained.mono fun _ hx => hx j) T.model.metric_smooth.continuous
      T.model.metric_pos T.model.metric_core

end CircleDomainRigidity.FiniteTransfer

end

end OAI
