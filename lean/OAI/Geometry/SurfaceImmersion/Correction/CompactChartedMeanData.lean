import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalBounds
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanData

namespace OAI

/-! Complete the actual charted mean data from compact geometric data;
the remaining high-jet and phase profiles follow from smoothness. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem compact_charted_mean_data {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {K : Compacts Base} (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (hlocal : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)
    (budgets : Budgets c.e.source c.e.target s c.realMap ψ Q c.e c.e.symm)
    {K₀ : Set Base} (hK₀ : IsCompact K₀) (hUK : c.U ⊆ K₀) (hs1 : s ≤ 1)
    {J : Set LowJet} (hJ : IsCompact J) (hJO : J ⊆ c.O) (hGJ : MapsTo (lowJet G) c.U J) :
    ∃ d : ChartedMeanData c r ρ R reference, d.cutoff = ψ ∧ d.form = Q := by
  choose B hB hb using fun m => compact_local_weighted_bound c.openU isOpen_univ hK₀ hUK
    (subset_univ K₀) (lowJet_smooth hG).contDiffOn (m+tensorOrder P)
  have hφ : ContDiff ℝ ∞ (fun x => fun v : Fin 2 => fderiv ℝ φ x (coordinateVector v)) := by
    apply contDiff_pi.mpr
    intro v
    exact (c.smoothPhase.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose F hF hf using fun m => compact_local_weighted_bound c.openU isOpen_univ hK₀ hUK
    (subset_univ K₀) hφ.contDiffOn (m+tensorOrder P)
  refine ⟨{
    cutoff := ψ
    form := Q
    localBounds := hlocal
    budgets := budgets
    compactJets := J
    compact := hJ
    subsetDomain := hJO
    mapsJets := hGJ
    B := B
    F := F
    oneLEB := hB
    nonnegF := fun m => zero_le_one.trans (hF m)
    jetsBound := fun m => hb m s s.coe_nonneg hs1
    phaseBound := ?_
  },rfl,rfl⟩
  intro m v
  exact (hf m s s.coe_nonneg hs1).component c.openU.uniqueDiffOn s.coe_nonneg
    (zero_le_one.trans (hF m)) hφ.contDiffOn v

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
