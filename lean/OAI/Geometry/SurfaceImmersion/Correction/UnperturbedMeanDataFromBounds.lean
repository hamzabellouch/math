import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverRestrictedDomain
import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearChartedMeanData

namespace OAI

/-! Complete actual mean data from the local geometry and its specified
budgets. Compact positional jets are obtained on a bounded source domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

theorem unperturbed_mean_data_from_bounds
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    {U : Set Base} (hU : IsOpen U) (K₀ : Compacts Base)
    (hUK : U ⊆ K₀) (hKU : (K : Set Base) ⊆ U)
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (loc : LocalBounds c.e.source c.e.target s r ρ R reference
      c.realMap ψ Q c.e c.e.symm)
    (b : Budgets c.e.source c.e.target s c.realMap ψ Q c.e c.e.symm)
    (Pjet : ℕ → ℝ) (hPjet : ∀ m, 0 ≤ Pjet m)
    (hpref : ∀ m j, j ≤ m+2 → WeightedBound U 1 j
      (Pjet m/(s : ℝ)^(j-2)) G) :
    ∃ d : ChartedMeanData (c.onSourceDomain U hU hKU) r ρ R reference,
      d.cutoff = ψ ∧ d.form = Q ∧
      d.budgets.inv = b.inv ∧ d.budgets.chi = b.chi ∧
      d.budgets.forms = b.forms ∧ d.budgets.pull = b.pull ∧
      d.budgets.psi = b.psi ∧ d.budgets.normal = b.normal ∧ d.budgets.mode = b.mode := by
  classical
  choose D hD hd using fun m => bounded_lowJet_prefix hU K₀ hUK m
  have hφ (v : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (c.smoothPhase.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose A hA ha using fun (m : ℕ) (v : Fin 2) => compact_local_weighted_bound
    hU isOpen_univ K₀.isCompact hUK (subset_univ _) (hφ v).contDiffOn m
  let B := fun m => D m+Pjet m
  let F := fun m => ∑ v : Fin 2, A m v
  refine ⟨{
    cutoff := ψ
    form := Q
    localBounds := loc
    budgets := b
    compactJets := lowJet G '' (K₀ : Set Base)
    compact := K₀.isCompact.image (lowJet_smooth hG).continuous
    subsetDomain := subset_univ _
    mapsJets := fun x hx => ⟨x,hUK hx,rfl⟩
    B := B
    F := F
    oneLEB := fun m => (hD m).trans (le_add_of_nonneg_right (hPjet m))
    nonnegF := fun m => Finset.sum_nonneg (fun v _ => zero_le_one.trans (hA m v))
    jetsBound := ?_
    phaseBound := ?_
  },rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro m
    change WeightedBound U s (m+tensorOrder emptyMetricPolynomial) (B m) (lowJet G)
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
      hd m G hG s (Pjet m) hs hs1 (hPjet m) (hpref m)
  · intro m v
    change WeightedBound U s (m+tensorOrder emptyMetricPolynomial) (F m)
      (fun x => fderiv ℝ φ x (coordinateVector v))
    have hv : A m v ≤ F m := Finset.single_le_sum
      (fun w _ => zero_le_one.trans (hA m w)) (Finset.mem_univ v)
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
      (ha m v s s.coe_nonneg hs1).mono_const hv

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
