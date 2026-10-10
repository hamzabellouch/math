import OAI.Probability.FreeIsing.Ising.CopyObservables
import OAI.Probability.FreeIsing.Trees.InfiniteCanonicalPathResponse
import OAI.Probability.FreeIsing.Trees.ResponseRowEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity ResponseRows PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def pathCavity (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) (i : ℕ)
    (x : Paths d) : ℝ :=
  cavityObservable hb t (ConnectedHull.takeVertex v (i + 1))
    (ConnectedHull.takeVertex v i) x

def row (beta : ℝ) (t : ℝ≥0) (v : TreeVertex d) (x : Paths d) : ℝ :=
  infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => x i t)

theorem row_eq_product_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    row beta t v =ᵐ[observationLaw μ] fun x =>
      Real.tanh beta ^ v.1.length * pathProduct (Real.tanh beta)
        (Finset.range v.1.length) (pathCavity hb t v) x := by
  let f := infiniteGibbsResponse beta (ConnectedHull.root d) v
  let g := CavityFieldLimit.rootResponseProduct hb v
  have hm : MeasurableSet {y | f y = g y} := measurableSet_eq_fun
    (measurable_infiniteGibbsResponse beta _ _) (CavityFieldLimit.measurable_rootResponseProduct hb v)
  have hg : ∀ᵐ y ∂(μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (PlantedSymmetry.observation t),
      f y = g y :=
    (ae_map_iff (PlantedSymmetry.measurable_observation t).aemeasurable hm).mpr
      (hμ.infiniteGibbsRootResponse_eq_canonical_product hb t v)
  have heval : Measurable (fun x : Paths d => fun i => x i t) :=
    Measurable.of_eval (fun vertex => measurable_evaluation vertex t)
  have ho : ∀ᵐ x ∂observationLaw μ, f (fun i => x i t) = g (fun i => x i t) := by
    apply (ae_map_iff heval.aemeasurable hm).mp
    rw [(IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).map_eq]
    exact hg
  exact ho

theorem rows_eq_products_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (t : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ v : TreeVertex d,
      row beta t v q.2.1 = coefficient (Real.tanh beta)
        (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
        (fun w => Finset.range w.1.length) (fun w i q => pathCavity hb t w i q.2.1) v q ∧
      row beta t v q.2.2 = coefficient (Real.tanh beta)
        (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
        (fun w => Finset.range w.1.length) (fun w i q => pathCavity hb t w i q.2.2) v q := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  apply ae_all_iff.mpr
  intro v
  filter_upwards [hl.quasiMeasurePreserving.ae (row_eq_product_ae hμ hb t v),
    hr.quasiMeasurePreserving.ae (row_eq_product_ae hμ hb t v)] with q hql hqr
  exact ⟨hql, hqr⟩

def noiseEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) : ℝ :=
  pathNoiseEnergy (copies beta μ) (Real.tanh beta) (Finset.range v.1.length)
    (fun i q => pathCavity hb t v i q.2.1) (fun i q => pathCavity hb t v i q.2.2)

def linearEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (v : TreeVertex d) : ℝ :=
  pathLinearEnergy (copies beta μ) (Real.tanh beta) (Finset.range v.1.length)
    (fun i q => pathCavity hb t v i q.2.1)
    (IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t)

theorem integral_density_le_shell_energies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (t : ℝ≥0)
    {Q L : ℕ → ℝ} (hQ0 : ∀ n, 0 ≤ Q n) (hL0 : ∀ n, 0 ≤ L n)
    (hQ : ∀ n (v : TreeVertex d), v.1.length = n + 1 → noiseEnergy (μ := μ) hb t v ≤ Q n)
    (hL : ∀ n (v : TreeVertex d), v.1.length = n + 1 → linearEnergy (μ := μ) hb t v ≤ L n)
    (hQs : Summable (fun n => regularPathWeight d (Real.tanh beta) n * Q n))
    (hLs : Summable (fun n => regularPathWeight d (Real.tanh beta) n * L n))
    (hRs : Summable (fun n => regularPathWeight d (Real.tanh beta) n * Real.sqrt (Q n)))
    (hrows : ∀ᵐ q ∂copies beta μ,
      Summable (fun v => row beta t v q.2.1 ^ 2) ∧ Summable (fun v => row beta t v q.2.2 ^ 2)) :
    let U := IsingConditionalCopyBounds.fieldDifference beta (ConnectedHull.root d) t
    let D := DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) U
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.1))
      (fun q => Real.tanh (field beta (ConnectedHull.root d) t q.2.2))
    Integrable D (copies beta μ) ∧
      (∫ q, D q ∂copies beta μ) ≤ 2 * (∫ q, U q ^ 2 ∂copies beta μ) +
        ∑' n, regularPathWeight d (Real.tanh beta) n *
          (Q n + 2 * L n + 4 * Real.sqrt (2 * ∫ q, U q ^ 2 ∂copies beta μ) * Real.sqrt (Q n)) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  let X := fun v i (q : IsingConditionalCopyBounds.CopySpace d) => pathCavity hb t v i q.2.1
  let Y := fun v i (q : IsingConditionalCopyBounds.CopySpace d) => pathCavity hb t v i q.2.2
  let H := fun q : IsingConditionalCopyBounds.CopySpace d => field beta (ConnectedHull.root d) t q.2.1
  let H' := fun q : IsingConditionalCopyBounds.CopySpace d => field beta (ConnectedHull.root d) t q.2.2
  have hpath (v : TreeVertex d) (i : ℕ) : MemLp (pathCavity hb t v i) 2 (observationLaw μ) :=
    memLp_cavityObservable hμ hb t _ _
  have hXm (v : TreeVertex d) (i : ℕ) : Measurable (X v i) :=
    (measurable_cavityObservable hb t _ _).comp hl.measurable
  have hYm (v : TreeVertex d) (i : ℕ) : Measurable (Y v i) :=
    (measurable_cavityObservable hb t _ _).comp hr.measurable
  have hInt (v : TreeVertex d) (i : ℕ) : Integrable (fun q => (X v i q - Y v i q) ^ 2) (copies beta μ) :=
    ((hpath v i).comp_measurePreserving hl |>.sub ((hpath v i).comp_measurePreserving hr)).integrable_sq
  have hU : MemLp (fun q => H q - H' q) 2 (copies beta μ) :=
    ((memLp_field_at hμ hb t _).comp_measurePreserving hl).sub
      ((memLp_field_at hμ hb t _).comp_measurePreserving hr)
  have heq := rows_eq_products_ae hμ hb t
  have hrs : ∀ᵐ q ∂copies beta μ,
      Summable (fun v => (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
        (fun w => Finset.range w.1.length) X v q) ^ 2) ∧
      Summable (fun v => (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
        (fun w => Finset.range w.1.length) Y v q) ^ 2) := by
    filter_upwards [hrows, heq] with q hq he
    simpa only [X, Y, ← (he _).1, ← (he _).2] using hq
  have hmain := ResponseRows.integral_tree_density_le_shell_energies
    (fun v : TreeVertex d => Finset.range v.1.length) (fun v => Finset.card_range _)
    (Real.tanh_sq_lt_one beta).le (fun v i _ => hXm v i) (fun v i _ => hYm v i)
    (fun v i _ => hInt v i) ((measurable_field_at beta t _).comp hl.measurable)
    ((measurable_field_at beta t _).comp hr.measurable) hU hQ0 hL0 hQ hL hQs hLs hRs hrs
  have hd : DiscrepancyEnergy.density (fun v q => row beta t v q.2.1)
      (fun v q => row beta t v q.2.2) (fun q => H q - H' q)
      (fun q => Real.tanh (H q)) (fun q => Real.tanh (H' q)) =ᵐ[copies beta μ]
      DiscrepancyEnergy.density
        (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
          (fun w => Finset.range w.1.length) X)
        (coefficient (Real.tanh beta) (fun w : TreeVertex d => Real.tanh beta ^ w.1.length)
          (fun w => Finset.range w.1.length) Y)
        (fun q => H q - H' q) (fun q => Real.tanh (H q)) (fun q => Real.tanh (H' q)) := by
    filter_upwards [heq] with q hq
    simp only [DiscrepancyEnergy.density, X, Y, (hq _).1, (hq _).2]
  exact ⟨hmain.1.congr hd.symm, (integral_congr_ae hd).trans_le hmain.2⟩

end Problem367.IsingCopyResponseRowPaths

end

end OAI
