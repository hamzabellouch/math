import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedSolverTransfer
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanProfile

namespace OAI

/-! Transfer actual geometric mean data to a fixed polynomial perturbation.
The cutoff, form, local geometry and reconstruction budgets stay the same.
Only the polynomial profile and the required input-jet orders change. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

private lemma empty_tensorOrder : tensorOrder emptyMetricPolynomial = 0 := by
  simp [tensorOrder,order,emptyMetricPolynomial]

def ChartedMeanProfile.withPolynomial {n : ℕ}
    (p₀ : ChartedMeanProfile emptyMetricPolynomial)
    (P : Fin 3 → Fin n → Expression) {O : Set LowJet} (hO : IsOpen O)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (hQO : p₀.Q ⊆ O) (D : ℕ → ℝ) :
    ChartedMeanProfile P where
  U := p₀.U
  O := O
  Q := p₀.Q
  V := p₀.V
  openU := p₀.openU
  openO := hO
  openV := p₀.openV
  compact := p₀.compact
  subsetDomain := hQO
  smoothP := hP
  C := p₀.C
  D := D
  J := p₀.J
  inv := p₀.inv
  forms := p₀.forms
  psi := p₀.psi
  normal := p₀.normal
  B := fun m => p₀.B (m + tensorOrder P)
  F := fun m => p₀.F (m + tensorOrder P)
  nonnegC := p₀.nonnegC
  oneLEJ := p₀.oneLEJ
  oneLEInv := p₀.oneLEInv
  oneLEForms := p₀.oneLEForms
  oneLEPsi := p₀.oneLEPsi
  oneLENormal := p₀.oneLENormal
  oneLEB := fun m => p₀.oneLEB (m + tensorOrder P)
  nonnegF := fun m => p₀.nonnegF (m + tensorOrder P)

namespace ChartedMeanData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    {c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def withPolynomial {n : ℕ} (d₀ : ChartedMeanData c₀ r ρ R reference)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (hGO : Set.MapsTo (lowJet G) c₀.U O) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z)
    (hQO : d₀.compactJets ⊆ O) :
    ChartedMeanData (c₀.withPolynomial P ε hO hP hGO D hD hpoly) r ρ R reference where
  cutoff := d₀.cutoff
  form := d₀.form
  localBounds := d₀.localBounds
  budgets := d₀.budgets
  compactJets := d₀.compactJets
  compact := d₀.compact
  subsetDomain := hQO
  mapsJets := d₀.mapsJets
  B := fun m => d₀.B (m + tensorOrder P)
  F := fun m => d₀.F (m + tensorOrder P)
  oneLEB := fun m => d₀.oneLEB (m + tensorOrder P)
  nonnegF := fun m => d₀.nonnegF (m + tensorOrder P)
  jetsBound := by
    intro m
    change WeightedBound c₀.U s (m + tensorOrder P)
      (d₀.B (m + tensorOrder P)) (lowJet G)
    simpa only [empty_tensorOrder,Nat.add_zero] using d₀.jetsBound (m + tensorOrder P)
  phaseBound := by
    intro m v
    change WeightedBound c₀.U s (m + tensorOrder P)
      (d₀.F (m + tensorOrder P)) (fun x => fderiv ℝ φ x (coordinateVector v))
    simpa only [empty_tensorOrder,Nat.add_zero] using d₀.phaseBound (m + tensorOrder P) v

end ChartedMeanData

theorem ChartedMeanProfile.Fits.withPolynomial {n : ℕ}
    {p₀ : ChartedMeanProfile emptyMetricPolynomial}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    {c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    {d₀ : ChartedMeanData c₀ r ρ R reference} (hf : p₀.Fits d₀)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (hGO : Set.MapsTo (lowJet G) c₀.U O) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z)
    (hQO : p₀.Q ⊆ O) :
    (p₀.withPolynomial P hO hP hQO D).Fits
      (d₀.withPolynomial P ε hO hP hGO D hD hpoly
        (fun _ hx => hQO (by simpa only [hf.range] using hx))) := by
  refine ⟨hf.domain,hf.coefficients,rfl,hf.coordinates,hf.target,
    hf.inverse,hf.forms,hf.cutoff,hf.normal,?_,?_,hf.range⟩
  · funext m
    exact congrFun hf.jets (m + tensorOrder P)
  · funext m
    exact congrFun hf.phase (m + tensorOrder P)

/-- The perturbed mean profile is fixed before the map and scales.  The
existing mean datum supplies the same cutoff, form and geometric budgets. -/
theorem uniform_perturbed_mean_transfer {n : ℕ}
    (p₀ : ChartedMeanProfile emptyMetricPolynomial)
    (P : Fin 3 → Fin n → Expression) {O : Set LowJet} (hO : IsOpen O)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (hQO : p₀.Q ⊆ O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ p₀.U)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hebound : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ p₀.J m)
    (hibound : ∀ m j, 1 ≤ j → j ≤ m + 1 → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ p₀.inv (m + 1)) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (φ : Base → ℝ)
        (τ ε : ℝ) (s : ℝ≥0),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      ∀ (c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s),
      c₀.e = e → ∀ {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
        (d₀ : ChartedMeanData c₀ r ρ R reference), p₀.Fits d₀ →
      ∃ c : PolynomialSolveData P ε G hG φ K τ s,
      ∃ d : ChartedMeanData c r ρ R reference,
        (p₀.withPolynomial P hO hP hQO D).Fits d ∧ c.e = e ∧
        (∀ x, d.cutoff x = d₀.cutoff x) ∧ d.form = d₀.form := by
  obtain ⟨D,hD,hd⟩ := phaseChartPolynomialOperator_bounds
    p₀.openU hO p₀.compact hQO P hP K hKU e he hi hKe
    (fun m => p₀.B (m + tensorOrder P)) (fun m => p₀.F (m + tensorOrder P))
    p₀.J (fun m => p₀.inv (m + 1))
    (fun m => p₀.oneLEB (m + tensorOrder P))
    (fun m => p₀.nonnegF (m + tensorOrder P)) p₀.oneLEJ
    (fun m => p₀.oneLEInv (m + 1)) hebound hibound
  refine ⟨D,hD,?_⟩
  intro G hG φ τ ε s hτ hs hτs hs1 hε hε1 c₀ he₀ r ρ R reference d₀ hf
  subst e
  have hGQ : Set.MapsTo (lowJet G) p₀.U p₀.Q := by
    simpa only [hf.domain,hf.range] using d₀.mapsJets
  have hGb (m : ℕ) : WeightedBound p₀.U s (m + tensorOrder P)
      (p₀.B (m + tensorOrder P)) (lowJet G) := by
    simpa only [empty_tensorOrder,Nat.add_zero,hf.domain,hf.jets] using
      d₀.jetsBound (m + tensorOrder P)
  have hφb (m : ℕ) (v : Fin 2) : WeightedBound p₀.U s (m + tensorOrder P)
      (p₀.F (m + tensorOrder P)) (fun x => fderiv ℝ φ x (coordinateVector v)) := by
    simpa only [empty_tensorOrder,Nat.add_zero,hf.domain,hf.phase] using
      d₀.phaseBound (m + tensorOrder P) v
  have hGO : Set.MapsTo (lowJet G) c₀.U O := by
    intro x hx
    exact hQO (hGQ (by simpa only [hf.domain] using hx))
  have hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z := by
    simpa only [← hf.domain] using
      hd G φ hG c₀.smoothPhase hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb
  let c := c₀.withPolynomial P ε hO hP hGO D hD hpoly
  let d := d₀.withPolynomial P ε hO hP hGO D hD hpoly
    (fun _ hx => hQO (by simpa only [hf.range] using hx))
  exact ⟨c,d,hf.withPolynomial P ε hO hP hGO D hD hpoly hQO,rfl,
    (fun _ => rfl),rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
