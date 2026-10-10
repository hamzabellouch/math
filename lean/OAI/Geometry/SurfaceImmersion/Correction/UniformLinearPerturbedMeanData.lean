import OAI.Geometry.SurfaceImmersion.Correction.PerturbedMeanTransfer
import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearChartedMeanData

namespace OAI

/-! Uniform perturbed mean data in a fixed linear phase chart.  Bounds for
transporting the polynomial may be chosen independently of the numerical
profiles retained by the geometric solver. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

/-- Independent fixed chart bounds control polynomial transport without
changing the geometric solver or the profile fitted by its mean data. -/
theorem uniform_perturbed_mean_transfer_with_chart_profiles {n : ℕ}
    (p₀ : ChartedMeanProfile emptyMetricPolynomial)
    (P : Fin 3 → Fin n → Expression) {O : Set LowJet} (hO : IsOpen O)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (hQO : p₀.Q ⊆ O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ p₀.U)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (J I : ℕ → ℝ) (hJ : ∀ m, 1 ≤ J m) (hI : ∀ m, 1 ≤ I m)
    (hebound : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hibound : ∀ m j, 1 ≤ j → j ≤ m + 1 → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m) :
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
    J I (fun m => p₀.oneLEB (m + tensorOrder P))
    (fun m => p₀.nonnegF (m + tensorOrder P)) hJ hI hebound hibound
  refine ⟨D,hD,?_⟩
  intro G hG φ τ ε s hτ hs hτs hs1 hε hε1 c₀ he₀ r ρ R reference d₀ hf
  subst e
  have hGQ : Set.MapsTo (lowJet G) p₀.U p₀.Q := by
    simpa only [hf.domain,hf.range] using d₀.mapsJets
  have hGb (m : ℕ) : WeightedBound p₀.U s (m + tensorOrder P)
      (p₀.B (m + tensorOrder P)) (lowJet G) := by
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero,hf.domain,hf.jets] using
      d₀.jetsBound (m + tensorOrder P)
  have hφb (m : ℕ) (v : Fin 2) : WeightedBound p₀.U s (m + tensorOrder P)
      (p₀.F (m + tensorOrder P)) (fun x => fderiv ℝ φ x (coordinateVector v)) := by
    simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero,hf.domain,hf.phase] using
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

/-- A fixed globally smooth polynomial and linear-phase geometry give one
perturbed mean profile before every nearby map and both scales. -/
theorem uniform_linear_perturbed_mean_data_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set SmallModes.Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω) {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
    (hImm : ∀ x ∈ Ω, Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ x ∈ Ω, Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) ξ)
    (S : Compacts Base) (hS : (modeSupport S : Set SmallModes.Base) ⊆ U)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : (S : Set Base) ⊆ U₀)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hphase : coordinatePhase φ = phaseLinear ξ)
    (ψ : SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart ξ hξ U hU) (modeSupport S) hS))
    (Q : Tensor →L[ℝ] ℝ) {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖ * r ≤ Q (reference x) ∧
      Q (reference x) ≤ R - ‖Q‖ * r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H Pjet : ℕ → ℝ),
      (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : ChartedMeanProfile P,
      p.U = U₀ ∧ p.O = univ ∧ (∀ m, 0 ≤ p.D m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
          (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart ξ hξ U hU).symm))) →
        (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ) ^ (j - 2)) G) →
        ∀ τ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
        ∃ c : PolynomialSolveData P ε G hG φ S τ s,
        ∃ d : ChartedMeanData c r ρ R reference,
          p.Fits d ∧ c.e = linearPhaseChart ξ hξ U hU ∧
          (∀ x, d.cutoff x = ψ x) ∧ d.form = fun _ => Q := by
  classical
  obtain ⟨ρ₀,hρ₀,hbase⟩ := uniform_linear_charted_mean_data_all_profiles
    hF hΩ hU hK hUK hKΩ hξ hImm hgood S hS hU₀ K₀ hU₀K hSU₀ hφ hphase ψ Q hmargin
  let e := linearPhaseChart ξ hξ U hU
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  have hsource : e.source ⊆ K := hUK
  let KV := (phaseEquiv ξ hξ) '' K
  have hKV : IsCompact KV := hK.image (phaseEquiv ξ hξ).continuous
  have htarget : e.target ⊆ KV := image_mono hUK
  choose J hJ hj using fun m => compact_local_weighted_bound e.open_source isOpen_univ
    hK hsource (subset_univ K) hsm.1.contDiffOn m
  choose I hI hi using fun m => compact_local_weighted_bound e.open_target isOpen_univ
    hKV htarget (subset_univ KV) hsm.2.contDiffOn (m + 1)
  have hJb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m)
      (x : SmallModes.Base) (hx : x ∈ e.source) :
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m := by
    simpa only [one_pow,one_mul] using hj m 1 zero_le_one le_rfl j hjm x hx
  have hIb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m + 1)
      (x : SmallModes.Base) (hx : x ∈ e.target) :
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m := by
    simpa only [one_pow,one_mul] using hi m 1 zero_le_one le_rfl j hjm x hx
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  obtain ⟨p₀,hpU,_hpO,_hpD,hdata⟩ := hbase H Pjet hH hPjet
  have hSp : (S : Set Base) ⊆ p₀.U := by simpa only [hpU] using hSU₀
  obtain ⟨D,hD,ht⟩ := uniform_perturbed_mean_transfer_with_chart_profiles
    p₀ P isOpen_univ hP (subset_univ _) S hSp e hsm.1.contDiffOn hsm.2.contDiffOn
    hS J I hJ hI hJb hIb
  let p := p₀.withPolynomial P isOpen_univ hP (subset_univ _) D
  refine ⟨p,hpU,rfl,hD,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ ε hτ hτs hε hε1
  obtain ⟨c₀,d₀,hfit,hce,hcut,hform⟩ := hdata G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ
  obtain ⟨c,d,hfit',hce',hcut',hform'⟩ :=
    ht G hG φ τ ε s hτ hs hτs hs1 hε hε1 c₀ hce d₀ hfit
  exact ⟨c,d,hfit',hce',(fun x => (hcut' x).trans (hcut x)),hform'.trans hform⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
