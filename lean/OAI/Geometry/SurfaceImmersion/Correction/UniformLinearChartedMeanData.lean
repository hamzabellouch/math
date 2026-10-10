import OAI.Geometry.SurfaceImmersion.Atlas.UniformLinearPhaseBudgets
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetCompactRange
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanProfile
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedGeometricSolver

namespace OAI

/-! Actual charted mean data with one profile for a nearby family. The
positional jet is read on a fixed bounded original-coordinate domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

@[simp] lemma tensorOrder_emptyMetricPolynomial : tensorOrder emptyMetricPolynomial = 0 := by
  simp [tensorOrder,order,emptyMetricPolynomial]

/-- A bounded original-coordinate domain and explicit weighted jet profiles
give one charted-mean profile before the nearby map and both scales. -/
theorem uniform_linear_charted_mean_data_all_profiles
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set SmallModes.Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω)
    {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
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
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖*r ≤ Q (reference x) ∧
      Q (reference x) ≤ R - ‖Q‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H Pjet : ℕ → ℝ),
      (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : ChartedMeanProfile emptyMetricPolynomial,
      p.U = U₀ ∧ p.O = univ ∧ (∀ m, p.D m = 0) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
          (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart ξ hξ U hU).symm))) →
        (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ)^(j-2)) G) →
        ∀ τ : ℝ, ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ S τ s,
          ∃ d : ChartedMeanData c r ρ R reference,
            p.Fits d ∧ c.e = linearPhaseChart ξ hξ U hU ∧
              (∀ x, d.cutoff x = ψ x) ∧ d.form = fun _ => Q := by
  classical
  have hFc : ContDiff ℝ ∞ (F ∘ planeCoordinateIsometry.symm) :=
    hF.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨ρ₀,hρ₀,hall⟩ := uniform_linear_phase_budgets_all_profiles hFc hΩ hU hK hUK hKΩ
    hξ hImm hgood ψ.contDiff Q
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  obtain ⟨b,hb⟩ := hall H hH
  choose D hD hd using fun m => bounded_lowJet_prefix hU₀ K₀ hU₀K m
  obtain ⟨Qjet,hQjet,hQrange⟩ := bounded_lowJet_range hU₀ K₀ hU₀K (hPjet 0)
  have hφderiv (v : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose A hA ha using fun (m : ℕ) (v : Fin 2) => compact_local_weighted_bound
    hU₀ isOpen_univ K₀.isCompact hU₀K (subset_univ _) (hφderiv v).contDiffOn m
  let B : ℕ → ℝ := fun m => D m + Pjet m
  let Ph : ℕ → ℝ := fun m => ∑ v : Fin 2, A m v
  have hB (m : ℕ) : 1 ≤ B m := (hD m).trans (le_add_of_nonneg_right (hPjet m))
  have hPh (m : ℕ) : 0 ≤ Ph m :=
    Finset.sum_nonneg (fun v _ => zero_le_one.trans (hA m v))
  have hP : ∀ k l, (emptyMetricPolynomial k l).SmoothCoeffs univ :=
    fun _ l => Fin.elim0 l
  let e := linearPhaseChart ξ hξ U hU
  have he := linearPhaseChart_smooth ξ hξ U hU
  let p : ChartedMeanProfile emptyMetricPolynomial := {
    U := U₀
    O := univ
    Q := Qjet
    V := e.target
    openU := hU₀
    openO := isOpen_univ
    openV := e.open_target
    compact := hQjet
    subsetDomain := subset_univ _
    smoothP := hP
    C := fun m => b.mode (m+1)
    D := fun _ => 0
    J := b.chi
    inv := b.inv
    forms := b.forms
    psi := b.psi
    normal := b.normal
    B := B
    F := Ph
    nonnegC := fun m => zero_le_one.trans (b.mode_pos (m+1))
    oneLEJ := b.chi_pos
    oneLEInv := b.inv_pos
    oneLEForms := b.forms_pos
    oneLEPsi := b.psi_pos
    oneLENormal := b.normal_pos
    oneLEB := hB
    nonnegF := hPh
  }
  refine ⟨p,rfl,rfl,(fun _ => rfl),?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ
  have hGc : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨hdom,d₀,hprofiles⟩ := hb (G ∘ planeCoordinateIsometry.symm) hGc C₀
    hC₀ hCρ hclose s hs hs1 hjet
  have hmode : d₀.mode = b.mode := congrArg BudgetProfiles.mode hprofiles
  have hchi : d₀.chi = b.chi := congrArg BudgetProfiles.chi hprofiles
  have hinv : d₀.inv = b.inv := congrArg BudgetProfiles.inv hprofiles
  have hforms : d₀.forms = b.forms := congrArg BudgetProfiles.forms hprofiles
  have hpsi : d₀.psi = b.psi := congrArg BudgetProfiles.psi hprofiles
  have hnormal : d₀.normal = b.normal := congrArg BudgetProfiles.normal hprofiles
  have hmap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) :=
    hGc.comp he.2
  let c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ S τ s := {
    U := U₀
    O := univ
    openU := hU₀
    openO := isOpen_univ
    smoothP := hP
    mapsG := mapsTo_univ _ _
    supportU := hSU₀
    smoothPhase := hφ
    e := e
    smoothForward := he.1.contDiffOn
    smoothInverse := he.2.contDiffOn
    supportChart := hS
    phase := by
      intro x _
      rw [hphase]
      exact linearPhaseChart_phase ξ hξ U hU x
    smoothMap := hmap
    domain := hdom.complexDomain hmap
    C := fun m => b.mode (m+1)
    D := fun _ => 0
    J := b.chi
    nonnegC := fun m => zero_le_one.trans (b.mode_pos (m+1))
    nonnegD := fun _ => le_rfl
    oneLEJ := b.chi_pos
    coordinates := by
      intro m j hj hjm x hx
      have hxU : x ∈ U := by simpa only [e,linearPhaseChart_source] using hx
      simpa only [e,linearPhaseChart_source,hchi] using d₀.chi_bound m j hj hjm x hxU
    coefficients := by
      intro m
      simpa only [e,hmode,Function.comp_def] using d₀.mode_bound (m+1)
    polynomial := by
      intro m Z
      have hsS : (modeSupport S : Set SmallModes.Base) ⊆ e.source := hS
      have hz := phaseChartPolynomialOperator_zero isOpen_univ hU₀ emptyMetricPolynomial hP hG
        (mapsTo_univ _ _) S hSU₀ hφ τ e he.1.contDiffOn he.2.contDiffOn hsS
      rw [hz]
      simp
  }
  have hpull : ContDiffOn ℝ ∞ (pullbackField e) U := by
    have hh : pullbackField e = fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [hh]
    exact contDiffOn_const
  let loc : LocalBounds U e.target s r ρ R reference c.realMap ψ (fun _ => Q) e e.symm := {
    openU := hU
    smoothF := hmap
    domain := hdom
    smoothPsi := ψ.contDiff.contDiffOn
    smoothQ := contDiffOn_const
    smoothChi := he.1.contDiffOn
    smoothInv := he.2.contDiffOn
    chiInto := fun x hx => e.map_source hx
    invInto := fun x hx => e.map_target hx
    smoothPullback := hpull
    margin := fun x hx => hmargin _ (e.map_target hx)
  }
  have hjetRange : MapsTo (lowJet G) U₀ Qjet := by
    apply hQrange G hG
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref 0 2 (by omega)
  let d : ChartedMeanData c r ρ R reference := {
    cutoff := ψ
    form := fun _ => Q
    localBounds := loc
    budgets := d₀
    compactJets := Qjet
    compact := hQjet
    subsetDomain := subset_univ _
    mapsJets := hjetRange
    B := B
    F := Ph
    oneLEB := hB
    nonnegF := hPh
    jetsBound := by
      intro m
      simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
        hd m G hG s (Pjet m) hs hs1 (hPjet m) (hpref m)
    phaseBound := by
      intro m v
      have hv : A m v ≤ Ph m := Finset.single_le_sum
        (fun w _ => zero_le_one.trans (hA m w)) (Finset.mem_univ v)
      simpa only [tensorOrder_emptyMetricPolynomial,Nat.add_zero] using
        (ha m v s s.coe_nonneg hs1).mono_const hv
  }
  refine ⟨c,d,?_,rfl,(fun _ => rfl),rfl⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,hinv,hforms,hpsi,hnormal,rfl,rfl,rfl⟩

/-- A bounded original-coordinate domain and explicit weighted jet profiles
give one charted-mean profile before the nearby map and both scales. -/
theorem uniform_linear_charted_mean_data
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    {Ω U K : Set SmallModes.Base} (hΩ : IsOpen Ω) (hU : IsOpen U) (hK : IsCompact K)
    (hUK : U ⊆ K) (hKΩ : K ⊆ Ω)
    {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
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
    (hmargin : ∀ x ∈ U, ρ + ‖Q‖*r ≤ Q (reference x) ∧
      Q (reference x) ≤ R - ‖Q‖*r)
    (H Pjet : ℕ → ℝ) (hH : ∀ m, 1 ≤ H m) (hPjet : ∀ m, 0 ≤ Pjet m) :
    ∃ (ρ₀ : ℝ) (p : ChartedMeanProfile emptyMetricPolynomial),
      0 < ρ₀ ∧ p.U = U₀ ∧ p.O = univ ∧ (∀ m, p.D m = 0) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (H m)
          (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart ξ hξ U hU).symm))) →
        (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ)^(j-2)) G) →
        ∀ τ : ℝ, ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ S τ s,
          ∃ d : ChartedMeanData c r ρ R reference,
            p.Fits d ∧ c.e = linearPhaseChart ξ hξ U hU ∧
              (∀ x, d.cutoff x = ψ x) ∧ d.form = fun _ => Q := by
  obtain ⟨ρ₀,hρ₀,hall⟩ := uniform_linear_charted_mean_data_all_profiles hF hΩ hU hK hUK hKΩ
    hξ hImm hgood S hS hU₀ K₀ hU₀K hSU₀ hφ hphase ψ Q hmargin
  obtain ⟨p,hU,hO,hD,hdata⟩ := hall H Pjet hH hPjet
  exact ⟨ρ₀,p,hρ₀,hU,hO,hD,hdata⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
