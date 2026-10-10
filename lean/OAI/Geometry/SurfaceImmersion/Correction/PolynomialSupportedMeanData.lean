import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLinearSolver
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLinearMeanData
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseCutoffBounds
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseDenominatorNeighborhood

namespace OAI

/-! Supported linear-phase mean data with numerical budgets chosen before
its phase domain. The domain is constructed from the actual denominator
bounds on the support. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

private lemma linear_phase_derivative (ξ x : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ) x = ξ := by
  unfold phaseDerivative
  rw [(phaseLinear ξ).hasFDerivAt.fderiv]
  ext <;> simp [phaseLinear_apply,SmallModes.dx,SmallModes.dy]

theorem polynomial_supported_linear_mean_data :
    ∃ (p p' : ℕ → ℕ) (C C' : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧ (∀ m, 1 ≤ C' m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
      {W : Set SmallModes.Base} (_hW : IsOpen W)
      (_hKW : (modeSupport K : Set SmallModes.Base) ⊆ W)
      {U₀ : Set Base} (_hU₀ : IsOpen U₀) (K₀ : Compacts Base)
      (_hU₀K : U₀ ⊆ K₀) (_hKU₀ : (K : Set Base) ⊆ U₀)
      {D : ℝ} (_hD : 0 < D),
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-ξ.2,ξ.1)‖⁻¹ ≤ D) →
      ∀ (Q : Tensor →L[ℝ] ℝ) {r ρ R : ℝ} {reference : SmallModes.Base → Tensor},
      (∀ x ∈ W, ρ+‖Q‖*r ≤ Q (reference x) ∧ Q (reference x) ≤ R-‖Q‖*r) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B P : ℕ → ℝ, (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
      (∀ m, 2*D ≤ B m ∧ ‖ξ‖ ≤ B m ∧
        ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧ ‖Q‖ ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j (B m/(s : ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∀ f : SupportedField (F := ℝ) (modeSupport K),
      (∀ m, WeightedBound univ s m (P m) f) →
      ∃ (U : Set SmallModes.Base) (hU : IsOpen U),
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG
          (phaseLinear ξ ∘ planeCoordinateIsometry) K τ s,
      ∃ d : ChartedMeanData c r ρ R reference,
        c.e = linearPhaseChart ξ hξ U hU ∧
        (∀ m, c.C m = C m*(B m)^(p m)) ∧ (∀ m, c.J m = 1+2*B m) ∧
        (∀ m, c.D m = 0) ∧
        (∀ x ∈ c.e.source, d.cutoff (c.e x) = f x) ∧ d.form = (fun _ => Q) ∧
        ∀ m, let b := linearMeanGeometryBudget p' C' B (fun j => 1+phaseCutoffBudget j (P j) (B j) 1) m;
          d.budgets.inv m ≤ b ∧ d.budgets.chi m ≤ b ∧ d.budgets.forms m ≤ b ∧
          d.budgets.pull m ≤ b ∧ d.budgets.psi m ≤ b ∧ d.budgets.normal m ≤ b ∧
          d.budgets.mode m ≤ b := by
  obtain ⟨p,C,hC,hsolver⟩ := polynomial_linear_unperturbed_solver
  obtain ⟨p',C',hC',hmean⟩ := polynomial_linear_charted_mean_data
  refine ⟨p,p',C,C',hC,hC',?_⟩
  intro G hG K ξ hξ W hW hKW U₀ hU₀ K₀ hU₀K hKU₀ D hD hImm hgood hgram hnormal
    Q r ρ R reference hmargin τ s hs hs1 B P hB hP hb hjets f hf
  have hGc := hG.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨V,hV,hKV,hVdata⟩ := phase_denominator_neighborhood hGc
    (phaseLinear ξ).contDiff (modeSupport K) hD hImm
    (by simpa only [linear_phase_derivative] using hgood) hgram
    (by simpa only [linear_phase_derivative] using hnormal)
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hKU : (modeSupport K : Set SmallModes.Base) ⊆ U := fun x hx => ⟨hKV hx,hKW hx⟩
  have hdata (x : SmallModes.Base) (hx : x ∈ U) :
      Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x) ∧
      Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ ∧
      ‖(NormalFrame.gramDet
        (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
        (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ 2*D ∧
      ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (-ξ.2,ξ.1)‖⁻¹ ≤ 2*D := by
    simpa only [linear_phase_derivative] using hVdata x hx.1
  have hphase : coordinatePhase (phaseLinear ξ ∘ planeCoordinateIsometry) = phaseLinear ξ := by
    funext x
    simp only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  have hsb (m : ℕ) := (hb m).1
  obtain ⟨c,hce,hcC,hcD,hcJ⟩ := hsolver hG K hU hξ
    ((phaseLinear ξ).contDiff.comp planeCoordinateIsometry.contDiff) hphase hKU
    (fun x hx => (hdata x hx).1) (fun x hx => (hdata x hx).2.1) τ s hs hs1 B hB
    (fun m => ⟨(hb m).2.1,(hb m).2.2.1,
      fun j hj => (hjets m j hj).restrict_open hU,
      fun x hx => (hdata x hx).2.2.1.trans (hsb m),
      fun x hx => (hdata x hx).2.2.2.trans (hsb m)⟩)
  let e := linearPhaseChart ξ hξ U hU
  let ψ : SupportedField (F := ℝ) c.chartCompact :=
    chartPush c.e c.smoothInverse (modeSupport K) c.supportChart f
  have hψeq : (ψ : SmallModes.Base → ℝ) =
      chartPush e (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn (modeSupport K) hKU f := by
    funext x
    simp only [ψ,chartPush_apply]
    rw [hce]
    rfl
  let P' := fun m => 1+phaseCutoffBudget m (P m) (B m) 1
  have hP' (m : ℕ) : 1 ≤ P' m := by
    apply le_add_of_nonneg_right
    have hPm := zero_le_one.trans (hP m)
    have hBm := zero_le_one.trans (hB m)
    dsimp [phaseCutoffBudget]
    positivity
  have hψ (m : ℕ) : WeightedBound c.e.target s m (P' m) ψ := by
    have hh := linear_phase_cutoff_bound hU hξ (modeSupport K) hKU hs hs1
      (zero_le_one.trans (hP m)) (hB m) (hb m).2.2.1
      (show |(1 : ℝ)⁻¹| ≤ 1 by norm_num) f (hf m)
    simp only [inv_one,one_smul] at hh
    have hh' : WeightedBound univ s m (phaseCutoffBudget m (P m) (B m) 1) ψ := by
      exact hh.congr (fun x _ => congrFun hψeq x)
    exact (hh'.mono_const (le_add_of_nonneg_left zero_le_one)).restrict_open c.e.open_target
  have hpref (m j : ℕ) (hj : j ≤ m+2) :
      WeightedBound U₀ 1 j (B m/(s : ℝ)^(j-2)) G := by
    have hh := weightedBound_comp_isometry planeCoordinateIsometry hGc (hjets m j (by omega))
    have he : (G ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = G := by
      funext x
      simp only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply]
    rw [he] at hh
    exact hh.restrict_open hU₀
  obtain ⟨d,hdψ,hdQ,hbd⟩ := hmean c hU hξ hce hU₀ K₀ hU₀K hKU₀ hs hs1 ψ Q
    (fun x hx => hmargin x hx.2) (fun x hx => (hdata x hx).1)
    (fun x hx => (hdata x hx).2.1) B P' B hB hP'
    (fun m => zero_le_one.trans (hB m))
    (fun m => ⟨(hb m).2.1,(hb m).2.2.1,(hb m).2.2.2,
      fun j hj => (hjets m j (by omega)).restrict_open hU,
      fun x hx => (hdata x hx).2.2.1.trans (hsb m),
      fun x hx => (hdata x hx).2.2.2.trans (hsb m)⟩) hψ hpref
  refine ⟨U,hU,c.onSourceDomain U₀ hU₀ hKU₀,d,hce,hcC,hcJ,fun _ => rfl,?_,hdQ,hbd⟩
  intro x hx
  rw [hdψ]
  have hx' : x ∈ e.source := by simpa only [PolynomialSolveData.onSourceDomain,hce,e] using hx
  change ψ (c.e x) = f x
  rw [hce,congrFun hψeq (e x)]
  exact chartPush_eval_source e (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn
    (modeSupport K) hKU f hx'

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
