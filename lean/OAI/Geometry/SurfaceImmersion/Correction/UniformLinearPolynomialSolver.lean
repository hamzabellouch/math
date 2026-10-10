import OAI.Geometry.SurfaceImmersion.Atlas.UniformPhaseChartSolver
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseChart
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetCompactRange
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartBounds

namespace OAI

/-! Actual polynomial solvers for a fixed linear phase, with all profiles
chosen before the nearby map and scales.  No mean target or cutoff enters
the construction. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseGeometry

theorem uniform_linear_polynomial_solver_all_profiles {n : ℕ}
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
    (hphase : coordinatePhase φ = phaseLinear ξ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H Pjet : ℕ → ℝ),
      (∀ m, 1 ≤ H m) → (∀ m, 0 ≤ Pjet m) →
      ∃ (Qjet : Set LowJet) (C D J I : ℕ → ℝ), IsCompact Qjet ∧
      (∀ m, 0 ≤ C m) ∧ (∀ m, 0 ≤ D m) ∧
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ I m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
      0 ≤ C₀ → C₀ < ρ₀ →
      WeightedBound univ 1 2 C₀
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s (m + 1) (H (m + 1))
        (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
          (linearPhaseChart ξ hξ U hU).symm))) →
      (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
        (Pjet m / (s : ℝ) ^ (j - 2)) G) →
      ∀ τ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      MapsTo (lowJet G) U₀ Qjet ∧
      ∃ c : PolynomialSolveData P ε G hG φ S τ s,
        c.U = U₀ ∧ c.O = univ ∧ c.e = linearPhaseChart ξ hξ U hU ∧
        c.C = C ∧ c.D = D ∧ c.J = J ∧
        ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ c.e.target,
          ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I m := by
  classical
  let e := linearPhaseChart ξ hξ U hU
  have hsm := linearPhaseChart_smooth ξ hξ U hU
  let KV := (phaseEquiv ξ hξ) '' K
  have hKV : IsCompact KV := hK.image (phaseEquiv ξ hξ).continuous
  let g : GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ) := {
    chart := e
    phase := by
      intro x
      rw [hphase]
      exact linearPhaseChart_phase ξ hξ U hU x
    smooth := hsm.1
    smoothInverse := hsm.2
    sourceCompact := ⟨K,hK⟩
    targetCompact := ⟨KV,hKV⟩
    domain := (phaseEquiv ξ hξ) '' Ω
    sourceBound := hUK
    targetBound := image_mono hUK
    targetInside := image_mono hKΩ
    good := realModeDomain_phase (hF.comp planeCoordinateIsometry.symm.contDiff)
      hΩ hξ hImm hgood
  }
  obtain ⟨ρ₀,R,N,hρ₀,hR,_hN,hnear⟩ :=
    g.uniform_mode_bounds (hF.comp planeCoordinateIsometry.symm.contDiff)
  choose J hJ hj using fun m => compact_local_weighted_bound e.open_source isOpen_univ
    hK hUK (subset_univ K) hsm.1.contDiffOn m
  choose I hI hi using fun m => compact_local_weighted_bound e.open_target isOpen_univ
    hKV (image_mono hUK) (subset_univ KV) hsm.2.contDiffOn (m + 1)
  have hJb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m)
      (x : SmallModes.Base) (hx : x ∈ e.source) :
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m := by
    simpa only [one_pow,one_mul] using hj m 1 zero_le_one le_rfl j hjm x hx
  have hIb (m j : ℕ) (_ : 1 ≤ j) (hjm : j ≤ m + 1)
      (x : SmallModes.Base) (hx : x ∈ e.target) :
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m := by
    simpa only [one_pow,one_mul] using hi m 1 zero_le_one le_rfl j hjm x hx
  have hφd (v : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  choose Fp hFp hf using fun m v => compact_local_weighted_bound hU₀ isOpen_univ
    K₀.isCompact hU₀K (subset_univ _) (hφd v).contDiffOn (m + tensorOrder P)
  let Ph : ℕ → ℝ := fun m => ∑ v : Fin 2, Fp m v
  have hPh (m : ℕ) : 0 ≤ Ph m :=
    Finset.sum_nonneg (fun v _ => zero_le_one.trans (hFp m v))
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  choose B₀ hB₀ hb using fun m => bounded_lowJet_prefix hU₀ K₀ hU₀K (m + tensorOrder P)
  let B : ℕ → ℝ := fun m => B₀ m + Pjet (m + tensorOrder P)
  have hB (m : ℕ) : 1 ≤ B m :=
    (hB₀ m).trans (le_add_of_nonneg_right (hPjet _))
  obtain ⟨Qjet,hQjet,hQrange⟩ := bounded_lowJet_range hU₀ K₀ hU₀K (hPjet 0)
  obtain ⟨D,hD,hd⟩ := phaseChartPolynomialOperator_bounds hU₀ isOpen_univ hQjet
    (subset_univ _) P hP S hSU₀ e hsm.1.contDiffOn hsm.2.contDiffOn hS
    B Ph J I hB hPh hJ hI hJb hIb
  let C : ℕ → ℝ := fun m => ((m + 1).factorial : ℝ) * R (m + 1) * H (m + 1) ^ (m + 1)
  have hC (m : ℕ) : 0 ≤ C m := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (hR _)))
    (pow_nonneg (zero_le_one.trans (hH _)) _)
  refine ⟨Qjet,C,D,J,I,hQjet,hC,hD,hJ,hI,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ ε hτ hτs hε hε1
  have hGQ : MapsTo (lowJet G) U₀ Qjet := by
    apply hQrange G hG
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref 0 2 (by omega)
  have hGb (m : ℕ) : WeightedBound U₀ s (m + tensorOrder P) (B m) (lowJet G) :=
    hb m G hG s (Pjet (m + tensorOrder P)) hs hs1 (hPjet _) (hpref _)
  have hφb (m : ℕ) (v : Fin 2) : WeightedBound U₀ s (m + tensorOrder P) (Ph m)
      (fun x => fderiv ℝ φ x (coordinateVector v)) :=
    (hf m v s s.coe_nonneg hs1).mono_const (Finset.single_le_sum
      (fun w _ => zero_le_one.trans (hFp m w)) (Finset.mem_univ v))
  obtain ⟨hdom,hbounds⟩ := hnear (G ∘ planeCoordinateIsometry.symm)
    (hG.comp planeCoordinateIsometry.symm.contDiff) C₀ hC₀ hCρ hclose
  have hmap : ContDiff ℝ ∞ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) :=
    (hG.comp planeCoordinateIsometry.symm.contDiff).comp hsm.2
  let c : PolynomialSolveData P ε G hG φ S τ s := {
    U := U₀
    O := univ
    openU := hU₀
    openO := isOpen_univ
    smoothP := hP
    mapsG := mapsTo_univ _ _
    supportU := hSU₀
    smoothPhase := hφ
    e := e
    smoothForward := hsm.1.contDiffOn
    smoothInverse := hsm.2.contDiffOn
    supportChart := hS
    phase := by
      intro x _
      rw [hphase]
      exact linearPhaseChart_phase ξ hξ U hU x
    smoothMap := hmap
    domain := by simpa only [g,Function.comp_def] using hdom.complexDomain hmap
    C := C
    D := D
    J := J
    nonnegC := hC
    nonnegD := hD
    oneLEJ := hJ
    coordinates := hJb
    coefficients := by
      intro m
      simpa only [C,g,Function.comp_def] using
        (hbounds (m + 1) s (H (m + 1)) hs (hH _) (hjet m)).1
    polynomial := hd G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb
  }
  refine ⟨hGQ,c,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro m j hj hjm x hx
  exact hIb m j hj (hjm.trans (Nat.le_succ m)) x hx

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
