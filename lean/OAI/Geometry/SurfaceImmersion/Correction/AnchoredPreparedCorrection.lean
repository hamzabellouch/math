import OAI.Geometry.SurfaceImmersion.Geometry.AnchoredInputStep
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCorrectionBudget
import OAI.Geometry.SurfaceImmersion.Correction.PreparedCorrection

namespace OAI

/-! Actual adaptive data with a polynomially controlled initial threshold. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
local instance anchoredPreparedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredPreparedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredPreparedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredPreparedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredPreparedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredPreparedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_prepared_correction (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ Base Wish : ℝ → ℝ, HasPolynomialBound Base → HasPolynomialBound Wish →
    ∃ Budget EpsInv : ℝ → ℝ, HasPolynomialBound Budget ∧ HasPolynomialBound EpsInv ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
      A.ShiftedBound 2 0 1 (Base z⁻¹) F →
      ∃ p : PreparedCorrection (⟨A,houter⟩ : CorrectionGeometry g F),
        p.a = a ∧ p.ρ = z^4/D ∧ p.budget = Budget z⁻¹ ∧
        Wish z⁻¹ < p.budget/4 ∧ (p.ε 0)⁻¹ ≤ EpsInv z⁻¹ := by
  classical
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hall⟩ := A.anchored_input_step g houter R c B b hc hB hb
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro Base Wish hBase hWish
  obtain ⟨A₀,hA₀,hsteps⟩ := hall Base hBase
  let Budget := fun x => 4*(A₀ x+Wish x+1)
  have hBudget : HasPolynomialBound Budget := (polynomialBound_const (by norm_num : (0:ℝ) ≤ 4)).mul
    ((hA₀.add hWish).add (polynomialBound_const zero_le_one))
  have hgap (x : ℝ) (hx : 1 ≤ x) : 1 ≤ Budget x-A₀ x := by
    have hA := hA₀.nonneg hx
    have hW := hWish.nonneg hx
    dsimp [Budget]; linarith
  have hBp (x : ℝ) (hx : 1 ≤ x) : 0 < Budget x := by
    have hA := hA₀.nonneg hx
    have hW := hWish.nonneg hx
    dsimp [Budget]; linarith
  have horders (k : ℕ) := hsteps Budget hBudget (correctionOrder k) (by unfold correctionOrder; omega)
  choose ε L N hε hL hN hεp hstep using horders
  let η := fun k x => ExactCorrection.correctionBudgetThreshold (A₀ x) (Budget x) a
    (N k (correctionInputOrder k) x) (L k x)
  have hpres (k : ℕ) (x : ℝ) (hx : 1 ≤ x) :=
    ExactCorrection.correctionBudgetThreshold_spec (A := A₀ x) (B := Budget x)
      (N := N k (correctionInputOrder k) x) (L := L k x) (by linarith [hgap x hx]) ha
  have hη (k : ℕ) : HasPolynomialBound (fun x => (η k x)⁻¹) :=
    ExactCorrection.correctionBudgetThreshold_inverse_polynomial A₀ Budget
      (N k (correctionInputOrder k)) (L k) a ha hBudget (hN k _) (hL k) hgap
  let EpsInv := fun x => (min (ε 0 x) (η 0 x))⁻¹
  have hEpsInv : HasPolynomialBound EpsInv := ExactCorrection.polynomial_inverse_min
    (hε 0) (hη 0) (fun x hx => (hεp 0 x hx).1) (fun x hx => (hpres 0 x hx).1)
  refine ⟨Budget,EpsInv,hBudget,hEpsInv,?_⟩
  intro z hz hzsmall F hF hFb hFm hbase
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  let p : PreparedCorrection (⟨A,houter⟩ : CorrectionGeometry g F) := {
    a := a
    ρ := z^4/D
    baseline := A₀ z⁻¹
    budget := Budget z⁻¹
    a_pos := ha
    ρ_pos := div_pos (pow_pos hz 4) (zero_lt_one.trans_le hD)
    baseline_nonneg := hA₀.nonneg hx
    budget_pos := hBp z⁻¹ hx
    baseline_lt := by
      have hw := hWish.nonneg hx
      dsimp [Budget]; linarith
    ε := fun k => min (ε k z⁻¹) (η k z⁻¹)
    L := fun k => L k z⁻¹
    N := fun k m => N k m z⁻¹
    ε_pos := fun k => lt_min (hεp k z⁻¹ hx).1 (hpres k z⁻¹ hx).1
    ε_le_one := fun k => (min_le_left _ _).trans (hεp k z⁻¹ hx).2
    L_nonneg := fun k => (hL k).nonneg hx
    N_nonneg := fun k m => (hN k m).nonneg hx
    preserve := by
      intro k t ht htε
      exact (hpres k z⁻¹ hx).2.2 t ht (htε.trans_le (min_le_right _ _))
    step := by
      intro k G hG t ht htε j hj hj' hin hnear hmetric
      exact hstep k z hz hzsmall F hF hFb hFm hbase G hG t ht
        (htε.trans_le (min_le_left _ _)) j hj hj' hin hnear hmetric
  }
  refine ⟨p,rfl,rfl,rfl,?_,le_rfl⟩
  change Wish z⁻¹ < Budget z⁻¹/4
  have hA := hA₀.nonneg hx
  dsimp [Budget]; linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
