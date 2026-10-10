import OAI.Geometry.SurfaceImmersion.Correction.LinearMeanBudgetsFromBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanIteration

namespace OAI

/-! Construct every numerical mean budget in a selected linear phase
chart with explicit polynomial dependence on the geometry. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes PhaseGeometry WeightedEstimates

def linearMeanGeometryBudget (p : ℕ → ℕ) (A B P : ℕ → ℝ) (m : ℕ) : ℝ :=
  1+3*B m+16*(B m)^2+P m+A m*(B m)^(p m)

lemma linearMeanGeometryBudget_growth (p : ℕ → ℕ) (A : ℕ → ℝ)
    (B P : ℕ → ℝ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hB : ∀ m, HasPolynomialBound (B m)) (hP : ∀ m, HasPolynomialBound (P m)) (m : ℕ) :
    HasPolynomialBound (fun x => linearMeanGeometryBudget p A
      (fun r => B r x) (fun r => P r x) m) :=
  ((((polynomialBound_const zero_le_one).add
      ((polynomialBound_const (show (0 : ℝ) ≤ 3 by norm_num)).mul (hB m))).add
      ((polynomialBound_const (show (0 : ℝ) ≤ 16 by norm_num)).mul ((hB m).pow 2))).add (hP m)).add
    ((polynomialBound_const (hA m)).mul ((hB m).pow (p m)))

theorem polynomial_linear_mean_budgets :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {F : RField 4} {U : Set Base}, ContDiff ℝ ∞ F → ∀ hU : IsOpen U,
    ∀ {ξ : Base} (hξ : ξ ≠ 0) {s : ℝ}, 0 < s → s ≤ 1 →
    ∀ (ψ : Base → ℝ) (Q : Tensor →L[ℝ] ℝ) (B P : ℕ → ℝ),
      (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
      (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
        ‖Q‖ ≤ B m ∧
        (∀ j ≤ m+2, WeightedBound U 1 j (B m/s^(j-2)) F) ∧
        (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ U, ‖secondQuadratic (realSecondTensor F x) (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
      (∀ x ∈ U, Function.Injective (fderiv ℝ F x)) →
      (∀ x ∈ U, Good (realSecondTensor F x) ξ) →
      (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ) →
      ∃ d : Budgets U (linearPhaseChart ξ hξ U hU).target s
        (F ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
        (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm,
        ∀ m, d.inv m ≤ linearMeanGeometryBudget p A B P m ∧
          d.chi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.forms m ≤ linearMeanGeometryBudget p A B P m ∧
          d.pull m ≤ linearMeanGeometryBudget p A B P m ∧
          d.psi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.normal m ≤ linearMeanGeometryBudget p A B P m ∧
          d.mode m ≤ linearMeanGeometryBudget p A B P m := by
  classical
  choose p A hA hframe using fun m => polynomial_phase_frame_bound m
  refine ⟨p,A,hA,?_⟩
  intro F U hF hU ξ hξ s hs hs1 ψ Q B P hB hP hb hImm hgood hψ
  have hset : (phaseEquiv ξ hξ) '' U = (phaseEquiv ξ hξ).symm ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hy
    · intro hx
      exact ⟨(phaseEquiv ξ hξ).symm x,hx,(phaseEquiv ξ hξ).apply_symm_apply x⟩
  let C := fun m => A m*(B m)^(p m)
  have hC (m : ℕ) : 1 ≤ C m :=
    one_le_mul_of_one_le_of_one_le (hA m) (one_le_pow₀ (hB m))
  have hf (m : ℕ) := hframe m hF hU hξ hs hs1 (hB m)
    (hb m).1 (hb m).2.1 (hb m).2.2.2.1 hImm hgood (hb m).2.2.2.2.1 (hb m).2.2.2.2.2
  have hc : ∀ m, ReconstructionCoefficientBound
      (fun x => complexify ((F ∘ (linearPhaseChart ξ hξ U hU).symm) x))
      (linearPhaseChart ξ hξ U hU).target s m (C m) := by
    intro m
    simpa only [linearPhaseChart_target, linearPhaseChart_symm_apply, hset, Function.comp_def] using (hf m).1
  have hn : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (C m)
      (freeNormal (F ∘ (linearPhaseChart ξ hξ U hU).symm)) := by
    intro m
    simpa only [linearPhaseChart_target, linearPhaseChart_symm_apply, hset, Function.comp_def] using (hf m).2
  let d := linearMeanBudgetsOfBounds hU hξ s (F ∘ (linearPhaseChart ξ hξ U hU).symm)
    ψ Q C C P hC hC hP hc hn hψ
  refine ⟨d,?_⟩
  intro m
  have hB0 : 0 ≤ B m := zero_le_one.trans (hB m)
  have hP0 : 0 ≤ P m := zero_le_one.trans (hP m)
  have hC0 : 0 ≤ C m := zero_le_one.trans (hC m)
  have hξB := (hb m).1
  have hiB := (hb m).2.1
  have hQB := (hb m).2.2.1
  have hsq : ‖ξ‖^2 ≤ (B m)^2 := pow_le_pow_left₀ (norm_nonneg ξ) hξB 2
  change max 1 ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ _ ∧
    max 1 (2*‖ξ‖) ≤ _ ∧ max 1 ‖Q‖ ≤ _ ∧ max 1 (16*‖ξ‖^2) ≤ _ ∧
    P m ≤ _ ∧ C m ≤ _ ∧ C m ≤ _
  unfold linearMeanGeometryBudget
  change _ ≤ 1+3*B m+16*(B m)^2+P m+C m ∧ _
  refine ⟨max_le (by nlinarith [sq_nonneg (B m)]) (by nlinarith),
    max_le (by nlinarith [sq_nonneg (B m)]) (by nlinarith),
    max_le (by nlinarith [sq_nonneg (B m)]) (by nlinarith),
    max_le (by nlinarith [sq_nonneg (B m)]) (by nlinarith),by nlinarith [sq_nonneg (B m)],by nlinarith [sq_nonneg (B m)],by nlinarith [sq_nonneg (B m)]⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
