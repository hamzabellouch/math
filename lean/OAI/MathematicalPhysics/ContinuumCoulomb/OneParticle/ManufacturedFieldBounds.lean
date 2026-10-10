import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarFieldBounds

namespace OAI

/-! Uniform derivatives through order six of the actual three-dimensional
manufactured field. Constants do not grow with the number of wells or slab width. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem linear_comp_six_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 6 f) {B D : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D) (hL : ‖L‖ ≤ D)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B) {k : ℕ} (hk : k ≤ 6) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B*D^6 := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ * ‖L‖^k := h
    _ ≤ B*D^k := mul_le_mul (hb k hk (L x))
      (pow_le_pow_left₀ (norm_nonneg L) hL k) (pow_nonneg (norm_nonneg L) k) hB
    _ ≤ B*D^6 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hk) hB

def wellPlanarProjection : Position →L[ℝ] PlanarPosition :=
  (ContinuousLinearMap.fst ℝ PlanarPosition ℝ).comp positionSplitCoordinates.toContinuousLinearMap

def wellVerticalProjection : Position →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ PlanarPosition ℝ).comp positionSplitCoordinates.toContinuousLinearMap

def wellPlanarDerivativeBound : ℝ :=
  (2*planarWellDerivativeConstant)*(max 1 ‖wellPlanarProjection‖)^6

private theorem cutoff_derivative_bound_exists : ∃ C : ℝ, 0 < C ∧
    ∀ k ≤ 6, ∀ z : ℝ, ‖iteratedFDeriv ℝ k (verticalCutoffBump : ℝ → ℝ) z‖ ≤ C := by
  obtain ⟨B,hB,hb⟩ := verticalCutoffBump.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) verticalCutoffBump.contDiff 6
  exact ⟨B+1, by linarith, fun k hk z => (hb k hk z).trans (by linarith)⟩

def wellCutoffDerivativeConstant : ℝ := Classical.choose cutoff_derivative_bound_exists

def wellCutoffDerivativeBound : ℝ :=
  wellCutoffDerivativeConstant*(max 1 (2*‖wellVerticalProjection‖))^6

def manufacturedFieldDerivativeConstant : ℝ :=
  64*wellCutoffDerivativeBound*wellPlanarDerivativeBound

theorem manufacturedFieldDerivativeConstant_positive : 0 < manufacturedFieldDerivativeConstant := by
  have hp := planarWellDerivativeConstant_positive
  have hc := (Classical.choose_spec cutoff_derivative_bound_exists).1
  unfold manufacturedFieldDerivativeConstant wellCutoffDerivativeBound
    wellPlanarDerivativeBound wellCutoffDerivativeConstant
  positivity

private theorem wellPlanar_bound_nonnegative : 0 ≤ wellPlanarDerivativeBound := by
  have hC := planarWellDerivativeConstant_positive.le
  unfold wellPlanarDerivativeBound
  positivity

private theorem wellCutoff_bound_nonnegative : 0 ≤ wellCutoffDerivativeBound := by
  have h := (Classical.choose_spec cutoff_derivative_bound_exists).1
  unfold wellCutoffDerivativeBound wellCutoffDerivativeConstant
  positivity

private theorem manufacturedField_planar_bound (freq : ℝ) {scale : ℝ} (hscale : 0 < scale)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun y : Position =>
      countertermWellSum freq scale u (positionSplitCoordinates y).1) x‖ ≤
        wellPlanarDerivativeBound := by
  have hC := planarWellDerivativeConstant_positive.le
  exact linear_comp_six_bound wellPlanarProjection (countertermWellSum freq scale u)
    ((countertermWellSum_C7 freq scale u).of_le (by norm_num))
    (by positivity) (le_max_left _ _) (le_max_right _ _)
    (fun j hj r => countertermWellSum_derivative_bound freq hscale u hsep hcounter hj r) hk x

private theorem manufacturedField_cutoff_bound {S : ℝ} (hS : 1 ≤ S)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (fun y : Position => slabWellCutoff S (positionSplitCoordinates y).2) x‖ ≤
      wellCutoffDerivativeBound := by
  let L : Position →L[ℝ] ℝ := (2/S) • wellVerticalProjection
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hscale : |2/S| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hS0).mpr (by linarith)
  have hL : ‖L‖ ≤ max 1 (2*‖wellVerticalProjection‖) := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hscale (norm_nonneg _)).trans (le_max_right _ _)
  exact linear_comp_six_bound L (verticalCutoffBump : ℝ → ℝ)
    (verticalCutoffBump.contDiff : ContDiff ℝ 6 (verticalCutoffBump : ℝ → ℝ))
    (Classical.choose_spec cutoff_derivative_bound_exists).1.le (le_max_left _ _) hL
    (Classical.choose_spec cutoff_derivative_bound_exists).2 hk x

/-- A fixed bound for all six derivatives, uniform over every separated
site family, every admissible counterterm and every slab width at least one. -/
theorem manufacturedWellField_derivative_bound (freq : ℝ) {scale S : ℝ}
    (hscale : 0 < scale) (hS : 1 ≤ S) {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (x : Position) :
    ‖iteratedFDeriv ℝ k (manufacturedWellField freq scale S u) x‖ ≤
      manufacturedFieldDerivativeConstant := by
  have hcut : ContDiff ℝ 6 (fun y : Position =>
      slabWellCutoff S (positionSplitCoordinates y).2) :=
    ((slabWellCutoff_smooth S).of_le (by simp)).comp
      positionSplitCoordinates.contDiff.snd
  have hplan : ContDiff ℝ 6 (fun y : Position =>
      countertermWellSum freq scale u (positionSplitCoordinates y).1) :=
    ((countertermWellSum_C7 freq scale u).of_le (show (6 : WithTop ℕ∞) ≤ 7 by norm_num)).comp
      positionSplitCoordinates.contDiff.fst
  have h := norm_iteratedFDeriv_mul_le hcut hplan x
    (show (k : WithTop ℕ∞) ≤ 6 by exact_mod_cast hk)
  change ‖iteratedFDeriv ℝ k (manufacturedWellField freq scale S u) x‖ ≤ _ at h
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (manufacturedField_cutoff_bound hS (hi'.trans hk) x)
          (Nat.cast_nonneg _))
        (manufacturedField_planar_bound freq hscale u hsep hcounter (Nat.sub_le k i |>.trans hk) x)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) wellCutoff_bound_nonnegative)
    _ = (2:ℝ)^k*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 64*wellCutoffDerivativeBound*wellPlanarDerivativeBound := by
      apply mul_le_mul_of_nonneg_right _ wellPlanar_bound_nonnegative
      apply mul_le_mul_of_nonneg_right _ wellCutoff_bound_nonnegative
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)
    _ = _ := rfl

end ContinuumCoulomb

end

end OAI
