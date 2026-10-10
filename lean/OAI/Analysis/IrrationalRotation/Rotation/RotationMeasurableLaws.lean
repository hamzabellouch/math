import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Rotation.RotationFieldRepresentation

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem measurableRepresentation_mul
    (θ : ℝ) (g h : Circle → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : Measurable g) (hh : Measurable h)
    (hgb : ∀ x, ‖g x‖ ≤ C) (hhb : ∀ x, ‖h x‖ ≤ D) :
    measurableRepresentation θ (fun x => g x * h x) (C * D) (mul_nonneg hC hD)
      (hg.mul hh) (fun x => by
        rw [norm_mul]
        exact mul_le_mul (hgb x) (hhb x) (norm_nonneg _) hC) =
      measurableRepresentation θ g C hC hg hgb *
        measurableRepresentation θ h D hD hh hhb := by
  apply WeightedShift.fieldDiagonal_mul_of_coeff_eq
  exact Eventually.of_forall fun _ _ => rfl

theorem measurableRepresentation_star
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    measurableRepresentation θ (fun x => star (g x)) C hC (continuous_star.measurable.comp hg)
      (fun x => by simpa using hb x) =
      star (measurableRepresentation θ g C hC hg hb) := by
  apply WeightedShift.fieldDiagonal_star_of_eq
  exact Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

theorem measurableRepresentation_eq_iff
    (θ : ℝ) (g h : Circle → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : Measurable g) (hh : Measurable h)
    (hgb : ∀ x, ‖g x‖ ≤ C) (hhb : ∀ x, ‖h x‖ ≤ D) :
    measurableRepresentation θ g C hC hg hgb =
      measurableRepresentation θ h D hD hh hhb ↔ g =ᵐ[circleMeasure] h := by
  constructor
  · intro heq
    have hv : vacuum =ᵐ[circleMeasure]
        fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 circleMeasure _
    filter_upwards [measurableRepresentation_coordinates_ae θ g C hC hg hgb vacuum,
      measurableRepresentation_coordinates_ae θ h D hD hh hhb vacuum, hv]
      with x hgx hhx hvx
    have he := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A vacuum x 0) heq
    rw [hgx 0, hhx 0, hvx] at he
    simpa [action] using he
  · exact measurableRepresentation_congr_ae θ

theorem vacuumFunctional_measurableRepresentation
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    vacuumFunctional (measurableRepresentation θ g C hC hg hb) =
      ∫ x, g x ∂circleMeasure := by
  change inner ℂ vacuum (measurableRepresentation θ g C hC hg hb vacuum) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : vacuum =ᵐ[circleMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 circleMeasure _
  filter_upwards [hv, measurableRepresentation_coordinates_ae θ g C hC hg hb vacuum]
    with x hvx hx
  rw [hvx, lp.inner_single_left]
  change inner ℂ (1 : ℂ) (measurableRepresentation θ g C hC hg hb vacuum x 0) = g x
  rw [hx 0, hvx]
  simp [action]

theorem lpNorm_le_norm_of_orbit_representation
    (θ : ℝ) {g : Circle → ℂ} (hg : MemLp g ∞ circleMeasure)
    (A : Hilbert →L[ℂ] Hilbert) (hA : A ∈ algebra θ)
    (hcoord : ∀ v : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      A v x k = g (action θ k x) * v x k) :
    lpNorm g ∞ circleMeasure ≤ ‖A‖ := by
  have hv : vacuum =ᵐ[circleMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 circleMeasure _
  have hn := L2Multiplication.ae_norm_apply_const_le A
    (algebra_commutes_multiplier θ hA) (lp.single 2 (0 : ℤ) (1 : ℂ))
  have hb : ∀ᵐ x ∂circleMeasure, ‖g x‖ ≤ ‖A‖ := by
    filter_upwards [hcoord vacuum, hv, hn] with x hx hvx hnx
    have hzero : A vacuum x 0 = g x := by
      simpa [action, hvx] using hx 0
    calc
      ‖g x‖ = ‖A vacuum x 0‖ := congrArg norm hzero.symm
      _ ≤ ‖A vacuum x‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖A‖ := by
        simpa only [vacuum, lp.norm_single (show (0 : ℝ≥0∞) < 2 by norm_num),
          norm_one, mul_one] using hnx
  have hb' : ∀ᵐ x ∂circleMeasure, ‖hg.toLp g x‖ ≤ ‖A‖ := by
    filter_upwards [hg.coeFn_toLp, hb] with x hx hbx
    rwa [hx]
  have hn' := Lp.norm_le_of_ae_bound (norm_nonneg A) hb'
  rw [Lp.norm_toLp, toReal_eLpNorm] at hn'
  simpa using hn'

theorem measurableRepresentation_norm
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    ‖measurableRepresentation θ g C hC hg hb‖ = lpNorm g ∞ circleMeasure := by
  have hgLp : MemLp g ∞ circleMeasure := memLp_top_of_bound hg.aestronglyMeasurable C
    (Eventually.of_forall hb)
  apply le_antisymm
  · obtain ⟨B, _, hBnorm, hBcoord⟩ := exists_mem_algebra_of_memLp_top θ hgLp
    have heq : measurableRepresentation θ g C hC hg hb = B := by
      apply operator_ext_of_coordinates
      intro v
      filter_upwards [measurableRepresentation_coordinates_ae θ g C hC hg hb v,
        hBcoord v] with x hx hy k
      exact (hx k).trans (hy k).symm
    rwa [heq]
  · exact lpNorm_le_norm_of_orbit_representation θ hgLp _
      (measurableRepresentation_mem_algebra θ g C hC hg hb)
      (measurableRepresentation_coordinates_ae θ g C hC hg hb)

theorem exists_unique_isometric_mem_algebra_of_memLp_top
    (θ : ℝ) {g : Circle → ℂ} (hg : MemLp g ∞ circleMeasure) :
    ∃! A : Hilbert →L[ℂ] Hilbert, A ∈ algebra θ ∧
      ‖A‖ = lpNorm g ∞ circleMeasure ∧
      ∀ v : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
        A v x k = g (action θ k x) * v x k := by
  obtain ⟨A, hA, hnorm, hcoord⟩ := exists_mem_algebra_of_memLp_top θ hg
  refine ⟨A, ⟨hA, le_antisymm hnorm
    (lpNorm_le_norm_of_orbit_representation θ hg A hA hcoord), hcoord⟩, ?_⟩
  intro B hB
  apply operator_ext_of_coordinates
  intro v
  filter_upwards [hB.2.2 v, hcoord v] with x hx hy k
  exact (hx k).trans (hy k).symm

end Invariant233.Rotation

end

end OAI
