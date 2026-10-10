import OAI.Geometry.SurfaceImmersion.Atlas.GridSupportedCutoffs
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseCutoffBounds

namespace OAI

/-! Refined chart weights with their actual small-cell support, and
polynomial bounds after transport to a selected linear phase. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseGrid
open WeightedEstimates JetPolynomial PhaseGeometry

def gridCutoffCompact (K : Compacts Base) (h : ℝ) (k : Index) : Compacts Base :=
  ⟨(K : Set Base) ∩ tsupport (cutoff h k),
    K.isCompact.of_isClosed_subset (K.isCompact.isClosed.inter (isClosed_tsupport _))
      inter_subset_left⟩

def supportedCellCutoff {K : Compacts Base} (f : SupportedField (F := ℝ) K)
    {a : Finset Index} {h : ℝ} (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h)
    (k : Index) : SupportedField (F := ℝ) (gridCutoffCompact K h k) :=
  ContDiffMapSupportedIn.of_support_subset (supportedNormalizedCutoff f hh hK k).contDiff
    (fun x hx => by
      have ht : x ∈ tsupport (fun y => f y * normalizedCutoff a h k y) :=
        subset_tsupport _ hx
      exact ⟨f.tsupport_subset (tsupport_mul_subset_left ht),
        normalizedCutoff_tsupport a h k (tsupport_mul_subset_right ht)⟩)

@[simp] lemma supportedCellCutoff_apply {K : Compacts Base}
    (f : SupportedField (F := ℝ) K) {a : Finset Index} {h : ℝ}
    (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h) (k : Index) (x : Base) :
    supportedCellCutoff f hh hK k x = f x * normalizedCutoff a h k x := rfl

theorem grid_phase_cutoff_bounds :
    ∃ C : ℕ → ℝ, (∀ m, 1 ≤ C m) ∧
    ∀ {K : Compacts Base} (f : SupportedField (F := ℝ) K)
      {a : Finset Index} {z : ℝ} (hz : 0 < z), z ≤ 1 →
      ∀ hK : (K : Set Base) ⊆ coverRegion a (z^6),
      ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) →
      (∀ m, WeightedBound univ 1 m (P m) f) →
      ∀ (k : Index) {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
        (hKU : (gridCutoffCompact K (z^6) k : Set Base) ⊆ U)
        {s : ℝ≥0}, 0 < (s : ℝ) → s ≤ 1 →
      ∀ {J w : ℝ}, 1 ≤ J → ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ J →
        1 ≤ w → ∀ m,
      WeightedBound univ s m (C m*P m*J^m/z^(6*m))
        (w⁻¹ • chartPush (linearPhaseChart ξ hξ U hU)
          (linearPhaseChart_smooth ξ hξ U hU).2.contDiffOn
          (gridCutoffCompact K (z^6) k) hKU
          (supportedCellCutoff f (pow_pos hz 6) hK k)) := by
  obtain ⟨C,hC,hb⟩ := supported_normalized_cutoff_bounds
  refine ⟨fun m => (m.factorial : ℝ)*C m,fun m =>
    one_le_mul_of_one_le_of_one_le (by
      exact_mod_cast (show 1 ≤ m.factorial from Nat.factorial_pos m)) (hC m),?_⟩
  intro K f a z hz hz1 hK P hP hf k U hU ξ hξ hKU s hs hs1 J w hJ hi hw m
  have hb' : WeightedBound univ s m (C m*P m/z^(6*m))
      (supportedCellCutoff f (pow_pos hz 6) hK k) := by
    have hh := (hb f (pow_pos hz 6) (pow_le_one₀ hz.le hz1) hK P hP hf k m).shrink_scale
      s.coe_nonneg hs1
    have hh' : WeightedBound univ s m (C m*P m/z^(6*m))
        (supportedNormalizedCutoff f (pow_pos hz 6) hK k) := by
      simpa only [pow_mul] using hh
    exact hh'.congr (fun _ _ => rfl)
  have hw' : |w⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hw))]
    exact inv_le_one_of_one_le₀ hw
  have hp := linear_phase_cutoff_bound hU hξ (gridCutoffCompact K (z^6) k) hKU
    hs hs1 (div_nonneg (mul_nonneg (zero_le_one.trans (hC m)) (hP m))
      (pow_nonneg hz.le _)) hJ hi hw' (supportedCellCutoff f (pow_pos hz 6) hK k) hb'
  convert hp using 1
  unfold phaseCutoffBudget
  ring

end ClosedSurfaceR4.PhaseGrid

end

end OAI
