import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.NativeHausdorffGrowth
import OAI.Analysis.RieszRectifiability.Flatness.ContractedAffinePatch

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem contracted_affine_patch_hausdorff_image_bound {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S.direction) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ)
    (b c : Ambient d) (hb : b ∈ S) (A : Set (Ambient d)) (r a R δ : ℝ)
    (hA : A ⊆ closedBall c r) (hcenter : dist c b ≤ a) (hrad : r + a ≤ R)
    (hheight : ∀ x ∈ A, infDist x (S : Set (Ambient d)) < δ)
    (hR : 0 < R) (hδ : 0 < δ) (hwidth : δ + κ * R ≤ R) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (T '' A) ≤
      ENNReal.ofReal (((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
        ((δ + κ * R) / R) * R ^ n) := by
  let ν := (μH[(n : ℝ)] : Measure (Ambient n))
  let C := (planeUnitHausdorffMeasure n).toReal
  have hg := native_hausdorff_global_upper_growth n
  have hreal := contracted_affine_patch_translated_real_measure_bound S hS T hT u hu
    κ hκ hTu ν C hg b c hb A r a R δ hA hcenter hrad hheight hR hδ hwidth
  have htranslate : ν ((fun x => T (x - b)) '' A) = ν (T '' A) := by
    have h := (IsometryEquiv.addRight (-T b)).isometry.hausdorffMeasure_image
      (Or.inl (show 0 ≤ (n : ℝ) by positivity)) (T '' A)
    rw [Set.image_image] at h
    change ν ((fun x => T x + -T b) '' A) = ν (T '' A) at h
    simpa only [map_sub, sub_eq_add_neg, map_add, map_neg] using! h
  have hball : (fun x => T (x - b)) '' A ⊆ ball 0 (2 * R) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxb : ‖x - b‖ ≤ R := by
      rw [← dist_eq_norm]
      exact (dist_triangle x c b).trans ((add_le_add (hA hx) hcenter).trans hrad)
    rw [mem_ball, dist_zero_right]
    exact (hT _).trans_lt (by linarith)
  have hfinite : ν ((fun x => T (x - b)) '' A) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono hball).trans (hg.2 0 (2 * R) (by positivity)))
  change (ν ((fun x => T (x - b)) '' A)).toReal ≤ _ at hreal
  rw [htranslate] at hreal hfinite
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

end

end RieszRectifiability

end OAI
