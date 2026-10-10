import OAI.Analysis.LipschitzHilbert.Geometry.HorizontalStripCover
import OAI.Analysis.LipschitzHilbert.Estimates.L2IndicatorAlgebra
import OAI.Analysis.LipschitzHilbert.Estimates.ShortHorizontalLocalization
import OAI.Analysis.LipschitzHilbert.Estimates.LocalizedSubbandOperator

namespace OAI

/-! Exact patching of the local band theorem over disjoint horizontal
strips, with a uniform finite-overlap cost. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem bandL2Operator_horizontal_patch (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (d : ℝ) (hd : 0<d) (hRd : R≤d) (j : ℤ) (f : Lp ℂ 2 planeMeasure) :
    l2Indicator planeMeasure ((Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j) (measurableSet_Ico.preimage measurable_fst)
      (bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
        (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
        (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w f)=
    l2Indicator planeMeasure ((Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j) (measurableSet_Ico.preimage measurable_fst)
      (localizedSharpBandOperator epsilon R he hR field hfield p w (((j:ℝ)-1)*d) (((j:ℝ)+2)*d) f) := by
  let lo := ((j:ℝ)-1)*d
  let hi := ((j:ℝ)+2)*d
  let M := stripL2Cutoff lo hi
  let Q := l2Indicator planeMeasure ((Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j) (measurableSet_Ico.preimage measurable_fst)
  let T := shortL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield)
  have hsub : (Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j⊆(Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalEnlargement d j :=
    preimage_mono (horizontalCell_subset d hd j)
  have hQM (g : Lp ℂ 2 planeMeasure) : Q (M g)=Q g :=
    l2Indicator_nested planeMeasure _ _ _ _ hsub g
  have hloc := shortL2Operator_horizontal_localization (sharpTimeKernel epsilon R)
    (sharpTimeKernel_measurable epsilon R) (sharpTimeKernel_integrable epsilon R he hR)
    (fun z => field (planeCoordinates z)) (by simpa only [mul_one] using product_slope_lipschitz field hfield)
    (horizontalCell d j) (horizontalEnlargement d j) measurableSet_Ico measurableSet_Icc R
    (fun t ht => by
      unfold sharpTimeKernel
      rw [ite_eq_right (by intro h; linarith only [h.2,ht])])
    (fun x hx t ht => horizontalEnlargement_translate d hd j x hx t (ht.trans hRd))
    (verticalL2Projection p w f)
  change Q (T (M (verticalL2Projection p w f)))=Q (T (verticalL2Projection p w f)) at hloc
  change Q (T (verticalL2Projection p w f))=Q (M (T (verticalL2Projection p w (M f))))
  rw [hQM]
  rw [verticalL2Projection_strip p w hw lo hi f]
  exact hloc.symm

theorem bandL2Operator_global_from_local (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (d : ℝ) (hd : 0<d) (hRd : R≤d) (C : ℝ) (hC : 0≤C)
    (hlocal : ∀ j : ℤ,
      ‖localizedSharpBandOperator epsilon R he hR field hfield p w (((j:ℝ)-1)*d) (((j:ℝ)+2)*d)‖≤C)
    (f : Lp ℂ 2 planeMeasure) :
    ‖bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w f‖≤3*C*‖f‖ := by
  let Q := fun j : ℤ => (Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalCell d j
  let S := fun j : ℤ => (Prod.fst : (ℝ×ℝ) → ℝ) ⁻¹' horizontalEnlargement d j
  let T := bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w
  have hbound (j : ℤ) : ‖l2Indicator planeMeasure (Q j) (measurableSet_Ico.preimage measurable_fst) (T f)‖≤
      C*‖l2Indicator planeMeasure (S j) (measurableSet_Icc.preimage measurable_fst) f‖ := by
    let lo := ((j:ℝ)-1)*d
    let hi := ((j:ℝ)+2)*d
    let A := localizedSharpBandOperator epsilon R he hR field hfield p w lo hi
    let M := stripL2Cutoff lo hi
    have hid : A (M f)=A f := by
      change stripL2Cutoff lo hi (shortL2Operator _ _ _ _ _
        (verticalL2Projection p w (M (M f))))=stripL2Cutoff lo hi (shortL2Operator _ _ _ _ _
        (verticalL2Projection p w (M f)))
      rw [show M (M f)=M f from l2Indicator_idempotent planeMeasure _ _ f]
    have hA : ‖A f‖≤C*‖M f‖ := by
      rw [←hid]
      exact (A.le_opNorm (M f)).trans (mul_le_mul_of_nonneg_right (hlocal j) (norm_nonneg _))
    rw [show T f=bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w f from rfl]
    rw [bandL2Operator_horizontal_patch epsilon R he hR field hfield p w hw d hd hRd j f]
    exact (l2Indicator_norm_le planeMeasure _ _ (A f)).trans hA
  have hcover : ⋃ j : ℤ, Q j=univ := by
    ext z
    simp only [Q,mem_iUnion,mem_preimage,mem_univ,iff_true]
    exact ⟨⌊z.1/d⌋,horizontalCell_floor d hd z.1⟩
  have hdisjoint : Pairwise (fun j k => Disjoint (Q j) (Q k)) := fun j k hjk =>
    (horizontalCell_disjoint d hd hjk).preimage _
  have he := l2Indicator_partition_bound Q S (fun _ => measurableSet_Ico.preimage measurable_fst)
    (fun _ => measurableSet_Icc.preimage measurable_fst) hdisjoint hcover (C^2) 5 (sq_nonneg C) f (T f)
    (fun j => by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hbound j) 2
      simpa only [mul_pow] using h)
    (fun J z => horizontalEnlargement_overlap d hd J z.1)
  change ‖T f‖≤3*C*‖f‖
  have htarget : 0≤3*C*‖f‖ := by positivity
  nlinarith only [he,htarget,norm_nonneg (T f),sq_nonneg (C*‖f‖)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
