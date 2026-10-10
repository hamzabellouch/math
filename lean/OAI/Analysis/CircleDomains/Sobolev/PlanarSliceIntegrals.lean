import OAI.Analysis.CircleDomains.Sobolev.CompactPhysicalFiberCoarea
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! Rectangles with arbitrary compact transverse sets, and their exact
slice integrals. Coordinates are Euclidean physical coordinates. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

 def planarSliceBox (I J : Set ℝ) : Set ℂ :=
  {z | z.re ∈ I ∧ z.im ∈ J}

 theorem planarSliceBox_eq_image (I J : Set ℝ) :
    planarSliceBox I J = Complex.measurableEquivRealProd.symm '' (I ×ˢ J) := by
  ext z
  constructor
  · intro hz
    exact ⟨(z.re, z.im), hz, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact hp

 theorem isCompact_planarSliceBox {I J : Set ℝ} (hI : IsCompact I) (hJ : IsCompact J) :
    IsCompact (planarSliceBox I J) := by
  rw [planarSliceBox_eq_image]
  exact (hI.prod hJ).image Complex.equivRealProdCLM.symm.continuous

 theorem planarSliceBox_mono {I I' J J' : Set ℝ} (hI : I ⊆ I') (hJ : J ⊆ J') :
    planarSliceBox I J ⊆ planarSliceBox I' J' := fun _ hz => ⟨hI hz.1, hJ hz.2⟩

 theorem lintegral_planarSliceBox {I J : Set ℝ} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in planarSliceBox I J, g z) =
      ∫⁻ y in J, ∫⁻ x in I, g ⟨x, y⟩ := by
  let e := Complex.measurableEquivRealProd.symm
  have hm : MeasurableSet (planarSliceBox I J) :=
    (hI.preimage Complex.continuous_re.measurable).inter
      (hJ.preimage Complex.continuous_im.measurable)
  rw [← lintegral_indicator hm,
    ← Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  change (∫⁻ p : ℝ × ℝ, (planarSliceBox I J).indicator g (e p)) = _
  have heq : (fun p : ℝ × ℝ => (planarSliceBox I J).indicator g (e p)) =
      (I ×ˢ J).indicator (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) := by
    funext p
    simp only [e, Complex.measurableEquivRealProd_symm_apply, Set.indicator_apply,
      planarSliceBox, mem_ofPred_eq, mem_prod]
  rw [heq, Measure.volume_eq_prod, lintegral_indicator (hI.prod hJ)]
  apply setLIntegral_prod_symm
  exact (hg.comp (show Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) from
    Complex.equivRealProdCLM.symm.continuous).measurable).aemeasurable

 theorem planarSliceBox_fiber_restrict (I J B : Set ℝ) (y : ℝ) :
    planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y} =
      if y ∈ B then planarSliceBox I J ∩ Complex.im ⁻¹' {y} else ∅ := by
  ext z
  by_cases hy : y ∈ B <;> simp only [hy, ite_true, ite_false]
  · simp only [planarSliceBox, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    aesop
  · simp only [planarSliceBox, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
      mem_empty_iff_false]
    aesop

variable {X : Type*} [MetricSpace X]

 theorem pathImageCount_planarSliceBox_restrict (π : ℂ → X) (γ : C(PathTime, X))
    (I J B : Set ℝ) (y : ℝ) :
    pathImageCount (π '' (planarSliceBox I (J ∩ B) ∩ Complex.im ⁻¹' {y})) γ =
      B.indicator (fun y => pathImageCount (π '' (planarSliceBox I J ∩ Complex.im ⁻¹' {y})) γ) y := by
  rw [planarSliceBox_fiber_restrict]
  by_cases hy : y ∈ B <;> simp [hy, pathImageCount]

end CircleDomainRigidity

end

end OAI
