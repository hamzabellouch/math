import OAI.MeasureTheory.Falconer.Fourier.ComplexMaskJets

namespace OAI

/-! # Spatial scalar factors commute with the angular inverse

This is used pointwise in the two original endpoints: their spatial
multipliers do not depend on the angular variable.
-/

namespace Falconer
open scoped ContDiff

private theorem localInverseAmplitude_single_jet (m j : ℕ)
    (f : Space (m+3) → ℂ) (hf : ContDiff ℝ ∞ f) (e : Space (m+3)) :
    let T := (MaskJetExpansion.product :
      MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j
    localInverseAmplitude m f j e =
      ∑ a : T.index, (T.term a).coefficient e *
        ((T.term a).jet ()).value f ((T.term a).point e) := by
  intro T
  let B : Unit → Unit → Space (m+3) → ℂ := fun _ _ => f
  have hv := MaskJetExpansion.inverse_value m j MaskJetExpansion.product B
    (fun _ _ => hf) () e
  have hp : (MaskJetExpansion.product : MaskJetExpansion Unit (m+3) (Space (m+3))).value
      B () = f := by
    funext z
    simp only [MaskJetExpansion.product_value,Fintype.prod_unique]
    rfl
  rw [hp] at hv
  simpa only [MaskJetExpansion.value,MaskJetTerm.value,Fintype.prod_unique] using hv.symm

theorem localInverseAmplitude_const_mul (m j : ℕ) (c : ℂ)
    (f : Space (m+3) → ℂ) (hf : ContDiff ℝ ∞ f) (e : Space (m+3)) :
    localInverseAmplitude m (fun z => c*f z) j e = c*localInverseAmplitude m f j e := by
  rw [localInverseAmplitude_single_jet m j _ (contDiff_const.mul hf) e,
    localInverseAmplitude_single_jet m j f hf e,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [MaskJetIndex.value_const_mul _ c f hf]
  ring

theorem localInverseAmplitude_real_smul (m j : ℕ) (c : ℝ)
    (f : Space (m+3) → ℂ) (hf : ContDiff ℝ ∞ f) (e : Space (m+3)) :
    localInverseAmplitude m (fun z => c • f z) j e = c • localInverseAmplitude m f j e := by
  simpa only [Complex.real_smul] using localInverseAmplitude_const_mul m j (c : ℂ) f hf e

end Falconer

end OAI
