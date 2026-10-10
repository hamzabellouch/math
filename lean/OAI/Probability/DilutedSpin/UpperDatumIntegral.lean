import OAI.Probability.DilutedSpin.UpperCountMean

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {R : Type} [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    {p N : ℕ} [NeZero N]

lemma integral_upperDatumLaw (M : Model p) (Q : FiniteLaw R)
    (g : UpperDatum p N R → ℝ) (hg : Measurable g) {B : ℝ}
    (hb : ∀ᵐ z ∂M.disorder.toMeasure,∀ i r,|g (z,i,r)|≤B) :
    (∫ a,g a ∂upperDatumLaw M Q) =
      ∫ z,(FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun i => (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r => g (z,i,r))) ∂M.disorder.toMeasure := by
  have hi : Integrable g (upperDatumLaw M Q) := by
    apply Integrable.of_bound hg.aestronglyMeasurable B
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb] with a ha
    exact ha a.2.1 a.2.2
  rw [upperDatumLaw,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hb] with z hz
  have hiz : Integrable (fun a : (Fin p → Fin N) × (Fin p → R) => g (z,a))
      (((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod
        ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    Integrable.of_bound (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
      (ae_of_all _ (fun a => hz a.1 a.2))
  rw [integral_prod _ hiz]
  rw [FiniteLaw.integral_asProbability]
  apply FiniteLaw.expect_congr
  intro i
  exact FiniteLaw.integral_asProbability _ _ _

end DilutedSpinGlass.PrescribedTree

end

end OAI
