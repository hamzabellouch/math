import OAI.Probability.InvariantIsing.Arrays.PathSymbolAEUniqueness

namespace OAI

/-! Interval integrals and symbols depend only on the path almost everywhere.
The endpoints have zero Lebesgue measure. -/

noncomputable section
open MeasureTheory Set

namespace InvariantIsing

lemma intervalIntegral_congr_path_ae {a b : ℝ → ℝ} (he : a =ᵐ[pathMeasure] b)
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) (hst : s ≤ t) :
    (∫ u in s..t, a u) = ∫ u in s..t, b u := by
  have hev : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → a u = b u :=
    (ae_restrict_iff' measurableSet_Ioo).mp he
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hev, volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ)] with u hu hu0 hu1 humem
  rw [uIoc_of_le hst] at humem
  exact hu ⟨hs.trans_lt humem.1, lt_of_le_of_ne (humem.2.trans ht) hu1⟩

lemma pathSymbol_congr_ae {a b : ℝ → ℝ} (d : ℝ) (he : a =ᵐ[pathMeasure] b) :
    (fun s => pathSymbol d a s) =ᵐ[pathMeasure] fun s => pathSymbol d b s := by
  filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  unfold pathSymbol
  rw [hs, intervalIntegral_congr_path_ae he hsmem.1.le le_rfl hsmem.2.le]

end InvariantIsing

end

end OAI
