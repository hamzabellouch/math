import OAI.Analysis.TriangularHilbert.SignedCenter

namespace OAI

universe uE uι

section
namespace TriangularHilbert
open MeasureTheory
noncomputable section

lemma intervalIntegrable_indicator {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L U a b : ℝ} (hf : IntervalIntegrable f volume L U) :
    IntervalIntegrable ((Set.Ico a b).indicator f) volume L U :=
  ⟨hf.1.indicator measurableSet_Ico,hf.2.indicator measurableSet_Ico⟩

lemma intervalIntegral_indicator_Ico {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {L U a b : ℝ} (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U) :
    (∫ s in L..U, (Set.Ico a b).indicator f s) = ∫ s in a..b, f s := by
  rw [intervalIntegral.integral_of_le (hLa.trans (hab.trans hbU)),
    ← integral_Icc_eq_integral_Ioc,integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  rw [Set.inter_eq_left.mpr (show Set.Ico a b ⊆ Set.Icc L U from fun s hs =>
    ⟨hLa.trans hs.1,hs.2.le.trans hbU⟩),integral_Ico_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

lemma intervalIntegrable_finsetSum {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ι → ℝ → E} (S : Finset ι) {a b : ℝ}
    (hf : ∀ i ∈ S, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun s => ∑ i ∈ S, f i s) volume a b := by
  have hh := IntervalIntegrable.sum S hf
  convert! hh using 1
  ext s
  simp
end
end TriangularHilbert
end

end OAI
