import OAI.Combinatorics.BalancedRyser.Profiles.AnalyticDetection
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileIdentifiability

namespace OAI

open MeasureTheory Set

namespace Balanced
open scoped _root_.Balanced

lemma power_series_equality_null {ι : Type*} (a b rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hb : Summable fun i ↦ |b i|)
    (hrate : ∀ i, 0 ≤ rate i) (hinj : Function.Injective rate)
    (hfinite : ∀ t : ℝ, {i | rate i ≤ t}.Finite) (hne : a ≠ b) :
    volume.restrict (Ioo (0 : ℝ) 1)
      {z | (∑' i, a i * z ^ rate i) = ∑' i, b i * z ^ rate i} = 0 := by
  apply analytic_equality_null (analytic_real_power_series a rate ha hrate)
    (analytic_real_power_series b rate hb hrate) isPreconnected_Ioo measurableSet_Ioo
  intro heq
  apply hne
  apply ProfileIdentifiability.laplaceSeries_injective a b rate ha hb hrate hinj hfinite
  intro s hs
  have hz : Real.exp (-s) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)⟩
  have h := heq hz
  change (∑' i, a i * (Real.exp (-s)) ^ rate i) =
    ∑' i, b i * (Real.exp (-s)) ^ rate i at h
  simpa only [power_series_at_exp_neg, ProfileIdentifiability.laplaceSeries] using h

end Balanced

end OAI
