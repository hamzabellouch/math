import OAI.Analysis.LipschitzHilbert.Estimates.WitnessBinCount
import OAI.Analysis.LipschitzHilbert.Phase.AngularBinTransfer

namespace OAI

/-! The reference count controls every separated list of popular tops. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LipschitzHilbert.SlopeBox

/-- Extract compact witnesses, transfer them to the reference line, and
assign distinct angular bins. The reference count is fixed before the list. -/
theorem separated_witness_list_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : SlopeBox) (T : ι → SlopeBox) (u : ℝ × ℝ → ℝ)
    {L : ℝ≥0} (hu : LipschitzWith L u) (z : ℝ × ℝ)
    {M : ℕ} (hM : 0 < M) {A q P K θ c c0 B rho m : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hP : 0 < P) (hK : 0 ≤ K)
    (hAK : A + K ≤ P) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c)
    (hB : 1 < B) (hrho : 0 < rho) (hMB : (M : ℝ) = B ^ 2) (hm : B ^ 2 ≤ m)
    (hθ : θ ≤ q / (8 * A * P))
    (d : ι → ℝ) (E : ι → Set (ℝ × ℝ))
    (hE : ∀ i, MeasurableSet (E i))
    (hfinite : ∀ i, (volume.prod volume) (E i) ≠ ∞)
    (hbox : ∀ i, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hwitness : ∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i)
    (hd : ∀ i, 0 ≤ d i) (hwidth : ∀ i, (T i).width = m * (T i).length * d i)
    (hprecision : ∀ i, d i ≤ rho / B ^ 2)
    (hsmall : ∀ i, L * P * m * (T i).length ≤ 1 / 2)
    (hlower : ∀ i, rho ≤ |(T i).slope - R.slope|)
    (hupper : ∀ i, |(T i).slope - R.slope| ≤ B * rho)
    (hsep : PhaseCombinatorics.Separated (fun i => (T i).slope) rho)
    (hlength : ∀ i, (T i).length ≤ R.length)
    (hz : ∀ i, (T i).radius z ≤ K)
    (N : ℝ × ℝ → ℝ≥0∞) (hN : R.ReferencePopularCount u c P θ M N) :
    (Fintype.card ι : ℝ≥0∞) ≤ N ((R.referenceChart.symm z).2, z.1) := by
  classical
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hslope : ∀ i, (T i).slope ≠ R.slope := by
    intro i heq
    have h := hlower i
    rw [heq, sub_self, abs_zero] at h
    exact (not_le_of_gt hrho) h
  choose bin hbin using fun i => AngularBins.exists_baseBin R.slope hM (hslope i)
  have hinj := AngularBins.separated_annulus_bins_injective R.slope hM hB hrho hMB
    (fun i => (T i).slope) bin hsep hbin hupper
  choose F hFE hF hareaF hboxF using fun i =>
    (T i).exists_compact_popularity_witness (E i) (hE i) (hfinite i) hq (harea i) (hbox i)
  have htransfer : ∀ i, ∀ w ∈ F i,
      u (referencePoint R.slope z w) ∈ AngularBins.enlargedBin R.slope c (bin i) := by
    intro i w hw
    have hprecision' : d i ≤ |(T i).slope - R.slope| / B ^ 2 :=
      (hprecision i).trans (div_le_div_of_nonneg_right (hlower i) (sq_nonneg B))
    have herr := (T i).transferred_slope_precision R.slope z w u hu (hd i) hB0 hc0
      (hboxF i w hw) (hz i) hAK (hwidth i) hm hprecision' (hsmall i)
      (hwitness i w (hFE i hw))
    apply AngularBins.transferred_slope_mem_enlarged R.slope hM hc0 hc (hbin i)
    simpa only [hMB] using herr
  have hθ' : θ ≤ (q / 2) / (4 * A * P) := by
    convert hθ using 1
    ring
  simpa only [Finset.card_univ] using
    R.compact_witness_list_count T Finset.univ u hu.continuous.measurable z
      hA (by positivity : 0 ≤ q / 2) hP (by linarith : A ≤ P) hθ'
      F bin (fun _ _ _ _ h => hinj h) (fun i _ => hF i)
      (fun i _ => hboxF i) (fun i _ => hareaF i) (fun i _ => hlength i)
      (fun i _ => (hz i).trans (by linarith)) (fun i _ => htransfer i) N hN

end LipschitzHilbert.SlopeBox

end

end OAI
