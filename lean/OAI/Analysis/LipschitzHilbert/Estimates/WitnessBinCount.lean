import OAI.Analysis.LipschitzHilbert.Fourier.ReferenceLineCount
import OAI.Analysis.LipschitzHilbert.Estimates.CompactWitness

namespace OAI

/-! Compact popularity witnesses give a simultaneous reference-line count. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

/-- Every compact witness supplies one of the popular bins counted by the
same reference count. The count was chosen independently of this finite list. -/
theorem compact_witness_list_count {ι : Type*} [DecidableEq ι]
    (R : SlopeBox) (T : ι → SlopeBox) (I : Finset ι)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (z : ℝ × ℝ)
    {A q P θ c : ℝ} {M : ℕ} (hA : 0 < A) (hq : 0 ≤ q)
    (hP : 0 < P) (hAP : A ≤ P) (hθ : θ ≤ q / (4 * A * P))
    (E : ι → Set (ℝ × ℝ)) (bin : ι → AngularBins.Bin M)
    (hbin : Set.InjOn bin I)
    (hcompact : ∀ i ∈ I, IsCompact (E i))
    (hbox : ∀ i ∈ I, ∀ w ∈ E i, (T i).radius w ≤ A)
    (harea : ∀ i ∈ I, q * (T i).length * (T i).width ≤ (volume.prod volume).real (E i))
    (hlength : ∀ i ∈ I, (T i).length ≤ R.length)
    (hz : ∀ i ∈ I, (T i).radius z ≤ P)
    (htransfer : ∀ i ∈ I, ∀ w ∈ E i,
      u (referencePoint R.slope z w) ∈ AngularBins.enlargedBin R.slope c (bin i))
    (N : ℝ × ℝ → ℝ≥0∞) (hN : R.ReferencePopularCount u c P θ M N) :
    (I.card : ℝ≥0∞) ≤ N ((R.referenceChart.symm z).2, z.1) := by
  classical
  have hpopular : ∀ b ∈ I.image bin, ∃ a d : ℝ,
      a < d ∧ d - a ≤ 2 * P * R.length ∧ z.1 ∈ Icc a d ∧
        θ * (d - a) ≤ ∫ x in Icc a d,
          AngularBins.binFunction R.slope c (R.referenceSlope u) b
            ((R.referenceChart.symm z).2, x) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    have hl := (T i).length_pos
    obtain ⟨hmem, havg⟩ := (T i).witness_centered_line_average (E i) (hcompact i hi)
      hA hq hP hAP (hbox i hi) (harea i hi) u hu R.slope z (hz i hi)
      (AngularBins.enlargedBin R.slope c (bin i))
      (AngularBins.measurableSet_enlargedBin _ _ _) (htransfer i hi)
    refine ⟨(T i).x - P * (T i).length, (T i).x + P * (T i).length,
      by nlinarith, ?_, hmem, ?_⟩
    · have h := mul_le_mul_of_nonneg_left (hlength i hi) (show 0 ≤ 2 * P by positivity)
      nlinarith
    · have hlen := (T i).witnessInterval_length hP.le
      have hlenpos : 0 < volume.real ((T i).witnessInterval P) := by
        rw [hlen]
        positivity
      have hint := (le_div_iff₀ hlenpos).mp (hθ.trans havg)
      rw [hlen] at hint
      have heq : (T i).x + P * (T i).length - ((T i).x - P * (T i).length) =
          2 * P * (T i).length := by ring
      rw [heq]
      simp_rw [R.referenceBinFunction_eq]
      exact hint
  have h := hN ((R.referenceChart.symm z).2, z.1) (I.image bin) hpopular
  rwa [Finset.card_image_of_injOn hbin] at h

/-- The same compact-witness count is bounded at every significant point
outside the fixed reference exceptional set. -/
theorem compact_witness_count_outside {R : SlopeBox} {N : ℝ × ℝ → ℝ≥0∞}
    {K lambda : ℝ} {z : ℝ × ℝ} {n : ℕ}
    (hcount : (n : ℝ≥0∞) ≤ N ((R.referenceChart.symm z).2, z.1))
    (hz : R.radius z ≤ K) (hout : z ∉ R.referenceException N K lambda)
    (hlambda : 0 ≤ lambda) : (n : ℝ) ≤ lambda := by
  have h := hcount.trans (R.count_le_outside_referenceException N hz hout)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlambda] using hr

end LipschitzHilbert.SlopeBox

end

end OAI
