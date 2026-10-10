import OAI.Analysis.LipschitzHilbert.Fourier.WitnessProjection

namespace OAI

/-! The compact transferred witness gives the required popular line bin. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

def linePoint (s : ℝ) (z : ℝ × ℝ) (x : ℝ) : ℝ × ℝ :=
  (x, z.2 + s * (x - z.1))

def lineBinSet (u : ℝ × ℝ → ℝ) (s : ℝ) (z : ℝ × ℝ) (bin : Set ℝ) : Set ℝ :=
  {x | u (linePoint s z x) ∈ bin}

theorem measurableSet_lineBinSet (u : ℝ × ℝ → ℝ) (hu : Measurable u)
    (s : ℝ) (z : ℝ × ℝ) (bin : Set ℝ) (hbin : MeasurableSet bin) :
    MeasurableSet (lineBinSet u s z bin) := by
  apply hbin.preimage
  exact hu.comp (by unfold linePoint; fun_prop)

/-- A transferred witness has its entire horizontal projection inside the
same measurable line bin. -/
theorem witness_projection_subset_lineBin (E : Set (ℝ × ℝ))
    (u : ℝ × ℝ → ℝ) (s : ℝ) (z : ℝ × ℝ) (bin : Set ℝ)
    (htransfer : ∀ w ∈ E, u (SlopeBox.referencePoint s z w) ∈ bin) :
    Prod.fst '' E ⊆ lineBinSet u s z bin := by
  rintro x ⟨w, hw, rfl⟩
  exact htransfer w hw

namespace SlopeBox

/-- Turning the geometric transfer into an integral lower bound requires
only the measurable bin and the actual compact witness. -/
theorem witness_line_integral (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q : ℝ} (hA : 0 < A) (hbox : ∀ w ∈ E, T.radius w ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (s : ℝ) (z : ℝ × ℝ)
    (bin I : Set ℝ) (hbin : MeasurableSet bin) (hIfinite : volume I ≠ ∞)
    (hproj : ∀ w ∈ E, w.1 ∈ I)
    (htransfer : ∀ w ∈ E, u (referencePoint s z w) ∈ bin) :
    q * T.length / (2 * A) ≤
      ∫ x in I, (lineBinSet u s z bin).indicator (fun _ => (1 : ℝ)) x := by
  have hsubset : Prod.fst '' E ⊆ I ∩ lineBinSet u s z bin := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨hproj w hw, htransfer w hw⟩
  have hmeasure := measureReal_mono hsubset
    ((measure_mono (inter_subset_left : I ∩ lineBinSet u s z bin ⊆ I)).trans_lt
      (lt_top_iff_ne_top.mpr hIfinite)).ne
  have hbound := T.witness_projection_lower E hE hA hbox harea
  rw [setIntegral_indicator (measurableSet_lineBinSet u hu s z bin hbin), setIntegral_const]
  simpa only [smul_eq_mul, mul_one] using hbound.trans hmeasure

/-- The popular-bin threshold is the witness fraction divided only by the
fixed geometric dilation factors. -/
theorem witness_line_average (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q P : ℝ} (hA : 0 < A) (hq : 0 ≤ q) (hP : 0 < P)
    (hbox : ∀ w ∈ E, T.radius w ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (s : ℝ) (z : ℝ × ℝ)
    (bin I : Set ℝ) (hbin : MeasurableSet bin) (hIfinite : volume I ≠ ∞)
    (hIpos : 0 < volume.real I) (hIlength : volume.real I ≤ P * T.length)
    (hproj : ∀ w ∈ E, w.1 ∈ I)
    (htransfer : ∀ w ∈ E, u (referencePoint s z w) ∈ bin) :
    q / (2 * A * P) ≤
      (∫ x in I, (lineBinSet u s z bin).indicator (fun _ => (1 : ℝ)) x) / volume.real I := by
  apply (le_div_iff₀ hIpos).2
  have hthreshold : 0 ≤ q / (2 * A * P) := by positivity
  calc
    _ ≤ (q / (2 * A * P)) * (P * T.length) :=
      mul_le_mul_of_nonneg_left hIlength hthreshold
    _ = q * T.length / (2 * A) := by field_simp
    _ ≤ _ := T.witness_line_integral E hE hA hbox harea u hu s z bin I hbin
      hIfinite hproj htransfer

end SlopeBox
end LipschitzHilbert

end

end OAI
