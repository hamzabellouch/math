import OAI.Probability.InvariantIsing.Spectral.SpectralLabelCounts
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure

namespace OAI

/-! Remove zero limiting weights without dropping their finite-volume labels. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical BigOperators

namespace InvariantIsing

def positiveSpectralLabel {ι : Type*} (w : ι → ℝ) (fallback : {i // 0 < w i})
    (i : ι) : {i // 0 < w i} := if h : 0 < w i then ⟨i,h⟩ else fallback

lemma positiveSpectralLabel_self {ι : Type*} (w : ι → ℝ)
    (fallback i : {i // 0 < w i}) : positiveSpectralLabel w fallback i=i := by
  simp only [positiveSpectralLabel, dite_eq_left i.property]

lemma positiveSpectralWeights_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) :
    ∑ i : {i // 0 < w i}, w i=1 := by
  have hz : (∑ i : {i // ¬0 < w i}, w i)=0 := Finset.sum_eq_zero fun i _ =>
    le_antisymm (le_of_not_gt i.property) (hw i)
  have hh := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i) w
  rw [hz,add_zero,hsum] at hh
  exact hh

lemma positiveSpectralLabel_weight {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (fallback b : {i // 0 < w i}) :
    (∑ a : {a // positiveSpectralLabel w fallback a=b}, w a)=w b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => positiveSpectralLabel w fallback a=b))
    (by simp) w]
  apply Finset.sum_eq_single b.val
  · intro a ha hab
    by_cases hp : 0 < w a
    · have hh : positiveSpectralLabel w fallback a=b := (Finset.mem_filter.mp ha).2
      have he : a=b.val := by
        simpa only [positiveSpectralLabel,dite_eq_left hp] using congrArg Subtype.val hh
      exact (hab he).elim
    · exact le_antisymm (le_of_not_gt hp) (hw a)
  · intro hb
    exact (hb (by simp [positiveSpectralLabel_self])).elim

lemma positive_spectral_counts_tendsto {ι : Type*} [Fintype ι]
    (N : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → ι)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (fallback : {i // 0 < w i})
    (hlim : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop (𝓝 w)) :
    Tendsto (fun k b =>
      (spectralLabelCount (positiveSpectralLabel w fallback ∘ g k) b : ℝ)/N k)
      atTop (𝓝 (fun b : {i // 0 < w i} => w b)) := by
  apply tendsto_pi_nhds.mpr
  intro b
  have hh := (tendsto_pi_nhds.mp
    (spectral_label_counts_relabel N g w hlim (positiveSpectralLabel w fallback))) b
  convert hh using 1
  apply congrArg nhds
  calc
    w b = ∑ a : {a // positiveSpectralLabel w fallback a=b}, w a :=
      (positiveSpectralLabel_weight w hw fallback b).symm
    _ = _ := by
      apply Finset.sum_congr
      · ext a
        simp only [Finset.mem_univ]
      · intro a _
        rfl

lemma finiteSpectralMeasure_positive {ι : Type*} [Fintype ι]
    (w lam : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    finiteSpectralMeasure (fun i : {i // 0 < w i} => w i) (fun i => lam i)=
      finiteSpectralMeasure w lam := by
  simp only [finiteSpectralMeasure,Measure.sum_fintype]
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    have hp : ¬0 < w i := fun hp => hi ⟨⟨i,hp⟩,rfl⟩
    have hz : w i=0 := le_antisymm (le_of_not_gt hp) (hw i)
    simp only [hz,ENNReal.ofReal_zero,zero_smul]
  · intro i
    rfl

end InvariantIsing

end

end OAI
