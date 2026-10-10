import OAI.NumberTheory.DirichletL.Hecke.DetectorAdaptiveCutoff
import OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorAmplitudeFirst
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorFiberPartition
open HeckeDetectorPhysicalSelection HeckeDetectorAdaptiveCutoff

def amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U cap mesh hm widths physical u=bin)

def rowMean {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : ℝ :=
  weightedMean slots widths (fun s => HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s))

def classMean {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (widths : Slot→ℝ) (bin : BinLabel slots cap mesh) : ℝ :=
  weightedMean slots widths (binValue slots cap mesh bin)

theorem rowMean_eq {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) (u : Row)
    (hu : u∈amplitudeRows rows slots U cap mesh hm widths physical bin) :
    rowMean slots U cap mesh widths physical u=classMean slots cap mesh widths bin := by
  have he := (Finset.mem_filter.mp hu).2
  unfold rowMean classMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hv := congrArg (fun f : BinLabel slots cap mesh => (f ⟨s,hs⟩).val) he
  have hval : HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s)=
      binValue slots cap mesh bin s := by
    simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv
  exact congrArg (fun x => widths s*x) hval

theorem classMean_bounds {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U δ mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots (δ/2) mesh) (hδ : 0≤δ)
    (hw : ∀ s∈slots,0≤widths s) (hsupply : 0<∑ s∈slots,widths s)
    (hne : (amplitudeRows rows slots U (δ/2) mesh hm widths physical bin).Nonempty) :
    0≤classMean slots (δ/2) mesh widths bin ∧ classMean slots (δ/2) mesh widths bin≤δ/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←rowMean_eq rows slots U (δ/2) mesh hm widths physical bin u hu]
  apply weightedMean_bounds slots widths _ δ hw hsupply
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

def recut {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    SupportedWitness χ U a ε t' T allowance i := he ▸ w

theorem recut_values {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    (recut w he).label=w.label ∧ (recut w he).zero=w.zero ∧
    (recut w he).left=w.left ∧ (recut w he).right=w.right ∧
    (recut w he).nu=w.nu ∧ (recut w he).r=w.r ∧ (recut w he).m=w.m := by
  cases he
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def classWitness {Row Label Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (U a ε T allowance mesh : ℝ) (i : ℕ) (hm : 0<mesh)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (w : ∀ u : rows,SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (rowMean slots U ((2*a-1)/2) mesh widths physical u)) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) mesh)
    (u : amplitudeRows rows slots U ((2*a-1)/2) mesh hm widths physical bin) :
    SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (classMean slots ((2*a-1)/2) mesh widths bin)) T allowance i :=
  recut (w ⟨u.val,(Finset.mem_filter.mp u.property).1⟩)
    (congrArg (cutoff (2*a-1))
      (rowMean_eq rows slots U ((2*a-1)/2) mesh hm widths physical bin u.val u.property))

theorem card_eq_sum_amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots cap mesh,(amplitudeRows rows slots U cap mesh hm widths physical bin).card := by
  exact Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=amplitudeLabel slots U cap mesh hm widths physical) (by intro u hu; exact Finset.mem_univ _)

end SevenEighths.HeckeDetectorAmplitudeFirst

end

end OAI
