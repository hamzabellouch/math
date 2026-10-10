import OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber
import OAI.NumberTheory.DirichletL.Hecke.DetectorDynamicSelection

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

abbrev BinLabel {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ) :=
  slots → ↥(HeckePrimeAmplitudeBins.labels cap mesh)

def amplitudeLabel {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : BinLabel slots cap mesh :=
  fun s => ⟨HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s),
    HeckePrimeAmplitudeBins.amplitude_mem_labels _ _ _ _ hm⟩

def fiber {Row Label Slot : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u=bin ∧
    (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots ((2*a-1)/2) mesh, ∑ label : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        (fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => (amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u,
      (w u).label,(w u).left,(w u).right)) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

def binValue {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (bin : BinLabel slots cap mesh) (s : Slot) : ℝ :=
  if hs : s∈slots then (bin ⟨s,hs⟩).val else 0

theorem fixed_bin {Row Label Slot : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u∈fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K)
    (s : Slot) (hs : s∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) mesh (physical u s)=
      binValue slots ((2*a-1)/2) mesh bin s := by
  have he := (Finset.mem_filter.mp hu).2.1
  have hv := congrArg (fun f : BinLabel slots ((2*a-1)/2) mesh => (f ⟨s,hs⟩).val) he
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

def toFiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) {Label Slot : Type*}
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (hrow : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (data : Label→RowData) (reverse : Label→Bool)
    (hcoeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hmesh : 0≤mesh) (hbw : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwmesh : ∀ s∈slots,widths s≤mesh)
    (hsupply : 7/37≤∑ s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (label : Label)
    (J K : Fin (dyadicLength U))
    (hne : (fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K).Nonempty) :
    Fiber M H Label Slot U a ε tstar T allowance i where
  rows := fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K
  nonempty := hne
  family := χ
  witness := w
  label := label
  left := J
  right := K
  fixed_label := fun _u hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_left := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.1
  fixed_right := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.2
  row_norm := fun u hu => hrow u (Finset.mem_filter.mp hu).1
  rowData := data label
  reverse := reverse label
  row_coeff := fun u hu => hcoeff u (Finset.mem_filter.mp hu).1 label
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  bin := binValue slots ((2*a-1)/2) binWidth bin
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hmesh
  binWidth_pos := hbw
  widths_pos := hw
  widths_mesh := hwmesh
  supply := hsupply
  fixed_bin := fun u hu s hs => fixed_bin rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K u hu s hs

end SevenEighths.HeckeDetectorFiberPartition

end

end OAI
