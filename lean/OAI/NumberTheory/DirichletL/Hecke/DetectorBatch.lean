import OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

structure Batch (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  data : Label→RowData
  reverse : Label→Bool
  row_coeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (family u j) I=
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤mesh
  supply : 7/37≤∑ s∈slots,widths s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

abbrev Batch.Bin (B : Batch M H Label Slot U a ε tstar T allowance i) :=
  BinLabel B.slots ((2*a-1)/2) B.binWidth

def Batch.fiberRows (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  fiber B.rows B.family U a ε tstar T allowance i B.witness B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) bin j J K

def Batch.fiber (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : Fiber M H Label Slot U a ε tstar T allowance i :=
  toFiber M H B.rows B.family U a ε tstar T allowance i B.witness B.row_norm B.data B.reverse
    B.row_coeff B.slots B.profile B.upper B.widths B.external B.mesh B.binWidth B.mesh_nonneg
    B.binWidth_pos B.widths_pos B.widths_mesh B.supply bin j J K hne

def Batch.q (B : Batch M H Label Slot U a ε tstar T allowance i) (bin : B.Bin) : ℝ :=
  weightedMean B.slots B.widths (binValue B.slots ((2*a-1)/2) B.binWidth bin)

theorem Batch.card_eq_sum_fibers [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i) :
    B.rows.card=∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows bin j J K).card :=
  HeckeDetectorFiberPartition.card_eq_sum_fibers B.rows B.family U a ε tstar T allowance i B.witness
    B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U)

theorem Batch.card_bound [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C : ℝ) (exponent : B.Bin→ℝ) (hC : 0≤C) (hU : 0<U)
    (hfiber : ∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ)≤C*U^(exponent bin)) :
    (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      ∑ bin : B.Bin,U^(exponent bin) := by
  have he : (B.rows.card : ℝ)=∑ bin : B.Bin, ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows bin j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C*U^(exponent bin) := by
      apply Finset.sum_le_sum
      intro bin _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows bin j J K).Nonempty
      · exact hfiber bin j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←mul_assoc]
      rw [←Finset.mul_sum]
      ring

end SevenEighths.HeckeDetectorBatch

end

end OAI
