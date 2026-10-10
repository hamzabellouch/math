import OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotInverseCount
import OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotPlainCount
import OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
import OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

structure Fiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u∈rows,(witness u).label=label
  fixed_left : ∀ u∈rows,(witness u).left=left
  fixed_right : ∀ u∈rows,(witness u).right=right
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u∈rows,∀ J : Ideal O,idealCoeff (family u label) J=
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  bin : Slot→ℝ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤mesh
  binWidth_pos : 0<binWidth
  widths_pos : ∀ s∈slots,0<widths s
  widths_mesh : ∀ s∈slots,widths s≤mesh
  supply : 7/37≤∑ s∈slots,widths s
  fixed_bin : ∀ u∈rows,∀ s∈slots,
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U u s)=bin s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def Fiber.r (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.left.val)
def Fiber.m (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.right.val)
def Fiber.q (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := weightedMean F.slots F.widths F.bin
def Fiber.inverseProfile (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ→ℂ := inverseTest U tstar F.r
def Fiber.physicalProduct (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (u : FreeRow) : ℂ :=
  ∏ s∈selected,physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u s

structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*(3/4+2*Δ)*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

theorem Fiber.mean_bounds (F : Fiber M H Label Slot U a ε tstar T allowance i) (ha : 1/2≤a) :
    0≤F.q ∧ F.q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := F.nonempty
  apply weightedMean_bounds F.slots F.widths F.bin (2*a-1)
    (fun s hs => (F.widths_pos s hs).le) (by linarith [F.supply])
  intro s hs
  rw [←F.fixed_bin u hu s hs]
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
