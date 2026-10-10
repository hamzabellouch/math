import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhasePartition
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.Immersion.ClosedSurface.ComplexPullback

namespace OAI

/-!
Split an actual smooth compactly supported target using the finite smooth
phase partition.  Every piece is a supported smooth field on a compact subset
of its phase domain, and the sum of the pieces is the original target.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)
open JetPolynomial (SupportedField)
open PhaseMean (ComplexTensor)

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Each target piece is supported both where the target was supported and
where its partition coefficient is supported. -/
def pieceSupport (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    Compacts Base :=
  ⟨(K : Set Base) ∩ tsupport (P.weight i),
    K.isCompact.inter_right (isClosed_tsupport _)⟩

@[simp] theorem coe_pieceSupport (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) = (K : Set Base) ∩ tsupport (P.weight i) := rfl

theorem pieceSupport_subset_original (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) ⊆ K := fun _ hx => hx.1

theorem pieceSupport_subset_domain (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    (P.pieceSupport i : Set Base) ⊆ U i := fun _ hx => P.subordinate i hx.2

/-- The piece is constructed by ordinary scalar multiplication of the target. -/
def splitSupported (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (i : ι) : SupportedField (F := F) (P.pieceSupport i) :=
  ContDiffMapSupportedIn.of_support_subset ((P.smooth i).smul A.contDiff)
    (subset_closure.trans (fun _x hx =>
      ⟨A.tsupport_subset (tsupport_smul_subset_right (P.weight i) A hx),
        tsupport_smul_subset_left (P.weight i) A hx⟩))

@[simp] theorem splitSupported_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (i : ι) (x : Base) :
    P.splitSupported A i x = P.weight i x • A x := rfl

/-- With the partition fixed, splitting is linear in the target. -/
def splitSupportedLM (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) (P.pieceSupport i) where
  toFun := fun A => P.splitSupported A i
  map_add' A B := by
    apply DFunLike.ext
    intro x
    change P.weight i x • (A x + B x) = P.weight i x • A x + P.weight i x • B x
    exact smul_add _ _ _
  map_smul' c A := by
    apply DFunLike.ext
    intro x
    change P.weight i x • (c • A x) = c • (P.weight i x • A x)
    exact smul_comm _ _ _

theorem splitSupported_tsupport_subset (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (i : ι) :
    tsupport (P.splitSupported A i) ⊆ U i :=
  (P.splitSupported A i).tsupport_subset.trans (P.pieceSupport_subset_domain i)

/-- The finite pieces sum to the original target at every point, including
outside the compact set on which the coefficients sum to one. -/
theorem sum_splitSupported_apply (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) (x : Base) :
    ∑ i, P.splitSupported A i x = A x := by
  classical
  simp only [splitSupported_apply, ← Finset.sum_smul]
  by_cases hx : x ∈ (K : Set Base)
  · rw [P.sum_eq_one x hx, one_smul]
  · simp only [A.zero_on_compl hx, Pi.zero_apply, smul_zero]

theorem sum_splitSupported (P : CompactPhasePartition ι (K : Set Base) U)
    (A : SupportedField (F := F) K) :
    (fun x => ∑ i, P.splitSupported A i x) = A := by
  funext x
  exact P.sum_splitSupported_apply A x

end CompactPhasePartition

/-- Split the actual complex tensor target into one smooth supported target
for each supplied phase domain, without changing their total. -/
theorem exists_split_supported_complex_target {ι : Type*} [Fintype ι]
    (K : Compacts Base) (U : ι → Set Base) (hU : ∀ i, IsOpen (U i))
    (hcover : (K : Set Base) ⊆ ⋃ i, U i)
    (A : SupportedField (F := ComplexTensor) K) :
    ∃ (L : ι → Compacts Base) (B : (i : ι) → SupportedField (F := ComplexTensor) (L i)),
      (∀ i, (L i : Set Base) ⊆ K) ∧ (∀ i, (L i : Set Base) ⊆ U i) ∧
      (∀ x, ∑ i, B i x = A x) := by
  obtain ⟨P⟩ := exists_compact_phase_partition K.isCompact U hU hcover
  exact ⟨P.pieceSupport, P.splitSupported A, P.pieceSupport_subset_original,
    P.pieceSupport_subset_domain, P.sum_splitSupported_apply A⟩

end ClosedSurfaceR4.PhasePartitions

end

end OAI
