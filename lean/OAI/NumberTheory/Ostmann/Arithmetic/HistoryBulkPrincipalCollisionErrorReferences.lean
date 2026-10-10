import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumDrawReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryCompensationBiasedKernelSum HistoryPairRepresentatives HistoryBulkReplacementGeometry
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : ι → ℕ}

structure PrincipalCollisionReference (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (a : SelectedNonbulkSample C l) (p : Pattern τ) where
  amplitude : PrincipalAmplitudeData C outside l
  referenceBulk : SelectedBulkSample C l
  leftSmall : amplitude.left.root.small =
    assignedSlots C.sources (SelectedTemplate k L l) (fibreAssignment C a referenceBulk)
  representative : Block p → Representative amplitude.left amplitude.right
  residues : SelectedBulkSample C l → (Fin (2^l) × Fin (2*(bulkSize k L/2))) →
    (ZMod (bulkModulus amplitude.left amplitude.right outside amplitude.K))ˣ

namespace PrincipalCollisionReference
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {a : SelectedNonbulkSample C l} {p : Pattern τ}

def patternReference (r : PrincipalCollisionReference C outside a p) :
    PatternReference p (frequencyBound Bs BD Bz k L) outside l :=
  ⟨r.amplitude.left,r.amplitude.right,r.amplitude.leftSupported,
    r.amplitude.rightSupported,r.representative⟩

omit [Fintype ι] [DecidableEq ι] in

theorem reference_guard (r : PrincipalCollisionReference C outside a p) :
    fibreSmallOutsideGuard C outside a r.referenceBulk := by
  have hc := History.supported_root_coprime r.amplitude.leftSupported
  simp only [State.Coprime,State.values,List.cons_append,List.pairwise_cons] at hc
  change ((assignedSlots C.sources (SelectedTemplate k L l)
    (fibreAssignment C a r.referenceBulk)).map SmallSlot.value ++ outside).Pairwise Nat.Coprime
  rw [←r.leftSmall]
  exact hc.2.2

def amplitudeAt (r : PrincipalCollisionReference C outside a p) (u : SelectedBulkSample C l) :
    PrincipalAmplitudeData C outside l := {r.amplitude with residue := r.residues u}

def value (r : PrincipalCollisionReference C outside a p) (corrected mixed : Bool)
    (u : SelectedBulkSample C l) : ℂ := (r.amplitudeAt u).value corrected mixed u

end PrincipalCollisionReference

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
