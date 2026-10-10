import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionSeparation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationAtomPatterns

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction Conclusion CompensationEqualityPatterns HistoryCompensationAtom
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
variable {ι η : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

omit [DecidableEq ι] [DecidableEq η] in

theorem selectedBlockWeight_source_ne_zero
    (C : InitialSourceChoice d Bs BD Bz k L E) (origin : ι → ℕ)
    (pick : η → ι) (v : CommonSample C.sources origin)
    (hv : selectedBlockWeight C origin pick v ≠ 0) (j : η) :
    sourceWeight C.sources origin (pick j) v ≠ 0 := by
  intro hz
  exact hv (blockWeight_eq_zero_of_mass_eq_zero
    (fun i => sourceWeight C.sources origin (pick i)) (fun w => (w.val : ℝ)) j v hz)

omit [DecidableEq ι] [DecidableEq η] in

theorem bulk_block_coprime
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hsep : C.CrossRoleSeparation spectator) (origin : ι → ℕ) (pick : η → ι)
    (j : η) (hlo : 2*(bulkSize k L/2) ≤ origin (pick j))
    (hhi : origin (pick j) < 2*(bulkSize k L/2)+6+4*k)
    (p : C.bulk.Sample) (hp : C.bulk.law.mass p ≠ 0)
    (v : CommonSample C.sources origin) (hv : selectedBlockWeight C origin pick v ≠ 0) :
    p.val.Coprime v.val := by
  have hs := selectedBlockWeight_source_ne_zero C origin pick v hv j
  unfold sourceWeight at hs
  split_ifs at hs with hmem
  · exact bulk_nonbulk_source_coprime C spectator hsep _ hlo hhi p hp ⟨v.val,hmem⟩ hs
  · exact (hs rfl).elim

omit [DecidableEq ι] in

theorem bulk_pattern_block_coprime
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hsep : C.CrossRoleSeparation spectator) (origin τ : ι → ℕ)
    (pattern : Pattern τ) (block : Block pattern) (j : Fiber pattern block)
    (hlo : 2*(bulkSize k L/2) ≤ origin j.val)
    (hhi : origin j.val < 2*(bulkSize k L/2)+6+4*k)
    (p : C.bulk.Sample) (hp : C.bulk.law.mass p ≠ 0)
    (v : CommonSample C.sources origin)
    (hv : CompensationEqualityPatterns.blockWeight pattern (sourceWeight C.sources origin) block v *
      (v.val : ℝ)^multiplicity pattern block / (v.val : ℝ) ≠ 0) :
    p.val.Coprime v.val := by
  apply bulk_block_coprime C spectator hsep origin (fun i : Fiber pattern block => i.val)
    j hlo hhi p hp v
  rwa [selectedBlockWeight_fiber_eq]

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
