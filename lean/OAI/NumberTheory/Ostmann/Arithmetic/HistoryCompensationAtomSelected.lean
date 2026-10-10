import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationAtomSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedSourceAtomBounds

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationAtom
open Construction CompensationEqualityPatterns HistoryCompensationMoment Filter
variable {ι η : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

omit [DecidableEq ι] in
theorem selected_block_bounds_eventually [DecidableEq ι] (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (origin : ι → ℕ) (pick : η → ι) (_j : η),
      (∑ v : CommonSample C.sources origin, selectedBlockWeight C origin pick v) ≤
        Real.exp ((Fintype.card η : ℝ)*L) ∧
      ∀ v : CommonSample C.sources origin,
        selectedBlockWeight C origin pick v ≤
          Real.exp ((Fintype.card η : ℝ)*L-Real.exp ((39/10000 : ℝ)*L)) := by
  filter_upwards [HistorySelectedSourceAtomBounds.selected_source_atom_bounds_eventually
    d Bs BD Bz hk, eventually_ge_atTop (0 : ℝ)] with L hs hL
  intro E C hG hGu hcl hcu hb hd origin pick j
  have hc := hs E C hG hGu hcl hcu hb hd
  have h := selectedBlockWeight_uniform_bounds C origin pick j (Real.one_le_exp hL)
    (fun i => hc.1 _) (hc.2.1 (origin (pick j)))
  have he : (Real.exp L)^Fintype.card η = Real.exp ((Fintype.card η : ℝ)*L) := by
    rw [← Real.exp_nat_mul]
  constructor
  · simpa only [he] using h.1
  · intro v
    convert h.2 v using 1
    rw [he, ← Real.exp_add]
    congr 1
    ring

end Ostmann.Arithmetic.HistoryCompensationAtom

end

end OAI
