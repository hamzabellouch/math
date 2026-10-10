import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalSelectedReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkPatternIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E}

theorem spectator_membership (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) :
    ∀q∈spectatorList spectator ds,q∈spectator.candidates := by
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (ds i).property

theorem actual_principal_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz)
    {k : ℕ} (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
    ∀(l : ℕ)(hl : l≤k),
    ∃hV : ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q,
    ∀mixed : Bool,
      ‖(spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        backgroundValue true (fun bg p b=>selectedReplacementBackground C
          (spectatorList spectator ds) hactual hl (spectator_membership spectator ds) bg p b mixed)
          false mixed (hV ds))‖ ≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+16*(bulkSize k L:ℝ))) := by
  filter_upwards [selected_aggregate_eventually d Bs BD Bz hBs hBD hBz hk] with L hL
  intro E C hG hGu hcl hcu hb hd spectator hspec
  obtain ⟨hactual,hbound⟩ := hL E C hG hGu hcl hcu hb hd spectator hspec
  refine ⟨hactual,?_⟩
  intro l hl
  have hs (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) :=
    hbound (spectatorList spectator ds) (spectator_membership spectator ds)
      (by simp only [spectatorList,List.length_ofFn]) l hl
  choose hV hmain using hs
  refine ⟨hV,?_⟩
  intro mixed
  apply le_trans ((spectatorPrior spectator (2*(bulkSize k L/2))).norm_cmean_le _)
  apply le_trans ((spectatorPrior spectator (2*(bulkSize k L/2))).mean_mono (fun ds=>?_))
  · exact (spectatorPrior spectator (2*(bulkSize k L/2))).mean_const _ |>.le
  · rw [←selectedAggregate_eq_replacementBackground]
    exact hmain ds mixed

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
