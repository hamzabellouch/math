import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseActual
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction Conclusion Filter

theorem selected_source_inputs_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      C.CrossRoleSeparation spectator ∧
      (∀j≤k,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)) ∧
      (∀p : spectator.Sample,∀j≤k,frequencyBound Bs BD Bz k L j<(p:ℕ)) := by
  filter_upwards [initial_source_cross_role_separation_eventually d Bs BD Bz hk,
    initial_sources_above_frequencies_eventually d Bs BD Bz hk,
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk
      (by norm_num : (0:ℝ)<1/2000)] with L hsep hfreq hspect
  intro E C hG hcl hcu hb hd spectator hspec
  refine ⟨hsep E C hG hcl hcu hb hd spectator hspec,
    fun j hj=>(hfreq E C hG hcl hcu hb hd j hj).2,?_⟩
  intro p j hj
  exact hspect j hj p.val (spectator.prime _ p.property).pos (hspec p).1

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
