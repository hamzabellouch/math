import OAI.NumberTheory.Ostmann.Conclusion.RegularNormPriors

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Filter
open Ostmann.Construction

theorem actualRegularEnergy_initial_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ (V : ℕ → ℕ) (spectator : PrimeSource) (m l : ℕ), l≤k →
      actualRegularEnergy C.sources (Template.initial (2*(bulkSize k L/2)) k) V C.giant spectator m
        (residueTransform d) (favorableGiantResidueTransform d C.favorable) l≤18*(2*(V l:ℝ)+1) := by
  filter_upwards [actual_regular_tuple_eventually,
    initial_source_regular_ranges_eventually d Bs BD Bz hk] with L htuple hranges
  intro E C hGlo hGhi hclo hchi htb htd V spectator m l hl
  apply actualRegularEnergy_le_of_tuple_means
  intro x hx outside s q
  have hr := hranges E C hGlo hclo hchi htb htd l hl x hx
  have hp := assignedSlots_prime C.sources
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) x
  exact htuple d C.favorable C.giantCenter C.giantPositive
    (assignedSlots C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) x)
    (by linarith) (by linarith) hr.1 (fun z hz => ⟨hp z hz,hr.2 z hz⟩) outside s q

end Ostmann.Conclusion

end

end OAI
