import OAI.NumberTheory.Ostmann.Construction.InitialSourceConstruction
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Construction
open Filter

theorem initial_source_construction_separated : ∃ δ : ℝ, 0<δ ∧
    ∀ (d : Decomposition) (Bs BD Bz : ℝ) (k : ℕ), 0<k →
      ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 → ∀ spectator : PrimeSource,
        (∀p : spectator.Sample, Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
          Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
        (1/2:ℝ)≤ spectator.law.mean (fun p => balancedPrimeIndicator d p) →
        ∃ C : InitialSourceChoice d Bs BD Bz k L E,
          C.favorable⊆Supply.nonsparsePrimes d δ L ∧
          Real.exp ((1/20:ℝ)*L)≤C.blockBase ∧
          C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
          C.blockBase-2<(C.giantCenter:ℝ) ∧
          (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 ∧
          |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 ∧
          |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 ∧
          Real.sqrt C.scale*Real.exp (-27*(Conclusion.bulkSize k L:ℝ))≤C.statistic spectator ∧
          C.CrossRoleSeparation spectator := by
  obtain ⟨δ,hδ,hbuild⟩ := initial_source_construction
  refine ⟨δ,hδ,?_⟩
  intro d Bs BD Bz k hk
  filter_upwards [hbuild d Bs BD Bz k hk,
    initial_source_cross_role_separation_eventually d Bs BD Bz hk] with L hbuild hsep
  intro E hE spectator hsupport hbalanced
  obtain ⟨C,hP,hG,hGu,hc,hcu,hb,hd,hstat⟩ := hbuild E hE spectator hsupport hbalanced
  exact ⟨C,hP,hG,hGu,hc,hcu,hb,hd,hstat,hsep E C hG hc hcu hb hd spectator hsupport⟩

end Ostmann.Construction

end

end OAI
