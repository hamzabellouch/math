import OAI.NumberTheory.Ostmann.Construction.InitialEtaLower
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationConstruction

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open Filter
namespace Ostmann.Construction

theorem initial_amplitude_construction : ∃ δ : ℝ, 0<δ ∧
    ∀ (d : Decomposition) (Bs BD Bz : ℝ), 200≤Bs → ∀ (k : ℕ), 0<k →
      ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
        ∀ (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (hZ : 0<harmonicPrimeMass P),
        L/5000≤harmonicPrimeMass P →
        (∀p∈P,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℝ) ∧
          Real.log (p:ℝ)≤Real.exp ((1/1000:ℝ)*L)) →
        (1/2:ℝ)≤ (harmonicPrimeSource P hP hZ).law.mean (fun p => balancedPrimeIndicator d p) →
        ∃ C : InitialSourceChoice d Bs BD Bz k L E,
          C.favorable⊆Supply.nonsparsePrimes d δ L ∧
          Real.exp ((1/20:ℝ)*L)≤C.blockBase ∧
          C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
          C.blockBase-2<(C.giantCenter:ℝ) ∧
          (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 ∧
          |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 ∧
          |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 ∧
          C.CrossRoleSeparation (harmonicPrimeSource P hP hZ) ∧
          Real.sqrt C.scale*Real.exp (-27*(Conclusion.bulkSize k L:ℝ))≤
            C.statistic (harmonicPrimeSource P hP hZ) ∧
          ∀G:ℝ,Real.exp (-28*(Conclusion.bulkSize k L:ℝ))≤
            ‖decompositionAmplitude d C.favorable C.sources (Conclusion.frequencyBound Bs BD Bz k L)
              C.giant (harmonicPrimeSource P hP hZ) C.scale G
              (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2) k C.bulkBin C.spectatorBin 0‖ := by
  obtain ⟨δ,hδ,hbuild⟩ := initial_source_construction_separated
  refine ⟨δ,hδ,?_⟩
  intro d Bs BD Bz hBs k hk
  filter_upwards [hbuild d Bs BD Bz k hk,
    InitialEta.initial_amplitude_lower_eventually d Bs BD Bz hBs hk] with L hbuild hlower
  intro E hE P hP hZ hPH hsupport hbalanced
  obtain ⟨C,hfav,hG,hGu,hcl,hcu,hb,hd,hstat,hsep⟩ :=
    hbuild E hE (harmonicPrimeSource P hP hZ) (fun p => hsupport p p.property) hbalanced
  refine ⟨C,hfav,hG,hGu,hcl,hcu,hb,hd,hsep,hstat,?_⟩
  exact hlower E C hG hGu hcl hcu hb hd P hP hZ hPH hsupport hstat

end Ostmann.Construction

end

end OAI
