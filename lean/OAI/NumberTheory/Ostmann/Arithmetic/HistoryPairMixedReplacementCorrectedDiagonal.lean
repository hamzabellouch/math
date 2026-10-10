import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedSample

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open scoped BigOperators

theorem exists_diagonalCorrectedXi_mixed_grid_replacement_constants :
    ∃ d K L₀ : ℝ,0<d ∧ 0<K ∧ 1≤L₀ ∧
      ∀ (b s k₀ : ℕ) (X tb td G Δ E : ℝ) (center : ℕ→ℝ) (outside : List ℕ),
        0<X → (∀q∈outside,0<q) → outside.length=2*s →
      ∀ (l : ℕ) (V : ℕ→ℕ) (h k : History l)
        (hs : h.Supported V outside) (ks : k.Supported V outside),
        l≤k₀ → TreeSourceLabels (Template.initial (2*b) k₀) h →
        TreeSourceLabels (Template.initial (2*b) k₀) k →
      ∀ (j₀ : ℕ) (T U WH Wu : ℝ),
      ∀ (I : Finset (PairKey h k)) (background : PairKey h k→ℝ),
        (∀i,0<background i) →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (e : Option ι ≃ I)
        (NI : ℕ) (N : ι→ℕ) (M : ℕ) [NeZero M] (loI hiI ηI : ℝ) (lo hi η Z : ι→ℝ),
        loI≤hiI → 0<ηI → ⌊Real.exp hiI⌋₊≤NI →
        (∀i,L₀≤lo i ∧ lo i≤hi i ∧ 0<η i ∧ η i≤1 ∧
          ⌊Real.exp (hi i)⌋₊≤N i ∧ 0<Z i ∧ (M:ℝ)≤Real.exp (d*(lo i)^(1/3:ℝ))) →
        SourceBounds b k₀ G center h (leftMap h k) I background
          (fun j=>Option.elim' loI lo (e.symm j)) (fun j=>Option.elim' hiI hi (e.symm j)) →
        SourceBounds b k₀ G center k (rightMap h k) I background
          (fun j=>Option.elim' loI lo (e.symm j)) (fun j=>Option.elim' hiI hi (e.symm j)) →
        CounterpartBounds T U WH Wu (pairedDiagonalHKeys h k j₀) (pairedDiagonalUKeys h k j₀) I background
          (fun j=>Option.elim' loI lo (e.symm j)) (fun j=>Option.elim' hiI hi (e.symm j)) →
        Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
          (∑a,∑i,topCenters b center a i)+
          (∑a,∑j:Fin k₀,∑i,compensationCenters b center a j i) →
      ∀ ε B error mesh : ℝ,0≤ε → 1≤B → 0≤error → 0 ≤ mesh → ηI ≤ mesh → (∀i,η i ≤ mesh) →
        (∀(j:MixedGridIndex loI hiI ηI lo hi η) i,
          (K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
            (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹≤ε) →
        (∀(j:MixedGridIndex loI hiI ηI lo hi η) i,
          |harmonicIntegral M (boxLower lo hi η j.2 i) (boxUpper lo hi η j.2 i)/Z i|+
            ((K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
              (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹)≤B) →
        (∀j:MixedGridIndex loI hiI ηI lo hi η,
          mixedGridError (ι:=ι) M loI hiI ηI G 1 partitionDerivativeConstant smoothPartition ε B j.1≤error) →
      ∀F:ZMod M→(ι→(ZMod M)ˣ)→ℂ,
        let f := reindexedCorrectedRealXi b s X tb td G h k hs ks T U (pairedDiagonalHKeys h k j₀) (pairedDiagonalUKeys h k j₀) (Finset.univ : Finset (Fin (diagonalCellKeys k j₀).length)) (pairedDiagonalCellCenter k j₀ G center) (pairedDiagonalCellKey h k j₀) I background e
        let v := ((Fintype.card ι:ℝ)+1)*correctedPairDerivativeBound WH Wu ((pairedDiagonalHKeys h k j₀).length) ((pairedDiagonalUKeys h k j₀).length) ((Finset.univ : Finset (Fin (diagonalCellKeys k j₀).length)).card) h k V b k₀ tb Δ E center*mesh
        let A := Real.exp (WH+Wu)*Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E)
        ‖mixedSmoothTestSum NI N M loI hiI G smoothPartition lo hi Z F f-
            mixedPrincipalIntegral M loI hiI G smoothPartition lo hi Z f*
              ∑r:ZMod M,∑u:ι→(ZMod M)ˣ,F r u‖≤
          (2*v*mixedPrincipalMass M loI hiI G smoothPartition lo hi Z+
            (v+A)*(Fintype.card (MixedGridIndex loI hiI ηI lo hi η)*error))*
              ∑r:ZMod M,∑u:ι→(ZMod M)ˣ,‖F r u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hgrid⟩ := exists_correctedXi_mixed_grid_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro b s k₀ X tb td G Δ E center outside hX houtside hout l V h k hs ks hlk hl₁ hl₂
    j₀ T U WH Wu
  exact hgrid b s k₀ X tb td G Δ E center outside hX houtside hout l V h k hs ks hlk hl₁ hl₂
    (Fin (diagonalCellKeys k j₀).length) T U WH Wu
    (pairedDiagonalHKeys h k j₀) (pairedDiagonalUKeys h k j₀) Finset.univ
    (pairedDiagonalCellCenter k j₀ G center) (pairedDiagonalCellKey h k j₀)

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
