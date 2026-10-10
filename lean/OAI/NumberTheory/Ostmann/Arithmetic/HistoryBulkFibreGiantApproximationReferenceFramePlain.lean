import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization
open HistoryBulkFibreGiantApproximationReference HistoryPairBulkCoordinates
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)

def plainPrimeFrame (y₀ : SelectedBulkSample C l) (draw : PrimeDraw C.giant)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hy₀ : 0 < (selectedBulkPrior C l).mass y₀)
    (hr : 0 < primeWeight C.giant draw)
    (hc : choicesMass C.sources _ _ l c ≠ 0)
    (he : choicesMass C.sources _ _ l e ≠ 0)
    (hs : FibreSupported C outside σ a s t c e y₀
      (primeP C.giant draw) (primeQ C.giant draw))
    (hp : ∀q∈outside,q.Prime) : Frame (l:=l) C outside :=
  let hd := plain_prime_reference_data C σ a y₀ draw ha hy₀ hr
  { leftSource := fibreAssignment C a y₀
    rightSource := permuteAssignment C σ (fibreAssignment C a y₀)
    s := s
    t := t
    P := primeP C.giant draw
    Q := primeQ C.giant draw
    leftChoices := c
    rightChoices := e
    left_mass := hd.left_mass
    right_mass := hd.right_mass
    left_choices_mass := hc
    right_choices_mass := he
    plus_pos := hd.plus_pos
    minus_pos := hd.minus_pos
    plus_cell := hd.plus_cell
    minus_cell := hd.minus_cell
    left_supported := hs.1
    right_supported := hs.2
    matching := plain_reference_matching C σ a s t c e y₀ _ _
    outside_primes := hp }

def plainMixedFrame (y₀ : SelectedBulkSample C l)
    (draw : MixedDraw C.giantCenter C.giant)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hy₀ : 0 < (selectedBulkPrior C l).mass y₀)
    (hr : 0 < mixedWeight C.giantCenter C.giant draw)
    (hc : choicesMass C.sources _ _ l c ≠ 0)
    (he : choicesMass C.sources _ _ l e ≠ 0)
    (hs : FibreSupported C outside σ a s t c e y₀
      (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw))
    (hp : ∀q∈outside,q.Prime) : Frame (l:=l) C outside :=
  let hd := plain_mixed_reference_data C σ a y₀ draw ha hy₀ hr
  { leftSource := fibreAssignment C a y₀
    rightSource := permuteAssignment C σ (fibreAssignment C a y₀)
    s := s
    t := t
    P := mixedP C.giantCenter C.giant draw
    Q := mixedQ C.giantCenter C.giant draw
    leftChoices := c
    rightChoices := e
    left_mass := hd.left_mass
    right_mass := hd.right_mass
    left_choices_mass := hc
    right_choices_mass := he
    plus_pos := hd.plus_pos
    minus_pos := hd.minus_pos
    plus_cell := hd.plus_cell
    minus_cell := hd.minus_cell
    left_supported := hs.1
    right_supported := hs.2
    matching := plain_reference_matching C σ a s t c e y₀ _ _
    outside_primes := hp }

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
