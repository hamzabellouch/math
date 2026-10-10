import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBoundsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinates

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding HistoryGiantReferenceMean
open HistoryPairPattern HistoryPairGiantCoordinates HistoryActiveCoordinates

theorem selected_prime_reference_sourceBounds {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ → ℕ) (l : ℕ)
    (x y : SourceAssignment C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
    (s t : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (r : PrimeDraw C.giant)
    (hx : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass x ≠ 0)
    (hy : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass y ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l e ≠ 0)
    (hr : 0 < primeWeight C.giant r) :
    let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
    let h := drawHistory C.sources seed V l
      (sourceState C.sources (Template.current seed l) x s) c
      (primeP C.giant) (primeQ C.giant) r
    let g := drawHistory C.sources seed V l
      (sourceState C.sources (Template.current seed l) y t) e
      (primeP C.giant) (primeQ C.giant) r
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (leftMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) ∧
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) g (rightMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) := by
  have hp := primeDraw_positive C.giant r
  have hcell := prime_reference_cells C r hr
  apply selected_reference_sourceBounds C V l x y s t c e
    (primeP C.giant r) (primeQ C.giant r) hx hy hc he hp.1 hp.2
  · simpa only [primeP,Int.cast_natCast] using hcell.1.le
  · simpa only [primeQ,Int.cast_natCast] using hcell.2.le

theorem selected_mixed_reference_sourceBounds {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (V : ℕ → ℕ) (l : ℕ)
    (x y : SourceAssignment C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))
    (s t : ℤ)
    (c e : HistoryChoices C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l)
    (r : MixedDraw C.giantCenter C.giant)
    (hx : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass x ≠ 0)
    (hy : (assignmentPrior C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)).mass y ≠ 0)
    (hc : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l c ≠ 0)
    (he : choicesMass C.sources (Template.initial (2*(Conclusion.bulkSize k L/2)) k) V l e ≠ 0)
    (hr : 0 < mixedWeight C.giantCenter C.giant r) :
    let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
    let h := drawHistory C.sources seed V l
      (sourceState C.sources (Template.current seed l) x s) c
      (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) r
    let g := drawHistory C.sources seed V l
      (sourceState C.sources (Template.current seed l) y t) e
      (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) r
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (leftMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) ∧
    SourceBounds (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) g (rightMap h g) (giantCoordinates h g)
      (pairBackground h g) (fun _ => (C.giantCenter : ℝ)-1)
      (fun _ => (C.giantCenter : ℝ)+1) := by
  have hp := mixedDraw_positive C.giantCenter C.giant r
  have hcell := mixed_reference_cells C r hr
  apply selected_reference_sourceBounds C V l x y s t c e
    (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) hx hy hc he hp.1 hp.2
  · simpa only [mixedP,Int.cast_natCast] using hcell.1.le
  · simpa only [mixedQ,Int.cast_natCast] using hcell.2.le

@[simp] theorem option_constant_endpoint (a : ℝ) (i : Option Unit) :
    Option.elim' a (fun _ : Unit => a) i = a := by
  cases i <;> rfl

theorem sourceBounds_option_endpoints {b k l : ℕ} {G : ℝ} {center : ℕ → ℝ}
    (q h g : History l) (f : Key q → PairKey h g)
    (hh : SourceBounds b k G center q f (giantCoordinates h g) (pairBackground h g)
      (fun _ => G-1) (fun _ => G+1)) :
    SourceBounds b k G center q f (giantCoordinates h g) (pairBackground h g)
      (fun j => Option.elim' (G-1) (fun _ : Unit => G-1) ((optionEquiv h g).symm j))
      (fun j => Option.elim' (G+1) (fun _ : Unit => G+1) ((optionEquiv h g).symm j)) := by
  simpa only [option_constant_endpoint] using hh

end Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds

end

end OAI
