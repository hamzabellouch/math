import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionErrorSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorReplacementMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorReplacementPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiPriorReplacementSamples
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction HistorySignedResidues PrimeCellFreezing

def guardedSourcePrimeMean {l : ℕ} (g : (q:ℕ)→ZMod q→ℂ)
    (V : ℕ→ℕ) (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (hd : pairModulus h k outside∣M)
    (f : (Bool→ℝ)→ℂ) : ℂ :=
  (logCellPrimeSource G E hZ).law.cmean (fun p=>
    (logCellPrimeSource G E hZ).law.cmean (fun q=>
      if Nat.Coprime (p:ℕ) (q:ℕ) then
        liftedResidueTest g V outside h k M hd (p.val,q.val)*
          f (fun t=>if t then (q.val:ℝ) else (p.val:ℝ)) else 0))

def guardedSourceMixedMean {l : ℕ} (g : (q:ℕ)→ZMod q→ℂ)
    (V : ℕ→ℕ) (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (hd : pairModulus h k outside∣M)
    (f : (Option Unit→ℝ)→ℂ) : ℂ :=
  ∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*
    (logCellPrimeSource G E hZ).law.cmean (fun q=>
      if Nat.Coprime n (q:ℕ) then
        liftedResidueTest g V outside h k M hd (n,q.val)*
          f (Option.elim' (n:ℝ) (fun _ : Unit=>(q.val:ℝ))) else 0)

private theorem weight_ne_zero_of_mass {G : ℝ} {E : Finset ℕ}
    {hZ : 0<Construction.logCellMass G E} (q : LogCellSample G E)
    (hq : (logCellPrior G E hZ).mass q≠0) : logCellWeight G q.val≠0 := by
  intro hz
  apply hq
  change logCellWeight G q.val/(∑p : LogCellSample G E,logCellWeight G p.val)=0
  rw [hz,zero_div]

theorem guardedSourcePrimeMean_error {l : ℕ} (d : Decomposition) (V : ℕ→ℕ)
    (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (hd : pairModulus h k outside∣M)
    (hout : ∀q∈outside,q.Prime) (f : (Bool→ℝ)→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
      ‖f (fun i=>Real.exp (z i))‖≤A) :
    ‖guardedSourcePrimeMean (residueTransform d) V outside h k G E hZ M hd f-
      sourcePrimeMean (residueTransform d) V outside h k G E hZ M hd f‖≤
      ((outside.prod:ℝ)^(2^(l+1))*A)*(Real.exp (1-G)/Construction.logCellMass G E) := by
  have hh := GiantCollisionError.logCell_guard_support G E hZ
    (fun x=>liftedResidueTest (residueTransform d) V outside h k M hd (x.1.val,x.2.val)*
      f (fun t=>if t then (x.2.val:ℝ) else (x.1.val:ℝ))) (by positivity : 0≤(outside.prod:ℝ)^(2^(l+1))*A) (by
      intro p q hp hq _
      exact HistoryGiantXiPriorReplacement.prime_sample_bound d V outside h k M hd hout G A f hf
        p.val (Finset.mem_sdiff.mp p.property).1 (weight_ne_zero_of_mass p hp)
        q.val (Finset.mem_sdiff.mp q.property).1 (weight_ne_zero_of_mass q hq))
  simp only [FinitePrior.pair_cmean,guardedSourcePrimeMean,sourcePrimeMean,logCellPrimeSource] at hh ⊢
  convert hh using 1
  congr 1

theorem guardedSourceMixedMean_error {l : ℕ} (d : Decomposition) (V : ℕ→ℕ)
    (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (hd : pairModulus h k outside∣M)
    (hout : ∀q∈outside,q.Prime) (f : (Option Unit→ℝ)→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
      (Option.elim' (G+1) (fun _ : Unit=>G+1)),‖f (fun i=>Real.exp (z i))‖≤A) :
    ‖guardedSourceMixedMean (residueTransform d) V outside h k G E hZ M hd f-
      sourceMixedMean (residueTransform d) V outside h k G E hZ M hd f‖≤
      ((outside.prod:ℝ)^(2^(l+1))*A)*(8*Real.exp (-G)) := by
  have hh := GiantCollisionError.logCell_integer_guard_support G E hZ
    (fun q n=>liftedResidueTest (residueTransform d) V outside h k M hd (n,q.val)*
      f (Option.elim' (n:ℝ) (fun _ : Unit=>(q.val:ℝ)))) (by positivity : 0≤(outside.prod:ℝ)^(2^(l+1))*A) (by
      intro q hq n hn hnw _
      exact HistoryGiantXiPriorReplacement.mixed_sample_bound d V outside h k M hd hout G A f hf
        n hn hnw q.val (Finset.mem_sdiff.mp q.property).1 (weight_ne_zero_of_mass q hq))
  simp only [guardedSourceMixedMean,sourceMixedMean,FinitePrior.cmean_sum,
    FinitePrior.cmean_mul_left,logCellPrimeSource] at hh ⊢
  convert hh using 1
  congr 1

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
