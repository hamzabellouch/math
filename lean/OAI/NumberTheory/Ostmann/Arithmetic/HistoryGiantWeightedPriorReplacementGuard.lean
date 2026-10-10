import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
open Construction HistorySignedResidues PrimeCellFreezing

private theorem weight_ne_zero_of_mass {G : ℝ} {E : Finset ℕ}
    {hZ : 0<Construction.logCellMass G E} (q : LogCellSample G E)
    (hq : (logCellPrior G E hZ).mass q≠0) : logCellWeight G q.val≠0 := by
  intro hz
  apply hq
  change logCellWeight G q.val/(∑p : LogCellSample G E,logCellWeight G p.val)=0
  rw [hz,zero_div]

theorem guardedWeightedSourcePrimeMean_error {l : ℕ} (d : Decomposition) (V : ℕ→ℕ)
    (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (hd : pairModulus h k outside∣M)
    (hout : ∀q∈outside,q.Prime) (W : ZMod M × ZMod M → ℂ)
    (BW : ℝ) (hBW : 0 ≤ BW) (hW : ∀z, ‖W z‖ ≤ BW) (f : (Bool→ℝ)→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
      ‖f (fun i=>Real.exp (z i))‖≤A) :
    ‖guardedPeriodicSourcePrimeMean G E hZ M (weightedResidueTest (residueTransform d) V outside h k M hd W) f-
      periodicSourcePrimeMean G E hZ M (weightedResidueTest (residueTransform d) V outside h k M hd W) f‖≤
      (BW*((outside.prod:ℝ)^(2^(l+1))*A))*(Real.exp (1-G)/Construction.logCellMass G E) := by
  have hh := GiantCollisionError.logCell_guard_support G E hZ
    (fun x=>weightedResidueTest (residueTransform d) V outside h k M hd W (x.1.val,x.2.val)*
      f (fun t=>if t then (x.2.val:ℝ) else (x.1.val:ℝ))) (by positivity : 0≤BW*((outside.prod:ℝ)^(2^(l+1))*A)) (by
      intro p q hp hq _
      exact weighted_prime_sample_bound d V outside h k M hd hout W BW hBW hW G A f hf
        p.val (Finset.mem_sdiff.mp p.property).1 (weight_ne_zero_of_mass p hp)
        q.val (Finset.mem_sdiff.mp q.property).1 (weight_ne_zero_of_mass q hq))
  simp only [FinitePrior.pair_cmean,guardedPeriodicSourcePrimeMean,periodicSourcePrimeMean,logCellPrimeSource] at hh ⊢
  convert hh using 1
  congr 1

theorem guardedWeightedSourceMixedMean_error {l : ℕ} (d : Decomposition) (V : ℕ→ℕ)
    (outside : List ℕ) (h k : History l) (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (hd : pairModulus h k outside∣M)
    (hout : ∀q∈outside,q.Prime) (W : ZMod M × ZMod M → ℂ)
    (BW : ℝ) (hBW : 0 ≤ BW) (hW : ∀z, ‖W z‖ ≤ BW) (f : (Option Unit→ℝ)→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
      (Option.elim' (G+1) (fun _ : Unit=>G+1)),‖f (fun i=>Real.exp (z i))‖≤A) :
    ‖guardedPeriodicSourceMixedMean G E hZ M (weightedResidueTest (residueTransform d) V outside h k M hd W) f-
      periodicSourceMixedMean G E hZ M (weightedResidueTest (residueTransform d) V outside h k M hd W) f‖≤
      (BW*((outside.prod:ℝ)^(2^(l+1))*A))*(8*Real.exp (-G)) := by
  have hh := GiantCollisionError.logCell_integer_guard_support G E hZ
    (fun q n=>weightedResidueTest (residueTransform d) V outside h k M hd W (n,q.val)*
      f (Option.elim' (n:ℝ) (fun _ : Unit=>(q.val:ℝ)))) (by positivity : 0≤BW*((outside.prod:ℝ)^(2^(l+1))*A)) (by
      intro q hq n hn hnw _
      exact weighted_mixed_sample_bound d V outside h k M hd hout W BW hBW hW G A f hf
        n hn hnw q.val (Finset.mem_sdiff.mp q.property).1 (weight_ne_zero_of_mass q hq))
  simp only [guardedPeriodicSourceMixedMean,periodicSourceMixedMean,FinitePrior.cmean_sum,
    FinitePrior.cmean_mul_left,logCellPrimeSource] at hh ⊢
  convert hh using 1
  congr 1

end Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement

end

end OAI
