import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistorySignedResidues PrimeCellFreezing HistoryGiantWeightedPriorReplacement

private theorem weight_ne_zero_of_mass {G : ℝ} {E : Finset ℕ}
    {hZ : 0<Construction.logCellMass G E} (q : LogCellSample G E)
    (hq : (logCellPrior G E hZ).mass q≠0) : logCellWeight G q.val≠0 := by
  intro hz
  apply hq
  change logCellWeight G q.val/(∑p : LogCellSample G E,logCellWeight G p.val)=0
  rw [hz,zero_div]

theorem guarded_periodic_prime_error (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (R : ZMod M × ZMod M → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hR : ∀z, ‖R z‖ ≤ B) (f : (Bool→ℝ)→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀z∈logRectangle (fun _ : Bool=>G-1) (fun _=>G+1),
      ‖f (fun i=>Real.exp (z i))‖≤A) :
    ‖guardedPeriodicSourcePrimeMean G E hZ M R f-
      periodicSourcePrimeMean G E hZ M R f‖≤
      (B*A)*(Real.exp (1-G)/Construction.logCellMass G E) := by
  have hh := GiantCollisionError.logCell_guard_support G E hZ
    (fun x=>R (x.1.val,x.2.val)*
      f (fun t=>if t then (x.2.val:ℝ) else (x.1.val:ℝ))) (by positivity : 0≤B*A) (by
      intro p q hp hq _
      exact periodic_prime_sample_bound M R B hB hR G A f hf
        p.val (Finset.mem_sdiff.mp p.property).1 (weight_ne_zero_of_mass p hp)
        q.val (Finset.mem_sdiff.mp q.property).1 (weight_ne_zero_of_mass q hq))
  simp only [FinitePrior.pair_cmean,guardedPeriodicSourcePrimeMean,periodicSourcePrimeMean,logCellPrimeSource] at hh ⊢
  convert hh using 1
  congr 1

theorem guarded_periodic_mixed_error (G : ℝ) (E : Finset ℕ)
    (hZ : 0<Construction.logCellMass G E) (M : ℕ) (R : ZMod M × ZMod M → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hR : ∀z, ‖R z‖ ≤ B) (f : (Option Unit→ℝ)→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀z∈logRectangle (Option.elim' (G-1) (fun _ : Unit=>G-1))
      (Option.elim' (G+1) (fun _ : Unit=>G+1)),‖f (fun i=>Real.exp (z i))‖≤A) :
    ‖guardedPeriodicSourceMixedMean G E hZ M R f-
      periodicSourceMixedMean G E hZ M R f‖≤
      (B*A)*(8*Real.exp (-G)) := by
  have hh := GiantCollisionError.logCell_integer_guard_support G E hZ
    (fun q n=>R (n,q.val)*
      f (Option.elim' (n:ℝ) (fun _ : Unit=>(q.val:ℝ)))) (by positivity : 0≤B*A) (by
      intro q hq n hn hnw _
      exact periodic_mixed_sample_bound M R B hB hR G A f hf
        n hn hnw q.val (Finset.mem_sdiff.mp q.property).1 (weight_ne_zero_of_mass q hq))
  simp only [guardedPeriodicSourceMixedMean,periodicSourceMixedMean,FinitePrior.cmean_sum,
    FinitePrior.cmean_mul_left,logCellPrimeSource] at hh ⊢
  convert hh using 1
  congr 1

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
