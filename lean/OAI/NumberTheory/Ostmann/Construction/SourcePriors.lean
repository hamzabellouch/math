import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior
import OAI.NumberTheory.Ostmann.Construction.PrimeSources

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def logCellPrimeSource (c : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass c E) :
    PrimeSource where
  candidates := logCellPrimes c \ E
  prime _p hp := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  law := logCellPrior c E hZ

theorem logCellPrimeSource_log_support (c : ℝ) (E : Finset ℕ)
    (hZ : 0<logCellMass c E) (p : (logCellPrimeSource c E hZ).Sample)
    (hp : (logCellPrimeSource c E hZ).law.mass p ≠ 0) :
    |Real.log (p:ℕ)-c|<1 := by
  have hn : Ostmann.smoothPartition (Real.log (p:ℕ)-c) ≠ 0 := by
    intro hz
    apply hp
    have hm := logCellPrior_mass c E hZ (⟨p.val,p.property⟩ : LogCellSample c E)
    change (logCellPrior c E hZ).mass (⟨p.val,p.property⟩ : LogCellSample c E)=0
    rw [hm, hz, zero_div]
  exact abs_lt.mpr (Ostmann.smoothPartition_support_subset hn)

def harmonicPrimeMass (P : Finset ℕ) : ℝ := ∑ p∈P, (1:ℝ)/p

def harmonicPrimeSource (P : Finset ℕ) (hP : ∀p∈P, Nat.Prime p)
    (hZ : 0<harmonicPrimeMass P) : PrimeSource where
  candidates := P
  prime := hP
  law := FinitePrior.fromWeights (fun p : ↥P => (1:ℝ)/(p:ℕ))
    (fun p => div_nonneg zero_le_one (Nat.cast_nonneg _))
    (by
      have hsum : (∑p:↥P,(1:ℝ)/(p:ℕ))=harmonicPrimeMass P :=
        by simpa only [harmonicPrimeMass] using (Finset.sum_coe_sort P (fun p : ℕ => (1:ℝ)/p))
      rw [hsum]
      exact hZ)

theorem harmonicPrimeSource_mass (P : Finset ℕ) (hP : ∀p∈P, Nat.Prime p)
    (hZ : 0<harmonicPrimeMass P) (p : (harmonicPrimeSource P hP hZ).Sample) :
    (harmonicPrimeSource P hP hZ).law.mass p=1/((p:ℕ)*harmonicPrimeMass P) := by
  change ((1:ℝ)/(p:ℕ))/(∑q:↥P,(1:ℝ)/(q:ℕ))=_
  have hsum : (∑q:↥P,(1:ℝ)/(q:ℕ))=harmonicPrimeMass P :=
        by simpa only [harmonicPrimeMass] using (Finset.sum_coe_sort P (fun p : ℕ => (1:ℝ)/p))
  rw [hsum, div_div]

end Ostmann.Construction

end

end OAI
