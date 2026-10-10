import OAI.NumberTheory.Jacobsthal.Estimates.ConditionalPatternCounts
import OAI.NumberTheory.Jacobsthal.Primes.ActualPrimeSelectors

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceMoments
attribute [local instance] Classical.propDecidable

noncomputable def actualFullPattern (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) : ErdosLargePatternLaw.FullPattern w H :=
  (ZMod.unitOfCoprime p.val ((Finset.mem_filter.mp p.property).2.symm.of_dvd_right (divisorModulus_dvd_H w H)),
    (primeK P H C0 hP p : ZMod (divisorModulus w H)),
    (primePoint P w H C0 hw hP hlarge p).2.1,
    (primeM P H C0 hP p : ZMod (coprimeModulus w H)))

theorem full_p0_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ divisorModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).1.val.val : ZMod t) = (p.val : ZMod t) :=
  cast_nat_residue (divisorModulus w H) t p.val ht

theorem full_k0_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ divisorModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).2.1.val : ZMod t) = (primeK P H C0 hP p : ZMod t) :=
  cast_nat_residue (divisorModulus w H) t (primeK P H C0 hP p) ht

theorem full_p1_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).2.2.1.val.val : ZMod t) = (p.val : ZMod t) :=
  primePoint_pValue P w H C0 hw hP hlarge p t ht

theorem full_m1_projection (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    ((actualFullPattern P w H C0 hw hP hlarge p).2.2.2.val : ZMod t) = (primeM P H C0 hP p : ZMod t) :=
  cast_int_residue (coprimeModulus w H) t ht (primeM P H C0 hP p)

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
