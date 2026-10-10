import OAI.NumberTheory.Ostmann.Characters.MixedPrimeBiasDefs
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonSourceDefs
import OAI.NumberTheory.Ostmann.Construction.ActualTests
import OAI.NumberTheory.Ostmann.Construction.SourcePositive

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Construction
variable {d : Decomposition} {BD Bz L ε : ℝ} {k : ℕ}
  {E : Finset ℕ} {C : InitialSourceChoice d 200 BD Bz k L E}
  {P : Finset ℕ} {hP : ∀p∈P,p.Prime} {hZ : 0<harmonicPrimeMass P}

theorem ActualComparisonSource.spectator_band
    (h : ActualComparisonSource C P hP hZ ε) :
    ∀p : (harmonicPrimeSource P hP hZ).Sample,
      Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
      Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L) :=
  fun p=>h.band p.val p.property

theorem ActualComparisonSource.spectator_balanced
    (h : ActualComparisonSource C P hP hZ ε) :
    ∀p : (harmonicPrimeSource P hP hZ).Sample,Supply.balancedDensity d p.val :=
  fun p=>(h.flat p.val p.property).1

theorem ActualComparisonSource.spectator_correlation_lt
    (h : ActualComparisonSource C P hP hZ ε) :
    ∀p : (harmonicPrimeSource P hP hZ).Sample,
      (FiniteField.correlationBound (residueTransform d p.val):ℝ)<ε := by
  intro p
  let : Fact p.val.Prime := ⟨hP p.val p.property⟩
  have heq : residueTransform d p.val=Supply.additiveTransform (d.residueSupport p.val) :=
    funext (residueTransform_eq d p.val)
  rw [heq,←Characters.mixedPrimeBias_prime]
  exact (h.flat p.val p.property).2

theorem ActualComparisonSource.spectator_correlation_le
    (h : ActualComparisonSource C P hP hZ ε) :
    ∀p : (harmonicPrimeSource P hP hZ).Sample,
      (FiniteField.correlationBound (residueTransform d p.val):ℝ)≤ε :=
  fun p=>(h.spectator_correlation_lt p).le

end Ostmann.Conclusion

end

end OAI
