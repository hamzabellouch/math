import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientAnnihilator

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
open scoped CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

lemma exists_quotient_positive_spectral_projection (x : selfAdjoint (T.CauchyQuotient hadd)) :
    ∃ p : T.CauchyQuotient hadd, IsSelfAdjoint p ∧ p*p=p ∧ Commute p x.1 ∧
      p*x.1=x.1⁺ ∧ (1-p)*x.1= -x.1⁻ ∧
      (∀ y, Commute x.1 y → Commute p y) := by
  let h : Positive (T.CauchyQuotient hadd) := ⟨x.1⁺,CFC.posPart_nonneg _⟩
  obtain ⟨p,hsa,hid,hph,hann,hcomm⟩ := T.exists_quotient_support_annihilator hadd hsqrt h
  have hpn : p*x.1⁻=0 := (hann _).mp (CFC.posPart_mul_negPart x.1)
  have hp : p*x.1=x.1⁺ := by
    calc
      p*x.1 = p*(x.1⁺-x.1⁻) := by rw [CFC.posPart_sub_negPart x.1 x.2]
      _ = x.1⁺ := by rw [mul_sub,hpn,sub_zero]; exact hph
  have hpc (y : T.CauchyQuotient hadd) (hy : Commute x.1 y) : Commute p y :=
    hcomm y (by exact hy.cfcₙ_real (fun t : ℝ => t⁺))
  refine ⟨p,hsa,hid,hpc x.1 (Commute.refl _),hp,?_,hpc⟩
  rw [sub_mul,one_mul,hp]
  have he := CFC.posPart_sub_negPart x.1 x.2
  calc
    x.1-x.1⁺ = (x.1⁺-x.1⁻)-x.1⁺ := congrArg (fun z => z-x.1⁺) he.symm
    _ = -x.1⁻ := by abel
end CuntzPureness.PositiveQuasitrace

end

end OAI
