import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientSpectralProjection

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in
lemma exists_quotient_spectral_cut (x : selfAdjoint (T.CauchyQuotient hadd)) (t : ℝ) :
    ∃ p : T.CauchyQuotient hadd, IsSelfAdjoint p ∧ p*p=p ∧
      (∀ y, Commute x.1 y → Commute p y) ∧
      t • p ≤ p*x.1 ∧ (1-p)*x.1 ≤ t • (1-p) := by
  let z : selfAdjoint (T.CauchyQuotient hadd) :=
    ⟨x.1-t • 1,by
      change star (x.1-t • 1)=x.1-t • 1
      rw [star_sub,star_smul,star_trivial t,star_one,x.2.star_eq]⟩
  obtain ⟨p,hsa,hid,hcomm,hpos,hneg,hbicom⟩ := T.exists_quotient_positive_spectral_projection hadd hsqrt z
  have hc (y : T.CauchyQuotient hadd) (hy : Commute x.1 y) : Commute p y :=
    hbicom y (hy.sub_left ((Commute.one_left _).smul_left t))
  refine ⟨p,hsa,hid,hc,?_,?_⟩
  · have he : p*x.1-t • p=z.1⁺ := by
      simpa only [z,mul_sub,mul_smul_comm,mul_one] using hpos
    apply sub_nonneg.mp
    rw [he]
    exact CFC.posPart_nonneg z.1
  · have he : (1-p)*x.1-t • (1-p)= -z.1⁻ := by
      simpa only [z,mul_sub,mul_smul_comm,mul_one] using hneg
    apply sub_nonpos.mp
    rw [he]
    exact neg_nonpos.mpr (CFC.negPart_nonneg z.1)

def quotientSpectralCut (x : selfAdjoint (T.CauchyQuotient hadd)) (t : ℝ) : T.CauchyQuotient hadd :=
  Classical.choose (T.exists_quotient_spectral_cut hadd hsqrt x t)

lemma quotientSpectralCut_spec (x : selfAdjoint (T.CauchyQuotient hadd)) (t : ℝ) :
    IsSelfAdjoint (T.quotientSpectralCut hadd hsqrt x t) ∧
    T.quotientSpectralCut hadd hsqrt x t*T.quotientSpectralCut hadd hsqrt x t=T.quotientSpectralCut hadd hsqrt x t ∧
    (∀ y, Commute x.1 y → Commute (T.quotientSpectralCut hadd hsqrt x t) y) ∧
    t • T.quotientSpectralCut hadd hsqrt x t ≤ T.quotientSpectralCut hadd hsqrt x t*x.1 ∧
    (1-T.quotientSpectralCut hadd hsqrt x t)*x.1 ≤ t • (1-T.quotientSpectralCut hadd hsqrt x t) :=
  Classical.choose_spec (T.exists_quotient_spectral_cut hadd hsqrt x t)

lemma quotientSpectralCuts_commute (x y : selfAdjoint (T.CauchyQuotient hadd))
    (hxy : Commute x.1 y.1) (s t : ℝ) :
    Commute (T.quotientSpectralCut hadd hsqrt x s) (T.quotientSpectralCut hadd hsqrt y t) := by
  apply (T.quotientSpectralCut_spec hadd hsqrt x s).2.2.1
  exact ((T.quotientSpectralCut_spec hadd hsqrt y t).2.2.1 x.1 hxy.symm).symm
end CuntzPureness.PositiveQuasitrace

end

end OAI
