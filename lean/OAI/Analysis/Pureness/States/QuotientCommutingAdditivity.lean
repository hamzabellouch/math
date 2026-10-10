import OAI.Analysis.Pureness.Projections.QuotientFiniteSpectralApproximation
import OAI.Analysis.Pureness.Projections.QuotientPartitionRefinement
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientNormContinuity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientValue_add_commute (x y : selfAdjoint (T.CauchyQuotient hadd))
    (hxy : Commute x.1 y.1) :
    T.quotientValue hadd hsqrt (x.1+y.1) = T.quotientValue hadd hsqrt x.1+T.quotientValue hadd hsqrt y.1 := by
  let V := T.quotientValue hadd hsqrt
  let K := 2*T ⟨1,zero_le_one⟩
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (T.nonneg _)
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(4*K+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨N,e,r,he,heo,hes,hec,hxe⟩ := T.exists_quotient_finite_spectral_approximation hadd hsqrt x hδ
  obtain ⟨M,f,v,hf,hfo,hfs,hfc,hyf⟩ := T.exists_quotient_finite_spectral_approximation hadd hsqrt y hδ
  let a := ∑ i ∈ Finset.range N, r i • e i
  let b := ∑ j ∈ Finset.range M, v j • f j
  have hval : V (a+b)=V a+V b := T.quotientValue_commuting_partitions_add hadd hsqrt
    (Finset.range N) (Finset.range M) e f (fun i _ => (he i).2.2) (fun j _ => (hf j).2.2)
    (fun i _ j _ hij => heo i j hij) (fun i _ j _ hij => hfo i j hij) hes hfs
    (fun i _ j _ => hec i (f j) (hfc j x.1 hxy.symm).symm) r v
  have hsum : ‖(x.1+y.1)-(a+b)‖ ≤ ‖x.1-a‖+‖y.1-b‖ := by
    have h : (x.1+y.1)-(a+b)=(x.1-a)+(y.1-b) := by abel
    rw [h]
    exact norm_add_le _ _
  have h1 := T.quotientValue_sub_norm_le hadd hsqrt (x.1+y.1) (a+b)
  have h2 := T.quotientValue_sub_norm_le hadd hsqrt a x.1
  have h3 := T.quotientValue_sub_norm_le hadd hsqrt b y.1
  rw [norm_sub_rev a x.1] at h2
  rw [norm_sub_rev b y.1] at h3
  have herr : V (x.1+y.1)-(V x.1+V y.1)=
      (V (x.1+y.1)-V (a+b))+(V a-V x.1)+(V b-V y.1) := by rw [hval]; ring
  change ‖V (x.1+y.1)-(V x.1+V y.1)‖ ≤ 0+ε
  rw [herr,zero_add]
  have ht1 := norm_add_le (V (x.1+y.1)-V (a+b)) (V a-V x.1)
  have ht2 := norm_add_le ((V (x.1+y.1)-V (a+b))+(V a-V x.1)) (V b-V y.1)
  have hkδ : (4*K+1)*δ=ε := by dsimp [δ]; field_simp
  change ‖x.1-a‖ < δ at hxe
  change ‖y.1-b‖ < δ at hyf
  change ‖V (x.1+y.1)-V (a+b)‖ ≤ K*‖(x.1+y.1)-(a+b)‖ at h1
  change ‖V a-V x.1‖ ≤ K*‖x.1-a‖ at h2
  change ‖V b-V y.1‖ ≤ K*‖y.1-b‖ at h3
  have hh := mul_le_mul_of_nonneg_left hsum hK
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hxe.le),mul_nonneg hK (sub_nonneg.mpr hyf.le)]
end CuntzPureness.PositiveQuasitrace

end

end OAI
