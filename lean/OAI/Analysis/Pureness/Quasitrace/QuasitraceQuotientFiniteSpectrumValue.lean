import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientOrthogonalSums

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientValue_selfAdjoint_shift (x : selfAdjoint (T.CauchyQuotient hadd)) (r : ℝ) :
    T.quotientValue hadd hsqrt (x.1+r • 1)=T.quotientValue hadd hsqrt x.1+(r:ℂ)*T.quotientValue hadd hsqrt 1 := by
  have h := T.quotientValue_cfc_add hadd hsqrt x (fun t : ℝ => t) (fun _ => r) continuous_id continuous_const
  have hi : cfc (fun t : ℝ => t) x.1=x.1 := cfc_id ℝ x.1 x.2
  have hc : cfc (fun _ : ℝ => r) x.1=r • 1 := by
    rw [cfc_const r x.1,Algebra.algebraMap_eq_smul_one]
    rfl
  rw [hi,hc,T.quotientValue_real_smul] at h
  exact h

lemma quotientValue_nonnegative_weighted_sum {ι : Type*} (s : Finset ι) (e : ι → T.CauchyQuotient hadd)
    (hn : ∀ i ∈ s, 0 ≤ e i) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i*e j=0)
    (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    T.quotientValue hadd hsqrt (∑ i ∈ s, r i • e i)=∑ i ∈ s, (r i:ℂ)*T.quotientValue hadd hsqrt (e i) := by
  have h := T.quotientValue_orthogonal_sum hadd hsqrt s (fun i => r i • e i)
    (fun i hi => (Positive.smul ⟨r i, hr i hi⟩ ⟨e i, hn i hi⟩).2) (by
      intro i hi j hj hij
      rw [smul_mul_assoc,mul_smul_comm,ho i hi j hj hij,smul_zero,smul_zero])
  simpa only [T.quotientValue_real_smul] using h

lemma quotientValue_weighted_partition {ι : Type*} (s : Finset ι) (e : ι → T.CauchyQuotient hadd)
    (hn : ∀ i ∈ s, 0 ≤ e i) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i*e j=0)
    (he : ∑ i ∈ s, e i=1) (r : ι → ℝ) :
    T.quotientValue hadd hsqrt (∑ i ∈ s, r i • e i)=∑ i ∈ s, (r i:ℂ)*T.quotientValue hadd hsqrt (e i) := by
  classical
  let K : ℝ := ∑ i ∈ s, |r i|
  have hK (i : ι) (hi : i ∈ s) : 0 ≤ r i+K := by
    have hk : |r i| ≤ K := Finset.single_le_sum (fun j _ => abs_nonneg (r j)) hi
    linarith [neg_abs_le (r i)]
  let x : selfAdjoint (T.CauchyQuotient hadd) := ⟨∑ i ∈ s, r i • e i,by
    change star (∑ i ∈ s, r i • e i)=∑ i ∈ s, r i • e i
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [star_smul,star_trivial (r i),(hn i hi).isSelfAdjoint.star_eq]⟩
  have hv := T.quotientValue_nonnegative_weighted_sum hadd hsqrt s e hn ho (fun i => r i+K) hK
  have heq : (∑ i ∈ s, (r i+K) • e i)=x.1+K • 1 := by
    have hs (i : ι) : (r i + K) • e i = r i • e i + K • e i :=
      add_smul (r i) K (e i)
    simp only [hs, Finset.sum_add_distrib]
    change (∑ i ∈ s, r i • e i) + (∑ i ∈ s, K • e i) =
      (∑ i ∈ s, r i • e i) + K • 1
    congr 1
    exact (show K • (∑ i ∈ s, e i) = ∑ i ∈ s, K • e i from Finset.smul_sum).symm.trans (congrArg (fun z => K • z) he)
  rw [heq,T.quotientValue_selfAdjoint_shift] at hv
  have hunit := T.quotientValue_orthogonal_sum hadd hsqrt s e hn ho
  rw [he] at hunit
  have heq' : (∑ i ∈ s, ((r i+K:ℝ):ℂ)*T.quotientValue hadd hsqrt (e i))=
      (∑ i ∈ s, (r i:ℂ)*T.quotientValue hadd hsqrt (e i))+(K:ℂ)*T.quotientValue hadd hsqrt 1 := by
    rw [hunit]
    simp only [Complex.ofReal_add,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  rw [heq'] at hv
  exact add_right_cancel hv
end CuntzPureness.PositiveQuasitrace

end

end OAI
