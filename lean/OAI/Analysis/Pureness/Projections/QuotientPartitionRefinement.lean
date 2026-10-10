import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFiniteSpectrumValue

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_partition_refinement {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (e : ι → T.CauchyQuotient hadd) (f : κ → T.CauchyQuotient hadd)
    (he : ∀ i ∈ s, 0 ≤ e i) (hf : ∀ j ∈ t, 0 ≤ f j)
    (heo : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i*e j=0)
    (hfo : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → f i*f j=0)
    (hes : ∑ i ∈ s, e i=1) (hfs : ∑ j ∈ t, f j=1)
    (hc : ∀ i ∈ s, ∀ j ∈ t, Commute (e i) (f j)) :
    (∀ k ∈ s.product t, 0 ≤ e k.1*f k.2) ∧
    (∀ k ∈ s.product t, ∀ l ∈ s.product t, k ≠ l →
      (e k.1*f k.2)*(e l.1*f l.2)=0) ∧
    (∑ k ∈ s.product t, e k.1*f k.2)=1 := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro k hk
    have hk := Finset.mem_product.mp hk
    exact Commute.mul_nonneg (he _ hk.1) (hf _ hk.2) (hc _ hk.1 _ hk.2)
  · intro k hk l hl hkl
    have hk := Finset.mem_product.mp hk
    have hl := Finset.mem_product.mp hl
    calc
      (e k.1*f k.2)*(e l.1*f l.2) = e k.1*(f k.2*e l.1)*f l.2 := by noncomm_ring
      _ = e k.1*(e l.1*f k.2)*f l.2 := by rw [←(hc _ hl.1 _ hk.2).eq]
      _ = (e k.1*e l.1)*(f k.2*f l.2) := by noncomm_ring
      _ = 0 := by
        by_cases h : k.1=l.1
        · have h' : k.2 ≠ l.2 := fun hh => hkl (Prod.ext h hh)
          rw [hfo _ hk.2 _ hl.2 h',mul_zero]
        · rw [heo _ hk.1 _ hl.1 h,zero_mul]
  · rw [Finset.product_eq_sprod,Finset.sum_product]
    simp only [←Finset.mul_sum,hfs,mul_one,hes]

lemma quotient_partition_refinement_left {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (e : ι → T.CauchyQuotient hadd) (f : κ → T.CauchyQuotient hadd)
    (hfs : ∑ j ∈ t, f j=1) (r : ι → ℝ) :
    (∑ k ∈ s.product t, r k.1 • (e k.1*f k.2))=∑ i ∈ s, r i • e i := by
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp only [←Finset.smul_sum,←Finset.mul_sum,hfs,mul_one]

lemma quotient_partition_refinement_right {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (e : ι → T.CauchyQuotient hadd) (f : κ → T.CauchyQuotient hadd)
    (hes : ∑ i ∈ s, e i=1) (r : κ → ℝ) :
    (∑ k ∈ s.product t, r k.2 • (e k.1*f k.2))=∑ j ∈ t, r j • f j := by
  rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_comm]
  simp only [←Finset.smul_sum,←Finset.sum_mul,hes,one_mul]

lemma quotientValue_commuting_partitions_add {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (e : ι → T.CauchyQuotient hadd) (f : κ → T.CauchyQuotient hadd)
    (he : ∀ i ∈ s, 0 ≤ e i) (hf : ∀ j ∈ t, 0 ≤ f j)
    (heo : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i*e j=0)
    (hfo : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → f i*f j=0)
    (hes : ∑ i ∈ s, e i=1) (hfs : ∑ j ∈ t, f j=1)
    (hc : ∀ i ∈ s, ∀ j ∈ t, Commute (e i) (f j)) (r : ι → ℝ) (v : κ → ℝ) :
    T.quotientValue hadd hsqrt ((∑ i ∈ s, r i • e i)+(∑ j ∈ t, v j • f j)) =
      T.quotientValue hadd hsqrt (∑ i ∈ s, r i • e i)+T.quotientValue hadd hsqrt (∑ j ∈ t, v j • f j) := by
  have hp := T.quotient_partition_refinement hadd s t e f he hf heo hfo hes hfs hc
  have H (a : ι × κ → ℝ) := T.quotientValue_weighted_partition hadd hsqrt (s.product t)
    (fun k => e k.1*f k.2) hp.1 hp.2.1 hp.2.2 a
  have hl := T.quotient_partition_refinement_left hadd s t e f hfs r
  have hr := T.quotient_partition_refinement_right hadd s t e f hes v
  have h := H (fun k => r k.1+v k.2)
  have hs (k : ι × κ) : (r k.1 + v k.2) • (e k.1 * f k.2) =
      r k.1 • (e k.1 * f k.2) + v k.2 • (e k.1 * f k.2) :=
    add_smul (r k.1) (v k.2) (e k.1 * f k.2)
  simp only [hs,Finset.sum_add_distrib,Complex.ofReal_add,add_mul] at h
  rw [hl,hr] at h
  rw [h,←H (fun k => r k.1),←H (fun k => v k.2),hl,hr]
end CuntzPureness.PositiveQuasitrace

end

end OAI
