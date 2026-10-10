import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OutwardWeightCap

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport

lemma template_right_weight {ι : Type*} [Fintype ι] {m B s : ι → ℝ}
    {eta center c : ℝ} (hm : ∀ i,0 ≤  m i) (hsum : ∑ i,m i=1)
    (hB : ∀ i,0 ≤ B i) (hleft : ∀ i,s i < 1-eta → 1 ≤ B i)
    (hcenter : center ≤ 1) (hparameter : c ≤ center-∑ i,m i*B i) :
    c ≤ ∑ i∈Finset.univ.filter (fun i =>  1-eta ≤ s i),m i := by
  classical
  let R := Finset.univ.filter (fun i =>  1-eta ≤ s i)
  let L := Finset.univ.filter (fun i =>  ¬1-eta ≤ s i)
  have hpart : (∑ i∈R,m i)+(∑ i∈L,m i)=1 := by
    rw [show (∑ i∈R,m i)+(∑ i∈L,m i)=∑ i,m i from
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun i =>  1-eta ≤ s i) m,hsum]
  have hbound : (∑ i∈L,m i) ≤ ∑ i,m i*B i := by
    calc
      _ ≤ ∑ i∈L,m i*B i := Finset.sum_le_sum (fun i hi =>  by
        have HB := hleft i (lt_of_not_ge (Finset.mem_filter.mp hi).2)
        simpa using mul_le_mul_of_nonneg_left HB (hm i))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
        (fun i _ _ =>  mul_nonneg (hm i) (hB i))
  change c ≤ ∑ i∈R,m i
  linarith

lemma outward_from_levels {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι ≤ n+1) {m d B si : ι → ℝ}
    {q D c eta delta zeta s center : ℝ}
    (hm : ∀ i,0  <  m i) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i*d i=0)
    (hq : 0 < q) (hD : 0 < D) (hc : 0 < c)
    (heta : eta ≤ 1/128) (hdelta : delta ≤ zeta) (hzeta : zeta ≤ 1/16)
    (hs : s < 3/4) (hlow : ∀ i,-2*eta ≤ si i)
    (hrange : ∀ i,|si i-s| ≤ 1+delta)
    (hnorm : ∀ i,|2*q*d i+d i^2+2*D*(si i-s)| ≤ zeta*D)
    (hB : ∀ i,0 ≤ B i) (hleft : ∀ i,si i < 1-eta → 1 ≤ B i)
    (hcenter : center ≤ 1) (hparameter : c ≤ center-∑ i,m i*B i) :
    ∃ i, 0 < d i ∧ c/(12*(n+1:ℝ)) ≤  m i ∧
      c*D/(8*(n+1:ℝ)*q) ≤  m i*d i ∧ d i ≤ 3*D/(2*q) ∧
      -2*eta ≤ si i ∧ si i < 1-eta ∧ B i ≤ 12*(n+1:ℝ)/c := by
  classical
  let R := Finset.univ.filter (fun i =>  1-eta ≤ si i)
  have hzm : zeta*D ≤ D/16 := by nlinarith [mul_le_mul_of_nonneg_right hzeta hD.le]
  have hdm : delta*D ≤ D/16 := by nlinarith [mul_le_mul_of_nonneg_right (hdelta.trans hzeta) hD.le]
  have hem : eta*D ≤ D/128 := by nlinarith [mul_le_mul_of_nonneg_right heta hD.le]
  have hr : ∀ i∈R,2*q*d i+d i^2 ≤ -D/4 := by
    intro i hi
    have hright := (Finset.mem_filter.mp hi).2
    have H := (abs_le.mp (hnorm i)).2
    have HA := mul_le_mul_of_nonneg_left hright hD.le
    have HB := mul_lt_mul_of_pos_left hs hD
    nlinarith only [H,HA,HB,hzm,hem,hD]
  have ho : ∀ i,0 < d i → 2*q*d i+d i^2 ≤ 3*D := by
    intro i hd
    have H := (abs_le.mp (hnorm i)).2
    have HA := mul_le_mul_of_nonneg_left (abs_le.mp (hrange i)).1 hD.le
    nlinarith only [H,HA,hzm,hdm,hD]
  have hcap : ∑ i,m i*B i ≤ 1 := by linarith
  obtain ⟨i,hdi,hmi,hprod,hdub,hBi⟩ := outward_weight_and_cap hn hm hsum hbar hq hD hc R
    (template_right_weight (fun i =>  (hm i).le) hsum hB hleft hcenter hparameter) hr ho hB hcap
  have hir : si i < 1-eta := by
    by_contra H
    have HR := hr i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,le_of_not_gt H⟩)
    have HX := mul_pos hq hdi
    nlinarith only [HR,HX,sq_nonneg (d i),hD]
  push_cast at hmi hprod hBi
  exact ⟨i,hdi,hmi,hprod,hdub,hlow i,hir,hBi⟩

end WeakMTWTransport

end

end

section

noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport

lemma barycenter_opposite_extension {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] (pj : ι → E) (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hsum : ∑ i,m i=1) (i : ι)
    {theta : ℝ} (hl : -m i/2 ≤ theta) (hu : theta ≤ 1) :
    (∑ j,m j • pj j)+theta • (pj i-(∑ j,m j • pj j)) ∈ convexHull ℝ (range pj) := by
  classical
  have hmi : m i ≤ 1 := (Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)).trans_eq hsum
  let w : ι → ℝ := fun j => (1-theta)*m j + if j=i then theta else 0
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    by_cases hji : j=i
    · rw [ite_eq_left hji,hji]
      by_cases ht : 0 ≤ theta
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu) (hm i)) ht
      · have H := mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hmi)
        nlinarith [sq_nonneg (m i),hm i]
    · rw [ite_eq_right hji,add_zero]
      exact mul_nonneg (sub_nonneg.mpr hu) (hm j)
  have hw1 : ∑ j,w j=1 := by
    dsimp [w]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,hsum]
    simp
  have he : (∑ j,w j • pj j)=(∑ j,m j • pj j)+theta • (pj i-(∑ j,m j • pj j)) := by
    dsimp [w]
    simp_rw [add_smul,mul_smul]
    rw [Finset.sum_add_distrib,←Finset.smul_sum]
    have H : (∑ j,(if j=i then theta else 0) • pj j)=theta • pj i := by
      simp_rw [ite_smul,zero_smul]
      simp
    rw [H]
    module
  rw [←he]
  exact (convex_convexHull ℝ (range pj)).sum_mem (fun j _ => hw j) hw1
    (fun j _ => subset_convexHull ℝ _ (mem_range_self j))

lemma outward_radial_ratio {q D d a theta : ℝ}
    (hq : 0 < q) (ha : 0 < a) (hd : 0 < d)
    (hqa : a*D ≤ q^2) (hdub : d ≤ 3*D/(2*q))
    (ht : -a/3 ≤ theta) :
    q/2 ≤ q+theta*d ∧ d^2/((q+theta*d)*d) ≤ 3/a := by
  have hdq : d*(2*q) ≤ 3*D := (le_div_iff₀ (by positivity : 0 < 2*q)).mp hdub
  have hadq : a*d ≤ 3*q/2 := by
    have H := mul_le_mul_of_nonneg_left hdq ha.le
    nlinarith only [H,hqa,hq]
  have hlow : q/2 ≤ q+theta*d := by
    have H := mul_le_mul_of_nonneg_right ht hd.le
    nlinarith only [H,hadq]
  refine ⟨hlow,?_⟩
  have hqp : 0 < q+theta*d := (half_pos hq).trans_le hlow
  apply (div_le_div_iff₀ (mul_pos hqp hd) ha).mpr
  have H := mul_le_mul_of_nonneg_right hadq hd.le
  have H' := mul_le_mul_of_nonneg_right hlow hd.le
  nlinarith only [H,H']

end WeakMTWTransport

end

end

end

end OAI
