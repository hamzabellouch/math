import Mathlib

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport

lemma outward_weight_and_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (hN : Fintype.card ι≤N) {m d B : ι → ℝ} {q D c : ℝ}
    (hm : ∀ i,0 < m i) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i*d i=0)
    (hq : 0<q) (hD : 0<D) (hc : 0<c) (right : Finset ι)
    (hrmass : c≤∑ i∈right,m i)
    (hr : ∀ i∈right,2*q*d i+d i^2≤-D/4)
    (ho : ∀ i,0<d i → 2*q*d i+d i^2≤3*D)
    (hB : ∀ i,0≤B i) (hcap : ∑ i,m i*B i≤1) :
    ∃ i, 0<d i ∧ c/(12*(N:ℝ))≤ m i ∧ c*D/(8*(N:ℝ)*q)≤ m i*d i ∧
      d i≤3*D/(2*q) ∧ B i≤12*(N:ℝ)/c := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra H
    have : (Finset.univ : Finset ι)=∅ := Finset.not_nonempty_iff_eq_empty.mp H
    rw [this,Finset.sum_empty] at hsum
    norm_num at hsum
  have hNp : 0<(N:ℝ) := by
    have : 0<Fintype.card ι := by simpa only [Finset.card_univ] using Finset.card_pos.mpr hne
    exact_mod_cast this.trans_le hN
  have hrneg : ∀ i∈right,d i<0 ∧ D/(8*q)≤-d i := by
    intro i hi
    have H := hr i hi
    constructor
    · by_contra hn
      have hdi : 0≤d i := le_of_not_gt hn
      nlinarith only [H,mul_nonneg hq.le hdi,sq_nonneg (d i),hD]
    · apply (div_le_iff₀ (by positivity : 0<8*q)).mpr
      nlinarith only [H,sq_nonneg (d i)]
  have hmoment : c*D/(8*q)≤∑ i,m i*max (d i) 0 := by
    have he : (∑ i,m i*max (d i) 0)=(∑ i,m i*max (-d i) 0) := by
      have HH : ∀ i,m i*d i=m i*max (d i) 0-m i*max (-d i) 0 := by
        intro i
        by_cases hd : 0≤d i
        · rw [max_eq_left hd,max_eq_right (neg_nonpos.mpr hd)]; ring
        · have hd' : d i≤0 := le_of_not_ge hd
          rw [max_eq_right hd',max_eq_left (neg_nonneg.mpr hd')]; ring
      simp_rw [HH] at hbar
      rw [Finset.sum_sub_distrib] at hbar
      linarith
    rw [he]
    calc
      c*D/(8*q)≤(∑ i∈right,m i)*(D/(8*q)) := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hrmass (by positivity : 0≤D/(8*q))
      _=∑ i∈right,m i*(D/(8*q)) := by rw [Finset.sum_mul]
      _≤∑ i∈right,m i*max (-d i) 0 := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left ((hrneg i hi).2.trans (le_max_left _ _)) (hm i).le)
      _≤∑ i,m i*max (-d i) 0 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ right) (fun i _ _ => mul_nonneg (hm i).le (le_max_right _ _))
  let a : ℝ := c*D/(8*(N:ℝ)*q)
  have ha : 0<a := by dsimp [a]; positivity
  have hsum_a : (∑ _i : ι,a)≤∑ i,m i*max (d i) 0 := by
    calc
      _=(Fintype.card ι:ℝ)*a := by simp
      _≤(N:ℝ)*a := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) ha.le
      _=c*D/(8*q) := by dsimp [a]; field_simp
      _≤_ := hmoment
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le hne hsum_a
  have hdi : 0<d i := by
    by_contra H
    rw [max_eq_right (le_of_not_gt H),mul_zero] at hi
    exact (not_le_of_gt ha) hi
  rw [max_eq_left hdi.le] at hi
  have hdub : d i≤3*D/(2*q) := by
    apply (le_div_iff₀ (by positivity : 0<2*q)).mpr
    have H := ho i hdi
    nlinarith only [H,sq_nonneg (d i)]
  have hmi : c/(12*(N:ℝ))≤ m i := by
    have HX := mul_le_mul_of_nonneg_left hdub (hm i).le
    have HY : c*D/(8*(N:ℝ)*q)≤ m i*(3*D/(2*q)) := hi.trans HX
    have hden : 0<8*(N:ℝ)*q := by positivity
    have HZ := (div_le_iff₀ hden).mp HY
    apply (div_le_iff₀ (by positivity : 0<12*(N:ℝ))).mpr
    have he : m i*(3*D/(2*q))*(8*(N:ℝ)*q)=12*(N:ℝ)*m i*D := by field_simp; ring
    rw [he] at HZ
    nlinarith only [HZ,hD]
  have hone : m i*B i≤1 := (Finset.single_le_sum
    (fun j _ => mul_nonneg (hm j).le (hB j)) (Finset.mem_univ i)).trans hcap
  have hBi : B i≤12*(N:ℝ)/c := by
    apply (le_div_iff₀ hc).mpr
    have HH := mul_le_mul_of_nonneg_right hmi (hB i)
    have HH' : c*B i/(12*(N:ℝ))≤1 := by
      calc
        c*B i/(12*(N:ℝ))=c/(12*(N:ℝ))*B i := by ring
        _≤ m i*B i := HH
        _≤1 := hone
    have := (div_le_iff₀ (by positivity : 0<12*(N:ℝ))).mp HH'
    nlinarith only [this]
  exact ⟨i,hdi,hmi,hi,hdub,hBi⟩

end WeakMTWTransport

end

end

end

end OAI
