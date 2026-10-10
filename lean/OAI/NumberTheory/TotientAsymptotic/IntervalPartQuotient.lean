import OAI.NumberTheory.TotientAsymptotic.PrimeBandProducts
import OAI.NumberTheory.TotientAsymptotic.IntervalAvoidance

namespace OAI

/-! Removing the complete interval part leaves an integer sifted by that interval. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_idempotent (n : ℕ) (U V : ℝ) :
    partBetween (partBetween n U V) U V = partBetween n U V := by
  have he : (partBetween n U V).primeFactorsList.filter
      (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ V) = (partBetween n U V).primeFactorsList := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true (partBetween_support n U V hp)
  rw [partBetween,he,Nat.prod_primeFactorsList (partBetween_pos n U V).ne']

lemma prime_dvd_partBetween {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    {U V : ℝ} (hU : U < (p:ℝ)) (hV : (p:ℝ) ≤ V) (hpn : p ∣ n) :
    p ∣ partBetween n U V := by
  apply Nat.dvd_of_mem_primeFactorsList
  apply (partBetween_factors n U V).mem_iff.mp
  apply List.mem_filter.mpr
  exact ⟨(Nat.mem_primeFactorsList_iff_dvd hn.ne' hp).mpr hpn,decide_eq_true ⟨hU,hV⟩⟩

lemma interval_part_quotient_avoids {n : ℕ} (hn : 0 < n) (U V : ℝ) :
    ∀ p : ℕ,p.Prime → U < (p:ℝ) → (p:ℝ) ≤ V → ¬ p ∣ n/partBetween n U V := by
  let m := partBetween n U V
  have hm : 0 < m := partBetween_pos n U V
  have hd : m ∣ n := partBetween_dvd hn.ne' U V
  have hq : 0 < n/m := Nat.div_pos (Nat.le_of_dvd hn hd) hm
  have he : m*(n/m)=n := Nat.mul_div_cancel' hd
  have hb := congrArg (fun r => partBetween r U V) he
  rw [partBetween_mul hm.ne' hq.ne',partBetween_idempotent] at hb
  have hone : partBetween (n/m) U V=1 := by
    have hh : m*partBetween (n/m) U V=m*1 := by simpa only [mul_one] using hb
    exact Nat.eq_of_mul_eq_mul_left hm hh
  intro p hp hU hV hpn
  have hpd := prime_dvd_partBetween hq hp hU hV hpn
  rw [hone] at hpd
  exact hp.not_dvd_one hpd

lemma interval_part_fiber_count {S X z m : ℕ} (hm : 0 < m) (hS : 2 ≤ S)
    (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ n ≤ X ∧ partBetween n S z=m) :
    Q.card ≤ (intervalSifted S (X/m) z).card := by
  classical
  have hd (n : ℕ) (hn : n ∈ Q) : m ∣ n := by
    have hh := partBetween_dvd (hQ n hn).1.ne' S z
    rwa [(hQ n hn).2.2] at hh
  have hi : Set.InjOn (fun n : ℕ => n/m) (↑Q : Set ℕ) := by
    intro n hn r hr he
    have hn' := Nat.mul_div_cancel' (hd n hn)
    have hr' := Nat.mul_div_cancel' (hd r hr)
    dsimp only at he
    rw [he] at hn'
    exact hn'.symm.trans hr'
  have hs : Q.image (fun n => n/m) ⊆ intervalSifted S (X/m) z := by
    intro q hq
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
    have h := hQ n hn
    apply (mem_intervalSifted hS).mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd h.1 (hd n hn)) hm,
      Nat.div_le_div_right h.2.1⟩,?_⟩
    have ha := interval_part_quotient_avoids h.1 (S:ℝ) (z:ℝ)
    rw [h.2.2] at ha
    intro p hp hSp hpz
    exact ha p hp (by exact_mod_cast hSp) (by exact_mod_cast hpz)
  rw [← Finset.card_image_of_injOn hi]
  exact Finset.card_le_card hs

theorem interval_part_fiber_bound : ∃ C : ℝ,0 < C ∧ ∀ S X z m : ℕ,
    0 < m → 2 ≤ S → S ≤ z → z ≤ X/m → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ X ∧ partBetween n S z=m) →
    (Q.card:ℝ) ≤ C*(X:ℝ)/(m:ℝ)*Real.log S/Real.log z := by
  obtain ⟨C,hC,hbound⟩ := interval_avoidance_count
  refine ⟨C,hC,?_⟩
  intro S X z m hm hS hSz hz Q hQ
  have hlS : 0 ≤ Real.log S := Real.log_nonneg (by exact_mod_cast (show 1 ≤ S by omega))
  have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hdiv : ((X/m:ℕ):ℝ) ≤ (X:ℝ)/m := Nat.cast_div_le
  calc
    _ ≤ ((intervalSifted S (X/m) z).card:ℝ) := Nat.cast_le.mpr (interval_part_fiber_count hm hS Q hQ)
    _ ≤ C*(X/m:ℕ)*Real.log S/Real.log z := hbound S (X/m) z hS hSz hz
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hdiv hC.le
      have hh' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hlS) hlz.le
      convert hh' using 1; ring

end TotientAsymptotic

end

end OAI
