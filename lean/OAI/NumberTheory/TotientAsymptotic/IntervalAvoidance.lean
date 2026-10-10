import OAI.NumberTheory.TotientAsymptotic.IntervalSieveEuler
import OAI.NumberTheory.TotientAsymptotic.SieveCutoff

namespace OAI

/-! Ford's interval-avoidance sieve, with natural-number endpoints. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma intervalSifted_card_le (S X z : ℕ) : (intervalSifted S X z).card ≤ X := by
  simpa [intervalSifted] using Finset.card_le_card
    (Finset.filter_subset (fun n => (∏ p ∈ intervalSievePrimes S z,p).Coprime n) (Finset.Icc 1 X))

lemma intervalSifted_antitone {S X z w : ℕ} (hwz : w ≤ z) :
    intervalSifted S X z ⊆ intervalSifted S X w := by
  intro n hn
  obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn,?_⟩
  apply hcop.of_dvd_left
  apply Finset.prod_dvd_prod_of_subset _ _ id
  intro p hp
  obtain ⟨hpw,hpp,hp2,hSp⟩ := mem_intervalSievePrimes.mp hp
  exact mem_intervalSievePrimes.mpr ⟨hpw.trans hwz,hpp,hp2,hSp⟩

lemma mem_intervalSifted {S X z n : ℕ} (hS : 2 ≤ S) :
    n ∈ intervalSifted S X z ↔ n ∈ Finset.Icc 1 X ∧
      ∀ p : ℕ,p.Prime → S < p → p ≤ z → ¬ p ∣ n := by
  constructor
  · intro hn
    obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
    refine ⟨hn,?_⟩
    intro p hp hSp hpz hpn
    have hmem := mem_intervalSievePrimes.mpr ⟨hpz,hp,by omega,hSp⟩
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem) hpn) hcop
  · rintro ⟨hn,havoid⟩
    refine Finset.mem_filter.mpr ⟨hn,?_⟩
    apply Nat.coprime_of_dvd
    intro p hp hpd hpn
    obtain ⟨q,hq,hpq⟩ := hp.prime.exists_mem_finset_dvd hpd
    have hqq := (mem_intervalSievePrimes.mp hq).2.1
    have he := (Nat.prime_dvd_prime_iff_eq hp hqq).mp hpq
    subst q
    have hmem := mem_intervalSievePrimes.mp hq
    exact havoid p hp hmem.2.2.2 hmem.1 hpn

/-- All cutoffs are uniform. The proof only uses the already proved concrete
Selberg error, finite Euler product, and explicit small-power cutoff. -/
theorem interval_avoidance_count : ∃ C : ℝ,0 < C ∧ ∀ S X z : ℕ,
    2 ≤ S → S ≤ z → z ≤ X →
      ((intervalSifted S X z).card:ℝ) ≤ C*X*Real.log S/Real.log z := by
  obtain ⟨C,hC,hbound⟩ := intervalSifted_bound
  let K : ℝ := 256*Real.log 4
  let D : ℝ := 4*K+C*K+192
  have hc : 1 ≤ Real.log (4:ℝ) := by
    have hh := Real.log_two_gt_d9
    have he : Real.log (4:ℝ)=2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith
  have hK : 1 ≤ K := by dsimp [K]; nlinarith
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro S X z hS hSz hzX
  have hS1 : (1:ℝ) < S := by exact_mod_cast (show 1 < S by omega)
  have hz1 : (1:ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hX1 : (1:ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlS : 0 < Real.log S := Real.log_pos hS1
  have hlz : 0 < Real.log z := Real.log_pos hz1
  have hLX : 0 < Real.log X := Real.log_pos hX1
  have hSl : (1/2:ℝ) ≤ Real.log S := by
    have hh : Real.log (2:ℝ) ≤ Real.log S :=
      Real.log_le_log (by norm_num : (0:ℝ)<2) (by exact_mod_cast hS)
    linarith [Real.log_two_gt_d9]
  have hlzX : Real.log z ≤ Real.log X := Real.log_le_log (by linarith) (by exact_mod_cast hzX)
  have hcard : ((intervalSifted S X z).card:ℝ) ≤ X := Nat.cast_le.mpr (intervalSifted_card_le S X z)
  have hD : 2*K ≤ D := by
    dsimp [D]
    have hh : 0 ≤ C*K := mul_nonneg hC.le (by linarith only [hK])
    linarith only [hh,hK]
  by_cases hlarge : 512*Real.log 4 ≤ Real.log X
  · let Z := shiftedPrimeCutoff (Real.log X)
    have hZ := shiftedPrimeCutoff_bounds hlarge
    have hLX1 : 1 ≤ Real.log X := by nlinarith only [hlarge,hc]
    have hlogZ : Real.log X/K ≤ Real.log Z := hZ.2.1
    by_cases hSZ : S ≤ Z
    · let w := min z Z
      have hw : S ≤ w := le_min hSz hSZ
      have hw2 : 2 ≤ w := hS.trans hw
      have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
      have hwz : w ≤ z := min_le_left _ _
      have hwZ : w ≤ Z := min_le_right _ _
      have hscale : 4*Real.log 4*(2+Real.log w) ≤
          Real.log (Real.exp (Real.log X/4)) := by
        have hm := Real.log_le_log (by exact_mod_cast (show 0 < w by omega))
          (by exact_mod_cast hwZ : (w:ℝ) ≤ Z)
        have hh := shiftedPrimeCutoff_scale hlarge
        have hnon : 0 ≤ Real.log 4*(2+Real.log w) := by positivity
        nlinarith
      have hy : 1 < Real.exp (Real.log X/4) := Real.one_lt_exp_iff.mpr (by positivity)
      have hf := hbound S X w hS hw _ hy hscale
      have hlogw : Real.log z/K ≤ Real.log w := by
        rcases le_total z Z with hh|hh
        · have he : w=z := min_eq_left hh
          rw [he]
          exact div_le_self hlz.le hK
        · have he : w=Z := min_eq_right hh
          rw [he]
          exact (div_le_div_of_nonneg_right hlzX (by positivity)).trans hlogZ
      have hmain : C*X*Real.log S/Real.log w ≤ C*K*X*Real.log S/Real.log z := by
        have hh := div_le_div_of_nonneg_left
          (show 0 ≤ C*X*Real.log S by positivity) (by positivity : 0 < Real.log z/K) hlogw
        calc
          _ ≤ C*X*Real.log S/(Real.log z/K) := hh
          _ = _ := by field_simp
      have herr := shiftedPrimeCutoff_error hlarge
      rw [Real.exp_log (by linarith : (0:ℝ)<X)] at herr
      have herr' : 2*(Real.exp (Real.log X/4))^3 ≤ 96*(X:ℝ)/(Real.log X)^2 := by
        have hnon : (0:ℝ) ≤ shiftedPrimeCutoff (Real.log X) := Nat.cast_nonneg _
        linarith
      have hfrac : (X:ℝ)/(Real.log X)^2 ≤ 2*X*Real.log S/Real.log z := by
        have hnum : Real.log z ≤ 2*Real.log S*(Real.log X)^2 := by
          have hsq : Real.log X ≤ (Real.log X)^2 := by nlinarith
          nlinarith [sq_nonneg (Real.log X)]
        apply (div_le_div_iff₀ (sq_pos_of_pos hLX) hlz).mpr
        have hh := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ X)
        nlinarith
      have herror : 2*(Real.exp (Real.log X/4))^3 ≤ 192*X*Real.log S/Real.log z := by
        have hh := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0:ℝ) ≤ 96)
        apply herr'.trans
        convert hh using 1 <;> ring
      have hsub : ((intervalSifted S X z).card:ℝ) ≤ (intervalSifted S X w).card :=
        Nat.cast_le.mpr (Finset.card_le_card (intervalSifted_antitone hwz))
      have hfin := hsub.trans (hf.trans (add_le_add hmain herror))
      have hcoef : C*K+192 ≤ D := by dsimp [D]; linarith only [hK]
      have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (X:ℝ)*Real.log S/Real.log z by positivity)
      calc
        _ ≤ (C*K+192)*X*Real.log S/Real.log z := by
          convert hfin using 1; ring
        _ ≤ _ := by convert hm using 1 <;> ring
    · have hlogS : Real.log X/K ≤ Real.log S := by
        exact hlogZ.trans (Real.log_le_log (by exact_mod_cast (show 0 < Z by omega))
          (by exact_mod_cast (show Z ≤ S by omega)))
      have hnum : Real.log z ≤ D*Real.log S := by
        have hh := (div_le_iff₀ (by positivity : 0<K)).mp hlogS
        have hDK : K ≤ D := by linarith
        have hm := mul_le_mul_of_nonneg_right hDK hlS.le
        linarith only [hh,hm,hlzX]
      apply hcard.trans
      apply (le_div_iff₀ hlz).mpr
      have hh := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ X)
      convert hh using 1; ring
  · have hnum : Real.log z ≤ D*Real.log S := by
      have hl : Real.log X ≤ 2*K := by dsimp [K]; linarith
      have hD' : 4*K ≤ D := by
        dsimp [D]
        have hh : 0 ≤ C*K := mul_nonneg hC.le (by linarith only [hK])
        linarith only [hh]
      nlinarith only [hlzX,hl,hD',hSl,hK]
    apply hcard.trans
    apply (le_div_iff₀ hlz).mpr
    have hh := mul_le_mul_of_nonneg_left hnum (by positivity : (0:ℝ) ≤ X)
    convert hh using 1; ring

end TotientAsymptotic

end

end OAI
