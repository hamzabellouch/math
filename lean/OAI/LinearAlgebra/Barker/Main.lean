import OAI.LinearAlgebra.Barker.Parity
import OAI.LinearAlgebra.Barker.Wraparound
import OAI.LinearAlgebra.Barker.PeriodicModFour
import OAI.LinearAlgebra.CirculantHadamard.Main

namespace OAI

namespace CirculantHadamard.Barker

theorem four_dvd_length {n : ℕ} [NeZero n] {h : Fin n → ℤ}
    (hb : IsBarker h) (hn : Even n) (hnlarge : 2 < n) : (4 : ℤ) ∣ (n : ℤ) := by
  let a : Fin n := ⟨2, hnlarge⟩
  have ha : a ≠ 0 := by
    intro heq
    have hv := congrArg Fin.val heq
    change 2 = 0 at hv
    omega
  have ht : aperiodic h 2 = 0 :=
    aperiodic_even_shift_zero hb hn 2 (by decide) (by omega) hnlarge
  have hnsub : Even (n - 2) := by
    obtain ⟨u, hu⟩ := hn
    exact ⟨u - 1, by omega⟩
  have ht' : aperiodic h (n - 2) = 0 :=
    aperiodic_even_shift_zero hb hn (n - 2) hnsub (by omega) (by omega)
  have hpa : periodic h a = 0 := by
    rw [periodic_eq_aperiodic_add h a ha]
    change aperiodic h 2 + aperiodic h (n - 2) = 0
    rw [ht, ht', add_zero]
  have hd := periodic_mod_four h hb.1 a
  rw [hpa, zero_sub] at hd
  exact dvd_neg.mp hd

theorem periodic_offpeak_zero {n : ℕ} [NeZero n] {h : Fin n → ℤ}
    (hb : IsBarker h) (hn : Even n) (hnlarge : 2 < n)
    (a : Fin n) (ha : a ≠ 0) : periodic h a = 0 := by
  have ha0 : 0 < a.val := by
    by_contra hnot
    have hz : a.val = 0 := by omega
    apply ha
    apply Fin.ext
    simpa using hz
  have hab := aperiodic_bounds hb a.val ha0 a.isLt
  have hac := aperiodic_bounds hb (n - a.val) (by omega) (by omega)
  have hp := periodic_eq_aperiodic_add h a ha
  obtain ⟨u, hu⟩ := periodic_mod_four h hb.1 a
  obtain ⟨v, hv⟩ := four_dvd_length hb hn hnlarge
  omega

theorem existsRealCirculantHadamard_of_even_barker {n : ℕ} {h : Fin n → ℤ}
    (hb : IsBarker h) (hn : Even n) (hnlarge : 2 < n) :
    ExistsRealCirculantHadamard n := by
  let : NeZero n := ⟨by omega⟩
  apply existsReal_iff_integer_autocorrelation.mpr
  refine ⟨h, hb.1, ?_⟩
  intro a
  change periodic h a = if a = 0 then (n : ℤ) else 0
  by_cases ha : a = 0
  · subst a
    simp [periodic_zero h hb.1]
  · rw [ite_eq_right ha]
    exact periodic_offpeak_zero hb hn hnlarge a ha

theorem even_length_eq_two_or_four {n : ℕ} (h : Fin n → ℤ)
    (hnpos : 0 < n) (hn : Even n) (hb : IsBarker h) : n = 2 ∨ n = 4 := by
  by_cases hsmall : n ≤ 2
  · left
    obtain ⟨u, hu⟩ := hn
    omega
  · have hnlarge : 2 < n := by omega
    have hH := existsRealCirculantHadamard_of_even_barker hb hn hnlarge
    have hc := (exists_iff_order_one_or_four n hnpos).mp hH
    right
    omega

end CirculantHadamard.Barker

end OAI
