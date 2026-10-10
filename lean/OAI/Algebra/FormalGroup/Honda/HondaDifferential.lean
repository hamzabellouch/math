import OAI.Algebra.FormalGroup.Honda.Differential
import OAI.Algebra.FormalGroup.Honda.SpecialFiber

namespace OAI

noncomputable section

namespace HeightThree.HondaDifferentials
open MvPowerSeries PTypical HondaConstruction HondaCoordinates HondaSpecialFiber
open PowerSeriesDifferential LogarithmicConstruction

lemma special_numerator_dvd (p : ℕ) (n : ℕ) (hn : 0 < n) :
    (p : ℤ)^2 ∣ numerator p (RingHom.id ℤ) specialParameters n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [numerator, Fin.sum_univ_three, specialParameters, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.val_zero, Fin.val_one,
    Fin.val_two, mul_zero, zero_mul, ite_self, zero_add]
  split_ifs <;> simp

lemma special_derivative_coeff_power (p : ℕ) [hp : Fact p.Prime]
    (n j : ℕ) (hj : n+1 = p^j) :
    (PowerSeries.derivative (specialLog p).series).coeff n =
      ((numerator p (RingHom.id ℤ) specialParameters j : ℤ) : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : (n : ℚ)+1 = (p : ℚ)^j := by exact_mod_cast hj
  rw [PowerSeries.coeff_derivative, he]
  change (logarithm (Int.castRingHom ℚ) p (RingHom.id ℤ) specialParameters).coeff (n+1) *
    (p : ℚ)^j = _
  rw [hj]
  simp only [logarithm, coeff_series_power p hp.out.two_le, smul_eq_mul,
    inv_pow]
  change ((p : ℚ)^j)⁻¹ * ((numerator p (RingHom.id ℤ) specialParameters j : ℤ) : ℚ) * (p : ℚ)^j = _
  field_simp

lemma special_derivative_integral (p : ℕ) [hp : Fact p.Prime] :
    ∃ b : PowerSeries ℤ,
      PowerSeries.derivative (specialLog p).series =
        (1 + (p : PowerSeries ℚ)^2 * b.map (Int.castRingHom ℚ)) := by
  have hc (n : ℕ) : ∃ b : ℤ,
      (PowerSeries.derivative (specialLog p).series).coeff n =
        (if n=0 then 1 else 0) + (p : ℚ)^2 * b := by
    by_cases hn : n=0
    · subst n
      refine ⟨0, ?_⟩
      simp [PowerSeries.coeff_derivative, (specialLog p).linear_one]
    · by_cases hj : ∃ j, p^j = n+1
      · obtain ⟨j, hj⟩ := hj
        have hjpos : 0 < j := by
          by_contra h
          have hj0 : j=0 := by omega
          rw [hj0, pow_zero] at hj
          omega
        obtain ⟨b, hb⟩ := special_numerator_dvd p j hjpos
        refine ⟨b, ?_⟩
        rw [special_derivative_coeff_power p n j hj.symm, hb, ite_eq_right hn, zero_add,
          Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      · refine ⟨0, ?_⟩
        rw [PowerSeries.coeff_derivative]
        dsimp [specialLog, heightThreeLog, logarithm]
        simp only [coeff_series_outside p (n+1) _ hj, zero_mul, ite_eq_right hn,
          mul_zero, add_zero]
  choose b hb using hc
  refine ⟨PowerSeries.mk b, ?_⟩
  ext n
  rw [hb]
  rw [show (p : PowerSeries ℚ)^2 = PowerSeries.C ((p : ℚ)^2) by simp,
    map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rfl

lemma law_map_special (p : ℕ) [hp : Fact p.Prime] :
    (integralSpecial p).toPowerSeries.map (Int.castRingHom ℚ) = (specialLog p).law := by
  exact congrArg FormalGroup.toPowerSeries (integralSpecial_map p)

lemma map_unisubst {R S σ : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (f : PowerSeries R) (a : MvPowerSeries σ R)
    (ha : PowerSeries.HasSubst a) :
    (f.subst a).map ρ = (f.map ρ).subst (a.map ρ) :=
  MvPowerSeries.map_subst ha.const f

lemma special_partial_integral (p : ℕ) [hp : Fact p.Prime] (i : Fin 2) :
    ∃ b : MvPowerSeries (Fin 2) ℤ,
      pderiv i (integralSpecial p).toPowerSeries = 1 + (p : MvPowerSeries (Fin 2) ℤ)^2*b := by
  obtain ⟨b, hb⟩ := special_derivative_integral p
  let F := (integralSpecial p).toPowerSeries
  let l := specialLog p
  have hlog := congrArg (pderiv i) l.log_law
  have hr : pderiv i l.sumSeries = (PowerSeries.derivative l.series).subst (X i) := by
    dsimp [StrictLog.sumSeries]
    rw [map_add, pderiv_subst l.series (X 0) (by simp) i,
      pderiv_subst l.series (X 1) (by simp) i]
    fin_cases i <;> simp
  rw [pderiv_subst _ _ l.law_constant, hr, hb] at hlog
  have hbF : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero (integralSpecial p).zero_constantCoeff
  have hf : (1 + (p : MvPowerSeries (Fin 2) ℤ)^2 * b.subst F) * pderiv i F =
      1 + (p : MvPowerSeries (Fin 2) ℤ)^2 * b.subst (X i) := by
    apply HeightThree.HondaConstruction.map_injective (Int.castRingHom ℚ) Int.cast_injective
    have hF : F.map (Int.castRingHom ℚ) = l.law := law_map_special p
    simp only [map_mul, map_add, map_one, map_pow, map_natCast, map_unisubst _ _ _ hbF,
      map_unisubst _ _ _ (PowerSeries.HasSubst.X i), map_X, ← pderiv_map, hF]
    simpa only [← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero l.law_constant),
      ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X i),
      map_add, map_one, map_mul, map_pow, map_natCast] using hlog
  refine ⟨b.subst (X i) - b.subst F * pderiv i F, ?_⟩
  calc
    pderiv i F = ((1 + (p : MvPowerSeries (Fin 2) ℤ)^2 * b.subst F) * pderiv i F) -
      (p : MvPowerSeries (Fin 2) ℤ)^2 * b.subst F * pderiv i F := by ring
    _ = _ := by rw [hf]; ring

lemma coeff_mul_index_dvd {σ : Type*} (f : MvPowerSeries σ ℤ)
    (q : ℤ) (h : ∀ i, ∃ b, pderiv i f = C q * b)
    (d : σ →₀ ℕ) (i : σ) : q ∣ coeff d f * (d i : ℤ) := by
  classical
  by_cases hi : d i = 0
  · simp [hi]
  let e := d.erase i + Finsupp.single i (d i - 1)
  have he : e + Finsupp.single i 1 = d := by
    ext j
    by_cases hj : j = i
    · subst j; simp [e, Nat.sub_add_cancel (by omega : 1 ≤ d i)]
    · simp [e, hj]
  have hei : (e i : ℤ) + 1 = (d i : ℤ) := by
    have hh := congrArg (fun d : σ →₀ ℕ => d i) he
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hh
    exact_mod_cast hh
  obtain ⟨b, hb⟩ := h i
  have hh := congrArg (coeff e) hb
  rw [coeff_pderiv, he, hei, coeff_C_mul] at hh
  exact ⟨coeff e b, hh⟩

lemma special_nonlinear_support (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] [CharP K p] (d : Fin 2 →₀ ℕ)
    (hd : coeff d ((hondaLaw p K).toPowerSeries - X 0 - X 1) ≠ 0) :
    ∀ i, p^2 ∣ d i := by
  let D := (integralSpecial p).toPowerSeries - X 0 - X 1
  have hD (i : Fin 2) : ∃ b, pderiv i D = C ((p : ℤ)^2) * b := by
    obtain ⟨b, hb⟩ := special_partial_integral p i
    refine ⟨b, ?_⟩
    dsimp [D]
    rw [map_sub, map_sub, hb]
    fin_cases i <;> simp
  have hn : ¬(p : ℤ) ∣ coeff d D := by
    intro hn
    apply hd
    have hz := (CharP.intCast_eq_zero_iff K p (coeff d D)).mpr hn
    have hDm : D.map (Int.castRingHom K) = (hondaLaw p K).toPowerSeries - X 0 - X 1 := by
      simp [D, hondaLaw]
    rw [← hDm, coeff_map]
    exact hz
  have hc : IsCoprime (p : ℤ) (coeff d D) :=
    (Prime.coprime_iff_not_dvd (Int.prime_iff_natAbs_prime.mpr (by simpa using hp.out))).mpr hn
  intro i
  have hh := hc.pow_left.dvd_of_dvd_mul_left (coeff_mul_index_dvd D ((p:ℤ)^2) hD d i)
  exact Int.natCast_dvd_natCast.mp (by simpa only [Nat.cast_pow] using hh)

lemma exists_expand_of_support {σ R : Type*} [CommRing R] (f : MvPowerSeries σ R)
    (q : ℕ) (hq : q ≠ 0) (h : ∀ d, coeff d f ≠ 0 → ∀ i, q ∣ d i) :
    ∃ g, expand q hq g = f := by
  classical
  let g : MvPowerSeries σ R := fun d => coeff (q • d) f
  refine ⟨g, ?_⟩
  ext d
  by_cases hd : ∀ i, q ∣ d i
  · let e := d.mapRange (fun n => n/q) (Nat.zero_div q)
    have he : q • e = d := by
      ext i
      simp only [Finsupp.smul_apply, smul_eq_mul, e, Finsupp.mapRange_apply]
      exact Nat.mul_div_cancel' (hd i)
    rw [← he, coeff_expand_smul]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.mp hd
    rw [coeff_expand_of_not_dvd _ _ _ hi]
    by_contra hf
    exact hi (h d (Ne.symm hf) i)

theorem honda_nonlinear_expand (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] [CharP K p] :
    ∃ H : MvPowerSeries (Fin 2) K,
      (hondaLaw p K).toPowerSeries = X 0 + X 1 + expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H := by
  obtain ⟨H, hH⟩ := exists_expand_of_support
    ((hondaLaw p K).toPowerSeries - X 0 - X 1) (p^2) (pow_ne_zero _ hp.out.ne_zero)
    (special_nonlinear_support p K)
  exact ⟨H, by rw [hH]; ring⟩

end HeightThree.HondaDifferentials

end

end OAI
