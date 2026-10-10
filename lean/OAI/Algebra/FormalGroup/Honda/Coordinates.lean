import OAI.Algebra.FormalGroup.Honda.Recurrence

namespace OAI

noncomputable section

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction
variable {A B : Type*} [CommRing A] [CommRing B]

@[simp] lemma multiplication_zero (F : FormalGroup A) : multiplicationSeries F 0 = 0 := rfl

lemma multiplication_succ (F : FormalGroup A) (n : ℕ) :
    multiplicationSeries F (n+1) =
      F.toPowerSeries.subst ![multiplicationSeries F n, PowerSeries.X] := by
  change ((n+1) • variablePoint F).val = _
  rw [succ_nsmul]
  rfl

@[simp] lemma multiplication_constant (F : FormalGroup A) (n : ℕ) :
    (multiplicationSeries F n).constantCoeff = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [multiplication_succ]
    apply MvPowerSeries.constantCoeff_subst_eq_zero
      (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i; exact ih; exact PowerSeries.constantCoeff_X))
      (by intro i; fin_cases i; exact ih; exact PowerSeries.constantCoeff_X) F.zero_constantCoeff

lemma multiplication_map (F : FormalGroup A) (φ : A →+* B) (n : ℕ) :
    multiplicationSeries (F.map φ) n = (multiplicationSeries F n).map φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [multiplication_succ, multiplication_succ]
    change _ = MvPowerSeries.map φ (F.toPowerSeries.subst ![multiplicationSeries F n, PowerSeries.X])
    have hs : MvPowerSeries.HasSubst ![multiplicationSeries F n, PowerSeries.X] :=
      hasSubst_of_constantCoeff_zero (by
        intro i; fin_cases i; exact multiplication_constant F n; exact PowerSeries.constantCoeff_X)
    rw [map_subst hs, ih]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact (MvPowerSeries.map_X φ ()).symm

lemma log_multiplication (l : StrictLog (R := A)) (n : ℕ) :
    l.series.subst (multiplicationSeries l.formalGroup n) = n • l.series := by
  induction n with
  | zero =>
    simp only [multiplication_zero, zero_nsmul]
    exact PowerSeries.subst_zero_of_constantCoeff_zero l.constant_zero
  | succ n ih =>
    rw [multiplication_succ]
    change l.series.subst (l.law.subst ![_, PowerSeries.X]) = _
    rw [l.log_law_pair _ _ (multiplication_constant _ _) PowerSeries.constantCoeff_X, ih,
      PowerSeries.X_subst, succ_nsmul]

lemma multiplication_linear (l : StrictLog (R := A)) (n : ℕ) :
    (multiplicationSeries l.formalGroup n).coeff 1 = (n : A) := by
  have h := congrArg (PowerSeries.coeff 1) (log_multiplication l n)
  rw [show (PowerSeries.coeff 1 : PowerSeries A →ₗ[A] A) =
    MvPowerSeries.coeff (Finsupp.single () 1) from rfl,
    StrictLog.coeff_subst_linear _ _ (multiplication_constant _ _) (), l.linear_one,
    one_mul] at h
  change (multiplicationSeries l.formalGroup n).coeff 1 = n • l.series.coeff 1 at h
  simpa only [l.linear_one, nsmul_one] using h

end HeightThree.HondaCoordinates

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction
variable {R : Type*} [CommRing R]

lemma coeff_pow_below (g : PowerSeries R) (hg : g.constantCoeff = 0)
    (n j : ℕ) (hjn : j < n) : (g^n).coeff j = 0 := by
  exact PowerSeries.coeff_of_lt_order j (lt_of_lt_of_le
    (by exact_mod_cast hjn) (PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hg))

lemma coeff_pow_leading (g : PowerSeries R) (hg : g.constantCoeff = 0) (n : ℕ) :
    (g^n).coeff n = (g.coeff 1)^n := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [mul_pow]
  have hc (h : PowerSeries R) (n : ℕ) : (PowerSeries.X^n * h).coeff n = h.constantCoeff := by
    simpa only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff] using
      PowerSeries.coeff_X_pow_mul h n 0
  rw [hc]
  rw [show PowerSeries.X * h = PowerSeries.X^1 * h by simp, hc, map_pow]

lemma coeff_subst_before (l : StrictLog (R := R)) (q : ℕ)
    (hl : ∀ j, 1 < j → j < q → l.series.coeff j = 0)
    (g : PowerSeries R) (hg : g.constantCoeff = 0) (j : ℕ) (hj : j < q) :
    PowerSeries.coeff j (l.series.subst g) = g.coeff j := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 1, l.linear_one, one_smul, pow_one]
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [PowerSeries.coeff_zero_eq_constantCoeff, l.constant_zero, zero_smul]
  by_cases hnq : n < q
  · rw [hl n (by omega) hnq, zero_smul]
  · rw [coeff_pow_below g hg n j (by omega), smul_zero]

lemma coeff_subst_first (l : StrictLog (R := R)) (q : ℕ) (hq : 1 < q)
    (hl : ∀ j, 1 < j → j < q → l.series.coeff j = 0)
    (g : PowerSeries R) (hg : g.constantCoeff = 0) :
    PowerSeries.coeff q (l.series.subst g) = g.coeff q + l.series.coeff q * (g.coeff 1)^q := by
  classical
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero hg)]
  rw [finsum_eq_sum_of_support_subset _ (s := {1, q})]
  · rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using (ne_of_lt hq)), Finset.sum_singleton]
    dsimp
    simp only [l.linear_one, one_mul, pow_one, coeff_pow_leading g hg q]
  · intro n hn
    by_contra hn'
    have hh : n ≠ 1 ∧ n ≠ q := by simpa using hn'
    obtain ⟨hn1, hnq⟩ := hh
    apply hn
    change l.series.coeff n • (g^n).coeff q = 0
    by_cases hn0 : n = 0
    · subst n
      rw [PowerSeries.coeff_zero_eq_constantCoeff, l.constant_zero, zero_smul]
    by_cases hnlt : n < q
    · rw [hl n (by omega) hnlt, zero_smul]
    · rw [coeff_pow_below g hg n q (by omega), smul_zero]

theorem multiplication_first_coeff (l : StrictLog (R := R)) (q : ℕ) (hq : 1 < q)
    (hl : ∀ j, 1 < j → j < q → l.series.coeff j = 0) (n : ℕ) :
    (∀ j < q, (multiplicationSeries l.formalGroup n).coeff j =
      (n : R) * (PowerSeries.X : PowerSeries R).coeff j) ∧
    (multiplicationSeries l.formalGroup n).coeff q =
      l.series.coeff q * ((n : R) - (n : R)^q) := by
  have hg := multiplication_constant l.formalGroup n
  constructor
  · intro j hj
    have h := congrArg (PowerSeries.coeff j) (log_multiplication l n)
    rw [coeff_subst_before l q hl _ hg j hj, map_nsmul] at h
    by_cases hj1 : j = 1
    · subst j
      simpa [l.linear_one] using h
    by_cases hj0 : j = 0
    · subst j
      simp
    · rw [hl j (by omega) hj, smul_zero] at h
      simpa [PowerSeries.coeff_X, hj1] using h
  · have h := congrArg (PowerSeries.coeff q) (log_multiplication l n)
    rw [coeff_subst_first l q hq hl _ hg, multiplication_linear, map_nsmul,
      nsmul_eq_mul] at h
    linear_combination h

end HeightThree.HondaCoordinates

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction PTypical
variable {A B : Type*} [CommRing A] [CommRing B]

lemma numerator_one (p : ℕ) (ψ : A →+* A) (v : Fin 3 → A) :
    numerator p ψ v 1 = v 0 := by
  simp [numerator]

lemma numerator_two (p : ℕ) (ψ : A →+* A) (v : Fin 3 → A) (hv : v 0 = 0) :
    numerator p ψ v 2 = (p : A) * v 1 := by
  simp [numerator, Fin.sum_univ_three, hv]

lemma logarithm_coeff_below [Algebra ℚ B] (ι : A →+* B) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (v : Fin 3 → A) (m : ℕ)
    (hm : ∀ n, 0 < n → n < m → numerator p ψ v n = 0)
    (j : ℕ) (hj1 : 1 < j) (hj : j < p^m) :
    (logarithm ι p ψ v).coeff j = 0 := by
  by_cases hn : ∃ n : ℕ, p^n = j
  · obtain ⟨n, rfl⟩ := hn
    rw [logarithm, coeff_series_power p hp]
    have hnpos : 0 < n := by by_contra h; simp [show n = 0 by omega] at hj1
    rw [hm n hnpos ((Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp hj),
      map_zero, smul_zero]
  · exact coeff_series_outside p j _ hn

lemma rational_first_cancel [Algebra ℚ B] (p : ℕ) (hp : p ≠ 0)
    (q : ℕ) (hq : 0 < q) (v : B) :
    ((p : ℚ)⁻¹ • v) * ((p : B) - (p : B)^q) = v * (1 - (p : B)^(q-1)) := by
  have hc : algebraMap ℚ B (p : ℚ)⁻¹ * (p : B) = 1 := by
    rw [← map_natCast (algebraMap ℚ B), ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hp), map_one]
  rw [Algebra.smul_def, show q = (q-1)+1 by omega, pow_succ]
  calc
    _ = (algebraMap ℚ B (p : ℚ)⁻¹ * (p : B)) * v * (1-(p : B)^(q-1)) := by ring
    _ = _ := by simp only [hc, one_mul, Nat.add_sub_cancel]

theorem multiplication_first_integral [Algebra ℚ B] (ι : A →+* B)
    (hinj : Function.Injective ι) (F : FormalGroup A) (l : StrictLog (R := B))
    (hF : F.map ι = l.formalGroup) (p : ℕ) (hp : p ≠ 0)
    (q : ℕ) (hq : 1 < q) (v : A)
    (hl : ∀ j, 1 < j → j < q → l.series.coeff j = 0)
    (hlq : l.series.coeff q = (p : ℚ)⁻¹ • ι v) :
    (∀ j < q, (multiplicationSeries F p).coeff j = (p : A) *
      (PowerSeries.X : PowerSeries A).coeff j) ∧
    (multiplicationSeries F p).coeff q = v * (1-(p : A)^(q-1)) := by
  have hmap : (multiplicationSeries F p).map ι = multiplicationSeries l.formalGroup p := by
    rw [← multiplication_map, hF]
  have h := multiplication_first_coeff l q hq hl p
  constructor
  · intro j hj
    apply hinj
    have he := congrArg (PowerSeries.coeff j) hmap
    rw [PowerSeries.coeff_map, h.1 j hj] at he
    simpa only [map_mul, map_natCast, PowerSeries.coeff_X, apply_ite ι,
      map_one, map_zero] using he
  · apply hinj
    have he := congrArg (PowerSeries.coeff q) hmap
    rw [PowerSeries.coeff_map, h.2, hlq, rational_first_cancel p hp q (by omega)] at he
    simpa only [map_mul, map_sub, map_one, map_pow, map_natCast] using he

lemma integralFormalGroup_map [Algebra ℚ B] (ι : A →+* B) (hinj : Function.Injective ι)
    (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p) (v : Fin 3 → A) :
    (integralFormalGroup ι hinj p ψ χ hc hψ v).map ι =
      (heightThreeLog ι p hp.out.two_le ψ v).formalGroup := map_descendFormalGroup ..

theorem integralFormalGroup_height_one [Algebra ℚ B]
    (ι : A →+* B) (hinj : Function.Injective ι) (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p) (v : Fin 3 → A) :
    (∀ j < p, (multiplicationSeries (integralFormalGroup ι hinj p ψ χ hc hψ v) p).coeff j =
      (p : A) * (PowerSeries.X : PowerSeries A).coeff j) ∧
    (multiplicationSeries (integralFormalGroup ι hinj p ψ χ hc hψ v) p).coeff p =
      v 0 * (1 - (p : A)^(p-1)) := by
  apply multiplication_first_integral ι hinj _ (heightThreeLog ι p hp.out.two_le ψ v)
    (integralFormalGroup_map ..) p hp.out.ne_zero p hp.out.one_lt (v 0)
  · intro j hj1 hj
    exact logarithm_coeff_below ι p hp.out.two_le ψ v 1 (by intro n hn hn'; omega)
      j hj1 (by simpa using hj)
  · change (logarithm ι p ψ v).coeff p = _
    have he := coeff_series_power p hp.out.two_le
      (fun n => ((p : ℚ)⁻¹)^n • ι (numerator p ψ v n)) 1
    simpa only [logarithm, pow_one, numerator_one] using he

end HeightThree.HondaCoordinates

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction PTypical
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

theorem integralFormalGroup_height_two [Algebra ℚ B]
    (ι : A →+* B) (hinj : Function.Injective ι) (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p) (v : Fin 3 → A) (hv : v 0 = 0) :
    (∀ j < p^2, (multiplicationSeries (integralFormalGroup ι hinj p ψ χ hc hψ v) p).coeff j =
      (p : A) * (PowerSeries.X : PowerSeries A).coeff j) ∧
    (multiplicationSeries (integralFormalGroup ι hinj p ψ χ hc hψ v) p).coeff (p^2) =
      v 1 * (1 - (p : A)^(p^2-1)) := by
  have hp2 : 1 < p^2 := one_lt_pow₀ hp.out.one_lt (by decide)
  apply multiplication_first_integral ι hinj _ (heightThreeLog ι p hp.out.two_le ψ v)
    (integralFormalGroup_map ..) p hp.out.ne_zero (p^2) hp2 (v 1)
  · intro j hj1 hj
    apply logarithm_coeff_below ι p hp.out.two_le ψ v 2 _ j hj1 hj
    intro n hn hn'
    have : n = 1 := by omega
    simp [this, numerator_one, hv]
  · change (logarithm ι p ψ v).coeff (p^2) = _
    rw [logarithm, coeff_series_power p hp.out.two_le, numerator_two p ψ v hv,
      map_mul, map_natCast]
    have hs : ((p : ℚ)⁻¹)^2 • ((p : B) * ι (v 1)) = (p : ℚ)⁻¹ • ι (v 1) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← map_natCast (algebraMap ℚ B),
        ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    exact hs

lemma numerator_map (α : A →+* B) (p : ℕ) (ψ : A →+* A) (χ : B →+* B)
    (hc : χ.comp α = α.comp ψ) (v : Fin 3 → A) (n : ℕ) :
    α (numerator p ψ v n) = numerator p χ (α ∘ v) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [numerator]
    | succ n =>
      rw [numerator, numerator, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with hn
      · rw [map_mul, map_mul, map_pow, map_natCast, ← iterate_comp α ψ χ hc,
          ih (n-i.val) (by omega)]
        rfl
      · exact map_zero α

end HeightThree.HondaCoordinates

namespace HeightThree.LogarithmicConstruction.StrictLog
open MvPowerSeries
variable {A B : Type*} [CommRing A] [CommRing B]

def map (l : StrictLog (R := A)) (φ : A →+* B) : StrictLog (R := B) where
  series := l.series.map φ
  constant_zero := by
    change φ l.series.constantCoeff = 0
    rw [l.constant_zero, map_zero]
  linear_one := by simp only [PowerSeries.coeff_map, l.linear_one, map_one]

lemma formalGroup_map (l : StrictLog (R := A)) (φ : A →+* B) :
    l.formalGroup.map φ = (l.map φ).formalGroup := by
  apply FormalGroup.ext
  apply (l.map φ).subst_injective
    (PowerSeries.HasSubst.of_constantCoeff_zero (l.formalGroup.map φ).zero_constantCoeff)
    (PowerSeries.HasSubst.of_constantCoeff_zero (l.map φ).law_constant)
  change (l.series.map φ).subst (l.law.map φ) = (l.map φ).series.subst (l.map φ).law
  rw [(l.map φ).log_law, ← PowerSeries.map_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero l.law_constant), l.log_law]
  simp only [StrictLog.sumSeries, map_add, PowerSeries.map_subst (PowerSeries.HasSubst.X _),
    map_X, map]

@[ext] lemma ext {l m : StrictLog (R := A)} (h : l.series = m.series) : l = m := by
  cases l
  cases m
  congr

end HeightThree.LogarithmicConstruction.StrictLog

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction PTypical
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

lemma logarithm_map [Algebra ℚ B] [Algebra ℚ D]
    (ι : A →+* B) (κ : C →+* D) (α : A →+* C) (β : B →ₐ[ℚ] D)
    (hi : β.toRingHom.comp ι = κ.comp α) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (χ : C →+* C) (hc : χ.comp α = α.comp ψ) (v : Fin 3 → A) :
    (logarithm ι p ψ v).map β.toRingHom = logarithm κ p χ (α ∘ v) := by
  ext j
  rw [PowerSeries.coeff_map]
  by_cases hj : ∃ n : ℕ, p^n = j
  · obtain ⟨n, rfl⟩ := hj
    simp only [logarithm, coeff_series_power p hp]
    change β (((p : ℚ)⁻¹)^n • ι (numerator p ψ v n)) = _
    rw [β.map_smul_of_tower]
    congr 1
    change (β.toRingHom.comp ι) _ = _
    rw [hi]
    change κ (α _) = _
    rw [numerator_map α p ψ χ hc]
  · simp only [logarithm, coeff_series_outside p j _ hj, map_zero]

lemma heightThreeLog_map [Algebra ℚ B] [Algebra ℚ D]
    (ι : A →+* B) (κ : C →+* D) (α : A →+* C) (β : B →ₐ[ℚ] D)
    (hi : β.toRingHom.comp ι = κ.comp α) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (χ : C →+* C) (hc : χ.comp α = α.comp ψ) (v : Fin 3 → A) :
    (heightThreeLog ι p hp ψ v).map β.toRingHom = heightThreeLog κ p hp χ (α ∘ v) := by
  apply StrictLog.ext
  exact logarithm_map ι κ α β hi p hp ψ χ hc v

end HeightThree.HondaCoordinates

end

end OAI
