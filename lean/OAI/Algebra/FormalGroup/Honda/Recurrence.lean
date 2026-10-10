import OAI.Algebra.FormalGroup.Honda.IntegralLaw

namespace OAI

noncomputable section

namespace HeightThree.HondaConstruction
open MvPowerSeries PTypical LogarithmicConstruction
variable {A B : Type*} [CommRing A] [CommRing B]

theorem logarithm_functional_equation [Algebra ℚ B]
    (ι : A →+* B) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (v : Fin 3 → A) :
    defect p (by omega) χ.toRingHom (ι ∘ v) (logarithm ι p ψ v) = PowerSeries.X := by
  apply PowerSeries.ext
  intro j
  simp only [defect, map_sub, map_sum, (PowerSeries.coeff j).map_smul_of_tower,
    Function.comp_apply]
  by_cases hj : ∃ n : ℕ, p^n = j
  · obtain ⟨n, rfl⟩ := hj
    simp only [logarithm, twisted_series_coeff p hp, coeff_series_power p hp]
    cases n with
    | zero => simp [numerator, PowerSeries.coeff_X]
    | succ n =>
      have hpn : p^(n+1) ≠ 1 := by
        have : 1 < p^(n+1) := one_lt_pow₀ (by omega : 1 < p) (by omega)
        omega
      rw [PowerSeries.coeff_X, ite_eq_right hpn, logarithm_recurrence ι p (by omega) ψ χ hc]
      apply sub_eq_zero.mpr
      apply Finset.sum_congr rfl
      intro i _
      simp only [Nat.add_le_add_iff_right, Nat.add_sub_add_right, smul_eq_mul]
  · rw [logarithm, coeff_series_outside p j _ hj]
    have ht (i : Fin 3) : PowerSeries.coeff j
        ((twist p (by omega) χ.toRingHom ^ (i.val+1))
          (series p (fun n => ((p : ℚ)⁻¹)^n • ι (numerator p ψ v n)))) = 0 :=
      twisted_series_coeff_outside p hp χ.toRingHom _ (i.val+1) j hj
    simp only [ht, smul_zero, Finset.sum_const_zero, sub_zero]
    rw [PowerSeries.coeff_X, ite_eq_right]
    intro h
    exact hj ⟨0, by simpa using h.symm⟩

def heightThreeLog [Algebra ℚ B] (ι : A →+* B) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (v : Fin 3 → A) : StrictLog (R := B) where
  series := logarithm ι p ψ v
  constant_zero := logarithm_constant ι p hp ψ v
  linear_one := logarithm_linear ι p hp ψ v

def integralFormalGroup [Algebra ℚ B] (ι : A →+* B) (hinj : Function.Injective ι)
    (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p) (v : Fin 3 → A) : FormalGroup A :=
  descendFormalGroup ι hinj (heightThreeLog ι p hp.out.two_le ψ v).formalGroup
    (law_integral ι p ψ χ hc hψ v (heightThreeLog ι p hp.out.two_le ψ v)
      (series_integralNumerators ι p hp.out.two_le _)
      (logarithm_functional_equation ι p hp.out.two_le ψ χ hc v))

instance integralFormalGroup_isComm [Algebra ℚ B] (ι : A →+* B) (hinj : Function.Injective ι)
    (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p) (v : Fin 3 → A) :
    (integralFormalGroup ι hinj p ψ χ hc hψ v).IsComm :=
  by
  apply descendFormalGroup_isComm

end HeightThree.HondaConstruction

namespace HeightThree.HondaConstruction
open MvPowerSeries PTypical LogarithmicConstruction

abbrev IntegralBase := MvPowerSeries (Fin 2) ℤ
abbrev RationalBase := MvPowerSeries (Fin 2) ℚ

def coefficientInclusion : IntegralBase →+* RationalBase :=
  MvPowerSeries.map (Int.castRingHom ℚ)

lemma coefficientInclusion_injective : Function.Injective coefficientInclusion :=
  map_injective (Int.castRingHom ℚ) Int.cast_injective

def integralFrobenius (p : ℕ) (hp : p ≠ 0) : IntegralBase →+* IntegralBase :=
  (MvPowerSeries.expand p hp).toRingHom

def rationalFrobenius (p : ℕ) (hp : p ≠ 0) : RationalBase →ₐ[ℚ] RationalBase :=
  MvPowerSeries.expand p hp

lemma frobenius_compatible (p : ℕ) (hp : p ≠ 0) :
    (rationalFrobenius p hp).toRingHom.comp coefficientInclusion =
      coefficientInclusion.comp (integralFrobenius p hp) := by
  ext f d
  exact congrArg (coeff d) (MvPowerSeries.map_expand p hp (Int.castRingHom ℚ) f).symm

lemma integralFrobenius_congr (p : ℕ) [hp : Fact p.Prime] (a : IntegralBase) :
    (p : IntegralBase) ∣ integralFrobenius p hp.out.ne_zero a - a^p := by
  have hInt (a : ℤ) : (p : ℤ) ∣ (RingHom.id ℤ) a - a^p :=
    dvd_sub_comm.mp (Int.prime_dvd_pow_self_sub hp.out a)
  simpa [MvPowerSeries.map_id, integralFrobenius] using
    frobenius_lift_series p (RingHom.id ℤ) hInt a

def parameters : Fin 3 → IntegralBase := ![X 0, X 1, 1]

def integralHonda (p : ℕ) [hp : Fact p.Prime] : FormalGroup IntegralBase :=
  integralFormalGroup coefficientInclusion coefficientInclusion_injective p
    (integralFrobenius p hp.out.ne_zero) (rationalFrobenius p hp.out.ne_zero)
    (frobenius_compatible p hp.out.ne_zero) (integralFrobenius_congr p) parameters

instance integralHonda_isComm (p : ℕ) [hp : Fact p.Prime] : (integralHonda p).IsComm := by
  unfold integralHonda
  exact integralFormalGroup_isComm ..

def reducedHonda (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] :
    FormalGroup (MvPowerSeries (Fin 2) K) :=
  (integralHonda p).map (MvPowerSeries.map (Int.castRingHom K))

end HeightThree.HondaConstruction

namespace HeightThree.HondaConstruction
open MvPowerSeries
variable {A B : Type*} [CommRing A] [CommRing B]

instance mapFormalGroup_isComm (F : FormalGroup A) [F.IsComm] (f : A →+* B) :
    (F.map f).IsComm where
  comm := by
    change F.toPowerSeries.map f = (F.toPowerSeries.map f).subst ![X 1, X 0]
    have hc := congrArg (MvPowerSeries.map f) (FormalGroup.IsComm.comm (F := F))
    rw [map_subst HasSubst.X_X] at hc
    rw [hc]
    congr 1
    funext i
    fin_cases i <;> simp

instance reducedHonda_isComm (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] :
    (reducedHonda p K).IsComm := mapFormalGroup_isComm ..

end HeightThree.HondaConstruction

end

end OAI
