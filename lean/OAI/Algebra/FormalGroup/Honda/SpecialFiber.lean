import OAI.Algebra.FormalGroup.Honda.HeightTwo

namespace OAI

noncomputable section

namespace HeightThree.HondaSpecialFiber
open MvPowerSeries HondaConstruction HondaTarget HondaCoordinates LogarithmicConstruction PTypical

def augmentation (R : Type*) [CommRing R] : MvPowerSeries (Fin 2) R →ₐ[R] R where
  __ := MvPowerSeries.constantCoeff
  commutes' _ := rfl

lemma integerFrobenius (p : ℕ) [hp : Fact p.Prime] (a : ℤ) :
    (p : ℤ) ∣ (RingHom.id ℤ) a - a^p :=
  dvd_sub_comm.mp (Int.prime_dvd_pow_self_sub hp.out a)

def specialParameters : Fin 3 → ℤ := ![0,0,1]

def integralSpecial (p : ℕ) [hp : Fact p.Prime] : FormalGroup ℤ :=
  integralFormalGroup (Int.castRingHom ℚ) Int.cast_injective p (RingHom.id ℤ)
    (AlgHom.id ℚ ℚ) (by rfl) (integerFrobenius p) specialParameters

def specialLog (p : ℕ) [hp : Fact p.Prime] : StrictLog (R := ℚ) :=
  heightThreeLog (Int.castRingHom ℚ) p hp.out.two_le (RingHom.id ℤ) specialParameters

lemma integralSpecial_map (p : ℕ) [hp : Fact p.Prime] :
    (integralSpecial p).map (Int.castRingHom ℚ) = (specialLog p).formalGroup :=
  integralFormalGroup_map ..

lemma integralHonda_specialize (p : ℕ) [hp : Fact p.Prime] :
    (integralHonda p).map MvPowerSeries.constantCoeff = integralSpecial p := by
  have hi : (augmentation ℚ).toRingHom.comp coefficientInclusion =
      (Int.castRingHom ℚ).comp MvPowerSeries.constantCoeff := by
    ext f
    rfl
  have hψ : (RingHom.id ℤ).comp (MvPowerSeries.constantCoeff (σ := Fin 2)) =
      MvPowerSeries.constantCoeff.comp (integralFrobenius p hp.out.ne_zero) := by
    ext f
    exact (constantCoeff_expand p hp.out.ne_zero f).symm
  have hv : MvPowerSeries.constantCoeff ∘ parameters = specialParameters := by
    funext i; fin_cases i <;> simp [parameters, specialParameters]
  have hh := integralFormalGroup_natural coefficientInclusion coefficientInclusion_injective
    (Int.castRingHom ℚ) Int.cast_injective MvPowerSeries.constantCoeff
    (augmentation ℚ) hi p
    (integralFrobenius p hp.out.ne_zero) (rationalFrobenius p hp.out.ne_zero)
    (frobenius_compatible p hp.out.ne_zero) (integralFrobenius_congr p)
    (RingHom.id ℤ) (AlgHom.id ℚ ℚ) (by rfl) (integerFrobenius p) hψ parameters
  rw [hv] at hh
  exact hh

lemma specialLog_functional (p : ℕ) [hp : Fact p.Prime] :
    (p : ℚ) • (specialLog p).series =
      (p : ℚ) • PowerSeries.X + (specialLog p).series.subst (PowerSeries.X^(p^3)) := by
  have he := logarithm_functional_equation (Int.castRingHom ℚ) p hp.out.two_le
    (RingHom.id ℤ) (AlgHom.id ℚ ℚ) (by rfl) specialParameters
  simp [defect, Fin.sum_univ_three, specialParameters] at he
  have he' := congrArg (fun x : PowerSeries ℚ => (p : ℚ) • x) he
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hp.out.ne_zero : (p : ℚ) ≠ 0),
    one_smul] at he'
  have ht : ((twist p hp.out.ne_zero (RingHom.id ℚ))^3) (specialLog p).series =
      (specialLog p).series.subst (PowerSeries.X^(p^3)) := by
    rw [twist_iterate]
    simp only [show (RingHom.id ℚ)^3 = RingHom.id ℚ by rfl, MvPowerSeries.map_id]
    exact PowerSeries.expand_apply ..
  change (p : ℚ) • (specialLog p).series -
    ((twist p hp.out.ne_zero (RingHom.id ℚ))^3) (specialLog p).series = _ at he'
  rw [ht] at he'
  exact sub_eq_iff_eq_add.mp he'

lemma specialLog_divided (p : ℕ) [hp : Fact p.Prime] :
    ∃ v : StrictLog (R := ℤ),
      (specialLog p).series.subst ((p : PowerSeries ℚ) * PowerSeries.X) =
        (p : PowerSeries ℚ) * v.series.map (Int.castRingHom ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hnum : HasIntegralNumerators (Int.castRingHom ℚ) p (specialLog p).series :=
    series_integralNumerators _ p hp.out.two_le _
  obtain ⟨v, hv⟩ := logarithm_difference (Int.castRingHom ℚ) p hp.out.ne_zero
    (specialLog p).series hnum ((p : PowerSeries ℤ) * PowerSeries.X) 0
    (by simp [PowerSeries.X]) (by simp) (by simp)
  simp only [map_mul, map_natCast, PowerSeries.X, map_X, map_zero,
    PowerSeries.subst_zero_of_constantCoeff_zero (specialLog p).constant_zero, sub_zero] at hv
  have hc : v.constantCoeff = 0 := by
    have hh := congrArg (MvPowerSeries.constantCoeff (σ := Unit)) hv
    rw [PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (specialLog p).constant_zero] at hh
    simp only [map_mul, map_natCast, MvPowerSeries.constantCoeff_map] at hh
    have hh' : (v.constantCoeff : ℚ) = 0 := (mul_eq_zero.mp hh.symm).resolve_left hpq
    exact_mod_cast hh'
  have hl : PowerSeries.coeff 1 v = 1 := by
    have hh := congrArg (PowerSeries.coeff 1) hv
    change MvPowerSeries.coeff (Finsupp.single () 1) _ = _ at hh
    rw [StrictLog.coeff_subst_linear _ _ (by simp), (specialLog p).linear_one,
      one_mul] at hh
    change PowerSeries.coeff 1 ((p : PowerSeries ℚ) * PowerSeries.X) =
      PowerSeries.coeff 1 ((p : PowerSeries ℚ) * PowerSeries.map (Int.castRingHom ℚ) v) at hh
    simp only [← map_natCast (PowerSeries.C (R := ℚ)), PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_map] at hh
    have hh' : ((PowerSeries.coeff 1 v : ℤ) : ℚ) = 1 := (mul_left_cancel₀ hpq (by simpa using hh.symm))
    exact_mod_cast hh'
  exact ⟨⟨v,hc,hl⟩,hv⟩

lemma specialLog_p_error (p : ℕ) [hp : Fact p.Prime] :
    ∃ a : PowerSeries ℤ, a.constantCoeff = 0 ∧ (p : PowerSeries ℤ) ∣ a ∧
      (specialLog p).series.subst (a.map (Int.castRingHom ℚ)) =
        (p : PowerSeries ℚ) * PowerSeries.X := by
  obtain ⟨v,hv⟩ := specialLog_divided p
  let b : PowerSeries ℚ := v.inv.map (Int.castRingHom ℚ)
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero
    (by
      change (Int.castRingHom ℚ) v.inv.constantCoeff = 0
      rw [v.inv_constant, map_zero])
  refine ⟨(p : PowerSeries ℤ) * v.inv, by simp, dvd_mul_right _ _, ?_⟩
  have hh := congrArg (PowerSeries.subst b) hv
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero (by simp [PowerSeries.X])) hb] at hh
  have hx : PowerSeries.subst b ((p : PowerSeries ℚ) * PowerSeries.X) = p * b := by
    rw [← PowerSeries.coe_substAlgHom hb, map_mul, map_natCast,
      PowerSeries.substAlgHom_X]
  have hvb : (v.series.map (Int.castRingHom ℚ)).subst b = PowerSeries.X := by
    rw [show b = MvPowerSeries.map (Int.castRingHom ℚ) v.inv from rfl,
      ← PowerSeries.map_subst v.inv_hasSubst, v.subst_inv]
    exact PowerSeries.map_X _
  rw [hx, PowerSeries.subst_mul hb] at hh
  have hnat : PowerSeries.subst b (p : PowerSeries ℚ) = p := by
    rw [← PowerSeries.coe_substAlgHom hb, map_natCast]
  rw [hnat, hvb] at hh
  simpa only [map_mul, map_natCast] using hh

lemma integralSpecial_p_split (p : ℕ) [hp : Fact p.Prime] :
    ∃ a : PowerSeries ℤ, a.constantCoeff = 0 ∧ (p : PowerSeries ℤ) ∣ a ∧
      multiplicationSeries (integralSpecial p) p =
        (integralSpecial p).toPowerSeries.subst ![a, PowerSeries.X^(p^3)] := by
  obtain ⟨a,ha,had,hal⟩ := specialLog_p_error p
  have ham : (MvPowerSeries.map (Int.castRingHom ℚ) a).constantCoeff = 0 := by
    rw [constantCoeff_map]
    change (Int.castRingHom ℚ) a.constantCoeff = 0
    rw [ha, map_zero]
  have hx : (PowerSeries.X^(p^3) : PowerSeries ℚ).constantCoeff = 0 := by
    simp [PowerSeries.constantCoeff, PowerSeries.X, hp.out.ne_zero]
  change (specialLog p).series.subst (MvPowerSeries.map (Int.castRingHom ℚ) a) = _ at hal
  have hQ : multiplicationSeries (specialLog p).formalGroup p =
      (specialLog p).law.subst ![a.map (Int.castRingHom ℚ), PowerSeries.X^(p^3)] := by
    apply (specialLog p).subst_injective
      (PowerSeries.HasSubst.of_constantCoeff_zero (multiplication_constant _ _))
      (PowerSeries.HasSubst.of_constantCoeff_zero ((specialLog p).law_pair_constant _ _ ham hx))
    rw [log_multiplication, (specialLog p).log_law_pair _ _ ham hx, hal]
    convert specialLog_functional p using 1 <;>
      simp only [smul_eq_C_mul, map_natCast, nsmul_eq_mul]
  refine ⟨a,ha,had,?_⟩
  apply map_injective (Int.castRingHom ℚ) Int.cast_injective
  change PowerSeries.map (Int.castRingHom ℚ) (multiplicationSeries (integralSpecial p) p) = _
  rw [← multiplication_map, integralSpecial_map]
  have hpairs : MvPowerSeries.HasSubst ![a, (PowerSeries.X : PowerSeries ℤ)^(p^3)] :=
    hasSubst_of_constantCoeff_zero (by
      intro i; fin_cases i; exact ha
      simp [PowerSeries.X, hp.out.ne_zero])
  rw [map_subst hpairs]
  change multiplicationSeries (specialLog p).formalGroup p =
    ((integralSpecial p).map (Int.castRingHom ℚ)).toPowerSeries.subst _
  rw [integralSpecial_map]
  convert hQ using 1
  congr 2
  funext i; fin_cases i <;> simp [PowerSeries.X, PowerSeries.map]

theorem integralSpecial_honda (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] [CharP K p] :
    multiplicationSeries ((integralSpecial p).map (Int.castRingHom K)) p =
      PowerSeries.X^(p^3) := by
  obtain ⟨a,ha,⟨b,hb⟩,hs⟩ := integralSpecial_p_split p
  have hap : a.map (Int.castRingHom K) = 0 := by
    rw [hb, map_mul, map_natCast]
    have hpK : (p : PowerSeries K) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg
        (PowerSeries.C (R := K)) (CharP.cast_eq_zero K p)
    rw [hpK, zero_mul]
  rw [multiplication_map, hs]
  have hpairs : MvPowerSeries.HasSubst ![a, (PowerSeries.X : PowerSeries ℤ)^(p^3)] :=
    hasSubst_of_constantCoeff_zero (by
      intro i; fin_cases i; exact ha
      simp [PowerSeries.X, hp.out.ne_zero])
  change MvPowerSeries.map (Int.castRingHom K) _ = _
  rw [map_subst hpairs]
  have hpair : (fun i => MvPowerSeries.map (Int.castRingHom K)
      (![a, (PowerSeries.X : PowerSeries ℤ)^(p^3)] i)) =
      ![0, (PowerSeries.X : PowerSeries K)^(p^3)] := by
    funext i; fin_cases i
    · exact hap
    · simp [PowerSeries.X]
  rw [hpair]
  change ((integralSpecial p).map (Int.castRingHom K)).toPowerSeries.subst
    ![0, (PowerSeries.X : PowerSeries K)^(p^3)] = _
  exact FormalGroup.zero_add ((integralSpecial p).map (Int.castRingHom K))
    (PowerSeries.HasSubst.of_constantCoeff_zero
      (by simp [PowerSeries.X, hp.out.ne_zero]))

def hondaLaw (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] : FormalGroup K :=
  (integralSpecial p).map (Int.castRingHom K)

instance hondaLaw_comm (p : ℕ) [hp : Fact p.Prime] (K : Type*) [CommRing K] :
    (hondaLaw p K).IsComm := by
  have : (integralSpecial p).IsComm := integralFormalGroup_isComm ..
  change ((integralSpecial p).map (Int.castRingHom K)).IsComm
  infer_instance

lemma reducedHonda_specialFiber (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] :
    (reducedHonda p K).map MvPowerSeries.constantCoeff = hondaLaw p K := by
  have hc : MvPowerSeries.constantCoeff.comp
      (MvPowerSeries.map (σ := Fin 2) (Int.castRingHom K)) =
      (Int.castRingHom K).comp MvPowerSeries.constantCoeff := by
    ext f
    rfl
  change ((integralHonda p).map (MvPowerSeries.map (Int.castRingHom K))).map _ = _
  rw [formalGroup_map_map, hc, ← formalGroup_map_map, integralHonda_specialize]
  rfl

theorem constructed_honda_deformation (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] [CharP K p] :
    (reducedHonda p K).IsComm ∧
    (reducedHonda p K).map MvPowerSeries.constantCoeff = hondaLaw p K ∧
    multiplicationSeries (hondaLaw p K) p = PowerSeries.X^(p^3) ∧
    HeightCoordinates p (reducedHonda p K) :=
  ⟨inferInstance, reducedHonda_specialFiber p K, integralSpecial_honda p K,
    reducedHonda_heightCoordinates p K⟩

end HeightThree.HondaSpecialFiber

end

end OAI
