import OAI.Algebra.FormalGroup.Honda.Rigidity

namespace OAI

noncomputable section

namespace HeightThree.TangentClassification
open MvPowerSeries PowerSeriesDifferential
variable {R σ : Type*} [CommRing R]

lemma expand_injective (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (MvPowerSeries.expand (R := R) (σ := σ) q hq) := by
  intro f g h
  ext d
  simpa only [coeff_expand_smul] using congrArg (coeff (q • d)) h

lemma pderiv_expand_zero (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (f : MvPowerSeries σ R) (i : σ) :
    pderiv i (expand p hp.out.ne_zero f) = 0 := by
  ext d
  rw [coeff_pderiv, map_zero]
  by_cases h : p ∣ d i + 1
  · have hn : (d i : R) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using (CharP.cast_eq_zero_iff R p (d i+1)).mpr h
    rw [hn, mul_zero]
  · rw [coeff_expand_of_not_dvd p hp.out.ne_zero f (i := i) (by simpa using h), zero_mul]

lemma exists_expand_derivative_zero [Nontrivial R] (p : ℕ)
    [hp : Fact p.Prime] [CharP R p] (f : PowerSeries R)
    (hf : PowerSeries.derivative f = 0) :
    ∃ g, PowerSeries.expand p hp.out.ne_zero g = f := by
  refine ⟨PowerSeries.mk (fun n => f.coeff (p*n)), ?_⟩
  ext n
  by_cases hn : p ∣ n
  · obtain ⟨n, rfl⟩ := hn
    rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hn]
    have hn0 : n ≠ 0 := by intro h; exact hn (h ▸ dvd_zero p)
    have hh := congrArg (PowerSeries.coeff (n-1)) hf
    rw [PowerSeries.coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ n), map_zero] at hh
    have hunit : IsUnit (n : R) := (CharP.isUnit_natCast_iff hp.out).mpr hn
    have he : (n-1 : ℕ) + 1 = n := Nat.sub_add_cancel (by omega)
    have he' : ((n-1 : ℕ) : R)+1 = (n : R) := by simpa only [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast : ℕ → R) he
    rw [he'] at hh
    exact (hunit.mul_left_eq_zero.mp hh).symm

lemma exists_linear_add_expand [Nontrivial R] (p : ℕ)
    [hp : Fact p.Prime] [CharP R p] (f : PowerSeries R)
    (hf0 : f.constantCoeff = 0)
    (hf : PowerSeries.derivative f = PowerSeries.C (f.coeff 1)) :
    ∃ g : PowerSeries R, g.constantCoeff = 0 ∧
      f = PowerSeries.C (f.coeff 1) * PowerSeries.X + PowerSeries.expand p hp.out.ne_zero g := by
  have hzero : PowerSeries.derivative (f - PowerSeries.C (f.coeff 1) * PowerSeries.X) = 0 := by
    simp [hf]
  obtain ⟨g, hg⟩ := exists_expand_derivative_zero p _ hzero
  refine ⟨g, ?_, ?_⟩
  · have hh := congrArg PowerSeries.constantCoeff hg
    simpa [hf0] using hh
  · rw [hg]; ring

def delta (F : FormalGroup R) (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  f.subst F.toPowerSeries - f.subst (X 0) - f.subst (X 1)

lemma delta_sub (F : FormalGroup R) (f g : PowerSeries R) :
    delta F (f-g) = delta F f - delta F g := by
  simp only [delta, PowerSeries.subst_sub (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.subst_sub (PowerSeries.HasSubst.X (0 : Fin 2)), PowerSeries.subst_sub (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

lemma delta_add (F : FormalGroup R) (f g : PowerSeries R) :
    delta F (f+g) = delta F f + delta F g := by
  simp only [delta, PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.subst_add (PowerSeries.HasSubst.X (0 : Fin 2)), PowerSeries.subst_add (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

lemma delta_smul (F : FormalGroup R) (a : R) (f : PowerSeries R) :
    delta F (a • f) = a • delta F f := by
  simp only [delta, PowerSeries.subst_smul (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.subst_smul (PowerSeries.HasSubst.X (0 : Fin 2)), PowerSeries.subst_smul (PowerSeries.HasSubst.X (1 : Fin 2)), smul_sub]

lemma delta_X (F : FormalGroup R) : delta F PowerSeries.X = F.toPowerSeries - X 0 - X 1 := by
  simp only [delta, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.subst_X (PowerSeries.HasSubst.X (0 : Fin 2)), PowerSeries.subst_X (PowerSeries.HasSubst.X (1 : Fin 2))]

lemma pderiv_delta (F : FormalGroup R) (hF : pderiv 0 F.toPowerSeries = 1)
    (f : PowerSeries R) :
    pderiv 0 (delta F f) =
      (PowerSeries.derivative f).subst F.toPowerSeries -
        (PowerSeries.derivative f).subst (X 0) := by
  simp only [delta, map_sub, pderiv_subst _ _ F.zero_constantCoeff,
    pderiv_subst _ _ (constantCoeff_X (R := R) (s := (0 : Fin 2))), pderiv_subst _ _ (constantCoeff_X (R := R) (s := (1 : Fin 2))),
    hF, pderiv_X]
  simp

lemma derivative_constant_of_delta_expand (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (F : FormalGroup R) (hF : pderiv 0 F.toPowerSeries = 1)
    (f : PowerSeries R) (D : MvPowerSeries (Fin 2) R)
    (h : delta F f = expand p hp.out.ne_zero D) :
    PowerSeries.derivative f = PowerSeries.C (f.coeff 1) := by
  have hh := congrArg (pderiv 0) h
  rw [pderiv_delta F hF, pderiv_expand_zero] at hh
  have he : (PowerSeries.derivative f).subst F.toPowerSeries =
      (PowerSeries.derivative f).subst (X 0) := sub_eq_zero.mp hh
  let a : Fin 2 → PowerSeries R := ![0, PowerSeries.X]
  have ha : MvPowerSeries.HasSubst a := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [a, PowerSeries.X])
  have he' := congrArg (MvPowerSeries.subst a) he
  change MvPowerSeries.subst a (MvPowerSeries.subst (fun _ : Unit => F.toPowerSeries) _) =
    MvPowerSeries.subst a (MvPowerSeries.subst (fun _ : Unit => X 0) _) at he'
  rw [MvPowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff).const ha,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X (0 : Fin 2)).const ha] at he'
  have hleft : F.toPowerSeries.subst a = PowerSeries.X := by
    exact F.zero_add PowerSeries.HasSubst.X'
  simp only [hleft, subst_X ha] at he'
  change (PowerSeries.derivative f).subst PowerSeries.X =
    (PowerSeries.derivative f).subst 0 at he'
  have hc : (PowerSeries.derivative f).constantCoeff = f.coeff 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_derivative]
    simp
  simpa [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.C, hc] using he'

lemma subst_expand_outer (q : ℕ) (hq : q ≠ 0) (f : PowerSeries R)
    (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) :
    (PowerSeries.expand q hq f).subst a = f.subst (a^q) := by
  rw [PowerSeries.expand_apply, PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.X_pow hq) ha, PowerSeries.subst_pow ha,
    PowerSeries.subst_X ha]

lemma delta_expand (q : ℕ) (hq : q ≠ 0) (F : FormalGroup R)
    (hF : F.toPowerSeries^q = expand q hq F.toPowerSeries) (f : PowerSeries R) :
    delta F (PowerSeries.expand q hq f) = expand q hq (delta F f) := by
  rw [delta, subst_expand_outer q hq f _ (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    subst_expand_outer q hq f _ (PowerSeries.HasSubst.X (0 : Fin 2)),
    subst_expand_outer q hq f _ (PowerSeries.HasSubst.X (1 : Fin 2)), hF]
  simp only [delta, map_sub, PowerSeries.expand_subst q hq
    (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.expand_subst q hq (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.expand_subst q hq (PowerSeries.HasSubst.X (1 : Fin 2)), expand_X]

lemma partial_of_nonlinear_expand (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (F : FormalGroup R) (H : MvPowerSeries (Fin 2) R)
    (hF : F.toPowerSeries - X 0 - X 1 = expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H) :
    pderiv 0 F.toPowerSeries = 1 := by
  have hfac : expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H =
      expand p hp.out.ne_zero (expand p hp.out.ne_zero H) := by
    simpa only [pow_two] using expand_mul p hp.out.ne_zero p hp.out.ne_zero H
  have he : F.toPowerSeries = X 0 + X 1 + expand p hp.out.ne_zero (expand p hp.out.ne_zero H) := by
    rw [← hfac, ← hF]; ring
  rw [he, map_add, map_add, pderiv_expand_zero]
  simp

theorem tangent_decomposition [Nontrivial R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (F : FormalGroup R) (H : MvPowerSeries (Fin 2) R)
    (hF : F.toPowerSeries^p = expand p hp.out.ne_zero F.toPowerSeries)
    (hH : F.toPowerSeries - X 0 - X 1 = expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H)
    (v : PowerSeries R) (hv0 : v.constantCoeff = 0) (hv1 : v.coeff 1 = 0)
    (D : MvPowerSeries (Fin 2) R)
    (hv : delta F v = expand (p^3) (pow_ne_zero _ hp.out.ne_zero) D) :
    ∃ (a b : R) (w : PowerSeries R), w.constantCoeff = 0 ∧
      v = a • PowerSeries.X^p + b • PowerSeries.X^(p^2) +
        PowerSeries.expand (p^3) (pow_ne_zero _ hp.out.ne_zero) w := by
  have hpartial := partial_of_nonlinear_expand p F H hH
  have hfac3 (D : MvPowerSeries (Fin 2) R) :
      expand (p^3) (pow_ne_zero _ hp.out.ne_zero) D =
        expand p hp.out.ne_zero (expand (p^2) (pow_ne_zero _ hp.out.ne_zero) D) := by
    simpa only [show p^3 = p*(p^2) by ring] using
      expand_mul p hp.out.ne_zero (p^2) (pow_ne_zero _ hp.out.ne_zero) D
  have hfac2 (D : MvPowerSeries (Fin 2) R) :
      expand (p^2) (pow_ne_zero _ hp.out.ne_zero) D =
        expand p hp.out.ne_zero (expand p hp.out.ne_zero D) := by
    simpa only [pow_two] using expand_mul p hp.out.ne_zero p hp.out.ne_zero D
  have hdv : PowerSeries.derivative v = 0 := by
    rw [derivative_constant_of_delta_expand p F hpartial v _ (by rw [← hfac3]; exact hv), hv1, map_zero]
  obtain ⟨v₁, hv₁⟩ := exists_expand_derivative_zero p v hdv
  have hv₁0 : v₁.constantCoeff = 0 := by
    simpa only [PowerSeries.constantCoeff_expand, hv0] using congrArg PowerSeries.constantCoeff hv₁
  have hdv₁ : delta F v₁ = expand (p^2) (pow_ne_zero _ hp.out.ne_zero) D := by
    apply expand_injective p hp.out.ne_zero
    rw [← delta_expand p hp.out.ne_zero F hF, hv₁, ← hfac3, hv]
  have hh₁ := derivative_constant_of_delta_expand p F hpartial v₁ _ (by rw [← hfac2]; exact hdv₁)
  obtain ⟨v₂, hv₂0, hv₂⟩ := exists_linear_add_expand p v₁ hv₁0 hh₁
  let a := v₁.coeff 1
  have he₁ : v₁ = a • PowerSeries.X + PowerSeries.expand p hp.out.ne_zero v₂ := by
    simpa only [smul_eq_mul, ← PowerSeries.smul_eq_C_mul] using hv₂
  have hdv₂ : delta F v₂ = expand p hp.out.ne_zero (D - a • H) := by
    have he := hdv₁
    rw [he₁, delta_add, delta_smul, delta_X, hH, delta_expand p hp.out.ne_zero F hF] at he
    apply expand_injective p hp.out.ne_zero
    rw [← hfac2, map_sub, map_smul]
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using he
  have hh₂ := derivative_constant_of_delta_expand p F hpartial v₂ _ hdv₂
  obtain ⟨w, hw0, hw⟩ := exists_linear_add_expand p v₂ hv₂0 hh₂
  let b := v₂.coeff 1
  have he₂ : v₂ = b • PowerSeries.X + PowerSeries.expand p hp.out.ne_zero w := by
    simpa only [smul_eq_mul, ← PowerSeries.smul_eq_C_mul] using hw
  refine ⟨a, b, w, hw0, ?_⟩
  rw [← hv₁, he₁, he₂]
  simp only [map_add, map_smul, map_pow, PowerSeries.expand_X]
  rw [← PowerSeries.expand_mul, ← PowerSeries.expand_mul, ← pow_mul]
  have he2 : p*p = p^2 := by ring
  have he3 : p^2*p = p^3 := by ring
  simp only [he2, he3, add_assoc]

end HeightThree.TangentClassification

end

end OAI
