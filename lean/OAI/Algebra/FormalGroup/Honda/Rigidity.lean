import OAI.Algebra.FormalGroup.Honda.HondaDifferential

namespace OAI

noncomputable section

namespace HeightThree.DeformationRigidity
open MvPowerSeries HondaTarget
variable {A B : Type*} [CommRing A] [CommRing B]
@[simp] lemma multiplication_zero (F : FormalGroup A) :
    multiplicationSeries F 0 = 0 := rfl

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

end HeightThree.DeformationRigidity

namespace HeightThree.DeformationRigidity
open MvPowerSeries HondaTarget
variable {R S : Type*} [CommRing R] [CommRing S]

def SquareZeroKernel (ρ : R →+* S) : Prop :=
  ∀ a b : R, ρ a = 0 → ρ b = 0 → a * b = 0

lemma subst_eq_of_squareZero (ρ : R →+* S) (hρ : SquareZeroKernel ρ)
    (f : PowerSeries R) (hf : f.map ρ = 0)
    {σ : Type*} (a b : MvPowerSeries σ R)
    (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (hab : a.map ρ = b.map ρ) : f.subst a = f.subst b := by
  ext d
  rw [PowerSeries.coeff_subst ha, PowerSeries.coeff_subst hb]
  apply finsum_congr
  intro j
  have hfj : ρ (PowerSeries.coeff j f) = 0 := by
    have hh := congrArg (PowerSeries.coeff j) hf
    simpa only [PowerSeries.coeff_map, map_zero] using hh
  have hpw : (a^j).map ρ = (b^j).map ρ := by simp only [map_pow, hab]
  have hc : ρ (coeff d (a^j) - coeff d (b^j)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa only [coeff_map] using congrArg (coeff d) hpw)
  rw [smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
  exact hρ _ _ hfj hc

lemma mul_eq_zero_of_map_zero (ρ : R →+* S) (hρ : SquareZeroKernel ρ)
    (a b : PowerSeries R) (ha : a.map ρ = 0) (hb : b.map ρ = 0) : a*b = 0 := by
  ext n
  rw [PowerSeries.coeff_mul, map_zero]
  apply Finset.sum_eq_zero
  intro ij _
  apply hρ
  · simpa only [PowerSeries.coeff_map, map_zero] using congrArg (PowerSeries.coeff ij.1) ha
  · simpa only [PowerSeries.coeff_map, map_zero] using congrArg (PowerSeries.coeff ij.2) hb

lemma highPower_unchanged (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (h : ℕ) (hh : 0 < h) (ρ : R →+* S) (hρ : SquareZeroKernel ρ)
    (u : PowerSeries R) (hu : u.map ρ = PowerSeries.X) :
    u^(p^h) = PowerSeries.X^(p^h) := by
  have : CharP (PowerSeries R) p := charP_of_injective_ringHom PowerSeries.C_injective p
  let d := u - PowerSeries.X
  have hd : d.map ρ = 0 := by simp [d, hu]
  have hd2 : d^2 = 0 := by simpa only [pow_two] using mul_eq_zero_of_map_zero ρ hρ d d hd hd
  have hdq : d^(p^h) = 0 := pow_eq_zero_of_le
    (by exact le_trans hp.out.two_le (Nat.le_pow hh)) hd2
  have hu' : u = PowerSeries.X + d := by dsimp [d]; ring
  rw [hu', add_pow_char_pow, hdq, add_zero]

lemma subst_after_mv {σ τ : Type*} (f : PowerSeries R)
    (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a)
    (b : σ → MvPowerSeries τ R) (hb : MvPowerSeries.HasSubst b) :
    (f.subst a).subst b = f.subst (a.subst b) :=
  MvPowerSeries.subst_comp_subst_apply ha.const hb f

lemma coordinate_add (F G : FormalGroup R) (e : CoordinateIso F G)
    {σ : Type*} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    e.series.subst (F.toPowerSeries.subst ![a,b]) =
      G.toPowerSeries.subst ![e.series.subst a, e.series.subst b] := by
  have hab : MvPowerSeries.HasSubst ![a,b] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption)
  have hes (i : Fin 2) : (e.series.subst (X i : MvPowerSeries (Fin 2) R)).constantCoeff = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) _ e.zero_series
  have hepair : MvPowerSeries.HasSubst
      ![e.series.subst (X 0 : MvPowerSeries (Fin 2) R),
        e.series.subst (X 1 : MvPowerSeries (Fin 2) R)] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> exact hes _)
  have he := congrArg (fun z : MvPowerSeries (Fin 2) R => z.subst ![a,b])
    e.preserves_addition
  rw [subst_after_mv _ _ (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff)
    _ hab, MvPowerSeries.subst_comp_subst_apply hepair hab] at he
  convert he using 1
  congr 1
  funext i; fin_cases i
  · change e.series.subst a = (e.series.subst (X 0 : MvPowerSeries (Fin 2) R)).subst ![a,b]
    rw [subst_after_mv _ _ (PowerSeries.HasSubst.X _) _ hab, MvPowerSeries.subst_X hab]
    rfl
  · change e.series.subst b = (e.series.subst (X 1 : MvPowerSeries (Fin 2) R)).subst ![a,b]
    rw [subst_after_mv _ _ (PowerSeries.HasSubst.X _) _ hab, MvPowerSeries.subst_X hab]
    rfl

lemma law_pair_subst (F : FormalGroup R) (a b c : PowerSeries R)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (hc : PowerSeries.HasSubst c) :
    PowerSeries.subst c (F.toPowerSeries.subst ![a,b]) =
      F.toPowerSeries.subst ![a.subst c, b.subst c] := by
  have hab : MvPowerSeries.HasSubst ![a,b] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption)
  change (F.toPowerSeries.subst ![a,b]).subst (fun _ : Unit => c) = _
  rw [MvPowerSeries.subst_comp_subst_apply hab hc.const]
  congr 1
  funext i; fin_cases i <;> rfl

lemma coordinate_multiplication (F G : FormalGroup R) (e : CoordinateIso F G) (n : ℕ) :
    e.series.subst (multiplicationSeries F n) =
      (multiplicationSeries G n).subst e.series := by
  have he : PowerSeries.HasSubst e.series := PowerSeries.HasSubst.of_constantCoeff_zero e.zero_series
  induction n with
  | zero =>
    simp only [multiplication_zero, PowerSeries.subst_zero_of_constantCoeff_zero e.zero_series]
    rw [← PowerSeries.coe_substAlgHom he, map_zero]
  | succ n ih =>
    rw [multiplication_succ, coordinate_add F G e _ _ (multiplication_constant F n)
      (by exact PowerSeries.constantCoeff_X), multiplication_succ,
      law_pair_subst G _ _ _ (multiplication_constant G n) PowerSeries.constantCoeff_X he,
      ih, PowerSeries.X_subst, PowerSeries.subst_X he]

lemma subst_near_X_highPower (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (h : ℕ) (hh : 0 < h) (ρ : R →+* S) (hρ : SquareZeroKernel ρ)
    (u f : PowerSeries R) (hu0 : u.constantCoeff = 0)
    (hu : u.map ρ = PowerSeries.X) (hf : f.map ρ = PowerSeries.X^(p^h)) :
    f.subst u = f := by
  let v := f - PowerSeries.X^(p^h)
  have hv : v.map ρ = 0 := by simp only [v, map_sub, map_pow, PowerSeries.map_X, hf, sub_self]
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu0
  have hvu : v.subst u = v := by
    have he := subst_eq_of_squareZero ρ hρ v hv u PowerSeries.X huS
      PowerSeries.HasSubst.X' (by change u.map ρ = (PowerSeries.X : PowerSeries R).map ρ; simpa only [PowerSeries.map_X] using hu)
    simpa only [PowerSeries.X_subst] using he
  have he : f = PowerSeries.X^(p^h) + v := by dsimp [v]; ring
  conv_lhs => rw [he]
  rw [PowerSeries.subst_add huS, PowerSeries.subst_pow huS, PowerSeries.subst_X huS,
    highPower_unchanged p h hh ρ hρ u hu, hvu]
  exact he.symm

lemma infinitesimal_pseries (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (h : ℕ) (hh : 0 < h) (ρ : R →+* S) (hρ : SquareZeroKernel ρ)
    (F G : FormalGroup R) (e : CoordinateIso F G)
    (he : e.series.map ρ = PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ = PowerSeries.X^(p^h))
    (hG : (multiplicationSeries G p).map ρ = PowerSeries.X^(p^h)) :
    multiplicationSeries F p +
        (e.series - PowerSeries.X).subst (PowerSeries.X^(p^h)) =
      multiplicationSeries G p := by
  let d := e.series - PowerSeries.X
  have hd : d.map ρ = 0 := by simp [d, he]
  have hpq : (p^h) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hq : PowerSeries.HasSubst (PowerSeries.X^(p^h) : PowerSeries R) :=
    PowerSeries.HasSubst.X_pow hpq
  have hdf : d.subst (multiplicationSeries F p) = d.subst (PowerSeries.X^(p^h)) :=
    subst_eq_of_squareZero ρ hρ d hd _ _
      (PowerSeries.HasSubst.of_constantCoeff_zero (multiplication_constant F p)) hq
      (by change (multiplicationSeries F p).map ρ = (PowerSeries.X^(p^h)).map ρ; simpa only [map_pow, PowerSeries.map_X] using hF)
  have hcentral := coordinate_multiplication F G e p
  have hes : e.series = PowerSeries.X + d := by dsimp [d]; ring
  rw [subst_near_X_highPower p h hh ρ hρ _ _ e.zero_series he hG] at hcentral
  conv_lhs at hcentral => rw [hes, PowerSeries.subst_add
    (PowerSeries.HasSubst.of_constantCoeff_zero (multiplication_constant F p)),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (multiplication_constant F p)), hdf]
  exact hcentral

theorem infinitesimal_automorphism_rigid (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (h : ℕ) (hh : 0 < h) (ρ : R →+* S) (hρ : SquareZeroKernel ρ)
    (F : FormalGroup R) (e : CoordinateIso F F)
    (he : e.series.map ρ = PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ = PowerSeries.X^(p^h)) :
    e.series = PowerSeries.X := by
  have hz := infinitesimal_pseries p h hh ρ hρ F F e he hF hF
  have hd : (e.series - PowerSeries.X).subst (PowerSeries.X^(p^h)) = 0 :=
    (add_eq_left.mp hz)
  have hpq : (p^h) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have heq : e.series - PowerSeries.X = 0 := by
    ext n
    have hn := congrArg (PowerSeries.coeff (p^h*n)) hd
    rw [← PowerSeries.expand_apply (p^h) hpq,
      PowerSeries.coeff_expand_mul, map_zero] at hn
    simpa only [map_zero] using hn
  exact sub_eq_zero.mp heq

end HeightThree.DeformationRigidity

end

end OAI
