import OAI.Algebra.FormalGroup.Honda.ChainRule
import OAI.Algebra.FormalGroup.Honda.Tangent

namespace OAI

noncomputable section

namespace HeightThree.SmallExtension
open MvPowerSeries HondaTarget DeformationRigidity TangentClassification
variable {R S K σ τ : Type*} [CommRing R] [CommRing S] [CommRing K]

structure IsSmall (π : R →+* S) (ρ : R →+* K) : Prop where
  ker_le : ∀ a, π a = 0 → ρ a = 0
  annihilate : ∀ a b, π a = 0 → ρ b = 0 → a*b = 0

lemma IsSmall.squareZero {π : R →+* S} {ρ : R →+* K} (h : IsSmall π ρ) :
    SquareZeroKernel π := fun a b ha hb => h.annihilate a b ha (h.ker_le b hb)

lemma subst_eq_of_annihilate (π : R →+* S) (ρ : R →+* K)
    (h : ∀ c e, π c = 0 → ρ e = 0 → c*e = 0)
    (f : MvPowerSeries σ R) (hf : f.map π = 0)
    (a b : σ → MvPowerSeries τ R) (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, (a i).map ρ = (b i).map ρ) : f.subst a = f.subst b := by
  ext d
  rw [coeff_subst ha, coeff_subst hb]
  apply finsum_congr
  intro e
  have hf' : π (coeff e f) = 0 := by
    simpa only [coeff_map, map_zero] using congrArg (coeff e) hf
  have he : (e.prod fun i n => (a i)^n).map ρ = (e.prod fun i n => (b i)^n).map ρ := by
    simp only [Finsupp.prod, map_prod, map_pow, hab]
  have hd : ρ (coeff d (e.prod fun i n => (a i)^n) - coeff d (e.prod fun i n => (b i)^n)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa only [coeff_map] using congrArg (coeff d) he)
  rw [smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
  exact h _ _ hf' hd

lemma unisubst_eq_of_annihilate (π : R →+* S) (ρ : R →+* K)
    (h : ∀ c e, π c = 0 → ρ e = 0 → c*e = 0)
    (f : PowerSeries R) (hf : f.map π = 0)
    (a b : MvPowerSeries τ R) (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (hab : a.map ρ = b.map ρ) : f.subst a = f.subst b :=
  subst_eq_of_annihilate π ρ h f hf _ _ ha.const hb.const (fun _ => hab)

lemma series_mul_zero (π : R →+* S) (ρ : R →+* K)
    (h : ∀ c e, π c = 0 → ρ e = 0 → c*e = 0)
    (a b : MvPowerSeries σ R) (ha : a.map π = 0) (hb : b.map ρ = 0) : a*b = 0 := by
  classical
  ext d
  rw [coeff_mul, map_zero]
  apply Finset.sum_eq_zero
  intro ij hij
  apply h
  · simpa only [coeff_map, map_zero] using congrArg (coeff ij.1) ha
  · simpa only [coeff_map, map_zero] using congrArg (coeff ij.2) hb

lemma highPower_eq (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (n : ℕ) (hn : 0 < n) (π : R →+* S) (hπ : SquareZeroKernel π)
    (a b : MvPowerSeries σ R) (hab : a.map π = b.map π) : a^(p^n) = b^(p^n) := by
  let : CharP (MvPowerSeries σ R) p := charP_of_injective_ringHom MvPowerSeries.C_injective p
  let d := a-b
  have hd : d.map π = 0 := by simp [d, hab]
  have hd2 : d^2 = 0 := by simpa only [pow_two] using series_mul_zero π π hπ d d hd hd
  have hdq : d^(p^n) = 0 := pow_eq_zero_of_le (le_trans hp.out.two_le (Nat.le_pow hn)) hd2
  have he : a = b+d := by dsimp [d]; ring
  rw [he, add_pow_char_pow, hdq, add_zero]

lemma subst_expand_inner (q : ℕ) (hq : q ≠ 0) (f : MvPowerSeries σ R)
    (a : σ → MvPowerSeries τ R) (ha : HasSubst a) :
    (expand q hq f).subst a = f.subst (fun i => (a i)^q) := by
  rw [expand, substAlgHom_apply, subst_comp_subst_apply (HasSubst.X_pow hq) ha]
  congr 1
  funext i
  rw [← coe_substAlgHom ha, map_pow, substAlgHom_X]

lemma law_perturbation (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F Γ : FormalGroup R) (hF : F.toPowerSeries.map ρ = Γ.toPowerSeries.map ρ)
    (H : MvPowerSeries (Fin 2) R)
    (hΓ : Γ.toPowerSeries = X 0 + X 1 + expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H)
    (a b : Fin 2 → MvPowerSeries σ R) (ha : HasSubst a) (hb : HasSubst b)
    (hab : ∀ i, (a i).map π = (b i).map π) :
    F.toPowerSeries.subst a - F.toPowerSeries.subst b = (a 0-b 0)+(a 1-b 1) := by
  have he : (F.toPowerSeries-Γ.toPowerSeries).subst a =
      (F.toPowerSeries-Γ.toPowerSeries).subst b := by
    apply subst_eq_of_annihilate ρ π (fun c e hc he => by rw [mul_comm]; exact h.annihilate e c he hc)
    · simpa only [map_sub] using sub_eq_zero.mpr hF
    · exact ha
    · exact hb
    · exact hab
  rw [← coe_substAlgHom ha, ← coe_substAlgHom hb, map_sub, map_sub] at he
  have hΓab : Γ.toPowerSeries.subst a - Γ.toPowerSeries.subst b = (a 0-b 0)+(a 1-b 1) := by
    rw [hΓ]
    simp only [← coe_substAlgHom ha, ← coe_substAlgHom hb, map_add, substAlgHom_X]
    have hpowers : (fun i => (a i)^(p^2)) = (fun i => (b i)^(p^2)) := by
      funext i; exact highPower_eq p 2 (by omega) π h.squareZero _ _ (hab i)
    rw [coe_substAlgHom ha, coe_substAlgHom hb,
      subst_expand_inner _ _ _ a ha, subst_expand_inner _ _ _ b hb, hpowers]
    ring
  simp only [coe_substAlgHom] at he
  linear_combination he + hΓab

lemma series_perturbation (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (n : ℕ) (hn : 0 < n) (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (f : PowerSeries R) (hf : f.map ρ = PowerSeries.X^(p^n))
    (a b : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (hab : a.map π = b.map π) : f.subst a = f.subst b := by
  have he : (f-PowerSeries.X^(p^n)).subst a = (f-PowerSeries.X^(p^n)).subst b := by
    apply unisubst_eq_of_annihilate ρ π (fun c e hc he => by rw [mul_comm]; exact h.annihilate e c he hc)
    · change MvPowerSeries.map ρ (f-PowerSeries.X^(p^n)) = 0
      rw [map_sub, map_pow, show MvPowerSeries.map ρ f = PowerSeries.X^(p^n) from hf]
      simp [PowerSeries.X]
    · exact ha
    · exact hb
    · exact hab
  rw [PowerSeries.subst_sub ha, PowerSeries.subst_sub hb, PowerSeries.subst_pow ha,
    PowerSeries.subst_pow hb, PowerSeries.subst_X ha, PowerSeries.subst_X hb,
    highPower_eq p n hn π h.squareZero a b hab] at he
  have hh := congrArg (fun z => z+b^(p^n)) he
  simpa only [sub_add_cancel] using hh

def point (F : FormalGroup R) (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) : F.Point σ := ⟨a,ha⟩

lemma multiplication_at_point (F : FormalGroup R) (n : ℕ)
    (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) :
    (multiplicationSeries F n).subst a = (n • point F a ha).val := by
  induction n with
  | zero =>
    rw [multiplication_zero, ← PowerSeries.coe_substAlgHom ha, map_zero]
    rfl
  | succ n ih =>
    rw [multiplication_succ, succ_nsmul]
    have hn : HasSubst ![multiplicationSeries F n, PowerSeries.X] :=
      hasSubst_of_constantCoeff_zero (by intro i; fin_cases i; exact multiplication_constant F n; exact PowerSeries.constantCoeff_X)
    change MvPowerSeries.subst (fun _ : Unit => a)
      (F.toPowerSeries.subst ![multiplicationSeries F n, PowerSeries.X]) =
      F.toPowerSeries.subst ![(n • point F a ha).val,a]
    rw [subst_comp_subst_apply hn ha.const]
    congr 1
    funext i; fin_cases i
    · exact ih
    · exact PowerSeries.subst_X ha

lemma multiplication_preserves_addition (F : FormalGroup R) [F.IsComm] (n : ℕ) :
    (multiplicationSeries F n).subst F.toPowerSeries =
      F.toPowerSeries.subst ![(multiplicationSeries F n).subst (X 0),
        (multiplicationSeries F n).subst (X 1)] := by
  let x : F.Point (Fin 2) := ⟨X 0, PowerSeries.HasSubst.X 0⟩
  let y : F.Point (Fin 2) := ⟨X 1, PowerSeries.HasSubst.X 1⟩
  have hxy : (x+y).val = F.toPowerSeries := by
    change F.toPowerSeries.subst ![X 0, X 1] = F.toPowerSeries
    rw [show (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) = X by funext i; fin_cases i <;> rfl]
    exact congrFun MvPowerSeries.subst_self F.toPowerSeries
  have hh := congrArg (fun a : F.Point (Fin 2) => a.val) (nsmul_add x y n)
  change (n • (x+y)).val = F.toPowerSeries.subst ![(n•x).val,(n•y).val] at hh
  have hv (a : F.Point (Fin 2)) : (n•a).val = (multiplicationSeries F n).subst a.val := by
    have hp : point F a.val a.prop = a := rfl
    have hh := (multiplication_at_point F n a.val a.prop).symm
    rw [hp] at hh
    exact hh
  rw [hv (x+y), hv x, hv y, hxy] at hh
  exact hh

lemma multiplication_reduction (F Γ : FormalGroup R) (ρ : R →+* K)
    (hF : F.map ρ = Γ.map ρ) (p q : ℕ)
    (hΓ : multiplicationSeries Γ p = PowerSeries.X^q) :
    (multiplicationSeries F p).map ρ = PowerSeries.X^q := by
  rw [← multiplication_map, hF, multiplication_map, hΓ]
  change MvPowerSeries.map ρ (PowerSeries.X^q) = _
  rw [map_pow]
  simp [PowerSeries.X]

theorem linearized_p_hom (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F G Γ : FormalGroup R) [F.IsComm] [G.IsComm]
    (hπ : F.map π = G.map π) (hF : F.map ρ = Γ.map ρ) (hG : G.map ρ = Γ.map ρ)
    (H : MvPowerSeries (Fin 2) R)
    (hΓ : Γ.toPowerSeries = X 0 + X 1 + expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H)
    (hΓp : multiplicationSeries Γ p = PowerSeries.X^(p^3)) :
    delta Γ (multiplicationSeries F p - multiplicationSeries G p) =
      expand (p^3) (pow_ne_zero _ hp.out.ne_zero) (F.toPowerSeries-G.toPowerSeries) := by
  let P := multiplicationSeries F p
  let Q := multiplicationSeries G p
  let v := P-Q
  let D := F.toPowerSeries-G.toPowerSeries
  have hPπ : P.map π = Q.map π := by
    dsimp [P,Q]; rw [← multiplication_map, ← multiplication_map, hπ]
  have hvπ : v.map π = 0 := by
    change MvPowerSeries.map π (P-Q) = 0
    rw [map_sub]; exact sub_eq_zero.mpr hPπ
  have hDπ : D.map π = 0 := by
    dsimp [D]
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg FormalGroup.toPowerSeries hπ)
  have hPρ : P.map ρ = PowerSeries.X^(p^3) := multiplication_reduction F Γ ρ hF p _ hΓp
  have hQρ : Q.map ρ = PowerSeries.X^(p^3) := multiplication_reduction G Γ ρ hG p _ hΓp
  have hFs : PowerSeries.HasSubst F.toPowerSeries := .of_constantCoeff_zero F.zero_constantCoeff
  have hGs : PowerSeries.HasSubst G.toPowerSeries := .of_constantCoeff_zero G.zero_constantCoeff
  have hΓs : PowerSeries.HasSubst Γ.toPowerSeries := .of_constantCoeff_zero Γ.zero_constantCoeff
  have hFGπ : F.toPowerSeries.map π = G.toPowerSeries.map π := congrArg FormalGroup.toPowerSeries hπ
  have hFΓρ : F.toPowerSeries.map ρ = Γ.toPowerSeries.map ρ := congrArg FormalGroup.toPowerSeries hF
  have hGΓρ : G.toPowerSeries.map ρ = Γ.toPowerSeries.map ρ := congrArg FormalGroup.toPowerSeries hG
  have heQ : Q.subst F.toPowerSeries = Q.subst G.toPowerSeries :=
    series_perturbation p 3 (by omega) π ρ h Q hQρ _ _ hFs hGs hFGπ
  have hev : v.subst F.toPowerSeries = v.subst Γ.toPowerSeries :=
    unisubst_eq_of_annihilate π ρ h.annihilate v hvπ _ _ hFs hΓs hFΓρ
  have hleft : P.subst F.toPowerSeries - Q.subst G.toPowerSeries = v.subst Γ.toPowerSeries := by
    rw [← hev, PowerSeries.subst_sub hFs]
    exact congrArg (fun z => P.subst F.toPowerSeries-z) heQ.symm
  let A : Fin 2 → MvPowerSeries (Fin 2) R := fun i => P.subst (X i)
  let B : Fin 2 → MvPowerSeries (Fin 2) R := fun i => Q.subst (X i)
  have hAz (i : Fin 2) : (A i).constantCoeff = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) P (multiplication_constant F p)
  have hBz (i : Fin 2) : (B i).constantCoeff = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) Q (multiplication_constant G p)
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero hAz
  have hBs : HasSubst B := hasSubst_of_constantCoeff_zero hBz
  have hABπ : ∀ i, (A i).map π = (B i).map π := by
    intro i; dsimp [A,B]
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X i), PowerSeries.map_subst (PowerSeries.HasSubst.X i), hPπ]
  have hAXρ : ∀ i, (A i).map ρ = ((X i : MvPowerSeries (Fin 2) R)^(p^3)).map ρ := by
    intro i; dsimp [A]
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X i), hPρ, map_X,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i), map_pow, map_X]
  have hDD : D.subst A = expand (p^3) (pow_ne_zero _ hp.out.ne_zero) D := by
    rw [expand, substAlgHom_apply]
    exact subst_eq_of_annihilate π ρ h.annihilate D hDπ A _ hAs (HasSubst.X_pow (pow_ne_zero _ hp.out.ne_zero)) hAXρ
  have hGG := law_perturbation p π ρ h G Γ hGΓρ H hΓ A B hAs hBs hABπ
  have hright : F.toPowerSeries.subst A - G.toPowerSeries.subst B =
      expand (p^3) (pow_ne_zero _ hp.out.ne_zero) D + v.subst (X 0) + v.subst (X 1) := by
    change (F.toPowerSeries-G.toPowerSeries).subst A = _ at hDD
    rw [MvPowerSeries.subst_sub hAs] at hDD
    simp only [v, PowerSeries.subst_sub (PowerSeries.HasSubst.X (0 : Fin 2)),
      PowerSeries.subst_sub (PowerSeries.HasSubst.X (1 : Fin 2))]
    dsimp [A,B] at hGG
    linear_combination hDD+hGG
  have heF := multiplication_preserves_addition F p
  have heG := multiplication_preserves_addition G p
  have hAF : A = ![P.subst (X 0),P.subst (X 1)] := by funext i; fin_cases i <;> rfl
  have hBG : B = ![Q.subst (X 0),Q.subst (X 1)] := by funext i; fin_cases i <;> rfl
  change P.subst F.toPowerSeries = F.toPowerSeries.subst _ at heF
  change Q.subst G.toPowerSeries = G.toPowerSeries.subst _ at heG
  rw [← hAF] at heF
  rw [← hBG] at heG
  change v.subst Γ.toPowerSeries-v.subst (X 0)-v.subst (X 1) = _
  linear_combination -hleft + hright + heF - heG

lemma series_map_zero_of_ker_le (π : R →+* S) (ρ : R →+* K)
    (h : ∀ a, π a = 0 → ρ a = 0) (f : MvPowerSeries σ R) (hf : f.map π = 0) :
    f.map ρ = 0 := by
  ext d
  rw [coeff_map, map_zero]
  apply h
  simpa only [coeff_map, map_zero] using congrArg (coeff d) hf

lemma coordinate_of_coboundary (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F G Γ : FormalGroup R) (hF : F.map ρ = Γ.map ρ) (hG : G.map ρ = Γ.map ρ)
    (H : MvPowerSeries (Fin 2) R)
    (hΓ : Γ.toPowerSeries = X 0 + X 1 + expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H)
    (w : PowerSeries R) (hw0 : w.constantCoeff = 0) (hwπ : w.map π = 0)
    (hd : delta Γ w = F.toPowerSeries-G.toPowerSeries) :
    ∃ e : CoordinateIso F G, e.series = PowerSeries.X-w ∧ e.series.map π = PowerSeries.X := by
  have hwρ : w.map ρ = 0 := series_map_zero_of_ker_le π ρ h.ker_le w hwπ
  let u := PowerSeries.X-w
  let z := PowerSeries.X+w
  have hu0 : u.constantCoeff = 0 := by simp [u, hw0]
  have hz0 : z.constantCoeff = 0 := by simp [z, hw0]
  have hu : PowerSeries.HasSubst u := .of_constantCoeff_zero hu0
  have hz : PowerSeries.HasSubst z := .of_constantCoeff_zero hz0
  have huπ : u.map π = PowerSeries.X := by simp [u,hwπ]
  have hzπ : z.map π = PowerSeries.X := by simp [z,hwπ]
  have hwu : w.subst u = w := by
    have hh := subst_eq_of_squareZero π h.squareZero w hwπ u PowerSeries.X hu PowerSeries.HasSubst.X' (by simpa only [PowerSeries.X, map_X] using (show MvPowerSeries.map π u = PowerSeries.X from huπ))
    simpa only [PowerSeries.X_subst] using hh
  have hwz : w.subst z = w := by
    have hh := subst_eq_of_squareZero π h.squareZero w hwπ z PowerSeries.X hz PowerSeries.HasSubst.X' (by simpa only [PowerSeries.X, map_X] using (show MvPowerSeries.map π z = PowerSeries.X from hzπ))
    simpa only [PowerSeries.X_subst] using hh
  have huz : u.subst z = PowerSeries.X := by
    dsimp [u]; rw [PowerSeries.subst_sub hz, PowerSeries.subst_X hz, hwz]
    dsimp [z]; ring
  have hzu : z.subst u = PowerSeries.X := by
    change (PowerSeries.X+w).subst u = _
    rw [PowerSeries.subst_add hu, PowerSeries.subst_X hu, hwu]
    dsimp [u]; ring
  have hFs : PowerSeries.HasSubst F.toPowerSeries := .of_constantCoeff_zero F.zero_constantCoeff
  have hΓs : PowerSeries.HasSubst Γ.toPowerSeries := .of_constantCoeff_zero Γ.zero_constantCoeff
  have hwF : w.subst F.toPowerSeries = w.subst Γ.toPowerSeries :=
    unisubst_eq_of_annihilate π ρ h.annihilate w hwπ _ _ hFs hΓs (congrArg FormalGroup.toPowerSeries hF)
  let A : Fin 2 → MvPowerSeries (Fin 2) R := fun i => u.subst (X i)
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero (fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) u hu0)
  have hAX : ∀ i, (A i).map π = (X i).map π := by
    intro i; dsimp [A]
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X i), huπ, map_X,
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  have hh := law_perturbation p π ρ h G Γ (congrArg FormalGroup.toPowerSeries hG) H hΓ A X hAs HasSubst.X hAX
  rw [congrFun subst_self G.toPowerSeries] at hh
  have hA (i : Fin 2) : A i = X i-w.subst (X i) := by
    dsimp [A,u]; rw [PowerSeries.subst_sub (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  rw [hA 0,hA 1] at hh
  dsimp only [id] at hh
  have he : u.subst F.toPowerSeries = G.toPowerSeries.subst ![u.subst (X 0),u.subst (X 1)] := by
    change (PowerSeries.X-w).subst F.toPowerSeries = _
    rw [PowerSeries.subst_sub hFs, PowerSeries.subst_X hFs,hwF]
    rw [show (![u.subst (X 0),u.subst (X 1)] : Fin 2 → MvPowerSeries (Fin 2) R) = A by
      funext i; fin_cases i <;> rfl]
    dsimp [delta] at hd
    linear_combination -hh-hd
  refine ⟨⟨u,z,hu0,hz0,huz,hzu,he⟩,rfl,huπ⟩

lemma multiplication_linear (F : FormalGroup R) (n : ℕ) :
    (multiplicationSeries F n).coeff 1 = (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [multiplication_succ, OriginalDifferentialSupport.coeff_one_formal_add _ _ _
      (multiplication_constant F n) PowerSeries.constantCoeff_X, ih]
    simp

lemma power_expand_iterate (p : ℕ) [hp : Fact p.Prime] (f : MvPowerSeries σ R)
    (hf : f^p = expand p hp.out.ne_zero f) (n : ℕ) :
    f^(p^n) = expand (p^n) (pow_ne_zero _ hp.out.ne_zero) f := by
  induction n with
  | zero => simp [MvPowerSeries.expand_one]
  | succ n ih =>
    calc
      f^(p^(n+1)) = (f^(p^n))^p := by rw [pow_succ,pow_mul]
      _ = expand (p^n) (pow_ne_zero _ hp.out.ne_zero) (expand p hp.out.ne_zero f) := by
        rw [ih, ← map_pow, hf]
      _ = expand (p^(n+1)) (pow_ne_zero _ hp.out.ne_zero) f := by
        simpa only [pow_succ] using (expand_mul (p^n) (pow_ne_zero _ hp.out.ne_zero) p hp.out.ne_zero f).symm

theorem small_equivalence_of_matching_parameters [Nontrivial R]
    (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F G Γ : FormalGroup R) [F.IsComm] [G.IsComm]
    (hπ : F.map π = G.map π) (hF : F.map ρ = Γ.map ρ) (hG : G.map ρ = Γ.map ρ)
    (H : MvPowerSeries (Fin 2) R)
    (hΓ : Γ.toPowerSeries = X 0 + X 1 + expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H)
    (hΓp : multiplicationSeries Γ p = PowerSeries.X^(p^3))
    (hΓFr : Γ.toPowerSeries^p = expand p hp.out.ne_zero Γ.toPowerSeries)
    (h₁ : (multiplicationSeries F p).coeff p = (multiplicationSeries G p).coeff p)
    (h₂ : (multiplicationSeries F p).coeff (p^2) = (multiplicationSeries G p).coeff (p^2)) :
    ∃ e : CoordinateIso F G, e.series.map π = PowerSeries.X := by
  let v := multiplicationSeries F p-multiplicationSeries G p
  let D := F.toPowerSeries-G.toPowerSeries
  have hv : delta Γ v = expand (p^3) (pow_ne_zero _ hp.out.ne_zero) D :=
    linearized_p_hom p π ρ h F G Γ hπ hF hG H hΓ hΓp
  have hv0 : v.constantCoeff = 0 := by simp [v]
  have hv1 : v.coeff 1 = 0 := by simp [v, multiplication_linear]
  have hH : Γ.toPowerSeries-X 0-X 1 = expand (p^2) (pow_ne_zero _ hp.out.ne_zero) H := by rw [hΓ]; ring
  obtain ⟨a,b,w,hw0,he⟩ := tangent_decomposition p Γ H hΓFr hH v hv0 hv1 D hv
  have hpp : p < p^2 := by nlinarith [hp.out.one_lt]
  have hppq : p^2 < p^3 := by exact pow_lt_pow_right₀ hp.out.one_lt (by omega)
  have hq1 : ¬p^3 ∣ p := Nat.not_dvd_of_pos_of_lt hp.out.pos (lt_trans hpp hppq)
  have hq2 : ¬p^3 ∣ p^2 := Nat.not_dvd_of_pos_of_lt (pow_pos hp.out.pos _) hppq
  have hvp : v.coeff p = 0 := by simp only [v,map_sub,h₁,sub_self]
  have hvp2 : v.coeff (p^2) = 0 := by simp only [v,map_sub,h₂,sub_self]
  have ha : a = 0 := by
    have hh := congrArg (PowerSeries.coeff p) he
    simpa [hvp, PowerSeries.coeff_expand_of_not_dvd _ _ _ hq1, PowerSeries.coeff_X_pow,
      ne_of_lt hpp, ne_of_gt hpp] using hh.symm
  have hb : b = 0 := by
    have hh := congrArg (PowerSeries.coeff (p^2)) he
    simpa [hvp2, ha, PowerSeries.coeff_expand_of_not_dvd _ _ _ hq2, PowerSeries.coeff_X_pow] using hh.symm
  have he' : v = PowerSeries.expand (p^3) (pow_ne_zero _ hp.out.ne_zero) w := by simpa [ha,hb] using he
  have hd : delta Γ w = D := by
    apply expand_injective (p^3) (pow_ne_zero _ hp.out.ne_zero)
    rw [← delta_expand (p^3) (pow_ne_zero _ hp.out.ne_zero) Γ
      (power_expand_iterate p Γ.toPowerSeries hΓFr 3), ← he', hv]
  have hvπ : v.map π = 0 := by
    change MvPowerSeries.map π (multiplicationSeries F p-multiplicationSeries G p) = 0
    rw [map_sub, show MvPowerSeries.map π (multiplicationSeries F p) = multiplicationSeries (F.map π) p from (multiplication_map F π p).symm,
      show MvPowerSeries.map π (multiplicationSeries G p) = multiplicationSeries (G.map π) p from (multiplication_map G π p).symm, hπ,sub_self]
  have hwπ : w.map π = 0 := by
    have hh := hvπ
    rw [he',PowerSeries.map_expand] at hh
    ext n
    have hhc := congrArg (PowerSeries.coeff ((p^3)*n)) hh
    simpa only [PowerSeries.coeff_expand_mul, map_zero] using hhc
  obtain ⟨e, _, heπ⟩ := coordinate_of_coboundary p π ρ h F G Γ hF hG H hΓ w hw0 hwπ hd
  exact ⟨e,heπ⟩

lemma small_isomorphism_pseries (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F G : FormalGroup R) (e : CoordinateIso F G)
    (he : e.series.map π = PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ = PowerSeries.X^(p^3))
    (hG : (multiplicationSeries G p).map ρ = PowerSeries.X^(p^3)) :
    multiplicationSeries F p + PowerSeries.expand (p^3) (pow_ne_zero _ hp.out.ne_zero)
      (e.series-PowerSeries.X) = multiplicationSeries G p := by
  let d := e.series-PowerSeries.X
  have hd : d.map π = 0 := by simp [d,he]
  have hpq : p^3 ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hq : PowerSeries.HasSubst (PowerSeries.X^(p^3) : PowerSeries R) := .X_pow hpq
  have hdf : d.subst (multiplicationSeries F p) = d.subst (PowerSeries.X^(p^3)) :=
    unisubst_eq_of_annihilate π ρ h.annihilate d hd _ _
      (.of_constantCoeff_zero (multiplication_constant F p)) hq
      (by simpa only [PowerSeries.X,map_pow,map_X] using
        (show MvPowerSeries.map ρ (multiplicationSeries F p) = PowerSeries.X^(p^3) from hF))
  have hes : PowerSeries.HasSubst e.series := .of_constantCoeff_zero e.zero_series
  have hQg : (multiplicationSeries G p).subst e.series = multiplicationSeries G p := by
    have HH := series_perturbation p 3 (by omega) π ρ h (multiplicationSeries G p) hG
      e.series PowerSeries.X hes PowerSeries.HasSubst.X'
      (by simpa only [PowerSeries.X,map_X] using
        (show MvPowerSeries.map π e.series = PowerSeries.X from he))
    simpa only [PowerSeries.X_subst] using HH
  have hc := coordinate_multiplication F G e p
  rw [hQg] at hc
  have he' : e.series = PowerSeries.X+d := by dsimp [d]; ring
  conv_lhs at hc => rw [he',PowerSeries.subst_add (.of_constantCoeff_zero (multiplication_constant F p)),
    PowerSeries.subst_X (.of_constantCoeff_zero (multiplication_constant F p)),hdf]
  simpa only [PowerSeries.expand_apply] using hc

lemma small_isomorphism_lowcoeff (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F G : FormalGroup R) (e : CoordinateIso F G)
    (he : e.series.map π = PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ = PowerSeries.X^(p^3))
    (hG : (multiplicationSeries G p).map ρ = PowerSeries.X^(p^3))
    (n : ℕ) (hn : 0 < n) (hnq : n < p^3) :
    (multiplicationSeries F p).coeff n = (multiplicationSeries G p).coeff n := by
  have HH := congrArg (PowerSeries.coeff n) (small_isomorphism_pseries p π ρ h F G e he hF hG)
  simpa only [map_add,PowerSeries.coeff_expand_of_not_dvd _ _ _ (Nat.not_dvd_of_pos_of_lt hn hnq),add_zero] using HH

lemma small_automorphism_rigid (p : ℕ) [hp : Fact p.Prime] [CharP R p]
    (π : R →+* S) (ρ : R →+* K) (h : IsSmall π ρ)
    (F : FormalGroup R) (e : CoordinateIso F F)
    (he : e.series.map π = PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ = PowerSeries.X^(p^3)) :
    e.series = PowerSeries.X := by
  have hh := small_isomorphism_pseries p π ρ h F F e he hF hF
  have hz : PowerSeries.expand (p^3) (pow_ne_zero _ hp.out.ne_zero) (e.series-PowerSeries.X) = 0 := add_eq_left.mp hh
  apply sub_eq_zero.mp
  ext n
  have hc := congrArg (PowerSeries.coeff ((p^3)*n)) hz
  simpa only [PowerSeries.coeff_expand_mul,map_zero] using hc

end HeightThree.SmallExtension

end

end OAI
