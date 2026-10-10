import OAI.Algebra.FormalGroup.Honda.Leading

namespace OAI

noncomputable section

namespace HeightThree.HondaFrobenius
open MvPowerSeries HeightThree.HondaLeading HeightThree.HondaTarget
open HeightThree.HondaJets HeightThree.HomogeneousCocycle
variable {K σ : Type*} [Field K]

lemma law_pair_subst (F : FormalGroup K) (a b : PowerSeries K) (c : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) (hc : PowerSeries.HasSubst c) :
    PowerSeries.subst c (pair F a b) = pair F (a.subst c) (b.subst c) := by
  have hab : MvPowerSeries.HasSubst ![a,b] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption)
  change (F.toPowerSeries.subst ![a,b]).subst (fun _ : Unit => c) = _
  rw [MvPowerSeries.subst_comp_subst_apply hab hc.const]
  congr 1
  funext i; fin_cases i <;> rfl

lemma point_multiplication (F : FormalGroup K) (a : F.Point σ) (ha : a.val.constantCoeff=0) (n : ℕ) :
    (n • a).val = (multiplicationSeries F n).subst a.val := by
  induction n with
  | zero =>
    change 0=PowerSeries.subst a.val 0
    rw [←PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero ha),map_zero]
  | succ n ih =>
    rw [succ_nsmul,FormalGroup.add_apply,ih,multiplication_succ,
      law_pair_subst F _ _ _ (multiplication_constant F n) PowerSeries.constantCoeff_X a.prop,
      PowerSeries.subst_X a.prop]

lemma multiplication_add (F : FormalGroup K) [F.IsComm] (n : ℕ) :
    (multiplicationSeries F n).subst F.toPowerSeries =
      F.toPowerSeries.subst ![(multiplicationSeries F n).subst (X 0),
        (multiplicationSeries F n).subst (X 1)] := by
  let a : F.Point (Fin 2) := ⟨X 0,PowerSeries.HasSubst.X 0⟩
  let b : F.Point (Fin 2) := ⟨X 1,PowerSeries.HasSubst.X 1⟩
  have ha : a.val.constantCoeff=0 := by simp [a]
  have hb : b.val.constantCoeff=0 := by simp [b]
  have he : (a+b).val=F.toPowerSeries := by
    change F.toPowerSeries.subst ![X 0,X 1]=_
    exact pair_subst_self _
  have hh := congrArg Subtype.val (nsmul_add a b n)
  rw [point_multiplication F (a+b) (pair_const F _ _ ha hb) n,he] at hh
  rw [FormalGroup.add_apply,point_multiplication F a ha n,point_multiplication F b hb n] at hh
  exact hh

lemma Xpow_subst (q : ℕ) (a : MvPowerSeries σ K) (ha : a.constantCoeff=0) :
    (PowerSeries.X^q : PowerSeries K).subst a=a^q := by
  rw [PowerSeries.subst_pow (.of_constantCoeff_zero ha),
    PowerSeries.subst_X (.of_constantCoeff_zero ha)]

lemma honda_expand (p q : ℕ) (hq : q≠0) (F : FormalGroup K) [F.IsComm]
    (hF : multiplicationSeries F p=PowerSeries.X^q) :
    F.toPowerSeries^q=F.toPowerSeries.expand q hq := by
  have hh := multiplication_add F p
  rw [hF,Xpow_subst q _ F.zero_constantCoeff,Xpow_subst q _ (constantCoeff_X 0),
    Xpow_subst q _ (constantCoeff_X 1)] at hh
  rw [MvPowerSeries.expand,MvPowerSeries.coe_substAlgHom]
  convert hh using 2
  funext i; fin_cases i <;> rfl

theorem honda_coefficients_fixed (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (h : ℕ) (F : FormalGroup K) [F.IsComm]
    (hF : multiplicationSeries F p=PowerSeries.X^(p^h)) :
    F.toPowerSeries.map (iterateFrobenius K p h)=F.toPowerSeries := by
  have hq : p^h≠0 := pow_ne_zero _ hp.out.ne_zero
  apply expand_injective (p^h) hq
  rw [←map_expand,MvPowerSeries.map_iterateFrobenius_expand p hp.out.ne_zero]
  exact honda_expand p (p^h) hq F hF

lemma map_leading (F G : FormalGroup K) (n : ℕ) (φ : K →+* K)
    (hF : F.toPowerSeries.map φ=F.toPowerSeries) (hG : G.toPowerSeries.map φ=G.toPowerSeries) :
    (leading F G n).map φ=leading F G n := by
  have he : (F.toPowerSeries-G.toPowerSeries).map φ=F.toPowerSeries-G.toPowerSeries := by
    rw [map_sub,hF,hG]
  ext d
  rw [coeff_map,coeff_homogeneousComponent]
  split_ifs with hd
  · exact congrArg (coeff d) he
  · exact map_zero _

lemma coboundary_fixed (n : ℕ) (φ : K →+* K) :
    (coboundary (K:=K) n).map φ=coboundary n := by
  simp [coboundary]

lemma fixed_coboundary_scalar (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : MvPowerSeries (Fin 2) K) (n : ℕ) (hn : 0<n)
    (hC : IsCocycle p D) (hH : D.IsHomogeneous n) (φ : K →+* K)
    (hD : D.map φ=D) : ∃a : K, φ a=a ∧ D=a • coboundary n := by
  obtain ⟨a,ha⟩ := cocycle_is_coboundary p n hn D hC hH
  by_cases he : coboundary (K:=K) n=0
  · refine ⟨0,map_zero _,?_⟩
    rw [ha,he,smul_zero,smul_zero]
  · obtain ⟨d,hd⟩ : ∃d,coeff d (coboundary (K:=K) n)≠0 := by
      by_contra hh
      apply he
      ext d
      have h0 : coeff d (coboundary (K:=K) n)=0 := not_not.mp (not_exists.mp hh d)
      simpa using h0
    have hc : φ (coeff d (coboundary (K:=K) n))=coeff d (coboundary (K:=K) n) :=
      congrArg (coeff d) (coboundary_fixed n φ)
    have hh := congrArg (coeff d) hD
    simp only [coeff_map,ha,map_smul,smul_eq_mul,map_mul,hc] at hh
    exact ⟨(a), (mul_right_cancel₀ hd hh), ha⟩

end HeightThree.HondaFrobenius

end

end OAI
