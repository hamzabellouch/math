import OAI.Combinatorics.FiniteCircle.Fourier

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem character_multiplier (G : Type*) [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) (x : G) : Complex.normSq (1-χ x) = 2-2*(χ x).re := by
  rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq (χ x), χ.norm_apply]
  norm_num

 theorem character_multiplier_le_four {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) (x : G) : Complex.normSq (1-χ x) ≤ 4 := by
  rw [character_multiplier]
  have h := ((abs_le.mp (Complex.abs_re_le_norm (χ x))).1)
  rw [χ.norm_apply] at h
  linarith

 theorem character_subgroup_mean {G : Type*} [AddCommGroup G] [Fintype G]
    (H : AddSubgroup G) [Fintype H] (χ : AddChar G ℂ)
    (hn : χ.compAddMonoidHom H.subtype ≠ 0) :
    (𝔼 x : H, Complex.normSq (1-χ x)) = 2 := by
  classical
  have hz := (AddChar.expect_eq_zero_iff_ne_zero (ψ := χ.compAddMonoidHom H.subtype)).mpr hn
  have hr : (𝔼 x : H, (χ x).re) = 0 := by
    have := congrArg Complex.re hz
    simpa only [Fintype.expect_eq_sum_div_card, Complex.div_ofReal_re,
      Complex.re_sum, Complex.zero_re, AddChar.compAddMonoidHom_apply,
      AddSubgroup.subtype_apply, ← Complex.ofReal_natCast] using this
  simp_rw [character_multiplier]
  rw [Finset.expect_sub_distrib, ← Finset.mul_expect, hr]
  simp

 theorem zmod_character_int {M : ℕ} [NeZero M] (a b : ℤ) :
    (AddChar.zmodAddEquiv (a : ZMod M)) (b : ZMod M) =
      Complex.exp ((2*Real.pi*((a:ℝ)*b/M):ℝ)*Complex.I) := by
  change ((AddChar.zmod M (a : ZMod M) (b : ZMod M) : Circle) : ℂ) = _
  rw [AddChar.zmod_intCast, Circle.coe_exp]

 theorem zmod_character_mul {M : ℕ} [NeZero M] (x y : ZMod M) :
    AddChar.zmodAddEquiv x y = AddChar.zmodAddEquiv (x*y) 1 := by
  change ((AddChar.zmod M x y : Circle) : ℂ) = ((AddChar.zmod M (x*y) 1 : Circle) : ℂ)
  simp only [AddChar.zmod, AddChar.compAddMonoidHom_apply, AddMonoidHom.comp_apply,
    AddMonoidHom.coe_mulLeft, mul_one]

 theorem zmod_character_one_injective {M : ℕ} [NeZero M] :
    Function.Injective (fun x : ZMod M => AddChar.zmodAddEquiv x 1) := by
  intro x y h
  dsimp only at h
  apply AddChar.zmodAddEquiv.injective
  apply AddChar.ext
  intro a
  obtain ⟨b,rfl⟩ := ZMod.natCast_zmod_surjective a
  have hx (z : ZMod M) : AddChar.zmodAddEquiv z (b : ZMod M) =
      (AddChar.zmodAddEquiv z 1)^b := by
    rw [← nsmul_one (n := b), AddChar.map_nsmul_eq_pow]
  rw [hx, hx, h]

 theorem zmod_character_eq_one {M : ℕ} [NeZero M] (x y : ZMod M) :
    AddChar.zmodAddEquiv x y = 1 ↔ x*y = 0 := by
  rw [zmod_character_mul]
  have hz : AddChar.zmodAddEquiv (0 : ZMod M) 1 = 1 := by
    rw [map_zero]; rfl
  rw [← hz]
  exact zmod_character_one_injective.eq_iff

 theorem circle_character_re {M : ℕ} [NeZero M] (x : ZMod M) (a : ℕ) :
    (AddChar.zmodAddEquiv x (a : ZMod M)).re =
      Real.cos (2*Real.pi*((x.valMinAbs.natAbs:ℝ)*a/M)) := by
  have he := zmod_character_int (M := M) x.valMinAbs (a:ℤ)
  simp only [ZMod.coe_valMinAbs, Int.cast_natCast] at he
  rw [he, Complex.exp_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, sub_self, Real.exp_zero,
    Complex.mul_im, mul_one, add_zero, one_mul]
  have habs : (x.valMinAbs.natAbs:ℝ) = |(x.valMinAbs:ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  by_cases hx : 0 ≤ x.valMinAbs
  · rw [habs, abs_of_nonneg (by exact_mod_cast hx)]
  · have hx' : (x.valMinAbs:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hx))
    rw [habs, abs_of_nonpos hx']
    rw [show 2*Real.pi*(-(x.valMinAbs:ℝ)*a/M) = -(2*Real.pi*((x.valMinAbs:ℝ)*a/M)) by ring,
      Real.cos_neg]

theorem dyadic_detect {M : ℕ} [NeZero M] (x : ZMod M) (hx : x ≠ 0) :
    ∃ j < Nat.log 2 M+1,
      4*(x.valMinAbs.natAbs:ℝ) ≤
        (M:ℝ)/(2:ℝ)^j * Complex.normSq (1-AddChar.zmodAddEquiv x ((2^j : ℕ):ZMod M)) := by
  have hM : (0:ℝ) < M := by exact_mod_cast NeZero.pos M
  have hn : 0 < x.valMinAbs.natAbs := by
    apply Nat.pos_of_ne_zero
    simpa [ZMod.valMinAbs_eq_zero] using hx
  have hnR : (0:ℝ) < x.valMinAbs.natAbs := by exact_mod_cast hn
  have hle : 2*x.valMinAbs.natAbs ≤ M := by have := ZMod.natAbs_valMinAbs_le x; omega
  have hleR : 2*(x.valMinAbs.natAbs:ℝ) ≤ M := by exact_mod_cast hle
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near
    ((le_div_iff₀ (by positivity : (0:ℝ)<2*x.valMinAbs.natAbs)).mpr (by simpa using hleR))
    (show (1:ℝ)<2 by norm_num)
  have hp : (0:ℝ) < (2:ℝ)^j := by positivity
  have hn1 : (1:ℝ) ≤ x.valMinAbs.natAbs := by exact_mod_cast hn
  have hpow : (2:ℝ)^j ≤ M := by
    have := (le_div_iff₀ (by positivity : (0:ℝ)<2*x.valMinAbs.natAbs)).mp hj
    nlinarith
  have hjlog : j < Nat.log 2 M+1 := by
    have hpN : 2^j ≤ M := by exact_mod_cast hpow
    have := Nat.le_log_of_pow_le (by norm_num : 1<2) hpN
    omega
  refine ⟨j,hjlog,?_⟩
  have ha : 1/4 < (x.valMinAbs.natAbs:ℝ)*(2:ℝ)^j/M := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<2*x.valMinAbs.natAbs), pow_succ] at hj'
    rw [lt_div_iff₀ hM]
    nlinarith
  have hb : (x.valMinAbs.natAbs:ℝ)*(2:ℝ)^j/M ≤ 1/2 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ)<2*x.valMinAbs.natAbs)).mp hj
    rw [div_le_iff₀ hM]
    nlinarith
  have hcos : Real.cos (2*Real.pi*((x.valMinAbs.natAbs:ℝ)*(2:ℝ)^j/M)) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  have hc : 2 ≤ Complex.normSq (1-AddChar.zmodAddEquiv x ((2^j : ℕ):ZMod M)) := by
    rw [character_multiplier, circle_character_re]
    push_cast
    linarith
  have hq : 2*(x.valMinAbs.natAbs:ℝ) ≤ (M:ℝ)/(2:ℝ)^j := by
    rw [le_div_iff₀ hp]
    have := (le_div_iff₀ (by positivity : (0:ℝ)<2*x.valMinAbs.natAbs)).mp hj
    nlinarith
  nlinarith [div_nonneg hM.le hp.le]

noncomputable def coordinateChar {I : Type*} [DecidableEq I] {M : ℕ}
    (χ : AddChar (I → ZMod M) ℂ) (i : I) : AddChar (ZMod M) ℂ :=
  χ.compAddMonoidHom (AddMonoidHom.single (fun _ : I => ZMod M) i)

noncomputable def coordinateFrequency {I : Type*} [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (i : I) : ZMod M :=
  AddChar.zmodAddEquiv.symm (coordinateChar χ i)

 theorem character_single {I : Type*} [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (i : I) (a : ZMod M) :
    χ (Pi.single i a) = AddChar.zmodAddEquiv (coordinateFrequency χ i) a := by
  rw [coordinateFrequency, AddEquiv.apply_symm_apply]
  rfl

theorem coordinate_dyadic_sum {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) :
    4*(∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ)) ≤
      ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
        Complex.normSq (1-χ (Pi.single i ((2^j.val : ℕ):ZMod M))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : coordinateFrequency χ i = 0
  · simp only [hx, ZMod.valMinAbs_zero, Int.natAbs_zero, Nat.cast_zero, mul_zero]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
  · obtain ⟨j,hj,hd⟩ := dyadic_detect (coordinateFrequency χ i) hx
    rw [← character_single] at hd
    apply hd.trans
    exact Finset.single_le_sum (f := fun j : Fin (Nat.log 2 M+1) =>
      (M:ℝ)/(2:ℝ)^j.val * Complex.normSq (1-χ (Pi.single i ((2^j.val:ℕ):ZMod M))))
      (fun j _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (Finset.mem_univ (⟨j,hj⟩ : Fin (Nat.log 2 M+1)))

theorem weighted_character_inequality {I : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (H : AddSubgroup (I → ZMod M)) [Fintype H]
    (w : I → ZMod M) (B : ℝ) (hB : 0 < B)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ,
      χ.compAddMonoidHom H.subtype = 0 → χ w ≠ 1 →
        B ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (χ : AddChar (I → ZMod M) ℂ) :
    Complex.normSq (1-χ w) ≤
      2*(𝔼 c : H, Complex.normSq (1-χ c)) + (1/B)*
      ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
        Complex.normSq (1-χ (Pi.single i ((2^j.val : ℕ):ZMod M))) := by
  have hs : 0 ≤ ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
      Complex.normSq (1-χ (Pi.single i ((2^j.val : ℕ):ZMod M))) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (by positivity) (Complex.normSq_nonneg _)))
  have hc : 0 ≤ (𝔼 c : H, Complex.normSq (1-χ c)) :=
    Finset.expect_nonneg (fun c _ => Complex.normSq_nonneg _)
  by_cases ht : χ.compAddMonoidHom H.subtype = 0
  · by_cases hw : χ w = 1
    · simp only [hw, sub_self, map_zero]
      positivity
    · have hm := coordinate_dyadic_sum χ
      have hmass := hb χ ht hw
      have hm' : 4*B ≤ ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
          Complex.normSq (1-χ (Pi.single i ((2^j.val : ℕ):ZMod M))) := by linarith
      have hdiv : 4 ≤ (1/B)*∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
          Complex.normSq (1-χ (Pi.single i ((2^j.val : ℕ):ZMod M))) := by
        rw [one_div_mul_eq_div, le_div_iff₀ hB]
        exact hm'
      have hfour := character_multiplier_le_four χ w
      linarith
  · rw [character_subgroup_mean H χ ht]
    have hfour := character_multiplier_le_four χ w
    have hnn := mul_nonneg (le_of_lt (one_div_pos.mpr hB)) hs
    linarith

 theorem weighted_l1_inequality {I : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (H : AddSubgroup (I → ZMod M)) [Fintype H]
    (w : I → ZMod M) (B : ℝ) (hB : 0 < B)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ,
      χ.compAddMonoidHom H.subtype = 0 → χ w ≠ 1 →
        B ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (f : (I → ZMod M) → RealL1) :
    (𝔼 v, ‖f (v+w)-f v‖) ≤
      2*(𝔼 c : H, 𝔼 v, ‖f (v+c)-f v‖) + (1/B)*
      ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
        (𝔼 v, ‖f (v+Pi.single i ((2^j.val : ℕ):ZMod M))-f v‖) := by
  classical
  let a : H ⊕ (I × Fin (Nat.log 2 M+1)) → (I → ZMod M) :=
    Sum.elim (fun c => c) (fun ij => Pi.single ij.1 ((2^ij.2.val : ℕ):ZMod M))
  let q : H ⊕ (I × Fin (Nat.log 2 M+1)) → ℝ :=
    Sum.elim (fun _ => 2/(Fintype.card H)) (fun ij => (1/B)*((M:ℝ)/(2:ℝ)^ij.2.val))
  have he (D : (I → ZMod M) → ℝ) : (∑ t, q t * D (a t)) =
      2*(𝔼 c : H, D c) + (1/B)*
      ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
        D (Pi.single i ((2^j.val : ℕ):ZMod M)) := by
    simp only [Fintype.sum_sum_type, q, a, Sum.elim_inl, Sum.elim_inr,
      Fintype.sum_prod_type, Fintype.expect_eq_sum_div_card]
    rw [← Finset.mul_sum]
    congr 1
    · ring
    · simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hs (χ : AddChar (I → ZMod M) ℂ) : Complex.normSq (1-χ w) ≤
      ∑ t, q t * Complex.normSq (1-χ (a t)) := by
    rw [he (fun x => Complex.normSq (1-χ x))]
    exact weighted_character_inequality H w B hB hb χ
  have h := spectral_l1_inequality w a q hs f
  rwa [he (fun t => 𝔼 v, ‖f (v+t)-f v‖)] at h

end FiniteCircle

end OAI
