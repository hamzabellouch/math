import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy
import OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
import OAI.NumberTheory.DirichletL.Moments.Counting
import OAI.NumberTheory.DirichletL.Hecke.PrimeRay
import OAI.NumberTheory.DirichletL.Moments.ComparisonReflection

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentOriginalReflectionErrorMass
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckePrimeRay
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma annularWeight_zero_norm (W : ℝ→ℂ) (D freq : ℝ) (hD : 0<D)
    (I : Ideal O) (hI : I≠0) :
    ‖annularWeight W D 0 freq I‖=‖W ((I.absNorm:ℝ)/D)‖ := by
  have hn : 0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn hD)]
  simp only [Complex.neg_re,shift_re,neg_zero,Real.rpow_zero,mul_one]

lemma actual_coefficient_norm (χ : Character) (W : ℝ→ℂ) (D freq B : ℝ)
    (hD : 0<D) (hB : 0≤B) (hW : ∀x,‖W x‖≤B) (I : Ideal O) :
    ‖idealCoeff χ I*annularWeight W D 0 freq I‖≤B := by
  by_cases hI:I=0
  · subst I
    simpa only [idealCoeff_zero,zero_mul,norm_zero] using hB
  rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
  exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma actual_coefficient_support (χ : Character) (W : ℝ→ℂ) (b D freq : ℝ)
    (hD : 0<D) (hs : Function.support W⊆Set.Iic b) (I : Ideal O)
    (hne : idealCoeff χ I*annularWeight W D 0 freq I≠0) :
    (I.absNorm:ℝ)≤max 1 b*D := by
  have hw : W ((I.absNorm:ℝ)/D)≠0:=by
    intro hz
    exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
  exact ((div_le_iff₀ hD).mp (hs hw)).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le)

lemma polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ false W D 0 freq=
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,idealCoeff χ I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he:(∑'I:NonzeroIdeal,idealCoeff χ I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,idealCoeff χ I*annularWeight W D 0 freq I:=by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>idealCoeff χ I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [idealCoeff_zero,zero_mul])
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,
    annularWeight,mul_assoc] using he

lemma normalized_linear_bound (D c : ℝ) (hD : 0<D) (v : ℂ)
    (hv : ‖v‖≤c*D) : ‖(D:ℂ)^(-(1/2:ℂ))*v‖≤c*Real.sqrt D := by
  rw [inverse_half_power D hD.le,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg D)]
  have hs:Real.sqrt D≠0:=(Real.sqrt_pos.mpr hD).ne'
  have hd:D/Real.sqrt D=Real.sqrt D:=by
    apply (div_eq_iff hs).mpr
    simpa only [pow_two] using (Real.sq_sqrt hD.le).symm
  calc
    _ ≤ (Real.sqrt D)⁻¹*(c*D):=mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg D))
    _ = c*(D/Real.sqrt D):=by ring
    _ = _:=by rw [hd]

theorem plain_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ false W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>idealCoeff χ I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change idealCoeff χ (0:Ideal O)*_ = 0
      rw [idealCoeff_zero,zero_mul])
    (actual_coefficient_norm χ W D freq B hD hB hW)
    (actual_coefficient_support χ W b D freq hD hs)
  convert hh using 1; ring

theorem finite_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) (S : Finset (Ideal O)) :
    ‖(D:ℂ)^(-(1/2:ℂ))*∑I∈S,idealCoeff χ I*annularWeight W D 0 freq I‖≤
      (128*max 1 b*B)*Real.sqrt D := by
  apply normalized_linear_bound D _ hD
  let f : Ideal O→ℂ:=fun I=>if I∈S then idealCoeff χ I*annularWeight W D 0 freq I else 0
  have he:(∑'I:Ideal O,f I)=∑I∈S,idealCoeff χ I*annularWeight W D 0 freq I:=by
    rw [tsum_eq_sum (s:=S) (fun I hI=>by simp only [f,ite_eq_right hI])]
    exact Finset.sum_congr rfl (fun I hI=>by simp only [f,ite_eq_left hI])
  have hh:=norm_tsum_ideal_ball f (max 1 b*D) B (by positivity) hB
    (by
      change f (0:Ideal O)=0
      simp only [f,idealCoeff_zero,zero_mul,ite_self])
    (by intro I;dsimp only [f];split_ifs;exact actual_coefficient_norm χ W D freq B hD hB hW I;simpa using hB)
    (by
      intro I hI
      have hm:I∈S:=by by_contra hn;exact hI (by simp only [f,ite_eq_right hn])
      exact actual_coefficient_support χ W b D freq hD hs I (by simpa only [f,ite_eq_left hm] using hI))
  rw [he] at hh
  convert hh using 1; ring

theorem ray_prime_polynomial_bound (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖rayPrimePolynomial M H χ W b D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  exact finite_polynomial_bound χ W b B D freq hB hD hW hs _

def remainingMultiplier {α : Type*} (J : Finset α)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (χ : Character) (χslot : α→Character) (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ)
    (b D : α→ℝ) (Xshort omega : ℝ) (freq : α→ℝ) : ℂ :=
  polynomial χ false Wshort Xshort 0 omega*
    ∏j∈J,rayPrimePolynomial M H (χslot j) (Wslot j) (b j) (D j) 0 (freq j)

def errorConstant {α : Type*} (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ) : ℝ :=
  (1+(128*max 1 bshort*Bshort)^2)*∏j∈F,max 1 ((128*max 1 (b j)*B j)^2)

lemma errorConstant_pos {α : Type*} (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ) :
    0<errorConstant F bshort Bshort b B := by
  apply mul_pos
  · positivity
  · exact Finset.prod_pos (fun j _=>zero_lt_one.trans_le (le_max_left _ _))

theorem remainingMultiplier_sq_bound {α : Type*} (F J : Finset α) (hJ : J⊆F)
    (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ) (bshort Bshort : ℝ) (b B : α→ℝ)
    (hBshort : 0≤Bshort) (hB : ∀j∈F,0≤B j)
    (hWshort : ∀x,‖Wshort x‖≤Bshort) (hWslot : ∀j∈F,∀x,‖Wslot j x‖≤B j)
    (hsshort : Function.support Wshort⊆Set.Iic bshort)
    (hsslot : ∀j∈F,Function.support (Wslot j)⊆Set.Iic (b j))
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (χ : Character) (χslot : α→Character) (D : α→ℝ) (Xshort omega : ℝ) (freq : α→ℝ)
    (hX : 0<Xshort) (hD : ∀j∈J,0<D j) :
    ‖remainingMultiplier J M H χ χslot Wshort Wslot b D Xshort omega freq‖^2≤
      errorConstant F bshort Bshort b B*Xshort*∏j∈J,D j := by
  have hs:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ Wshort bshort Bshort Xshort omega hBshort hX hWshort hsshort) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hs
  have hj (j:α) (hj:j∈J):
      ‖rayPrimePolynomial M H (χslot j) (Wslot j) (b j) (D j) 0 (freq j)‖^2≤
        (128*max 1 (b j)*B j)^2*D j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (ray_prime_polynomial_bound M H (χslot j) (Wslot j) (b j) (B j) (D j) (freq j)
        (hB j (hJ hj)) (hD j hj) (hWslot j (hJ hj)) (hsslot j (hJ hj))) 2
    simpa only [mul_pow,Real.sq_sqrt (hD j hj).le] using hh
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈J,(128*max 1 (b j)*B j)^2)≤
      errorConstant F bshort Bshort b B := by
    have hp : (∏j∈J,(128*max 1 (b j)*B j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*B j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hJ (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort*Bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  calc
    _ = ‖polynomial χ false Wshort Xshort 0 omega‖^2*
      ∏j∈J,‖rayPrimePolynomial M H (χslot j) (Wslot j) (b j) (D j) 0 (freq j)‖^2 := by
        simp only [remainingMultiplier,norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*Xshort)*∏j∈J,(128*max 1 (b j)*B j)^2*D j :=
      mul_le_mul hs (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈J,(128*max 1 (b j)*B j)^2))*(Xshort*∏j∈J,D j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ errorConstant F bshort Bshort b B*(Xshort*∏j∈J,D j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hD j hj).le)))
    _ = _ := by ring

theorem uniform_radial_error_mass {α : Type*} (F : Finset α)
    (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ) (bshort Bshort : ℝ) (b B : α→ℝ)
    (hBshort : 0≤Bshort) (hB : ∀j∈F,0≤B j)
    (hWshort : ∀x,‖Wshort x‖≤Bshort) (hWslot : ∀j∈F,∀x,‖Wslot j x‖≤B j)
    (hsshort : Function.support Wshort⊆Set.Iic bshort)
    (hsslot : ∀j∈F,Function.support (Wslot j)⊆Set.Iic (b j)) :
    ∃C:ℝ,0<C ∧ ∀J:Finset α,J⊆F →
      ∀(M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
        (χ:O→Character) (χslot:α→O→Character) (omega:O→ℝ) (freq:α→O→ℝ)
        (D:α→ℝ) (Xshort K:ℝ) (Φ:𝓢(ℝ,ℂ)),
        0<Xshort → (∀j∈J,0<D j) → 0<K →
        let P:=fun z:O=>remainingMultiplier J M H (χ z) (fun j=>χslot j z)
          Wshort Wslot b D Xshort (omega z) (fun j=>freq j z)
        Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2) ∧
        (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) ∧
        ∀E:Finset O,(∑z∈E,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) := by
  let C:=errorConstant F bshort Bshort b B
  have hC:0<C:=errorConstant_pos F bshort Bshort b B
  refine ⟨C,hC,?_⟩
  intro J hJ M _ H χ χslot omega freq D Xshort K Φ hX hD hK P
  let A:=C*Xshort*∏j∈J,D j
  have hA:0≤A:=mul_nonneg (mul_nonneg hC.le hX.le) (Finset.prod_nonneg (fun j hj=>(hD j hj).le))
  have hp (z:O):‖P z‖^2≤A:=remainingMultiplier_sq_bound F J hJ Wshort Wslot
    bshort Bshort b B hBshort hB hWshort hWslot hsshort hsslot M H (χ z) (fun j=>χslot j z)
    D Xshort (omega z) (fun j=>freq j z) hX hD
  have hs:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hp z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right A)
  have hb:(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
      C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j):=by
    calc
      _ ≤ ∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*A:=
        hs.tsum_le_tsum (fun z=>mul_le_mul_of_nonneg_left (hp z) (norm_nonneg _))
          ((radial_norm_summable Φ K hK).mul_right A)
      _ = (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*A:=tsum_mul_right
      _ ≤ (diagonalControl Φ*max 1 K)*A:=
        mul_le_mul_of_nonneg_right (radial_weight_lattice_bound_all Φ K hK) hA
      _ = _:=by dsimp [A];ring
  refine ⟨hs,hb,?_⟩
  intro E
  exact (sum_le_hasSum E (fun z _=>mul_nonneg (norm_nonneg _) (sq_nonneg _)) hs.hasSum).trans hb

lemma compact_norm_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B:ℝ,0<B ∧ ∀x,‖W x‖≤B := by
  obtain ⟨B,hB,hbound⟩:=fixed_profile_norm_bound W hW a b 0 0 ha
  refine ⟨B,hB,?_⟩
  intro x
  by_cases hx:W x=0
  · simpa only [hx,norm_zero] using hB.le
  · simpa using hbound 0 (by simp) x (hs hx)

theorem smooth_radial_error_mass {α : Type*} (F : Finset α)
    (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ) (ashort bshort : ℝ) (a b : α→ℝ)
    (hashort : 0<ashort) (ha : ∀j∈F,0<a j)
    (hsshort : Function.support Wshort⊆Set.Icc ashort bshort)
    (hsslot : ∀j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWshort : ContDiff ℝ ∞ Wshort) (hWslot : ∀j∈F,ContDiff ℝ ∞ (Wslot j)) :
    ∃C:ℝ,0<C ∧ ∀J:Finset α,J⊆F →
      ∀(M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
        (χ:O→Character) (χslot:α→O→Character) (omega:O→ℝ) (freq:α→O→ℝ)
        (D:α→ℝ) (Xshort K:ℝ) (Φ:𝓢(ℝ,ℂ)),
        0<Xshort → (∀j∈J,0<D j) → 0<K →
        let P:=fun z:O=>remainingMultiplier J M H (χ z) (fun j=>χslot j z)
          Wshort Wslot b D Xshort (omega z) (fun j=>freq j z)
        Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2) ∧
        (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) ∧
        ∀E:Finset O,(∑z∈E,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) := by
  obtain ⟨Bshort,hBshort,hshort⟩:=compact_norm_bound Wshort ashort bshort hashort hsshort hWshort.continuous
  have hex (j:α):∃B:ℝ,0≤B ∧ (j∈F → ∀x,‖Wslot j x‖≤B):=by
    by_cases hj:j∈F
    · obtain ⟨B,hB,hbound⟩:=compact_norm_bound (Wslot j) (a j) (b j) (ha j hj) (hsslot j hj) (hWslot j hj).continuous
      exact ⟨B,hB.le,fun _=>hbound⟩
    · exact ⟨0,le_rfl,fun h=>False.elim (hj h)⟩
  choose B hB hbound using hex
  exact uniform_radial_error_mass F Wshort Wslot bshort Bshort b B hBshort.le
    (fun j _=>hB j) hshort hbound (fun x hx=>(hsshort hx).2)
    (fun j hj x hx=>(hsslot j hj hx).2)

end SevenEighths.CenteredMomentOriginalReflectionErrorMass

end

end OAI
