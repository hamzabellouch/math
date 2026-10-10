import OAI.NumberTheory.PowerFree.RationalCoordinates

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped Classical BigOperators

theorem weightedFunctions_mono {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {A B : ℝ} (h : A ≤ B) : weightedFunctions I ω A ≤ weightedFunctions I ω B :=
  Submodule.span_mono (Set.image_mono (weightedMonomials_mono ω hω h))

theorem weightedFunctions_one {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j) :
    (1 : MvPolynomial σ K ⧸ I) ∈ weightedFunctions I ω 0 := by
  apply Submodule.subset_span
  refine ⟨0,(mem_weightedMonomials ω hω 0 0).mpr (by simp [monomialWeight]),?_⟩
  simp

theorem weightedFunctions_mul {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {A B : ℝ} {x y : MvPolynomial σ K ⧸ I}
    (hx : x ∈ weightedFunctions I ω A) (hy : y ∈ weightedFunctions I ω B) :
    x*y ∈ weightedFunctions I ω (A+B) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b,hb,rfl⟩ := hy
      rw [←map_mul,monomial_mul_monomial,one_mul]
      apply Submodule.subset_span
      refine ⟨a+b,(mem_weightedMonomials ω hω (A+B) (a+b)).mpr ?_,rfl⟩
      have he : monomialWeight ω (a+b) = monomialWeight ω a+monomialWeight ω b := by
        simp only [monomialWeight,Finsupp.coe_add,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
      rw [he]
      exact add_le_add ((mem_weightedMonomials ω hω A a).mp ha) ((mem_weightedMonomials ω hω B b).mp hb)
    | zero => simp
    | add y z _ _ hy hz => simpa only [mul_add] using (weightedFunctions I ω (A+B)).add_mem hy hz
    | smul c y _ hy => simpa only [mul_smul_comm] using (weightedFunctions I ω (A+B)).smul_mem c hy
  | zero => simp
  | add x z _ _ hx hz => simpa only [add_mul] using (weightedFunctions I ω (A+B)).add_mem hx hz
  | smul c x _ hx => simpa only [smul_mul_assoc] using (weightedFunctions I ω (A+B)).smul_mem c hx

theorem weightedFunctions_pow {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    {A : ℝ} {x : MvPolynomial σ K ⧸ I} (hx : x ∈ weightedFunctions I ω A) (e : ℕ) :
    x^e ∈ weightedFunctions I ω (A*e) := by
  induction e with
  | zero => simpa using weightedFunctions_one I ω hω
  | succ e ih =>
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,mul_add,mul_one] using weightedFunctions_mul I ω hω ih hx

theorem weightedFunctions_coordinate {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j) (j : σ) :
    Ideal.Quotient.mk I (X j) ∈ weightedFunctions I ω (ω j) := by
  classical
  apply Submodule.subset_span
  refine ⟨Finsupp.single j 1,(mem_weightedMonomials ω hω _ _).mpr ?_,rfl⟩
  simp [monomialWeight,Finsupp.single_apply]

theorem polynomial_curve_strip {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (s b : MvPolynomial σ K ⧸ I) (hs : Transcendental K s)
    (P : Polynomial K) (hP : Polynomial.aeval s P = b) (g : ℕ) (hg : 0 < g)
    (hdeg : g ≤ P.natDegree) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hsw : s ∈ weightedFunctions I ω U) (hbw : b ∈ weightedFunctions I ω V)
    (M : ℕ) (T : ℝ) (hT : U*(g-1:ℕ)+V*M ≤ T) :
    g*(M+1) ≤ weightedHilbert I ω T := by
  classical
  let v : Fin g × Fin (M+1) → MvPolynomial σ K ⧸ I := fun i => s^i.1.val*b^i.2.val
  have hl := (curve_polynomial_families_independent P hg hdeg).comp
    (fun i : Fin g × Fin (M+1) => (i.1,(i.2.val:ℕ))) (by
      intro i j h
      change (i.1,i.2.val) = (j.1,j.2.val) at h
      exact Prod.ext (congrArg (fun z : Fin g × ℕ => z.1) h) (Fin.ext (congrArg (fun z : Fin g × ℕ => z.2) h)))
  have hi : LinearIndependent K v := by
    have hh := hl.map' (Polynomial.aeval s).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hs))
    simpa only [v,Function.comp_def,AlgHom.toLinearMap_apply,map_mul,map_pow,Polynomial.aeval_X,hP] using hh
  have hv (i : Fin g × Fin (M+1)) : v i ∈ weightedFunctions I ω T := by
    apply weightedFunctions_mono I ω hω _ (weightedFunctions_mul I ω hω
      (weightedFunctions_pow I ω hω hsw i.1.val) (weightedFunctions_pow I ω hω hbw i.2.val))
    have h1 : (i.1.val:ℝ) ≤ (g-1:ℕ) := by exact_mod_cast (show i.1.val ≤ g-1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    nlinarith [mul_le_mul_of_nonneg_left h1 hU,mul_le_mul_of_nonneg_left h2 hV]
  let u : Fin g × Fin (M+1) → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype hi
  simpa only [Fintype.card_prod,Fintype.card_fin,weightedHilbert] using hu.fintype_card_le_finrank

theorem polynomial_curve_hilbert_gain {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ j, 0 < ω j)
    (s b : MvPolynomial σ K ⧸ I) (hs : Transcendental K s)
    (P : Polynomial K) (hP : Polynomial.aeval s P = b) (g : ℕ) (hg : 0 < g)
    (hdeg : g ≤ P.natDegree) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 < V)
    (hsw : s ∈ weightedFunctions I ω U) (hbw : b ∈ weightedFunctions I ω V) :
    ∀ T : ℝ, 0 ≤ T → (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V ≤ weightedHilbert I ω T := by
  intro T _
  let W : ℝ := U*(g-1:ℕ)
  by_cases hT : W ≤ T
  · let M := ⌊(T-W)/V⌋₊
    have hf : (M:ℝ) ≤ (T-W)/V := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) hV.le)
    have ht : U*(g-1:ℕ)+V*M ≤ T := by
      have := (le_div_iff₀ hV).mp hf
      dsimp [W] at this
      nlinarith
    have hb := polynomial_curve_strip I ω hω s b hs P hP g hg hdeg U V hU hV.le hsw hbw M T ht
    have hbr : (g:ℝ)*((M:ℝ)+1) ≤ weightedHilbert I ω T := by exact_mod_cast hb
    have hl : (T-W)/V < (M:ℝ)+1 := Nat.lt_floor_add_one _
    have hg0 : (0:ℝ) < g := by exact_mod_cast hg
    have hm := mul_lt_mul_of_pos_left hl hg0
    dsimp [W] at hm
    have he : (g:ℝ)*((T-U*(g-1:ℕ))/V) = (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V := by ring
    rw [he] at hm
    linarith
  · have hs : T-W < 0 := by linarith
    have hh : (g:ℝ)*((T-W)/V) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (div_nonpos_of_nonpos_of_nonneg hs.le hV.le)
    have he : (g:ℝ)*((T-W)/V) = (g:ℝ)*T/V-(g:ℝ)*U*(g-1:ℕ)/V := by dsimp [W]; ring
    rw [he] at hh
    exact hh.trans (Nat.cast_nonneg _)

theorem rational_selected_count_general {n : ℕ} (D : ℕ) (hD : 0 < D)
    (W Cbox : ℝ) (hW : 0 < W) (hCbox : 0 < Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin n → ℤ)),
      ∀ (s j : Fin n), Set.InjOn (fun z : Fin n → ℤ => z s) (S:Set _) →
      (∀ z ∈ S, ∀ i, |(z i:ℝ)| ≤ Cbox*X^W) →
      ∀ (A B : Polynomial ℂ), IsCoprime A B → 0 < B.natDegree →
      A.natDegree ≤ D → B.natDegree ≤ D →
      (∀ z ∈ S, A.eval (z s:ℂ) = (z j:ℂ)*B.eval (z s:ℂ)) →
      (S.card:ℝ) ≤ C*X^ε := by
  classical
  obtain ⟨C,hC,hbound⟩ := ComplexValues.rational_integer_values_uniform D hD W W Cbox hW hW hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S s j hinj hbox A B hcop hB hAD hBD he
  let v : ℤ → ℤ := fun a => if ha : ∃ z ∈ S, z s = a then ha.choose j else 0
  have hv (z) (hz : z ∈ S) : v (z s) = z j := by
    have ha : ∃ u ∈ S, u s = z s := ⟨z,hz,rfl⟩
    dsimp only [v]
    rw [dite_eq_left ha]
    exact congrArg (fun u => u j) (hinj ha.choose_spec.1 hz ha.choose_spec.2)
  have hcard : (S.image fun z => z s).card = S.card := Finset.card_image_of_injOn hinj
  rw [←hcard]
  apply hbound A B hcop hB hAD hBD _ v X hX
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    rw [hv z hz]
    exact he z hz
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact hbox z hz s
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    rw [hv z hz]
    exact hbox z hz j

theorem bounded_polynomial_of_constant_denominator {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) (x y : R) (A B : Polynomial K) (hB : B ≠ 0)
    (hdeg : B.natDegree = 0) (he : A.eval₂ φ x = y*B.eval₂ φ x) :
    ∃ P : Polynomial K, P.natDegree ≤ A.natDegree ∧ P.eval₂ φ x = y := by
  have hBc : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hb : B.coeff 0 ≠ 0 := by intro h; apply hB; rw [hBc,h,Polynomial.C_0]
  refine ⟨Polynomial.C (B.coeff 0)⁻¹ * A,?_,?_⟩
  · exact Polynomial.natDegree_C_mul_le _ _
  · have hev : B.eval₂ φ x = φ (B.coeff 0) := by
      conv_lhs => rw [hBc]
      rw [Polynomial.eval₂_C]
    rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,he,hev,←mul_assoc,mul_comm (φ _),mul_assoc,
      ←map_mul,inv_mul_cancel₀ hb,map_one,mul_one]

theorem curve_polynomial_left_gain {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (s j : Fin n) (hweight : ω j = ω s)
    (hs : Transcendental ℂ (Ideal.Quotient.mk I (X s)))
    (P : Polynomial ℂ) (hP : Polynomial.aeval (Ideal.Quotient.mk I (X s)) P = Ideal.Quotient.mk I (X j))
    (hdeg : 2 ≤ P.natDegree) :
    ∀ T : ℝ, 0 ≤ T → 2*T/(ω s)-2 ≤ weightedHilbert I ω T := by
  have hh := polynomial_curve_hilbert_gain I ω hω _ _ hs P hP 2 (by decide) hdeg
    (ω s) (ω s) (hω s).le (hω s) (weightedFunctions_coordinate I ω hω s)
    (hweight ▸ weightedFunctions_coordinate I ω hω j)
  intro T hT
  have he : (2:ℝ)*(ω s)*(2-1:ℕ)/(ω s) = 2 := by
    norm_num
    exact mul_div_cancel_right₀ _ (hω s).ne'
  simpa only [Nat.cast_ofNat,he] using hh T hT

theorem norm_curve_polynomial_reduction {n d : ℕ}
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (x : Fin d → Fin n)
    (U W Cbox : ℝ) (hU : 0 < U) (hW : 0 < W) (hCbox : 0 < Cbox)
    (hxw : ∀ j, ω (x j) = U) (hωW : ∀ j, ω j ≤ W)
    (e : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin n → ℤ)),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime →
      affineDimension I ≤ 1 → affineDegree I ≤ e → (∀ z ∈ S, PointOn I z) →
      ∀ s : Fin d, Transcendental ℂ (Ideal.Quotient.mk I (MvPolynomial.X (x s))) →
      (S.card:ℝ) ≤ C*X^ε ∨
      (∀ T : ℝ, 0 ≤ T → 2*T/U-2*(W/U+1) ≤ weightedHilbert I ω T) ∨
      (∃ P : Fin n → Polynomial ℂ, (∀ j, (P j).natDegree ≤ e ∧
        Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X (x s))) (P j) =
          Ideal.Quotient.mk I (MvPolynomial.X j)) ∧ ∀ j, (P (x j)).natDegree ≤ 1) := by
  classical
  obtain ⟨C,hC,hcount⟩ := rational_selected_count_general (n := n) (e+1) (by omega) W Cbox hW hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S hbox I hI hdim hdeg hon s hs
  let : I.IsPrime := hI
  rcases curve_coordinate_rationalization I hdim e hdeg ω hω (x s) hs with ⟨j,hj⟩ | ⟨A,B,hAB⟩
  · right; left
    intro T hT
    have hh := hj T hT
    rw [hxw] at hh
    have hw := (div_le_div_iff_of_pos_right hU).mpr (hωW j)
    linarith
  have hcop (j) := (hAB j).1
  have hrel (j) := (hAB j).2.2.2.2
  by_cases hb : ∃ j, 0 < (B j).natDegree
  · obtain ⟨j,hj⟩ := hb
    left
    apply hcount X hX S (x s) j
      ((rational_coordinates_injOn I (x s) A B hcop hrel).mono (fun z hz => hon z hz))
    · intro z hz i
      apply (hbox z hz i).trans
      gcongr
      · linarith
      · exact hωW i
    · exact hcop j
    · exact hj
    · exact (hAB j).2.2.1.trans (by omega)
    · exact (hAB j).2.2.2.1.trans (by omega)
    · intro z hz
      exact rational_coordinate_at_point I z (hon z hz) (x s) j (A j) (B j) (hrel j)
  push Not at hb
  choose P hPd hP using fun j => bounded_polynomial_of_constant_denominator
    (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I)) _ _ (A j) (B j) (hAB j).2.1 (by have := hb j; omega) (hrel j)
  by_cases hp : ∃ j, 2 ≤ (P (x j)).natDegree
  · obtain ⟨j,hj⟩ := hp
    right; left
    intro T hT
    have hh := curve_polynomial_left_gain I ω hω (x s) (x j) (by rw [hxw,hxw]) hs (P (x j)) (hP (x j)) hj T hT
    rw [hxw] at hh
    have hw : 0 ≤ W/U := div_nonneg hW.le hU.le
    linarith
  · right; right
    refine ⟨P,fun j => ⟨(hPd j).trans (hAB j).2.2.1,hP j⟩,?_⟩
    intro j
    have := not_exists.mp hp j
    omega

end
open scoped BigOperators Classical

theorem integer_conjugate_form_injective {d : ℕ} {K : Type*} [Field K] [CharZero K]
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : K →+* ℂ) :
    Function.Injective (fun z : Fin d → ℤ => ∑ j, σ (v j)*(z j:ℂ)) := by
  intro z w h
  have he : ∑ j, (z j:K)*v j = ∑ j, (w j:K)*v j := by
    apply σ.injective
    simpa only [map_sum,map_mul,map_intCast,mul_comm] using h
  have hz : ∑ j, ((z j:ℚ)-(w j:ℚ)) • v j = 0 := by
    simpa only [Algebra.smul_def,map_sub,map_intCast,sub_mul,Finset.sum_sub_distrib] using sub_eq_zero.mpr he
  funext j
  have hj := linearIndependent_iff'.mp hv Finset.univ _ hz j (Finset.mem_univ j)
  exact Int.cast_injective (α := ℚ) (sub_eq_zero.mp hj)

noncomputable def conjugateLinePolynomial {d : ℕ} {K : Type*} [Field K]
    (v : Fin d → K) (σ : K →+* ℂ) (P : Fin d → Polynomial ℂ) : Polynomial ℂ :=
  ∑ j, Polynomial.C (σ (v j))*P j

theorem conjugateLinePolynomial_degree {d : ℕ} {K : Type*} [Field K]
    (v : Fin d → K) (σ : K →+* ℂ) (P : Fin d → Polynomial ℂ)
    (hP : ∀ j, (P j).natDegree ≤ 1) : (conjugateLinePolynomial v σ P).natDegree ≤ 1 := by
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => (Polynomial.natDegree_C_mul_le _ _).trans (hP j))

theorem conjugateLinePolynomial_slope_ne_zero {d : ℕ} {K : Type*} [Field K] [CharZero K]
    (v : Fin d → K) (hv : LinearIndependent ℚ v) (σ : K →+* ℂ)
    (P : Fin d → Polynomial ℂ) (hP : ∀ j, (P j).natDegree ≤ 1)
    (s : Fin d) (z w : Fin d → ℤ) (hne : z s ≠ w s)
    (hz : ∀ j, (P j).eval (z s:ℂ) = (z j:ℂ))
    (hw : ∀ j, (P j).eval (w s:ℂ) = (w j:ℂ)) :
    (conjugateLinePolynomial v σ P).coeff 1 ≠ 0 := by
  intro hzero
  have hp := Polynomial.eq_X_add_C_of_natDegree_le_one (conjugateLinePolynomial_degree v σ P hP)
  rw [hzero,Polynomial.C_0,zero_mul,zero_add] at hp
  have he : (conjugateLinePolynomial v σ P).eval (z s:ℂ) =
      (conjugateLinePolynomial v σ P).eval (w s:ℂ) := by rw [hp]; simp
  simp only [conjugateLinePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,hz,hw] at he
  exact hne (congrArg (fun a => a s) (integer_conjugate_form_injective v hv σ he))

theorem curve_polynomial_substitution {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (s : Fin n) (P : Fin n → Polynomial K)
    (hP : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X s)) (P j) =
      Ideal.Quotient.mk I (MvPolynomial.X j))
    (q : MvPolynomial (Fin n) K) :
    Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X s)) (MvPolynomial.aeval P q) =
      Ideal.Quotient.mk I q := by
  rw [MvPolynomial.comp_aeval_apply]
  simp only [hP]
  have he : MvPolynomial.aeval (fun j => Ideal.Quotient.mk I (MvPolynomial.X j)) = Ideal.Quotient.mkₐ K I := by
    ext j; simp
  rw [he]
  rfl

end QuarticPowerFree

end OAI
