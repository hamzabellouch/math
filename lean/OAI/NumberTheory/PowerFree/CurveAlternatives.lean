import OAI.NumberTheory.PowerFree.ComplexValues

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem algebraic_coordinate_constant {K A : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] (x : A) (hx : IsAlgebraic K x) :
    ∃ c : K, algebraMap K A c = x := by
  have hi := hx.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have he := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd,
    (minpoly.monic hi).leadingCoeff, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at he
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact he.symm⟩

theorem curve_coordinate_relation {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (x y : Fin n)
    (hx : Transcendental K (Ideal.Quotient.mk I (X x))) :
    ∃ q : MvPolynomial (Fin 2) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree:ℚ) ≤ affineDegree I ∧
      (∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) := by
  have hind : AlgebraicIndependent K
      (fun a : Fin 1 => Ideal.Quotient.mk I (X (![y,x] a.succ))) := by
    apply algebraicIndependent_unique_type_iff.mpr
    simpa using hx
  have hdim : affineDimension I = 1 := by
    have htr := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
    have hh := hind.lift_cardinalMk_le_trdeg
    rw [← htr] at hh
    have hl : 1 ≤ affineDimension I := by simpa [affineDimension] using hh
    omega
  obtain ⟨q,hq,hd,hb,hker⟩ := bounded_projection_relation I (coordinateHilbert I)
    hI (coordinateHilbert_eventually I) ![y,x] hind
  refine ⟨q,hq,hd,?_,hker⟩
  simpa only [affineDegree,hdim] using hb

noncomputable def binaryPolynomialEquiv (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (finSuccEquiv K 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1)))

@[simp] theorem binaryPolynomialEquiv_natDegree {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) : (binaryPolynomialEquiv K q).natDegree = q.degreeOf 0 := by
  rw [binaryPolynomialEquiv,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,
    Polynomial.natDegree_map_eq_of_injective (uniqueAlgEquiv K (Fin 1)).injective,
    natDegree_finSuccEquiv]

theorem binaryPolynomialEquiv_eval {K A : Type*} [CommSemiring K] [CommSemiring A]
    (f : K →+* A) (x y : A) (q : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ (Polynomial.eval₂RingHom f x) y (binaryPolynomialEquiv K q) =
      MvPolynomial.eval₂ f ![y,x] q := by
  let e : MvPolynomial (Fin 2) K →+* A :=
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f x) y).comp
      (binaryPolynomialEquiv K).toRingHom
  have he : e = MvPolynomial.eval₂Hom f ![y,x] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
      · simp [e,binaryPolynomialEquiv,finSuccEquiv_apply,uniqueAlgEquiv]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →+* A => g q) he

theorem uniquePolynomial_natDegree_le {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 1) K) : (uniqueAlgEquiv K (Fin 1) q).natDegree ≤ q.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [coeff_uniqueAlgEquiv]
  apply coeff_eq_zero_of_totalDegree_lt
  change q.totalDegree < (Finsupp.single (default : Fin 1) m).sum (fun _ e => e)
  rw [Finsupp.sum_single_index (by simp)]
  exact hm

theorem binaryPolynomial_coeff_degree {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) (i : ℕ) :
    ((binaryPolynomialEquiv K q).coeff i).natDegree ≤ q.totalDegree := by
  simp only [binaryPolynomialEquiv,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,Polynomial.coeff_map]

  by_cases hz : (finSuccEquiv K 1 q).coeff i = 0
  · simp [hz]
  · exact (uniquePolynomial_natDegree_le _).trans
      (Nat.le_sub_of_add_le (totalDegree_coeff_finSuccEquiv_add_le q i hz) |>.trans (Nat.sub_le _ _))

theorem linear_projection_rational {K : Type*} [Field K]
    (q : MvPolynomial (Fin 2) K) (hq : Irreducible q) (hd : q.degreeOf 0 = 1) :
    ∃ A B : Polynomial K, IsCoprime A B ∧ B ≠ 0 ∧ A.natDegree ≤ q.totalDegree ∧
      B.natDegree ≤ q.totalDegree ∧
      ∀ {S : Type*} [CommRing S] (f : K →+* S) (x y : S),
        MvPolynomial.eval₂ f ![y,x] q = 0 ↔
          A.eval₂ f x = y * B.eval₂ f x := by
  let p := binaryPolynomialEquiv K q
  have hp : Irreducible p := (MulEquiv.irreducible_iff (binaryPolynomialEquiv K)).mpr hq
  have hpd : p.natDegree = 1 := (binaryPolynomialEquiv_natDegree q).trans hd
  have he : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) := by
    simpa only [hpd] using Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.degree_le_of_natDegree_le (le_of_eq hpd))
  have hbn : p.coeff 1 ≠ 0 := by
    rw [← hpd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero
  have prim := hp.isPrimitive (by rw [hpd]; decide)
  have hcop : IsCoprime (p.coeff 0) (p.coeff 1) := by
    apply IsRelPrime.isCoprime
    intro d hd0 hd1
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp prim
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i = 0
    · subst i; exact hd0
    by_cases hi1 : i = 1
    · subst i; exact hd1
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  refine ⟨-p.coeff 0,p.coeff 1,hcop.neg_left,hbn,?_,binaryPolynomial_coeff_degree q 1,?_⟩
  · simpa using binaryPolynomial_coeff_degree q 0
  · intro S _ f x y
    rw [← binaryPolynomialEquiv_eval,show binaryPolynomialEquiv K q = p from rfl]
    conv_lhs => rw [he]
    simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
      Polynomial.eval₂_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_neg]
    constructor <;> intro h <;> linear_combination -h

noncomputable def binaryStripExponent {M : ℕ} (i : Fin 2 × Fin (M+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.1.val + Finsupp.single 1 i.2.val

theorem binaryStripExponent_injective (M : ℕ) :
    Function.Injective (binaryStripExponent (M := M)) := by
  intro i j h
  have h0 := congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
  have h1 := congrArg (fun a : Fin 2 →₀ ℕ => a 1) h
  simp only [binaryStripExponent,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),
    Finsupp.single_eq_of_ne (show (1:Fin 2) ≠ 0 by decide),add_zero,zero_add] at h0 h1
  exact Prod.ext (Fin.ext h0) (Fin.ext h1)

theorem projection_strip_independent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) (M : ℕ) :
    LinearIndependent K (fun i : Fin 2 × Fin (M+1) =>
      Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc i hi
  let p : MvPolynomial (Fin 2) K := ∑ j ∈ s, c j • monomial (binaryStripExponent j) 1
  have hpker : Ideal.Quotient.mk I (rename ![y,x] p) = 0 := by
    change (Ideal.Quotient.mkₐ K I) (rename ![y,x] p) = 0
    simpa only [p,map_sum,map_smul,Ideal.Quotient.mkₐ_eq_mk] using hc
  have hpdeg : p.degreeOf 0 ≤ 1 := by
    apply (degreeOf_sum_le 0 s _).trans
    apply Finset.sup_le
    intro j _
    rw [smul_monomial,smul_eq_mul,mul_one]
    by_cases hz : c j = 0
    · simp [hz]
    · rw [degreeOf_monomial_eq _ _ hz]
      simp only [binaryStripExponent,Finsupp.coe_add,Pi.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0:Fin 2) ≠ 1 by decide),add_zero]
      omega
  have hp : p = 0 := by
    by_contra hp
    obtain ⟨t,ht⟩ := (hker p).mp hpker
    have hmul : q*t ≠ 0 := ht ▸ hp
    have hd := degreeOf_mul_eq (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul) (n := 0)
    rw [← ht] at hd
    omega
  have hl := (basisMonomials (Fin 2) K).linearIndependent.comp
    (binaryStripExponent (M := M)) (binaryStripExponent_injective M)
  simp only [coe_basisMonomials,Function.comp_def] at hl
  exact linearIndependent_iff'.mp hl s c hp i hi

theorem coordinate_power_mem_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (a b : ℕ) (T : ℝ) (hb : ω y*a+ω x*b ≤ T) :
    Ideal.Quotient.mk I ((X y)^a*(X x)^b) ∈ weightedFunctions I ω T := by
  classical
  have hweight : monomialWeight ω (Finsupp.single y a + Finsupp.single x b) = ω y*a+ω x*b := by
    simp only [monomialWeight,Finsupp.coe_add,Pi.add_apply,Nat.cast_add,mul_add,Finset.sum_add_distrib]
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial,X_pow_eq_monomial,monomial_mul_monomial,one_mul]
  apply Submodule.subset_span
  refine ⟨_,(mem_weightedMonomials ω hω T _).mpr (hweight ▸ hb),rfl⟩

theorem projection_strip_hilbert {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (hx : ω x = 1)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p)
    (M : ℕ) (T : ℝ) (hT : (M:ℝ)+ω y ≤ T) :
    2*(M+1) ≤ weightedHilbert I ω T := by
  classical
  let v := fun i : Fin 2 × Fin (M+1) =>
    Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))
  have hv (i : Fin 2 × Fin (M+1)) : v i ∈ weightedFunctions I ω T := by
    have he : rename ![y,x] (monomial (binaryStripExponent i) (1:K)) = (X y)^i.1.val*(X x)^i.2.val := by
      rw [binaryStripExponent,← one_mul (1:K),← monomial_mul_monomial,← X_pow_eq_monomial,← X_pow_eq_monomial]
      simp
    dsimp only [v]
    rw [he]
    apply coordinate_power_mem_weighted I ω hω x y _ _ T
    rw [hx,one_mul]
    have h1 : (i.1.val:ℝ) ≤ 1 := by exact_mod_cast (show i.1.val ≤ 1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    have hh := mul_le_mul_of_nonneg_left h1 (hω y).le
    linarith
  let u : (Fin 2 × Fin (M+1)) → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype
    (projection_strip_independent I x y q hq hker M)
  simpa only [Fintype.card_prod,Fintype.card_fin,weightedHilbert] using hu.fintype_card_le_finrank

theorem projection_curve_hilbert_gain {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (hx : ω x = 1)
    (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) :
    ∀ T : ℝ, 0 ≤ T → 2*T-2*(ω y+1) ≤ weightedHilbert I ω T := by
  intro T _
  by_cases hT : ω y ≤ T
  · have hf : (⌊T-ω y⌋₊:ℝ)+ω y ≤ T := by linarith [Nat.floor_le (sub_nonneg.mpr hT)]
    have hb := projection_strip_hilbert I ω hω x y hx q hq hker ⌊T-ω y⌋₊ T hf
    have hbr : 2*((⌊T-ω y⌋₊:ℝ)+1) ≤ weightedHilbert I ω T := by exact_mod_cast hb
    have hl := Nat.lt_floor_add_one (T-ω y)
    linarith
  · have hh : (0:ℝ) ≤ weightedHilbert I ω T := Nat.cast_nonneg _
    linarith

theorem polynomial_of_constant_denominator {K R : Type*} [Field K] [CommRing R]
    (φ : K →+* R) (x y : R) (A B : Polynomial K) (hB : B ≠ 0)
    (hdeg : B.natDegree = 0) (he : A.eval₂ φ x = y*B.eval₂ φ x) :
    ∃ P : Polynomial K, P.eval₂ φ x = y := by
  have hBc : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hb : B.coeff 0 ≠ 0 := by intro h; apply hB; rw [hBc,h,Polynomial.C_0]
  refine ⟨Polynomial.C (B.coeff 0)⁻¹ * A,?_⟩
  have hev : B.eval₂ φ x = φ (B.coeff 0) := by
    conv_lhs => rw [hBc]
    rw [Polynomial.eval₂_C]
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_C,he,hev,← mul_assoc,mul_comm (φ _),mul_assoc,
    ← map_mul,inv_mul_cancel₀ hb,map_one,mul_one]

theorem squarefree_surface_polynomial_coordinate {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (f Y Z : Polynomial K) (k : ℕ) (hk : 2 ≤ k)
    (hf : Squarefree f) (x y z : R) (hx : Transcendental K x)
    (hY : Polynomial.aeval x Y = y) (hZ : Polynomial.aeval x Z = z)
    (he : Polynomial.aeval x f = y*z^k) :
    ∃ c : K, algebraMap K R c = z := by
  have hid : f = Y*Z^k := (transcendental_iff_injective.mp hx) (by simpa only [map_mul,map_pow,hY,hZ] using he)
  have hu : IsUnit Z := by
    by_contra hn
    have hs : Squarefree (Z^k) := hf.squarefree_of_dvd ⟨Y,by rw [hid]; ring⟩
    have hh := hs.eq_zero_or_one_of_pow_of_not_isUnit hn
    omega
  have hz := Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)
  refine ⟨Z.coeff 0,?_⟩
  rw [← hZ]
  conv_rhs => rw [hz]
  rw [Polynomial.aeval_C]

theorem projection_equation_quotient {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (x y : Fin n)
    (q : MvPolynomial (Fin 2) K)
    (hq : Ideal.Quotient.mk I (rename ![y,x] q) = 0) :
    MvPolynomial.eval₂ (algebraMap K (MvPolynomial (Fin n) K ⧸ I))
      ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] q = 0 := by
  have he : MvPolynomial.aeval ![Ideal.Quotient.mk I (X y),Ideal.Quotient.mk I (X x)] =
      (Ideal.Quotient.mkₐ K I).comp (rename ![y,x]) := by
    ext i
    fin_cases i <;> simp
  change (MvPolynomial.aeval _) q = 0
  rw [he]
  exact hq

theorem direct_curve_alternative (I : Ideal (MvPolynomial (Fin 3) ℂ)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (e : ℕ) (hdeg : affineDegree I ≤ e)
    (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (f : Polynomial ℂ) (hf : Squarefree f) (k : ℕ) (hk : 2 ≤ k)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X 0)) f =
      Ideal.Quotient.mk I (X 1) * (Ideal.Quotient.mk I (X 2))^k) :
    (∃ c : ℂ, algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I) c = Ideal.Quotient.mk I (X 0)) ∨
    (∃ (j : Fin 3) (A B : Polynomial ℂ), (j = 1 ∨ j = 2) ∧ IsCoprime A B ∧
      0 < B.natDegree ∧ A.natDegree ≤ e ∧ B.natDegree ≤ e ∧
      Polynomial.aeval (Ideal.Quotient.mk I (X 0)) A =
        Ideal.Quotient.mk I (X j) * Polynomial.aeval (Ideal.Quotient.mk I (X 0)) B) ∨
    (∃ c : ℂ, algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I) c = Ideal.Quotient.mk I (X 2)) ∨
    (∀ T : ℝ, 1 ≤ T → 2*T-2*(ω 1+ω 2+1) ≤ weightedHilbert I ω T) := by
  by_cases hx : IsAlgebraic ℂ (Ideal.Quotient.mk I (X 0))
  · exact Or.inl (algebraic_coordinate_constant _ hx)
  have relations (j : Fin 3) := curve_coordinate_relation I hI 0 j hx
  obtain ⟨qY,hqY,hdY,hbY,hkerY⟩ := relations 1
  obtain ⟨qZ,hqZ,hdZ,hbZ,hkerZ⟩ := relations 2
  have hbY' : qY.totalDegree ≤ e := by exact_mod_cast hbY.trans hdeg
  have hbZ' : qZ.totalDegree ≤ e := by exact_mod_cast hbZ.trans hdeg
  by_cases h2Y : 2 ≤ qY.degreeOf 0
  · right; right; right
    intro T hT
    have hh := projection_curve_hilbert_gain I ω hω 0 1 hω0 qY h2Y hkerY T (by linarith)
    linarith [hω 2]
  by_cases h2Z : 2 ≤ qZ.degreeOf 0
  · right; right; right
    intro T hT
    have hh := projection_curve_hilbert_gain I ω hω 0 2 hω0 qZ h2Z hkerZ T (by linarith)
    linarith [hω 1]
  obtain ⟨AY,BY,hcopY,hBY,hAYb,hBYb,hY⟩ := linear_projection_rational qY hqY (by omega)
  obtain ⟨AZ,BZ,hcopZ,hBZ,hAZb,hBZb,hZ⟩ := linear_projection_rational qZ hqZ (by omega)
  have heY := (hY (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    (Ideal.Quotient.mk I (X 0)) (Ideal.Quotient.mk I (X 1))).mp
    (projection_equation_quotient I 0 1 qY ((hkerY qY).mpr (dvd_refl _)))
  have heZ := (hZ (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    (Ideal.Quotient.mk I (X 0)) (Ideal.Quotient.mk I (X 2))).mp
    (projection_equation_quotient I 0 2 qZ ((hkerZ qZ).mpr (dvd_refl _)))
  by_cases hYpos : 0 < BY.natDegree
  · exact Or.inr (Or.inl ⟨1,AY,BY,Or.inl rfl,hcopY,hYpos,hAYb.trans hbY',hBYb.trans hbY',heY⟩)
  by_cases hZpos : 0 < BZ.natDegree
  · exact Or.inr (Or.inl ⟨2,AZ,BZ,Or.inr rfl,hcopZ,hZpos,hAZb.trans hbZ',hBZb.trans hbZ',heZ⟩)
  obtain ⟨Y,hY⟩ := polynomial_of_constant_denominator (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    _ _ AY BY hBY (by omega) heY
  obtain ⟨Z,hZ⟩ := polynomial_of_constant_denominator (algebraMap ℂ (MvPolynomial (Fin 3) ℂ ⧸ I))
    _ _ AZ BZ hBZ (by omega) heZ
  exact Or.inr (Or.inr (Or.inl (squarefree_surface_polynomial_coordinate f Y Z k hk hf _ _ _ hx hY hZ he)))

end QuarticPowerFree

end OAI
