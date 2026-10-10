import OAI.NumberTheory.PowerFree.Jacobians

namespace OAI

open scoped BigOperators

open Matrix
open scoped BigOperators

namespace QuarticPowerFree

def integralKernelMatrix {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) : Matrix β β R :=
  (B * B.transpose).det • 1 - B.transpose * (B * B.transpose).adjugate * B

theorem mul_integralKernelMatrix {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) :
    B * integralKernelMatrix B = 0 := by
  unfold integralKernelMatrix
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.one_mul, sub_self]

theorem integralKernelMatrix_mulVec_of_kernel {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R)
    (x : β → R) (hx : B *ᵥ x = 0) :
    integralKernelMatrix B *ᵥ x = (B * B.transpose).det • x := by
  unfold integralKernelMatrix
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

theorem gram_det_ne_zero_of_linearIndependent {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (B : Matrix α β F) (hB : LinearIndependent F B) :
    (B * B.transpose).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hz : B.transpose *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec] at hker
    have hh := congrArg (fun y => dotProduct x y) hker
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at hh
    exact hh
  apply hx
  have hinj : Function.Injective (fun x => x ᵥ* B) :=
    Matrix.vecMul_injective_iff.mpr hB
  apply hinj
  simpa only [Matrix.mulVec_transpose, Matrix.zero_vecMul] using hz

theorem mulVec_eq_zero_of_row_mem_span {α β γ F : Type*}
    [Fintype β] [CommSemiring F] [Fintype γ]
    (A : Matrix α β F) (B : Matrix γ β F)
    (hspan : ∀ i, A i ∈ Submodule.span F (Set.range B))
    (x : β → F) (hx : B *ᵥ x = 0) : A *ᵥ x = 0 := by
  ext i
  change dotProduct (A i) x = 0
  have hsub : Submodule.span F (Set.range B) ≤
      LinearMap.ker ((dotProductBilin F F).flip x) := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact congrFun hx j
  exact hsub (hspan i)

theorem integralKernelMatrix_column_mem_kernel {α β γ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [CommRing R]
    (A : Matrix γ β R) (B : Matrix α β R)
    (hspan : ∀ i, A i ∈ Submodule.span R (Set.range B)) (j : β) :
    A *ᵥ (fun i => integralKernelMatrix B i j) = 0 := by
  apply mulVec_eq_zero_of_row_mem_span A B hspan
  have hh := mul_integralKernelMatrix B
  ext i
  exact congrArg (fun M => M i j) hh

theorem mem_span_integralKernelMatrix_columns {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Field F]
    (B : Matrix α β F) (hdet : (B * B.transpose).det ≠ 0)
    (x : β → F) (hx : B *ᵥ x = 0) :
    x ∈ Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)) := by
  have heq := integralKernelMatrix_mulVec_of_kernel B x hx
  have hmem : integralKernelMatrix B *ᵥ x ∈
      Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)) := by
    rw [Matrix.mulVec_eq_sum]
    apply Submodule.sum_mem
    intro j _
    change (fun i => integralKernelMatrix B i j * x j) ∈ _
    have hh := Submodule.smul_mem
      (Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)))
      (x j) (Submodule.subset_span (Set.mem_range_self j))
    convert hh using 1
    ext i
    exact mul_comm _ _
  rw [heq] at hmem
  exact (Submodule.smul_mem_iff _ hdet).mp hmem

theorem exists_independent_spanning_rows {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℚ) :
    ∃ r : ℕ, r ≤ Fintype.card β ∧ ∃ a : Fin r → α,
      Function.Injective a ∧ LinearIndependent ℚ (fun i => A (a i)) ∧
      Submodule.span ℚ (Set.range (fun i => A (a i))) =
        Submodule.span ℚ (Set.range A) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ A
  let := Fintype.ofInjective a ha
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, ?_, a ∘ e.symm, ha.comp e.symm.injective, ?_, ?_⟩
  · simpa only [Module.finrank_fintype_fun_eq_card] using hli.fintype_card_le_finrank
  · exact hli.comp e.symm e.symm.injective
  · have hrange : Set.range (fun i => A (a (e.symm i))) = Set.range (A ∘ a) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, congrArg (fun j => A (a j)) (e.symm_apply_apply i)⟩
    simpa only [Function.comp_def, hrange] using hspan

theorem integralKernelMatrix_map {α β R S : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [CommRing R] [CommRing S] (f : R →+* S) (B : Matrix α β R) :
    (integralKernelMatrix B).map f = integralKernelMatrix (B.map f) := by
  have hadj := f.map_adjugate (B * B.transpose)
  have hdet := f.map_det (B * B.transpose)
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hadj hdet
  unfold integralKernelMatrix
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.smul_apply,
    smul_eq_mul, map_mul]
  rw [hdet]
  have hone : f ((1 : Matrix β β R) i j) = (1 : Matrix β β S) i j := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [hone]
  change _ - ((B.transpose * (B * B.transpose).adjugate * B).map f) i j = _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hadj]

theorem det_abs_le_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]

theorem det_abs_le_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    det_abs_le_row_product (A.map fun x => (x : ℝ)) (fun _ => B) hA

theorem matrix_mul_entry_abs_le {α β γ : Type*} [Fintype β]
    (A : Matrix α β ℤ) (B : Matrix β γ ℤ) (H K : ℝ)
    (hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) (hB : ∀ i j, |(B i j : ℝ)| ≤ K)
    (i : α) (j : γ) : |((A * B) i j : ℝ)| ≤ (Fintype.card β : ℝ) * H * K := by
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul]
  calc
    |∑ k, (A i k : ℝ) * (B k j : ℝ)| ≤ ∑ k, |(A i k : ℝ) * (B k j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : β, H * K := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hH
    _ = (Fintype.card β : ℝ) * H * K := by simp [mul_assoc]

def integralKernelHeight (n : ℕ) (H : ℝ) : ℝ :=
  (1 + (n : ℝ) ^ 2 * H ^ 2) * (Nat.factorial n : ℝ) *
    (1 + (n : ℝ) * H ^ 2) ^ n

theorem integralKernelMatrix_abs_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (B : Matrix α β ℤ) (n : ℕ)
    (hα : Fintype.card α ≤ n) (hβ : Fintype.card β ≤ n)
    (H : ℝ) (hH : 1 ≤ H) (hB : ∀ i j, |(B i j : ℝ)| ≤ H) (i j : β) :
    |((integralKernelMatrix B i j : ℤ) : ℝ)| ≤ integralKernelHeight n H := by
  let G := B * B.transpose
  let C : ℝ := 1 + (n : ℝ) * H ^ 2
  let K : ℝ := (Nat.factorial n : ℝ) * C ^ n
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg H)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG : ∀ u v, |(G u v : ℝ)| ≤ C := by
    intro u v
    have hh := matrix_mul_entry_abs_le B B.transpose H H hH0 hH0 hB
      (fun i j => hB j i) u v
    apply hh.trans
    have hc : (Fintype.card β : ℝ) ≤ n := by exact_mod_cast hβ
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg H)]
  have hdetbound {A : Matrix α α ℤ} (hA : ∀ u v, |(A u v : ℝ)| ≤ C) :
      |(A.det : ℝ)| ≤ K := by
    apply (det_abs_le_uniform A C hA).trans
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le hα)
      (pow_le_pow_right₀ hC hα) (by positivity) (by positivity)
  have hdet : |(G.det : ℝ)| ≤ K := hdetbound hG
  have hadj : ∀ u v, |(G.adjugate u v : ℝ)| ≤ K := by
    intro u v
    rw [Matrix.adjugate_apply]
    apply hdetbound
    intro a b
    by_cases hav : a = v
    · subst a
      rw [Matrix.updateRow_self]
      by_cases hbu : b = u
      · subst b
        simpa using hC
      · simp [Pi.single_eq_of_ne hbu, zero_le_one.trans hC]
    · rw [Matrix.updateRow_ne hav]
      exact hG a b
  have hb₁ : ∀ u v, |((B.transpose * G.adjugate) u v : ℝ)| ≤
      (Fintype.card α : ℝ) * H * K :=
    matrix_mul_entry_abs_le B.transpose G.adjugate H K hH0 hK
      (fun i j => hB j i) hadj
  have hb₂ := matrix_mul_entry_abs_le (B.transpose * G.adjugate) B
    ((Fintype.card α : ℝ) * H * K) H (by positivity) hH0 hb₁ hB i j
  have hdiag : |(((G.det • (1 : Matrix β β ℤ)) i j : ℤ) : ℝ)| ≤ K := by
    by_cases hij : i = j
    · subst j
      simpa using hdet
    · simpa [Matrix.one_apply, hij] using hK
  have hαr : (Fintype.card α : ℝ) ≤ n := by exact_mod_cast hα
  have hαnonneg : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hsquare : (Fintype.card α : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    sq_le_sq₀ hαnonneg (Nat.cast_nonneg _) |>.mpr hαr
  unfold integralKernelMatrix
  change |(((G.det • (1 : Matrix β β ℤ)) i j -
    ((B.transpose * G.adjugate * B) i j) : ℤ) : ℝ)| ≤ _
  rw [Int.cast_sub]
  apply (abs_sub _ _).trans
  apply (add_le_add hdiag hb₂).trans
  have hsqbound := mul_le_mul_of_nonneg_right hsquare (mul_nonneg (sq_nonneg H) hK)
  dsimp [integralKernelHeight, K] at *
  nlinarith

theorem exists_bounded_integral_kernel_spanning {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field F] [CharZero F]
    (A : Matrix α β ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    ∃ C : Matrix β β ℤ, A * C = 0 ∧
      (∀ i j, |(C i j : ℝ)| ≤ integralKernelHeight (Fintype.card β) H) ∧
      ∀ x : β → F, (A.map (Int.castRingHom F)) *ᵥ x = 0 →
        x ∈ Submodule.span F (Set.range
          (fun j => fun i => (C i j : F))) := by
  classical
  let AQ : Matrix α β ℚ := A.map (Int.castRingHom ℚ)
  obtain ⟨r, hr, a, _ha, hli, hspan⟩ := exists_independent_spanning_rows AQ
  let B : Matrix (Fin r) β ℤ := fun i => A (a i)
  have hliQ : LinearIndependent ℚ (B.map (Int.castRingHom ℚ)) := hli
  have hdetQ := gram_det_ne_zero_of_linearIndependent _ hliQ
  have hdetInt : (B * B.transpose).det ≠ 0 := by
    intro heq
    apply hdetQ
    have hh := (Int.castRingHom ℚ).map_det (B * B.transpose)
    simpa only [heq, map_zero, RingHom.mapMatrix_apply,
      Matrix.map_mul, Matrix.transpose_map] using hh.symm
  have hdetF : ((B.map (Int.castRingHom F)) *
      (B.map (Int.castRingHom F)).transpose).det ≠ 0 := by
    have hh := (Int.castRingHom F).map_det (B * B.transpose)
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hh
    rw [← hh]
    exact Int.cast_ne_zero.mpr hdetInt
  let C := integralKernelMatrix B
  refine ⟨C, ?_, ?_, ?_⟩
  · have hmulQ : AQ * integralKernelMatrix (B.map (Int.castRingHom ℚ)) = 0 := by
      ext i j
      have hh := integralKernelMatrix_column_mem_kernel AQ (B.map (Int.castRingHom ℚ))
        (fun i => by
          change AQ i ∈ Submodule.span ℚ (Set.range (fun t => AQ (a t)))
          rw [hspan]
          exact Submodule.subset_span (Set.mem_range_self i)) j
      exact congrFun hh i
    ext i j
    apply Int.cast_injective (α := ℚ)
    change ((A * C).map (Int.castRingHom ℚ)) i j = 0
    rw [Matrix.map_mul]
    change (AQ * (integralKernelMatrix B).map (Int.castRingHom ℚ)) i j = 0
    rw [integralKernelMatrix_map, hmulQ]
    rfl
  · intro i j
    exact integralKernelMatrix_abs_le B (Fintype.card β) (by simpa using hr)
      le_rfl H hH (fun i j => hA (a i) j) i j
  · intro x hx
    have hxB : (B.map (Int.castRingHom F)) *ᵥ x = 0 := by
      ext i
      exact congrFun hx (a i)
    have hmem := mem_span_integralKernelMatrix_columns _ hdetF x hxB
    rw [← integralKernelMatrix_map (Int.castRingHom F) B] at hmem
    exact hmem

def monomialOrder {ι : Type*} (a : ι →₀ ℕ) : ℕ := a.sum (fun _ e => e)

noncomputable def monomialsUpTo (ι : Type*) [Fintype ι] (t : ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact (Finset.range (t + 1)).biUnion (fun n => Finset.univ.finsuppAntidiag n)

theorem mem_monomialsUpTo {ι : Type*} [Fintype ι] {a : ι →₀ ℕ} {t : ℕ} :
    a ∈ monomialsUpTo ι t ↔ monomialOrder a ≤ t := by
  classical
  simp only [monomialsUpTo, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true, monomialOrder]
  exact ⟨fun ⟨n, hn, heq⟩ => heq ▸ Nat.le_of_lt_succ hn,
    fun h => ⟨a.sum (fun _ e => e), Nat.lt_succ_of_le h, rfl⟩⟩

theorem card_monomialsUpTo (ι : Type*) [Fintype ι] (t : ℕ) :
    (monomialsUpTo ι t).card = (t + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  rw [monomialsUpTo, Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ]
    exact Nat.sum_range_multichoose t (Fintype.card ι)
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro a hi hj
  apply hij
  rw [Finset.mem_finsuppAntidiag'] at hi hj
  exact hi.1.symm.trans hj.1

noncomputable def polynomialFromCoefficients {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) : (M → R) →ₗ[R] MvPolynomial σ R where
  toFun c := ∑ m : M, MvPolynomial.monomial m.val (c m)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' r c := by
    change (∑ m : M, MvPolynomial.monomial m.val (r • c m)) =
      r • ∑ m : M, MvPolynomial.monomial m.val (c m)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun m _ => map_smul (MvPolynomial.monomial m.val) r (c m))

theorem polynomialFromCoefficients_coeff {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (m : M) :
    (polynomialFromCoefficients M c).coeff m.val = c m := by
  classical
  change (∑ t : M, MvPolynomial.monomial t.val (c t)).coeff m.val = _
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, ← Subtype.ext_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem polynomialFromCoefficients_coeff_of_not_mem {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (m : σ →₀ ℕ) (hm : m ∉ M) :
    (polynomialFromCoefficients M c).coeff m = 0 := by
  classical
  change (∑ t : M, MvPolynomial.monomial t.val (c t)).coeff m = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro t _
  rw [MvPolynomial.coeff_monomial, ite_eq_right]
  intro h
  exact hm (h ▸ t.property)

theorem polynomialFromCoefficients_support {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) :
    (polynomialFromCoefficients M c).support ⊆ M := by
  intro m hm
  by_contra h
  exact MvPolynomial.mem_support_iff.mp hm
    (polynomialFromCoefficients_coeff_of_not_mem M c m h)

theorem polynomialFromCoefficients_coefficients {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (p : MvPolynomial σ R) (hp : p.support ⊆ M) :
    polynomialFromCoefficients M (fun m => p.coeff m.val) = p := by
  classical
  ext m
  by_cases hm : m ∈ M
  · exact polynomialFromCoefficients_coeff M _ ⟨m, hm⟩
  · rw [polynomialFromCoefficients_coeff_of_not_mem M _ m hm]
    symm
    by_contra hn
    exact hm (hp (MvPolynomial.mem_support_iff.mpr hn))

theorem polynomialFromCoefficients_map {σ R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (M : Finset (σ →₀ ℕ)) (c : M → R) :
    MvPolynomial.map f (polynomialFromCoefficients M c) =
      polynomialFromCoefficients M (fun m => f (c m)) := by
  change MvPolynomial.map f (∑ m : M, MvPolynomial.monomial m.val (c m)) = _
  simp [map_sum, MvPolynomial.map_monomial, polynomialFromCoefficients]

theorem eval_polynomialFromCoefficients {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (z : σ → R) :
    MvPolynomial.eval z (polynomialFromCoefficients M c) =
      dotProduct (fun m : M => m.val.prod (fun i e => z i ^ e)) c := by
  change MvPolynomial.eval z (∑ m : M, MvPolynomial.monomial m.val (c m)) = _
  simp [MvPolynomial.eval_monomial, dotProduct, mul_comm]

theorem polynomialFromCoefficients_totalDegree {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (D : ℕ)
    (hM : ∀ m ∈ M, monomialOrder m ≤ D) :
    (polynomialFromCoefficients M c).totalDegree ≤ D := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  exact fun m hm => hM m (polynomialFromCoefficients_support M c hm)

theorem exists_bounded_polynomial_kernel {σ ι F : Type*}
    [Fintype ι] [Field F] [CharZero F]
    (M : Finset (σ →₀ ℕ)) (z : ι → σ → ℤ) (H : ℝ) (hH : 1 ≤ H)
    (heval : ∀ i (m : M), |((m.val.prod (fun l e => z i l ^ e) : ℤ) : ℝ)| ≤ H) :
    ∃ G : M → MvPolynomial σ ℤ,
      (∀ j, (G j).support ⊆ M) ∧
      (∀ j m, |(((G j).coeff m : ℤ) : ℝ)| ≤ integralKernelHeight M.card H) ∧
      (∀ j i, MvPolynomial.eval (z i) (G j) = 0) ∧
      ∀ p : MvPolynomial σ F, p.support ⊆ M →
        (∀ i, MvPolynomial.eval (fun l => (z i l : F)) p = 0) →
        p ∈ Submodule.span F (Set.range (fun j => MvPolynomial.map (Int.castRingHom F) (G j))) := by
  classical
  let A : Matrix ι M ℤ := fun i m => m.val.prod (fun l e => z i l ^ e)
  obtain ⟨C, hAC, hC, hspan⟩ := exists_bounded_integral_kernel_spanning (F := F) A H hH heval
  let G : M → MvPolynomial σ ℤ := fun j => polynomialFromCoefficients M (fun m => C m j)
  refine ⟨G, (fun j => polynomialFromCoefficients_support M _), ?_, ?_, ?_⟩
  · intro j m
    by_cases hm : m ∈ M
    · change |(((polynomialFromCoefficients M (fun t => C t j)).coeff m : ℤ) : ℝ)| ≤ _
      rw [polynomialFromCoefficients_coeff M _ ⟨m, hm⟩]
      simpa only [Fintype.card_coe] using hC ⟨m, hm⟩ j
    · rw [show (G j).coeff m = 0 from polynomialFromCoefficients_coeff_of_not_mem M _ m hm]
      simp only [Int.cast_zero, abs_zero]
      dsimp [integralKernelHeight]
      positivity
  · intro j i
    rw [show G j = polynomialFromCoefficients M (fun m => C m j) from rfl,
      eval_polynomialFromCoefficients]
    exact congrArg (fun B => B i j) hAC
  · intro p hp hpz
    have hcast : A.map (Int.castRingHom F) =
        (fun i m => m.val.prod (fun l e => (z i l : F) ^ e) : Matrix ι M F) := by
      ext i m
      change ((m.val.prod (fun l e => z i l ^ e) : ℤ) : F) = _
      simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow]
    have hker : (A.map (Int.castRingHom F)) *ᵥ (fun m => p.coeff m.val) = 0 := by
      rw [hcast]
      ext i
      change dotProduct (fun m : M => m.val.prod (fun l e => (z i l : F) ^ e))
        (fun m => p.coeff m.val) = 0
      rw [← eval_polynomialFromCoefficients, polynomialFromCoefficients_coefficients M p hp]
      exact hpz i
    have hh := Submodule.apply_mem_span_image_of_mem_span
      (polynomialFromCoefficients (R := F) M) (hspan _ hker)
    rw [polynomialFromCoefficients_coefficients M p hp] at hh
    have hG : (fun j => polynomialFromCoefficients (R := F) M (fun i => (C i j : F))) =
        (fun j => MvPolynomial.map (Int.castRingHom F) (G j)) := by
      funext j
      exact (polynomialFromCoefficients_map (Int.castRingHom F) M (fun i => C i j)).symm
    rw [← Set.range_comp] at hh
    change p ∈ Submodule.span F (Set.range (fun j =>
      polynomialFromCoefficients (R := F) M (fun i => (C i j : F)))) at hh
    rwa [hG] at hh

theorem monomial_eval_abs_le {σ : Type*} (z : σ → ℤ) (m : σ →₀ ℕ)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i, |(z i : ℝ)| ≤ H) (D : ℕ)
    (hD : monomialOrder m ≤ D) :
    |((m.prod (fun i e => z i ^ e) : ℤ) : ℝ)| ≤ H ^ D := by
  classical
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  rw [Finsupp.prod, Int.cast_prod, Finset.abs_prod]
  simp only [Int.cast_pow, abs_pow]
  calc
    (∏ i ∈ m.support, |(z i : ℝ)| ^ m i) ≤ ∏ i ∈ m.support, H ^ m i :=
      Finset.prod_le_prod₀ (fun i _ => by positivity)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hz i) _)
    _ = H ^ monomialOrder m := by simp [monomialOrder, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
    _ ≤ H ^ D := pow_le_pow_right₀ hH hD

theorem exists_bounded_degree_vanishing_polynomials {σ ι F : Type*}
    [Fintype σ] [Fintype ι] [Field F] [CharZero F]
    (z : ι → σ → ℤ) (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H)
    (D : ℕ) :
    ∃ G : monomialsUpTo σ D → MvPolynomial σ ℤ,
      (∀ j, (G j).totalDegree ≤ D) ∧
      (∀ j m, |(((G j).coeff m : ℤ) : ℝ)| ≤
        integralKernelHeight ((D + Fintype.card σ).choose (Fintype.card σ)) (H ^ D)) ∧
      (∀ j i, MvPolynomial.eval (z i) (G j) = 0) ∧
      ∀ p : MvPolynomial σ F, p.totalDegree ≤ D →
        (∀ i, MvPolynomial.eval (fun l => (z i l : F)) p = 0) →
        p ∈ Submodule.span F (Set.range (fun j => MvPolynomial.map (Int.castRingHom F) (G j))) := by
  classical
  obtain ⟨G, hs, hc, he, hspan⟩ := exists_bounded_polynomial_kernel
    (F := F) (monomialsUpTo σ D) z (H ^ D) (one_le_pow₀ hH)
    (fun i m => monomial_eval_abs_le (z i) m.val H hH (hz i) D
      (mem_monomialsUpTo.mp m.property))
  refine ⟨G, ?_, ?_, he, ?_⟩
  · intro j
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    exact fun m hm => mem_monomialsUpTo.mp (hs j hm)
  · simpa only [card_monomialsUpTo] using hc
  · intro p hp heval
    apply hspan p _ heval
    intro m hm
    exact mem_monomialsUpTo.mpr ((MvPolynomial.le_totalDegree hm).trans hp)

end QuarticPowerFree

end OAI
