import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.CubicSieve.Algebra
import OAI.NumberTheory.DirichletL.CubicSieve.Factorization
import OAI.NumberTheory.DirichletL.CubicSieve.Blocks

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def Admissible (I : Ideal Eis) : Prop := Squarefree I ∧ primaryGenerator I ≠ 0

def idealKernel (I J : Ideal Eis) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I (primaryGenerator J))

theorem idealKernel_reciprocity (I J : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealKernel I J = idealKernel J I :=
  congrArg eisEmbedding (CubicJacobiGlobal.idealSymbol_reciprocity I J hI hJ)

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm (primaryGenerator J) I) 2).trans_eq (by norm_num)

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, ite_eq_right hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem idealSymbol_cube_mask (I : Ideal Eis) (x : Eis)
    (hI : primaryGenerator I ≠ 0) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 3 =
      if IsCoprime I (Ideal.span {x}) then 1 else 0 := by
  have hlocal (P : Ideal Eis) (hP : P.IsMaximal ∧ goodLambda ∉ P) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 3 =
        if IsCoprime P (Ideal.span {x}) then 1 else 0 := by
    let : P.IsMaximal := hP.1
    let : Field (Eis ⧸ P) := Ideal.Quotient.field P
    let : Fintype (Eis ⧸ P) := Fintype.ofFinite _
    let χ := actualSextic P hP.2 ^ 2
    have hχ : χ ^ 3 = 1 :=
      (congrArg (fun φ : MulChar (Eis ⧸ P) ℂ => φ ^ 3)
        (canonicalSextic_pow_two P hP.2)).trans <|
          (MulChar.ringHomComp_pow _ _ _).trans <|
            (congrArg (fun φ : MulChar (Eis ⧸ P) Eis => φ.ringHomComp eisEmbedding)
              (cubicChar_pow_three P hP.2)).trans (MulChar.ringHomComp_one eisEmbedding)
    rw [CubicJacobiGlobal.primeValue_eq P hP.2]
    have hv := congrArg (fun φ : MulChar (Eis ⧸ P) ℂ => φ (Ideal.Quotient.mk P x))
      (canonicalSextic_pow_two P hP.2)
    change χ (Ideal.Quotient.mk P x) = _ at hv
    simp only [MulChar.ringHomComp_apply] at hv
    rw [← hv]
    rw [← map_pow, cubic_cube_eq_mask χ hχ, SixthPowerAverage.prime_coprime_span_iff]
    have hu : IsUnit (Ideal.Quotient.mk P x) ↔ x ∉ P := by
      rw [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    simp only [hu]
    split_ifs <;> rfl
  have hprod (S : Multiset (Ideal Eis))
      (hS : ∀ P ∈ S, P.IsMaximal ∧ goodLambda ∉ P) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 3 =
        if IsCoprime S.prod (Ideal.span {x}) then 1 else 0 := by
    induction S using Multiset.induction_on with
    | empty => simp only [Multiset.map_zero, Multiset.prod_zero, map_one, one_pow,
        isCoprime_one_left, ite_true]
    | @cons P S ih =>
      have hp := hS P (Multiset.mem_cons_self _ _)
      have ht := fun Q hQ => hS Q (Multiset.mem_cons_of_mem hQ)
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow,
        hlocal P hp, ih ht, IsCoprime.mul_left_iff]
      by_cases hP : IsCoprime P (Ideal.span {x}) <;>
        by_cases hS : IsCoprime S.prod (Ideal.span {x}) <;> simp [hP, hS]
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hf : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      P.IsMaximal ∧ goodLambda ∉ P := by
    intro P hP
    have h := primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)
    exact ⟨h.1, h.2.1⟩
  have h := hprod (UniqueFactorizationMonoid.normalizedFactors I) hf
  rw [Ideal.prod_normalizedFactors_eq_self hI0] at h
  simpa only [CubicJacobiGlobal.idealSymbol, ite_eq_right hI0] using h

theorem idealKernel_square_eq_star (I J : Ideal Eis) :
    idealKernel I J ^ 2 = star (idealKernel I J) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I (primaryGenerator J))

def idealNumeratorHom (I : Ideal Eis) (hI : primaryGenerator I ≠ 0) : Ideal Eis →* ℂ where
  toFun := idealKernel I
  map_one' := by
    change eisEmbedding (CubicJacobiGlobal.idealSymbol I (primaryGenerator 1)) = 1
    rw [primaryGenerator_one, CubicJacobiGlobal.idealSymbol_map_one I hI, map_one]
  map_mul' A B := by
    simp only [idealKernel, primaryGenerator_mul,
      CubicJacobiGlobal.idealSymbol_map_mul I hI, map_mul]

theorem idealKernel_row_decomposition (I A B C : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) :
    idealKernel I (A * B ^ 2 * C ^ 3) =
      idealKernel I A * star (idealKernel I B) * idealKernel I C ^ 3 := by
  change idealNumeratorHom I hI (A * B ^ 2 * C ^ 3) = _
  rw [map_mul, map_mul, map_pow, map_pow]
  change idealKernel I A * idealKernel I B ^ 2 * idealKernel I C ^ 3 = _
  rw [idealKernel_square_eq_star]

def idealRange (X : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌊X⌋₊).filter Admissible

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

def idealMatrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => idealKernel J.val I.val

def sieveNorm (M N : ℝ) : ℝ := squaredNorm (idealMatrix M N)

theorem sieveNorm_reciprocity (M N : ℝ) : sieveNorm M N = sieveNorm N M := by
  apply squaredNorm_reciprocity
  intro I J
  exact idealKernel_reciprocity J.val I.val
    (mem_idealRange.mp J.property).1.2 (mem_idealRange.mp I.property).1.2

theorem ideal_energy_bound (M N : ℝ) (coef : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      idealKernel J.val I.val * coef J‖ ^ 2) ≤
        sieveNorm M N * ∑ J, ‖coef J‖ ^ 2 :=
  energy_le_squaredNorm (idealMatrix M N) coef

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem ideal_cube_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal Eis) (B : b → Ideal Eis) (C : c → Ideal Eis)
    (cols : n → Ideal Eis) (hc : ∀ j, primaryGenerator (cols j) ≠ 0)
    (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j *
      idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * idealKernel (cols j) (A i * B k ^ 2 * C l ^ 3)) =
        ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
          coef j * idealKernel (cols j) (C l) ^ 3 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [idealKernel_row_decomposition _ _ _ _ (hc j)]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · intro l j
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (idealKernel_norm_le_one _ _) 3).trans_eq (by norm_num)

theorem ideal_cubic_factorization (I : Ideal Eis) (hI : I ≠ 0) :
    I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI

end
end SevenEighths.CubicSieve

end OAI
