import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.AuxiliarySqrtPairCharacterField
import OAI.NumberTheory.SiegelZeros.Structure.SqrtTwoField

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField



namespace WeightedTorusJets

open NumberField

theorem source_biquadratic_arithmetic_full (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hq8 : q ≠ 8) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  have hquad := real_character_isQuadratic χ hreal
  obtain ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, _, _, hadj, hfields, hsign⟩ :=
    exists_auxiliary_sqrt_pair_with_characterField q L χ hquad hprim hne hq8
  have haRat : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hbRat : b ^ 2 = algebraMap ℚ L (2 : ℚ) := by simpa using hb
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
  have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
  have hint := biquadratic_monomials_integral a' b' d 2 ha' (by simpa using hb')
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hdesc⟩ :=
    sqrtPair_frobenius_directions a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  obtain ⟨hformula, hfund, _⟩ := quadraticAdjoin_discriminant a d ha hd hdns
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, hadj, ?_, hfund, hformula, v, hv, ?_, ?_,
    σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  · rw [hadj]
    exact characterField_changeLevel_discr_natAbs (dvd_mul_left q 8) χ hquad hprim hne
  · intro i
    rw [hv]
    fin_cases i
    · exact hint.1
    · exact hint.2.1
    · exact hint.2.2.1
    · exact hint.2.2.2
  · exact finrank_adjoin_pair_sqrt a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  · intro p hp hpn hχp
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero (8 * q) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    have hpm : ¬ p ∣ 8 * q := hp.coprime_iff_not_dvd.mp (h8.mul_right hq)
    obtain ⟨φ, hfrob, hglobal⟩ := exists_cyclotomic_frobenius_congruence (8 * q) L p hpm
    obtain ⟨P, hP, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    exact hdesc p φ (hsign p hp hpn P hover.over.symm φ (hfrob P inferInstance hover) hχp) hglobal

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

theorem source_biquadratic_arithmetic_canonical_full (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hq8 : q ≠ 8) :
    let L := CyclotomicField (8 * q) ℚ
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  exact source_biquadratic_arithmetic_full q (CyclotomicField (8 * q) ℚ)
    χ hreal hprim hne hq8






open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

namespace WeightedTorusJets

theorem exists_lower_triangular_replacement
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A B : Matrix ι ι K)
    (hspan : ∀ i, B i - A i ∈ Submodule.span K (A '' {j | j < i})) :
    ∃ L : Matrix ι ι K, L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧ B = L * A := by
  classical
  have hcoeff (i : ι) : ∃ c : ι → K,
      ∑ j ∈ Finset.univ.filter (fun j => j < i), c j • A j = B i - A i := by
    apply (Submodule.mem_span_image_finset_iff_exists_fun' K).mp
    simpa using hspan i
  choose c hc using hcoeff
  refine ⟨Matrix.of (fun i j =>
    (if j < i then c i j else 0) + (if i = j then 1 else 0)),
    ?_, ?_, ?_⟩
  · intro i j hij
    change i < j at hij
    simp [not_lt_of_ge hij.le, hij.ne]
  · intro i
    simp
  · apply Matrix.ext
    intro i k
    have hi := congrFun (hc i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi
    simpa only [Matrix.mul_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      ite_mul, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_filter] using (eq_sub_iff_add_eq.mp hi).symm

theorem determinant_dvd_of_earlier_row_replacement
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (A B : Matrix ι ι R)
    (hspan : ∀ i, f.mapMatrix B i - f.mapMatrix A i ∈
      Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (p : R) (e : ι → ℕ) (hdiv : ∀ i j, p ^ e i ∣ B i j) :
    p ^ (∑ i, e i) ∣ A.det := by
  classical
  obtain ⟨L, hL, hdiag, hreplace⟩ :=
    exists_lower_triangular_replacement (f.mapMatrix A) (f.mapMatrix B) hspan
  have hdet : B.det = A.det := hf <| by
    rw [f.map_det, f.map_det, hreplace, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular L hL]
    simp [hdiag]
  choose C hC using hdiv
  have hB : B = Matrix.of (fun i j => p ^ e i * (Matrix.of C) i j) := by
    ext i j
    exact hC i j
  rw [← hdet, hB, Matrix.det_mul_column (fun i => p ^ e i) (Matrix.of C),
    Finset.prod_pow_eq_pow_sum]
  exact dvd_mul_right _ _

theorem replacement_row_expansion {K ι : Type*} [CommRing K]
    (x y z : ι → K) (p k r b c : ℕ) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c =
      ∑ m ∈ Finset.range (k + 1),
        (((-1) ^ m * (k.choose m : K)) •
          (x ^ (p * (k - m) + r) * y ^ (b + m) * z ^ c)) := by
  rw [sub_eq_add_neg, add_comm (x ^ p), add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
    Pi.natCast_apply, pow_add, pow_mul]
  rw [neg_pow]
  ring

theorem replacement_row_sub_mem {K ι : Type*} [CommRing K]
    (x y z : ι → K) (W : Submodule K (ι → K)) (H p k r b c : ℕ) (hp : H < p)
    (hspan : ∀ a b' c', a + H * b' + H * c' < p * k + r + H * b + H * c →
      x ^ a * y ^ b' * z ^ c' ∈ W) :
    x ^ r * (x ^ p - y) ^ k * y ^ b * z ^ c -
      x ^ (p * k + r) * y ^ b * z ^ c ∈ W := by
  rw [replacement_row_expansion, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
    Nat.sub_zero, Nat.add_zero, add_sub_cancel_right]
  apply W.sum_mem
  intro m hm
  apply W.smul_mem
  apply hspan
  have hmle : m + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hm)
  have hprod : H * (m + 1) < p * (m + 1) :=
    Nat.mul_lt_mul_of_pos_right hp (Nat.succ_pos m)
  have hdecomp : p * k = p * (k - (m + 1)) + p * (m + 1) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hmle]
  simp only [Nat.mul_add, Nat.mul_one] at hprod hdecomp ⊢
  omega

theorem weighted_interpolation_determinant_dvd
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (a b c : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i n, A i n = x n ^ a i * y n ^ b i * z n ^ c i)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (f ∘ x) ^ a' * (f ∘ y) ^ b' * (f ∘ z) ^ c' ∈
        Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (hFrob : ∀ n, (p : R) ∣ x n ^ p - y n) :
    (p : R) ^ (∑ i, a i / p) ∣ A.det := by
  classical
  let B : Matrix ι ι R := Matrix.of fun i n =>
    x n ^ (a i % p) * (x n ^ p - y n) ^ (a i / p) * y n ^ b i * z n ^ c i
  apply determinant_dvd_of_earlier_row_replacement f hf A B
  · intro i
    have h := replacement_row_sub_mem (f ∘ x) (f ∘ y) (f ∘ z)
      (Submodule.span K (f.mapMatrix A '' {j | j < i}))
      H p (a i / p) (a i % p) (b i) (c i) hp (by
        intro a' b' c' hw
        apply hspan i a' b' c'
        simpa only [Nat.div_add_mod] using hw)
    have heq : f.mapMatrix B i - f.mapMatrix A i =
        (f ∘ x) ^ (a i % p) * ((f ∘ x) ^ p - f ∘ y) ^ (a i / p) *
          (f ∘ y) ^ b i * (f ∘ z) ^ c i -
          (f ∘ x) ^ a i * (f ∘ y) ^ b i * (f ∘ z) ^ c i := by
      ext n
      simp [B, hA, map_mul, map_pow, map_sub]
    rw [heq]
    simpa only [Nat.div_add_mod] using h
  · intro i n
    exact (((pow_dvd_pow_of_dvd (hFrob n) (a i / p)).mul_left
      (x n ^ (a i % p))).mul_right (y n ^ b i)).mul_right (z n ^ c i)

theorem weighted_interpolation_determinant_dvd_of_frobenius_choice
    {R K ι : Type*} [CommRing R] [CommRing K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (a b c : ι → ℕ) (A : Matrix ι ι R)
    (hA : ∀ i n, A i n = x n ^ a i * y n ^ b i * z n ^ c i)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (f ∘ x) ^ a' * (f ∘ y) ^ b' * (f ∘ z) ^ c' ∈
        Submodule.span K (f.mapMatrix A '' {j | j < i}))
    (hFrob : (∀ n, (p : R) ∣ x n ^ p - y n) ∨
      (∀ n, (p : R) ∣ x n ^ p - z n)) :
    (p : R) ^ (∑ i, a i / p) ∣ A.det := by
  rcases hFrob with hFrob | hFrob
  · exact weighted_interpolation_determinant_dvd f hf x y z a b c A hA H p hp
      hspan hFrob
  · apply weighted_interpolation_determinant_dvd f hf x z y a c b A
      (fun i n => by rw [hA]; ring) H p hp _ hFrob
    intro i a' c' b' hw
    have h := hspan i a' b' c' (by omega)
    convert h using 1
    ring

open NumberField

theorem galois_derivative_determinant_mem_prime_power
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (θ : ι → 𝓞 K) (ν₂ ν₃ : K →+* K) (a b c : ι → ℕ)
    (H p : ℕ) (hp : H < p)
    (hspan : ∀ i a' b' c', a' + H * b' + H * c' < a i + H * b i + H * c i →
      (fun n => (θ n : K) ^ a' * ν₂ (θ n) ^ b' * ν₃ (θ n) ^ c') ∈
        Submodule.span K ((fun i n =>
          (θ n : K) ^ a i * ν₂ (θ n) ^ b i * ν₃ (θ n) ^ c i) '' {j | j < i}))
    (hFrob : (∀ n, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (θ n ^ p) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom ν₂ (θ n))) ∨
      (∀ n, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (θ n ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom ν₃ (θ n)))) :
    (Matrix.of (fun i n => θ n ^ a i * (RingOfIntegers.mapRingHom ν₂ (θ n)) ^ b i *
      (RingOfIntegers.mapRingHom ν₃ (θ n)) ^ c i)).det ∈
      (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, a i / p) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  apply weighted_interpolation_determinant_dvd_of_frobenius_choice (algebraMap (𝓞 K) K)
    RingOfIntegers.coe_injective θ
    ((RingOfIntegers.mapRingHom ν₂) ∘ θ) ((RingOfIntegers.mapRingHom ν₃) ∘ θ)
    a b c _ (fun _ _ => rfl) H p hp
  · intro i a' b' c' hw
    convert hspan i a' b' c' hw using 1
    · apply congrArg (Submodule.span K)
      apply congrArg (fun f : ι → ι → K => f '' {j | j < i})
      ext j n
      change algebraMap (𝓞 K) K (_ * _ * _) = _
      simp
    · funext n
      rfl
  · rcases hFrob with hFrob | hFrob
    · exact Or.inl fun n => Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hFrob n))
    · exact Or.inr fun n => Ideal.mem_span_singleton.mp
        ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hFrob n))

theorem integral_jet_matrix_lift {K : Type*} [Field K]
    (σ τ : K →+* K) {a b : K} {d : ℤ} {m : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (n : Fin m → Fin 4 → ℕ) (α : Fin m → Fin 3 → ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    ∃ θ₀ : Fin m → 𝓞 K,
      (∀ j, (θ₀ j : K) = θ j) ∧
      let A₀ := Matrix.of fun i j => θ₀ j ^ α i 0 *
        NumberField.RingOfIntegers.mapRingHom σ (θ₀ j) ^ α i 1 *
        NumberField.RingOfIntegers.mapRingHom (σ.comp τ) (θ₀ j) ^ α i 2
      A₀.map (algebraMap (𝓞 K) K) = A ∧
        (A₀.det : K) = A.det ∧ (A.det ≠ 0 → A₀.det ≠ 0) := by
  let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
  obtain ⟨h1, hai, hbi, hab⟩ :=
    biquadratic_monomials_integral a b d 2 ha (by simpa using hb)
  have hθ (j : Fin m) : IsIntegral ℤ (θ j) := by
    apply IsIntegral.sum
    intro i _
    apply (isIntegral_natCast _).mul
    fin_cases i <;> assumption
  let θ₀ : Fin m → 𝓞 K := fun j => ⟨θ j, hθ j⟩
  refine ⟨θ₀, fun _ => rfl, ?_⟩
  dsimp only
  have hmap :
      (Matrix.of fun i j => θ₀ j ^ α i 0 *
        NumberField.RingOfIntegers.mapRingHom σ (θ₀ j) ^ α i 1 *
        NumberField.RingOfIntegers.mapRingHom (σ.comp τ) (θ₀ j) ^ α i 2).map
          (algebraMap (𝓞 K) K) =
      Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
        (σ.comp τ) (θ j) ^ α i 2 := by
    ext i j
    change algebraMap (𝓞 K) K (_ * _ * _) = _
    simp only [map_mul, map_pow]
    rfl
  refine ⟨hmap, ?_⟩
  have hdet := congrArg Matrix.det hmap
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
  exact ⟨hdet, fun h => NumberField.RingOfIntegers.coe_ne_zero_iff.mp (hdet.symm ▸ h)⟩

theorem exists_integral_jet_determinant_divisible
    {K : Type*} [Field K]
    (σ τ : K →+* K) {a b : K} {d : ℤ} {m : ℕ}
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (n : Fin m → Fin 4 → ℕ) (α : Fin m → Fin 3 → ℕ) (H : ℕ) :
    let θ := fun j => ∑ i : Fin 4, (n j i : K) * ![1, a, b, a * b] i
    let A := Matrix.of fun i j => θ j ^ α i 0 * σ (θ j) ^ α i 1 *
      (σ.comp τ) (θ j) ^ α i 2
    (∀ i a' b' c', a' + H * b' + H * c' < α i 0 + H * α i 1 + H * α i 2 →
      (fun j => θ j ^ a' * σ (θ j) ^ b' * (σ.comp τ) (θ j) ^ c') ∈
        Submodule.span K (A '' {j | j < i})) →
    A.det ≠ 0 →
    ∃ Δ : 𝓞 K, (Δ : K) = A.det ∧ Δ ≠ 0 ∧
      ∀ p : ℕ, H < p →
        ((∀ t : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (t ^ p) =
            Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (RingOfIntegers.mapRingHom σ t)) ∨
          (∀ t : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (t ^ p) =
            Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
              (RingOfIntegers.mapRingHom (σ.comp τ) t))) →
        Δ ∈ (Ideal.span {(p : 𝓞 K)}) ^ (∑ i, α i 0 / p) := by
  dsimp only
  intro hspan hnonzero
  obtain ⟨θ₀, hθ₀, _hmap, hdet, hne⟩ := integral_jet_matrix_lift σ τ ha hb n α
  refine ⟨_, hdet, hne hnonzero, ?_⟩
  intro p hp hFrob
  apply galois_derivative_determinant_mem_prime_power θ₀ σ (σ.comp τ)
    (fun i => α i 0) (fun i => α i 1) (fun i => α i 2) H p hp
  · intro i a' b' c' hw
    convert hspan i a' b' c' hw using 1
    · apply congrArg (Submodule.span K)
      apply congrArg (fun f : Fin m → Fin m → K => f '' {j | j < i})
      ext k j
      simp only [Matrix.of_apply, hθ₀]
    · funext j
      simp only [hθ₀]
  · rcases hFrob with hFrob | hFrob
    · exact Or.inl fun j => hFrob (θ₀ j)
    · exact Or.inr fun j => hFrob (θ₀ j)

end WeightedTorusJets

open scoped NumberField

namespace WeightedTorusJets

theorem frobenius_action_choice_iff_mapRingHom
    {K : Type*} [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) (p : ℕ) :
    ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) ↔
    ((∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p -
        NumberField.RingOfIntegers.mapRingHom σ.toRingHom x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p -
        NumberField.RingOfIntegers.mapRingHom (σ.toRingHom.comp τ.toRingHom) x)) := by
  rfl

theorem frobenius_action_choice_quotient
    {K : Type*} [Field K] [NumberField K] (σ τ : K ≃ₐ[ℚ] K) (p : ℕ)
    (hFrob : (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x) ∨
      (∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - (σ * τ) • x)) :
    ((∀ x : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (x ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
          (NumberField.RingOfIntegers.mapRingHom σ.toRingHom x)) ∨
      (∀ x : 𝓞 K, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (x ^ p) =
        Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})
          (NumberField.RingOfIntegers.mapRingHom (σ.toRingHom.comp τ.toRingHom) x))) := by
  rcases (frobenius_action_choice_iff_mapRingHom σ τ p).mp hFrob with h | h
  · exact Or.inl fun x => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h x))
  · exact Or.inr fun x => (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h x))

end WeightedTorusJets

open scoped BigOperators


end SiegelZeros

end OAI
