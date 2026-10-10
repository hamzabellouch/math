import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.IntegerCharacter
import OAI.NumberTheory.SiegelZeros.Determinants.SqrtPairFrobeniusDirections

namespace OAI

namespace SiegelZeros

open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets

open Module NumberField

theorem trace_norm_quadratic_basis {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.trace ℚ K ((r : K) + s * a) = 2 * r ∧
      Algebra.norm ℚ ((r : K) + s * a) = r ^ 2 - d * s ^ 2 := by
  have hu0 : u 0 = 1 := congrFun hu 0
  have hu1 : u 1 = a := congrFun hu 1
  have hr0 : u.repr 1 = Finsupp.single 0 1 := by rw [← hu0, u.repr_self]
  have hr1 : u.repr a = Finsupp.single 1 1 := by rw [← hu1, u.repr_self]
  have hrc (c : ℚ) : u.repr (c : K) = c • Finsupp.single 0 1 := by
    simpa [Algebra.smul_def, hr0] using u.repr.map_smul c (1 : K)
  have hm0 : ((r : K) + s * a) * 1 = r • (1 : K) + s • a := by
    simp [Algebra.smul_def]
  have hm1 : ((r : K) + s * a) * a = (d * s) • (1 : K) + r • a := by
    calc
      _ = (s : K) * a ^ 2 + r * a := by ring
      _ = _ := by rw [ha]; simp [Algebra.smul_def, mul_comm]
  have hmat : Algebra.leftMulMatrix u ((r : K) + s * a) = !![r, d*s; s,r] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j
    all_goals simp [-Rat.cast_mul, hu0, hu1, hm0, hm1, hrc, hr1]
  rw [Algebra.trace_eq_matrix_trace u, Algebra.norm_eq_matrix_det u, hmat]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ]
  constructor <;> ring

theorem rat_int_of_squarefree_mul_sq_eq_int (d n : ℤ) (hd : Squarefree d)
    (x : ℚ) (hx : (d : ℚ) * x ^ 2 = n) : ∃ m : ℤ, x = m := by
  have heq : d * x.num ^ 2 = n * (x.den : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← x.num_div_den] at hx
    have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    field_simp at hx
    nlinarith [hx]
  have hdiv : (x.den : ℤ) * (x.den : ℤ) ∣ d * x.num ^ 2 := by
    rw [heq, ← pow_two]
    exact dvd_mul_left _ _
  have hden := hd.dvd_of_squarefree_of_mul_dvd_mul_right hdiv
  have hden_nat : x.den ∣ x.num.natAbs ^ 2 := by
    simpa only [Int.natCast_dvd, Int.natAbs_pow] using hden
  have hone : x.den = 1 := Nat.eq_one_of_dvd_coprimes (x.reduced.pow_left 2)
    hden_nat (dvd_refl _)
  exact ⟨x.num, ((Rat.den_eq_one_iff x).mp hone).symm⟩

theorem integral_quadratic_half_coordinates {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ) (r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hx : IsIntegral ℤ ((r : K) + s * a)) :
    ∃ m k : ℤ, 2 * r = m ∧ 2 * s = k ∧ 4 ∣ m ^ 2 - d * k ^ 2 := by
  obtain ⟨ht, hn⟩ := trace_norm_quadratic_basis u a (d : ℚ) r s hu (by simpa using ha)
  have hit : IsIntegral ℤ (2 * r) := ht ▸ Algebra.isIntegral_trace hx
  have hin : IsIntegral ℤ (r ^ 2 - (d : ℚ) * s ^ 2) := hn ▸ Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hit
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hin
  change (m : ℚ) = 2 * r at hm
  change (n : ℚ) = r ^ 2 - (d : ℚ) * s ^ 2 at hn
  have hsq : (d : ℚ) * (2 * s) ^ 2 = (m ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [hm, hn]
    ring
  obtain ⟨k, hk⟩ := rat_int_of_squarefree_mul_sq_eq_int d (m ^ 2 - 4 * n) hd (2 * s) hsq
  refine ⟨m, k, hm.symm, hk, n, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, ← hk, hn]
  ring

theorem even_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even m ∧ Even k := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four] at heq
  simp only [Int.even_iff]
  rcases hd with hd | hd <;> rw [hd] at heq <;> omega

theorem even_sub_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 1)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even (m - k) := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four, hd] at heq
  simp only [Int.even_iff]
  omega

theorem integral_quadratic_eq_int_add_int_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * a := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨hm2, hk2⟩ := even_coordinates_of_four_dvd d m k hd4 hmk
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp hm2
  obtain ⟨j, hj⟩ := even_iff_two_dvd.mp hk2
  have hri : r = (i : ℚ) := by
    have hi' : (m : ℚ) = 2 * i := by exact_mod_cast hi
    linarith
  have hsj : s = (j : ℚ) := by
    have hj' : (k : ℚ) = 2 * j := by exact_mod_cast hj
    linarith
  refine ⟨i, j, ?_⟩
  rw [← hrep, hri, hsj]
  norm_cast

theorem integral_quadratic_eq_int_add_int_mul_half {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * ((1 + a) / 2) := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp (even_sub_coordinates_of_four_dvd d m k hd4 hmk)
  have hri : r = (i : ℚ) + (k : ℚ) / 2 := by
    have hi' : (m : ℚ) - k = 2 * i := by exact_mod_cast hi
    linarith
  have hsk : s = (k : ℚ) / 2 := by linarith
  refine ⟨i, k, ?_⟩
  rw [← hrep, hri, hsk]
  push_cast
  ring

theorem integral_quadratic_half_generator {K : Type*} [Field K] [CharZero K]
    (a : K) (d : ℤ) (ha : a ^ 2 = d) (hd : d % 4 = 1) :
    IsIntegral ℤ ((1 + a) / 2) := by
  have hdv : d = 4 * (d / 4) + 1 := by omega
  refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4)),
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_add_C]; norm_num), ?_⟩
  change Polynomial.aeval ((1 + a) / 2)
    (Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4))) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_add, Polynomial.aeval_C]
  have hdK : (d : K) = 4 * ((d / 4 : ℤ) : K) + 1 := by exact_mod_cast hdv
  field_simp
  linear_combination ha + hdK

theorem exists_ringOfIntegers_pair_basis {K : Type*} [Field K] [NumberField K]
    (w : K) (hw : IsIntegral ℤ w) (hdim : Module.finrank ℚ K = 2)
    (hspan : ∀ x : K, IsIntegral ℤ x → ∃ m n : ℤ, x = m + n * w) :
    ∃ B : Basis (Fin 2) ℤ (𝓞 K),
      (fun i => ((B i : 𝓞 K) : K)) = ![1, w] := by
  let W : 𝓞 K := ⟨w, hw⟩
  let v : Fin 2 → 𝓞 K := ![1, W]
  have hs : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    obtain ⟨m, n, hmn⟩ := hspan x x.property
    have hmn' : x = m • (1 : 𝓞 K) + n • W := by
      apply RingOfIntegers.ext
      change (x : K) = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + n • W)
      rw [map_add, map_zsmul, map_zsmul, map_one]
      change (x : K) = m • (1 : K) + n • w
      simpa [Algebra.smul_def] using hmn
    rw [hmn']
    exact Submodule.add_mem _
      (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩))
  have hc : Fintype.card (Fin 2) = Module.finrank ℤ (𝓞 K) := by
    simpa [RingOfIntegers.rank] using hdim.symm
  let B : Basis (Fin 2) ℤ (𝓞 K) := basisOfTopLeSpanOfCardEqFinrank v hs hc
  refine ⟨B, ?_⟩
  ext i
  fin_cases i <;> simp [B, v, W]
  rfl

theorem discr_quadratic_pair {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.discr ℚ ![1, (r : K) + s * a] = 4 * d * s ^ 2 := by
  have ht := (trace_norm_quadratic_basis u a d r s hu ha).1
  have ht1 : Algebra.trace ℚ K 1 = 2 := by
    simpa using Algebra.trace_algebraMap_of_basis u (1 : ℚ)
  have hww : ((r : K) + s * a) * ((r : K) + s * a) =
      ((r ^ 2 + d * s ^ 2 : ℚ) : K) + ((2 * r * s : ℚ) : K) * a := by
    push_cast
    linear_combination (s : K) ^ 2 * ha
  have htww : Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) =
      2 * (r ^ 2 + d * s ^ 2) := by
    rw [hww]
    exact (trace_norm_quadratic_basis u a d (r ^ 2 + d * s ^ 2) (2 * r * s) hu ha).1
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change Algebra.trace ℚ K (1 * 1) *
      Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) -
    Algebra.trace ℚ K (1 * ((r : K) + s * a)) *
      Algebra.trace ℚ K (((r : K) + s * a) * 1) = _
  rw [one_mul, one_mul, mul_one, ht, ht1, htww]
  ring

theorem coe_discr_eq_pair_of_integer_basis {K : Type*} [Field K] [NumberField K]
    (B : Basis (Fin 2) ℤ (𝓞 K)) (w : K)
    (hB : (fun i => ((B i : 𝓞 K) : K)) = ![1, w]) :
    (NumberField.discr K : ℚ) = Algebra.discr ℚ ![1, w] := by
  rw [← NumberField.discr_eq_discr K B]
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ B) = _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K B]
  congr 1
  funext i
  rw [Basis.localizationLocalization_apply]
  exact congrFun hB i

theorem numberField_discr_quadratic_eq_four_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) : NumberField.discr K = 4 * d := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis a hai hdim
    (integral_quadratic_eq_int_add_int_mul u a d hu ha hd hd4)
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [coe_discr_eq_pair_of_integer_basis B a hB]
  simpa using discr_quadratic_pair u a (d : ℚ) 0 1 hu (by simpa using ha)

theorem numberField_discr_quadratic_eq_self {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) : NumberField.discr K = d := by
  have hwi := integral_quadratic_half_generator a d ha hd4
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis ((1 + a) / 2) hwi hdim
    (integral_quadratic_eq_int_add_int_mul_half u a d hu ha hd hd4)
  have hw : (1 + a) / 2 = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * a := by
    push_cast
    ring
  apply Int.cast_injective (α := ℚ)
  rw [coe_discr_eq_pair_of_integer_basis B ((1 + a) / 2) hB, hw,
    discr_quadratic_pair u a (d : ℚ) (1 / 2) (1 / 2) hu (by simpa using ha)]
  ring

theorem isFundamentalDiscr_quadratic {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    exact Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hd1, hd⟩)
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    exact Int.isFundamentalDiscr_four_mul.mpr ⟨hd, hd4⟩

theorem isUnramifiedIn_two_iff_radical_mod_four {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1 := by
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K)
    ((Int.prime_iff_natAbs_prime (k := 2)).mpr Nat.prime_two)]
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    have hodd : ¬ (2 : ℤ) ∣ d := by
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    simp [hodd, hd1]
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    have hdiv : (2 : ℤ) ∣ 4 * d := dvd_mul_of_dvd_left (by norm_num) d
    simp [hdiv, hd1]

end WeightedTorusJets

namespace WeightedTorusJets

theorem isUnramifiedIn_of_numberField_extension
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (P : Ideal ℤ) (hunr : Algebra.IsUnramifiedIn (𝓞 L) P) :
    Algebra.IsUnramifiedIn (𝓞 K) P := by
  intro Q hQ hover
  obtain ⟨⟨Q', hQ', hover'⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) Q
  have : Q'.LiesOver P := Ideal.LiesOver.trans Q' Q P
  have : Algebra.IsUnramifiedAt ℤ Q' := hunr Q' inferInstance inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ Q Q'



theorem quadratic_radical_mod_four_of_odd_cyclotomic_overfield
    (n : ℕ) [NeZero n] (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [IsCyclotomicExtension {n} ℚ L]
    (u : Module.Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d)
    (hd : Squarefree d) (hn : Odd n) : d % 4 = 1 := by
  apply (isUnramifiedIn_two_iff_radical_mod_four u a d hu ha hd).mp
  exact isUnramifiedIn_of_numberField_extension (L := L) _
    (cyclotomic_isUnramifiedIn n L 2 hn.not_two_dvd_nat)



noncomputable def quadraticAdjoinBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (ha : IsIntegral F a)
    (hdim : Module.finrank F (IntermediateField.adjoin F {a}) = 2) :
    Module.Basis (Fin 2) F (IntermediateField.adjoin F {a}) :=
  let pb := IntermediateField.adjoin.powerBasis ha
  pb.basis.reindex (finCongr (pb.finrank.symm.trans hdim))

@[simp]
theorem quadraticAdjoinBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (ha : IsIntegral F a)
    (hdim : Module.finrank F (IntermediateField.adjoin F {a}) = 2) (i : Fin 2) :
    quadraticAdjoinBasis a ha hdim i = ![1, IntermediateField.AdjoinSimple.gen F a] i := by
  fin_cases i <;>
    simp [quadraticAdjoinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]



open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem primitive_odd_quadratic_signed_level_mod_four {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hodd : Odd q) : (χ (-1) * (q : ℤ)) % 4 = 1 := by
  classical
  by_cases hne : χ = 1
  · subst χ
    have hq : q = 1 := hprim.symm.trans DirichletCharacter.conductor_one
    subst q
    rw [MulChar.one_apply isUnit_neg_one]
    norm_num
  let K := CyclotomicField q ℚ
  let : IsCyclotomicExtension {q} ℚ K := CyclotomicField.isCyclotomicExtension q ℚ
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  let χK := χ.ringHomComp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χ (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hprim
  let e := AddChar.zmodChar q (zeta_spec q ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root q (zeta_spec q ℚ K)
  let g := gaussSum χK e
  let D : ℤ := χ (-1) * q
  have hgD : g ^ 2 = (D : K) := by
    change gaussSum χK e ^ 2 = ((χ (-1) * (q : ℤ) : ℤ) : K)
    rw [primitive_quadratic_gaussSum_sq hpK (hχ.comp (Int.castRingHom K)) he]
    change (χ (-1) : K) * (q : K) = ((χ (-1) * (q : ℤ) : ℤ) : K)
    rw [Int.cast_mul, Int.cast_natCast]
  have hqsf : Squarefree q := odd_divisor_primitive_quadratic_squarefree χ hχ hprim hodd dvd_rfl
  have hDsf : Squarefree D := by
    apply Int.squarefree_natAbs.mp
    change Squarefree (χ (-1) * (q : ℤ)).natAbs
    rw [Int.natAbs_mul, Int.natAbs_of_isUnit (isUnit_neg_one.map χ), one_mul]
    exact hqsf
  have hneC : χ.ringHomComp (Int.castRingHom ℂ) ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ)
      (Int.cast_injective (α := ℂ))).mpr hne
  have hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {g}) = 2 := by
    rw [show IntermediateField.adjoin ℚ {g} =
        characterField q K ℂ (χ.ringHomComp (Int.castRingHom ℂ)) from
      gaussSum_adjoin_eq_characterField χ hχ hprim e he]
    exact characterField_finrank q K ℂ _ (hχ.comp (Int.castRingHom ℂ)) hneC
  have hgi : IsIntegral ℚ g := IsIntegral.of_pow (by decide : 0 < 2)
    (hgD ▸ isIntegral_intCast D)
  let F := IntermediateField.adjoin ℚ {g}
  let a : F := IntermediateField.AdjoinSimple.gen ℚ g
  let u := quadraticAdjoinBasis g hgi hdim
  have hu : (u : Fin 2 → F) = ![1, a] := by
    funext i
    exact quadraticAdjoinBasis_apply g hgi hdim i
  have ha : a ^ 2 = (D : F) := by
    apply Subtype.ext
    exact hgD
  exact quadratic_radical_mod_four_of_odd_cyclotomic_overfield q F K u a D hu ha hDsf hodd

end WeightedTorusJets

namespace WeightedTorusJets

noncomputable def crtUnits {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

@[simp]
theorem crtUnits_fst {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    (crtUnits h u).1 = ZMod.unitsMap (Nat.dvd_mul_right m n) u := by
  apply Units.ext
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m))) (u : ZMod (m * n))

@[simp]
theorem crtUnits_snd {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    (crtUnits h u).2 = ZMod.unitsMap (Nat.dvd_mul_left n m) u := by
  apply Units.ext
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n))) (u : ZMod (m * n))

noncomputable def crtCharacterLeft {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) : DirichletCharacter R m :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inl _ _)))

noncomputable def crtCharacterRight {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) : DirichletCharacter R n :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inr _ _)))

@[simp]
theorem crtCharacterLeft_apply_unit {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) (u : (ZMod m)ˣ) :
    crtCharacterLeft h χ u = χ ((crtUnits h).symm (u, 1)) := by
  simp [crtCharacterLeft]

@[simp]
theorem crtCharacterRight_apply_unit {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) (u : (ZMod n)ˣ) :
    crtCharacterRight h χ u = χ ((crtUnits h).symm (1, u)) := by
  simp [crtCharacterRight]

theorem crtCharacter_decomposition {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) :
    χ = DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ) *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ) := by
  apply MulChar.ext
  intro u
  rw [MulChar.mul_apply]
  simp only [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe,
    MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [crtCharacterLeft_apply_unit, crtCharacterRight_apply_unit, ← map_mul]
  congr 1
  have hu : u = (crtUnits h).symm (ZMod.unitsMap (Nat.dvd_mul_right m n) u, 1) *
      (crtUnits h).symm (1, ZMod.unitsMap (Nat.dvd_mul_left n m) u) := by
    apply (crtUnits h).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Prod.ext <;> simp
  exact congrArg Units.val hu

theorem crtCharacterLeft_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    {R : Type*} [CommRing R] (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (hprim : χ.IsPrimitive) :
    (crtCharacterLeft h χ).IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ))
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ))
  rw [← crtCharacter_decomposition h χ, hprim,
    DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hdiv
  apply Nat.dvd_antisymm (crtCharacterLeft h χ).conductor_dvd_level
  apply Nat.dvd_of_mul_dvd_mul_right (NeZero.pos n)
  exact hdiv.trans (Nat.lcm_dvd (Nat.dvd_mul_right _ n)
    ((crtCharacterRight h χ).conductor_dvd_level.trans (Nat.dvd_mul_left n _)))

theorem crtCharacterRight_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    {R : Type*} [CommRing R] (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (hprim : χ.IsPrimitive) :
    (crtCharacterRight h χ).IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ))
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ))
  rw [← crtCharacter_decomposition h χ, hprim,
    DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hdiv
  apply Nat.dvd_antisymm (crtCharacterRight h χ).conductor_dvd_level
  apply Nat.dvd_of_mul_dvd_mul_left (NeZero.pos m)
  exact hdiv.trans (Nat.lcm_dvd
    ((crtCharacterLeft h χ).conductor_dvd_level.trans (Nat.dvd_mul_right m _))
    (Nat.dvd_mul_left _ m))

theorem changeLevel_neg_one {m n : ℕ} {R : Type*} [CommRing R]
    (h : m ∣ n) (χ : DirichletCharacter R m) :
    DirichletCharacter.changeLevel h χ (-1) = χ (-1) := by
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (-1 : (ZMod n)ˣ)
  simpa only [Units.val_neg, Units.val_one, ZMod.cast_neg h, ZMod.cast_one h] using he

theorem crtCharacter_neg_one {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) :
    χ (-1) = crtCharacterLeft h χ (-1) * crtCharacterRight h χ (-1) := by
  have he := congrArg (fun ψ : DirichletCharacter R (m * n) => ψ (-1))
    (crtCharacter_decomposition h χ)
  simpa only [MulChar.mul_apply, changeLevel_neg_one] using he

end WeightedTorusJets


end SiegelZeros

end OAI
