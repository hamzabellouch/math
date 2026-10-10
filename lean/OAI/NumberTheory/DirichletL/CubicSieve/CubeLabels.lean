import OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

section
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase)

private theorem cross_sixth {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg i k ^ 6 = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  simpa only [crossSymbol, map_pow, ite_eq_right hnot] using
    canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem reverse_cross_eq_quadratic {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    crossSymbol p hg k i = crossSymbol p hg i k *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) := by
  have hr : crossSymbol p hg i k ^ 2 = crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  symm
  calc
    _ = crossSymbol p hg i k ^ 4 *
        (crossSymbol p hg k i ^ 2 * crossSymbol p hg k i) := by ring
    _ = crossSymbol p hg i k ^ 6 * crossSymbol p hg k i := by rw [← hr]; ring
    _ = _ := by rw [cross_sixth p hcop hg i k hik, one_mul]

private theorem local_quadratic_sq {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) (hik : i ≠ k) :
    (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^ 2 = 1 := by
  rw [mul_pow, ← pow_mul, ← pow_mul]
  norm_num only [show 3 * 2 = 6 by decide, cross_sixth p hcop hg i k hik,
    cross_sixth p hcop hg k i hik.symm, one_mul]

private theorem crt_exponent_table (side parityBit ε₁ ε₂ : Bool)
    (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) % 6 =
      ((if side then 5 else 1) * crtExponent side parityBit ε₁ ε₂) % 6 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    first | exact False.elim (he (by decide)) | decide

theorem active_cube_cross_local {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) (he : conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3) ^
        (conductorExponent parityBit ε₁ ε₂).val := by
  let x := crossSymbol p hg i k
  let q := crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3
  have hrev : crossSymbol p hg k i = x * q := reverse_cross_eq_quadratic p hcop hg hpr i k hik
  have h6 : x ^ 6 = 1 := cross_sixth p hcop hg i k hik
  have hs : star x = x ^ 5 := by
    have h := canonicalSextic_conj_as_row_label (Ideal.span {p i}) (hg i) (p k)
    change star x = x * x ^ 4 at h
    rw [h]
    ring
  calc
    _ = x ^ ((if side then 5 else 1) + (conductorExponent parityBit ε₁ ε₂).val) *
        q ^ (conductorExponent parityBit ε₁ ε₂).val := by rw [hrev, mul_pow, pow_add]; ring
    _ = _ := by
      congr 1
      cases side
      · change x ^ (1 + (conductorExponent parityBit ε₁ ε₂).val) = x ^ crtExponent false parityBit ε₁ ε₂
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        simpa only [Bool.false_eq_true, ↓reduceIte, one_mul] using crt_exponent_table false parityBit ε₁ ε₂ he
      · change x ^ (5 + (conductorExponent parityBit ε₁ ε₂).val) = star (x ^ crtExponent true parityBit ε₁ ε₂)
        rw [star_pow, hs, ← pow_mul]
        conv_lhs => rw [pow_eq_pow_mod _ h6]
        conv_rhs => rw [pow_eq_pow_mod _ h6]
        congr 1
        exact crt_exponent_table true parityBit ε₁ ε₂ he

def cubeOddSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1

def mixedCubeCross {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) : ℂ :=
  ∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
    crossSymbol p hg i k ^ (if side then 5 else 1) *
      crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val

theorem mixedCubeCross_eq_ordered {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (U B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (∏ i ∈ U, ∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        crossSymbol p hg i k ^ (if side then 5 else 1)) *
      (∏ k ∈ B.filter (fun k => conductorExponent (parity (v k)) (ε₁ k) (ε₂ k) ≠ 0),
        ∏ i ∈ U, crossSymbol p hg k i ^ (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) := by
  rw [Finset.prod_comm (s := B.filter _) (t := U)]
  simp only [mixedCubeCross, Finset.prod_mul_distrib]

private theorem cube_cross_local_if {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k)
    (side parityBit ε₁ ε₂ : Bool) :
    (if conductorExponent parityBit ε₁ ε₂ ≠ 0 then
      crossSymbol p hg i k ^ (if side then 5 else 1) *
        crossSymbol p hg k i ^ (conductorExponent parityBit ε₁ ε₂).val else 1) =
    (if side then star (crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂)
      else crossSymbol p hg i k ^ crtExponent side parityBit ε₁ ε₂) *
      (if (conductorExponent parityBit ε₁ ε₂).val % 2 = 1 then
        crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
  by_cases he : conductorExponent parityBit ε₁ ε₂ = 0
  · simp [he, crtExponent]
  · rw [ite_eq_left he, active_cube_cross_local p hcop hg hpr i k hik side parityBit ε₁ ε₂ he]
    congr 1
    rw [pow_eq_pow_mod _ (local_quadratic_sq p hcop hg i k hik)]
    by_cases ho : (conductorExponent parityBit ε₁ ε₂).val % 2 = 1
    · simp [ho]
    · have hz : (conductorExponent parityBit ε₁ ε₂).val % 2 = 0 := by omega
      simp [ hz]

theorem mixedCubeCross_eq_row_quadratic {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      quadraticCrossPhase p hg U (cubeOddSupport B v ε₁ ε₂) := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
      (crtLabel p B v ε₁ ε₂ side) =
      ∏ i ∈ U, ∏ k ∈ B, crossSymbol p hg i k ^
        crtExponent side (parity (v k)) (ε₁ k) (ε₂ k) := by
    simp only [finiteSquarefreeRow, crtLabel, primeProduct, map_prod, map_pow, crossSymbol]
  calc
    _ = (∏ i ∈ U, ∏ k ∈ B,
        if side then star (crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k))
        else crossSymbol p hg i k ^ crtExponent side (parity (v k)) (ε₁ k) (ε₂ k)) *
      (∏ i ∈ U, ∏ k ∈ B,
        if (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val % 2 = 1 then
          crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3 else 1) := by
      simp only [mixedCubeCross, Finset.prod_filter, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro k hk
      apply cube_cross_local_if p hcop hg hpr i k
      exact fun he => Finset.disjoint_left.mp hd hi (he ▸ hk)
    _ = _ := by
      congr 1
      · rw [hr]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, star_prod]
      · simp only [quadraticCrossPhase, cubeOddSupport, Finset.prod_filter]

theorem mixedCubeCross_eq_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side))
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U
          (crtLabel p B v ε₁ ε₂ side)) *
      (∑ χ : RayFourExpansion.RayCharacter, ∑ η : RayFourExpansion.RayCharacter,
        RayFourExpansion.crossCoeff χ η * RayFourExpansion.rayCharacter χ (∏ i ∈ U, p i) *
          RayFourExpansion.rayCharacter η (∏ k ∈ cubeOddSupport B v ε₁ ε₂, p k)) := by
  rw [mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd v ε₁ ε₂ side,
    RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc]
  exact hd.mono_right (Finset.filter_subset _ _)

end FirstPassCubeLabels

open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel
abbrev O := ActualEisensteinCubic.O

def squarePart (I : Ideal O) : Ideal O := (exists_sq_mul_squarefree I).choose

def squarefreePart (I : Ideal O) : Ideal O :=
  (exists_sq_mul_squarefree I).choose_spec.choose

theorem squarePart_sq_mul_squarefreePart (I : Ideal O) :
    squarePart I ^ 2 * squarefreePart I = I :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.1

theorem squarefree_squarefreePart (I : Ideal O) : Squarefree (squarefreePart I) :=
  (exists_sq_mul_squarefree I).choose_spec.choose_spec.2

theorem squarePart_ne_zero {I : Ideal O} (hI : I ≠ 0) : squarePart I ≠ 0 := by
  intro hz
  have h := squarePart_sq_mul_squarefreePart I
  rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  exact hI h.symm

theorem squarefree_decomposition_unique {A B D E : Ideal O}
    (hA : A ≠ 0) (hB : B ≠ 0) (hD : Squarefree D) (hE : Squarefree E)
    (h : A ^ 2 * D = B ^ 2 * E) : A = B ∧ D = E := by
  have hf := congrArg normalizedFactors h
  rw [normalizedFactors_mul (pow_ne_zero _ hA) hD.ne_zero,
    normalizedFactors_mul (pow_ne_zero _ hB) hE.ne_zero,
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have hd := (squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD
  have he := (squarefree_iff_nodup_normalizedFactors hE.ne_zero).mp hE
  have hcount (P : Ideal O) :
      (normalizedFactors A).count P = (normalizedFactors B).count P ∧
      (normalizedFactors D).count P = (normalizedFactors E).count P := by
    have hc := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hc
    have hd1 := Multiset.nodup_iff_count_le_one.mp hd P
    have he1 := Multiset.nodup_iff_count_le_one.mp he P
    omega
  constructor
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hA hB).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).1)
  · apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors hD.ne_zero hE.ne_zero).mpr
    exact Multiset.ext.mpr (fun P => (hcount P).2)

theorem squarePart_mul_squarefree {A D : Ideal O} (hA : A ≠ 0) (hD : Squarefree D) :
    squarePart (A ^ 2 * D) = A ∧ squarefreePart (A ^ 2 * D) = D :=
  squarefree_decomposition_unique
    (squarePart_ne_zero (mul_ne_zero (pow_ne_zero _ hA) hD.ne_zero)) hA
    (squarefree_squarefreePart _) hD (squarePart_sq_mul_squarefreePart _)

def decompositionEquiv : {I : Ideal O // I ≠ 0} ≃
    {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D} where
  toFun I := (⟨squarePart I.val, squarePart_ne_zero I.property⟩,
    ⟨squarefreePart I.val, squarefree_squarefreePart I.val⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val, mul_ne_zero (pow_ne_zero _ p.1.property) p.2.property.ne_zero⟩
  left_inv I := Subtype.ext (squarePart_sq_mul_squarefreePart I.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property p.2.property).2

theorem squarefree_decomposition_tsum {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (f : Ideal O → V) :
    (∑' I : {I : Ideal O // I ≠ 0}, f I.val) =
      ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
        f (p.1.val ^ 2 * p.2.val) := by
  exact (decompositionEquiv.symm.tsum_eq (fun I => f I.val)).symm

theorem norm_decomposition (I : Ideal O) :
    Ideal.absNorm (squarePart I) ^ 2 * Ideal.absNorm (squarefreePart I) = Ideal.absNorm I := by
  simpa only [map_mul, map_pow] using congrArg Ideal.absNorm (squarePart_sq_mul_squarefreePart I)

open ActualEisensteinCubic QuadraticInitialBound CompletedGauss

theorem quadraticRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    quadraticRow P hg S (a * b) = quadraticRow P hg S a * quadraticRow P hg S b := by
  rw [quadraticRow, finiteSquarefreeRow_mul, mul_pow]
  rfl

theorem quadraticRow_square {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    quadraticRow P hg S (a ^ 2) = rowCoprimeMask P S a := by
  have heq : quadraticRow P hg S (a ^ 2) = finiteSquarefreeRow P hg S (a ^ 6) := by
    simp only [quadraticRow, finiteSquarefreeRow, map_pow, ← Finset.prod_pow, ← pow_mul]
  rw [heq, finiteSquarefreeRow_sixth_power]
  rfl

theorem quadraticRow_primary_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (I : Ideal O) :
    quadraticRow P hg S (primaryGenerator I) =
      rowCoprimeMask P S (primaryGenerator (squarePart I)) *
        quadraticRow P hg S (primaryGenerator (squarefreePart I)) := by
  conv_lhs => rw [← squarePart_sq_mul_squarefreePart I]
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (squarePart I ^ 2) = primaryGenerator (squarePart I) ^ 2 :=
    map_pow primaryGeneratorHom _ _
  rw [hpow, quadraticRow_mul, quadraticRow_square]

theorem quadraticRow_primary_tsum_decomposition {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : {I : Ideal O // I ≠ 0},
      quadraticRow P hg S (primaryGenerator I.val) * W ((Ideal.absNorm I.val : ℝ) / X)) =
    ∑' p : {A : Ideal O // A ≠ 0} × {D : Ideal O // Squarefree D},
      rowCoprimeMask P S (primaryGenerator p.1.val) *
      quadraticRow P hg S (primaryGenerator p.2.val) *
      W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * Ideal.absNorm p.2.val) / X) := by
  rw [squarefree_decomposition_tsum (fun I =>
    quadraticRow P hg S (primaryGenerator I) * W ((Ideal.absNorm I : ℝ) / X))]
  apply tsum_congr
  intro p
  have hpow : primaryGenerator (p.1.val ^ 2) = primaryGenerator p.1.val ^ 2 :=
    map_pow primaryGeneratorHom _ _
  simp only [primaryGenerator_mul, hpow, quadraticRow_mul, quadraticRow_square,
    map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

end QuadraticSquarefreeKernel
end

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
abbrev O := ActualEisensteinCubic.O
open QuadraticSquarefreeKernel

def cutoffDifference (K : ℝ) (H D : Ideal O) : ℝ :=
  (if (Ideal.absNorm (H * D) : ℝ) ≤ K then 1 else 0) -
    (if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0)

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

theorem cutoffDifference_nonzero_iff (K : ℝ) (H D : Ideal O) (hD : D ≠ 0) :
    cutoffDifference K H D ≠ 0 ↔
      (Ideal.absNorm H : ℝ) ≤ K ∧ K < (Ideal.absNorm (H * D) : ℝ) := by
  have hmono : (Ideal.absNorm H : ℝ) ≤ Ideal.absNorm (H * D) := by
    rw [map_mul, Nat.cast_mul]
    nlinarith [norm_one_le hD, Nat.cast_nonneg (α := ℝ) (Ideal.absNorm H)]
  unfold cutoffDifference
  split_ifs <;> simp_all ; linarith

theorem cutoffDifference_eq_neg_one_of_nonzero (K : ℝ) (H D : Ideal O) (hD : D ≠ 0)
    (h : cutoffDifference K H D ≠ 0) : cutoffDifference K H D = -1 := by
  obtain ⟨hH, hHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  simp only [cutoffDifference, ite_eq_right (not_le.mpr hHD), ite_eq_left hH]
  norm_num

theorem squarePart_dvd {G H D E : Ideal O} (hG : G ≠ 0) (hH : Squarefree H)
    (hDG : D ∣ G) (hEG : E ∣ G) : squarePart (H * D * E) ∣ G := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarePart_ne_zero hB) hG).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have hfac := congrArg normalizedFactors (squarePart_sq_mul_squarefreePart (H * D * E))
  rw [normalizedFactors_mul (pow_ne_zero _ (squarePart_ne_zero hB))
    (squarefree_squarefreePart _).ne_zero, normalizedFactors_pow,
    normalizedFactors_mul (mul_ne_zero hH.ne_zero hD) hE,
    normalizedFactors_mul hH.ne_zero hD] at hfac
  have hcnt := congrArg (Multiset.count P) hfac
  simp only [Multiset.count_add, Multiset.count_nsmul] at hcnt
  have hd := (dvd_iff_normalizedFactors_le_normalizedFactors hD hG).mp hDG
  have he := (dvd_iff_normalizedFactors_le_normalizedFactors hE hG).mp hEG
  have hdc := Multiset.count_le_of_le P hd
  have hec := Multiset.count_le_of_le P he
  have hhc := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hH.ne_zero).mp hH) P
  omega

theorem cutoffDifference_eq_zero_of_product_le (K : ℝ) {H D E : Ideal O}
    (hD : D ≠ 0) (hE : E ≠ 0)
    (hB : (Ideal.absNorm (H * D * E) : ℝ) ≤ K) : cutoffDifference K H D = 0 := by
  by_contra h
  have hh := (cutoffDifference_nonzero_iff K H D hD).mp h
  have he := norm_one_le hE
  rw [map_mul, Nat.cast_mul] at hB
  have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
  nlinarith

theorem main_boundary_localization (K : ℝ) {G H D E : Ideal O}
    (hG : G ≠ 0) (hH : Squarefree H) (hDG : D ∣ G) (hEG : E ∣ G)
    (h : cutoffDifference K H D ≠ 0) :
    K < (Ideal.absNorm (H * D * E) : ℝ) ∧
    (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 ∧
    squarePart (H * D * E) ∣ G ∧
    K / (Ideal.absNorm G : ℝ) ^ 2 < (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ∧
    (Ideal.absNorm (squarefreePart (H * D * E)) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
  have hD := ne_zero_of_dvd_ne_zero hG hDG
  have hE := ne_zero_of_dvd_ne_zero hG hEG
  have hB0 : H * D * E ≠ 0 := mul_ne_zero (mul_ne_zero hH.ne_zero hD) hE
  obtain ⟨hHK, hKHD⟩ := (cutoffDifference_nonzero_iff K H D hD).mp h
  have hHpos := norm_pos hH.ne_zero
  have hDpos := norm_pos hD
  have hEpos := norm_pos hE
  have hGone := norm_one_le hG
  have hEone := norm_one_le hE
  have hDle := norm_le_of_dvd hG hDG
  have hEle := norm_le_of_dvd hG hEG
  have hK : 0 ≤ K := le_trans hHpos.le hHK
  have hBlo : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    rw [map_mul, Nat.cast_mul]
    have hp := Nat.cast_nonneg (Ideal.absNorm (H * D)) (α := ℝ)
    nlinarith
  have hBhi : (Ideal.absNorm (H * D * E) : ℝ) ≤ K * (Ideal.absNorm G : ℝ) ^ 2 := by
    simp only [map_mul, Nat.cast_mul]
    calc
      (Ideal.absNorm H : ℝ) * Ideal.absNorm D * Ideal.absNorm E ≤
        K * Ideal.absNorm G * Ideal.absNorm G :=
        mul_le_mul (mul_le_mul hHK hDle hDpos.le hK) hEle hEpos.le (by positivity)
      _ = _ := by ring
  have hroot := squarePart_dvd hG hH hDG hEG
  have hrootle := norm_le_of_dvd hG hroot
  have hrootone := norm_one_le (squarePart_ne_zero hB0)
  have hkerpos := norm_pos (squarefree_squarefreePart (H * D * E)).ne_zero
  have hdecomp : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 *
      Ideal.absNorm (squarefreePart (H * D * E)) = Ideal.absNorm (H * D * E) := by
    exact_mod_cast norm_decomposition (H * D * E)
  have hrootpow : (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 ≤
      (Ideal.absNorm G : ℝ) ^ 2 := pow_le_pow_left₀ (le_trans zero_le_one hrootone) hrootle 2
  refine ⟨hBlo, hBhi, hroot, ?_, ?_⟩
  · apply (div_lt_iff₀ (by positivity : 0 < (Ideal.absNorm G : ℝ) ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hrootpow hkerpos.le]
  · have hrpow : 1 ≤ (Ideal.absNorm (squarePart (H * D * E)) : ℝ) ^ 2 := by nlinarith
    nlinarith

theorem cutoffDifference_of_common_one (K : ℝ) {H D : Ideal O} (hD : D ∣ 1) :
    cutoffDifference K H D = 0 := by
  have hD1 : D = 1 := associated_iff_eq.mp (associated_one_iff_isUnit.mpr (isUnit_of_dvd_one hD))
  simp [cutoffDifference, hD1]

end QuadraticMainBoundary

open scoped BigOperators Classical
namespace QuadraticDivisorCancellation
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound QuadraticSquarefreeKernel

def normalizedRow {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) : ℂ :=
  quadraticRow P hg S z / (‖eisEmbedding z‖ : ℂ)

theorem normalizedRow_mul {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    normalizedRow P hg S (a * b) = normalizedRow P hg S a * normalizedRow P hg S b := by
  simp only [normalizedRow, quadraticRow_mul, map_mul, norm_mul, Complex.ofReal_mul,
    div_mul_div_comm]

theorem normalizedRow_one {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : normalizedRow P hg S 1 = 1 := by
  simp [normalizedRow, quadraticRow, finiteSquarefreeRow]

def normalizedRowHom {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) : O →* ℂ where
  toFun := normalizedRow P hg S
  map_one' := normalizedRow_one P hg S
  map_mul' := normalizedRow_mul P hg S

theorem normalizedRow_prod {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (q : κ → O) (T : Finset κ) :
    normalizedRow P hg S (∏ i ∈ T, q i) = ∏ i ∈ T, normalizedRow P hg S (q i) :=
  map_prod (normalizedRowHom P hg S) q T

theorem normalizedRow_sq {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (z : O) :
    normalizedRow P hg S z ^ 2 = rowCoprimeMask P S z /
      (Ideal.absNorm (Ideal.span {z}) : ℂ) := by
  have hrow : quadraticRow P hg S z ^ 2 = rowCoprimeMask P S z := by
    simpa only [pow_two, quadraticRow_mul] using quadraticRow_square P hg S z
  have hn : (‖eisEmbedding z‖ : ℂ) ^ 2 = (Ideal.absNorm (Ideal.span {z}) : ℂ) := by
    exact_mod_cast eisEmbedding_norm_sq_eq_absNorm_span z
  rw [normalizedRow, div_pow, hrow, hn]

theorem double_divisor_factorization {κ : Type*} [DecidableEq κ]
    (z : κ → ℂ) (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (-1 : ℂ) ^ E.card * (∏ i ∈ D, z i) * ∏ i ∈ E, z i) =
    (∏ i ∈ T, (1 - z i ^ 2)) *
      ∑ E ∈ U.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i := by
  have hm (V : Finset κ) :
      (∑ E ∈ V.powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) =
      ∏ i ∈ V, (1 - z i) := by
    rw [Finset.prod_sub]
    simp only [Finset.prod_const_one, mul_one]
  calc
    _ = (∑ D ∈ T.powerset, ∏ i ∈ D, z i) *
        (∑ E ∈ (T ∪ U).powerset, (-1 : ℂ) ^ E.card * ∏ i ∈ E, z i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = (∏ i ∈ T, (1 + z i)) * ((∏ i ∈ T, (1 - z i)) * ∏ i ∈ U, (1 - z i)) := by
      rw [← Finset.prod_one_add, hm, Finset.prod_union hTU]
    _ = (∏ i ∈ T, (1 - z i ^ 2)) * ∏ i ∈ U, (1 - z i) := by
      rw [← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by rw [hm]

theorem actual_double_divisor_cancellation {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T U : Finset κ) (hTU : Disjoint T U) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ D, q i) * ∏ i ∈ E, q i)) =
    (∏ i ∈ T, (1 - rowCoprimeMask P S (q i) /
        (Ideal.absNorm (Ideal.span {q i}) : ℂ))) *
      ∑ E ∈ U.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
          normalizedRow P hg S (∏ i ∈ E, q i) := by
  simp only [prime_product_moebius (fun i => Ideal.span {q i}) hprime hinj,
    normalizedRow_mul, normalizedRow_prod, ← mul_assoc]
  have h := double_divisor_factorization (normalizedRow P hg S ∘ q) T U hTU
  simpa only [Function.comp_apply, normalizedRow_sq] using h

theorem actual_double_divisor_cancellation_coprime {ι κ : Type*} [DecidableEq κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
    (q : κ → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hprime : ∀ i, Prime (Ideal.span {q i}))
    (hinj : Function.Injective (fun i => (Ideal.span {q i} : Ideal O)))
    (T U : Finset κ) (hTU : Disjoint T U)
    (havoid : ∀ i ∈ T, ∀ j ∈ S, q i ∉ P j) :
    (∑ D ∈ T.powerset, ∑ E ∈ (T ∪ U).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
        normalizedRow P hg S ((∏ i ∈ D, q i) * ∏ i ∈ E, q i)) =
    (∏ i ∈ T, (1 - (1 : ℂ) / (Ideal.absNorm (Ideal.span {q i}) : ℂ))) *
      ∑ E ∈ U.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {q i}) : ℂ) *
          normalizedRow P hg S (∏ i ∈ E, q i) := by
  rw [actual_double_divisor_cancellation P hg S q hprime hinj T U hTU]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hm : rowCoprimeMask P S (q i) = 1 := by
    simp only [rowCoprimeMask]
    rw [ite_eq_right]
    push Not
    exact havoid i hi
  rw [hm]

end QuadraticDivisorCancellation

end

end OAI
