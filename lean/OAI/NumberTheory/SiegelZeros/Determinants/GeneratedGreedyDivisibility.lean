import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.NumberField.Norm
import OAI.NumberTheory.SiegelZeros.Differentials.DerivativeMatrix
import OAI.NumberTheory.SiegelZeros.Selection.OrderedGreedyRows
import OAI.NumberTheory.SiegelZeros.Structure.ConcreteArchimedean
import OAI.NumberTheory.SiegelZeros.Structure.ThetaJetBridge

namespace OAI

namespace SiegelZeros

section

open scoped BigOperators NumberField

namespace SiegelZerosAwei.W37

variable {K : Type*} [Field K]

def thetaIntegral (u : Fin 4 → 𝓞 K) (n : Fin 4 → ℕ) : 𝓞 K :=
  ∑ i, (n i : 𝓞 K) * u i

def thetaField (u : Fin 4 → 𝓞 K) (n : Fin 4 → ℕ) : K :=
  ∑ i, (n i : K) * (u i : K)

theorem coe_thetaIntegral (u : Fin 4 → 𝓞 K) (n : Fin 4 → ℕ) :
    (thetaIntegral u n : K) = thetaField u n := by
  simp [thetaIntegral, thetaField, NumberField.RingOfIntegers.coe_eq_algebraMap]

theorem thetaField_isIntegral (u : Fin 4 → 𝓞 K) (n : Fin 4 → ℕ) :
    IsIntegral ℤ (thetaField u n) := by
  rw [← coe_thetaIntegral]
  exact (thetaIntegral u n).2

def rowIntegral (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (alpha : Fin 3 → ℕ) (n : Fin 4 → ℕ) : 𝓞 K :=
  thetaIntegral u n ^ alpha 0 *
    NumberField.RingOfIntegers.mapRingHom sigma (thetaIntegral u n) ^ alpha 1 *
    NumberField.RingOfIntegers.mapRingHom sigmaTau (thetaIntegral u n) ^ alpha 2

def rowField (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (alpha : Fin 3 → ℕ) (n : Fin 4 → ℕ) : K :=
  thetaField u n ^ alpha 0 * sigma (thetaField u n) ^ alpha 1 *
    sigmaTau (thetaField u n) ^ alpha 2

theorem coe_rowIntegral (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (alpha : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    (rowIntegral u sigma sigmaTau alpha n : K) = rowField u sigma sigmaTau alpha n := by
  simp only [rowIntegral, map_mul, map_pow]
  change (thetaIntegral u n : K) ^ alpha 0 * sigma (thetaIntegral u n : K) ^ alpha 1 *
    sigmaTau (thetaIntegral u n : K) ^ alpha 2 = _
  rw [coe_thetaIntegral]
  rfl

theorem rowField_isIntegral (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (alpha : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    IsIntegral ℤ (rowField u sigma sigmaTau alpha n) := by
  rw [← coe_rowIntegral]
  exact (rowIntegral u sigma sigmaTau alpha n).2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def deltaIntegral (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (rows : ι → Fin 3 → ℕ) (columns : ι → Fin 4 → ℕ) : 𝓞 K :=
  Matrix.det (fun i j => rowIntegral u sigma sigmaTau (rows i) (columns j))

noncomputable def deltaField (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (rows : ι → Fin 3 → ℕ) (columns : ι → Fin 4 → ℕ) : K :=
  Matrix.det (fun i j => rowField u sigma sigmaTau (rows i) (columns j))

theorem coe_deltaIntegral (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (rows : ι → Fin 3 → ℕ) (columns : ι → Fin 4 → ℕ) :
    (deltaIntegral u sigma sigmaTau rows columns : K) =
      deltaField u sigma sigmaTau rows columns := by
  unfold deltaIntegral deltaField
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
  erw [RingHom.map_det]
  congr 1

theorem deltaField_isIntegral (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (rows : ι → Fin 3 → ℕ) (columns : ι → Fin 4 → ℕ) :
    IsIntegral ℤ (deltaField u sigma sigmaTau rows columns) := by
  rw [← coe_deltaIntegral]
  exact (deltaIntegral u sigma sigmaTau rows columns).2

variable [NumberField K]

theorem norm_nonzero_integer (x : 𝓞 K) (hx : (x : K) ≠ 0) :
    ∃ z : ℤ, z ≠ 0 ∧ (z : ℚ) = Algebra.norm ℚ (x : K) := by
  refine ⟨Algebra.norm ℤ x, ?_, Algebra.coe_norm_int x⟩
  intro hz
  have hnorm : Algebra.norm ℚ (x : K) = 0 := by
    rw [← Algebra.coe_norm_int x, hz, Int.cast_zero]
  exact hx (Algebra.norm_eq_zero_iff.mp hnorm)

theorem delta_norm_nonzero_integer (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (rows : ι → Fin 3 → ℕ) (columns : ι → Fin 4 → ℕ)
    (hdelta : deltaField u sigma sigmaTau rows columns ≠ 0) :
    ∃ z : ℤ, z ≠ 0 ∧ (z : ℚ) =
      Algebra.norm ℚ (deltaField u sigma sigmaTau rows columns) := by
  have h := norm_nonzero_integer (deltaIntegral u sigma sigmaTau rows columns)
    (by rwa [coe_deltaIntegral])
  simpa only [coe_deltaIntegral] using h

theorem integer_norm_natCast (p : ℕ) :
    Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℚ K := by
  have hnorm : Algebra.norm ℚ ((p : 𝓞 K) : K) =
      (p : ℚ) ^ Module.finrank ℚ K := by
    simpa [NumberField.RingOfIntegers.coe_eq_algebraMap] using
      (Algebra.norm_algebraMap (S := K) (p : ℚ))
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_pow, Int.cast_natCast] using
    (Algebra.coe_norm_int (p : 𝓞 K)).trans hnorm

theorem norm_dvd_of_pow_dvd (p e : ℕ) (x : 𝓞 K)
    (hdiv : (p : 𝓞 K) ^ e ∣ x) :
    (p : ℤ) ^ (Module.finrank ℚ K * e) ∣ Algebra.norm ℤ x := by
  obtain ⟨y, hy⟩ := hdiv
  refine ⟨Algebra.norm ℤ y, ?_⟩
  rw [hy, map_mul, map_pow, integer_norm_natCast, ← pow_mul]

theorem norm_dvd_of_pow_dvd_degree_four (hdegree : Module.finrank ℚ K = 4)
    (p e : ℕ) (x : 𝓞 K) (hdiv : (p : 𝓞 K) ^ e ∣ x) :
    (p : ℤ) ^ (4 * e) ∣ Algebra.norm ℤ x := by
  simpa only [hdegree] using norm_dvd_of_pow_dvd p e x hdiv

end SiegelZerosAwei.W37

end

section

open scoped NumberField BigOperators

namespace SiegelZerosAwei.W37

variable {K : Type*} [Field K]

def automorphismDirections (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K) :
    Fin 3 → Fin 4 → K :=
  ![fun i => (u i : K), fun i => sigma (u i), fun i => sigmaTau (u i)]

theorem coe_rowIntegral_eq_derivativeMatrix
    {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (exponents : ι → Fin 4 →₀ ℕ) (orders : ρ → Fin 3 → ℕ) (r : ρ) (c : ι) :
    (rowIntegral u sigma sigmaTau (orders r) (fun i => exponents c i) : K) =
      WeightedTorusJets.W28.derivativeMatrix
        (automorphismDirections u sigma sigmaTau) exponents orders r c := by
  rw [coe_rowIntegral]
  simp [rowField, thetaField, WeightedTorusJets.W28.derivativeMatrix,
    automorphismDirections, WeightedTorusJets.W18.eigenvalue, map_sum, mul_comm]

theorem coe_deltaIntegral_eq_derivativeMatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Fin 4 → 𝓞 K) (sigma sigmaTau : K →+* K)
    (exponents : ι → Fin 4 →₀ ℕ) (orders : ι → Fin 3 → ℕ) :
    (deltaIntegral u sigma sigmaTau orders (fun c i => exponents c i) : K) =
      (WeightedTorusJets.W28.derivativeMatrix
        (automorphismDirections u sigma sigmaTau) exponents orders).det := by
  unfold deltaIntegral
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
  erw [RingHom.map_det]
  congr 1
  funext r c
  exact coe_rowIntegral_eq_derivativeMatrix u sigma sigmaTau exponents orders r c

variable [CharZero K] [Algebra ℚ K]

def adjoinIntegralGenerators (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    Fin 4 → 𝓞 (SiegelZeros.W10.rootField a b) :=
  fun i => ⟨SiegelZeros.W10.adjoinGenerators a b i,
    SiegelZeros.W10.adjoinGenerators_isIntegral a b d ha hb i⟩

omit [CharZero K] in
@[simp] theorem coe_adjoinIntegralGenerators (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (i : Fin 4) :
    (adjoinIntegralGenerators a b d ha hb i : SiegelZeros.W10.rootField a b) =
      SiegelZeros.W10.adjoinGenerators a b i := rfl

noncomputable def actualSigma (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    SiegelZeros.W10.rootField a b →+* SiegelZeros.W10.rootField a b :=
  (WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb true false).toRingHom

noncomputable def actualSigmaTau (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    SiegelZeros.W10.rootField a b →+* SiegelZeros.W10.rootField a b :=
  (WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb true true).toRingHom

noncomputable def concreteDirections (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    Fin 3 → Fin 4 → SiegelZeros.W10.rootField a b :=
  automorphismDirections (adjoinIntegralGenerators a b d ha hb)
    (actualSigma a b d hd hd1 hd2 ha hb) (actualSigmaTau a b d hd hd1 hd2 ha hb)

noncomputable def concreteDelta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (exponents : ι → Fin 4 →₀ ℕ) (orders : ι → Fin 3 → ℕ) :
    𝓞 (SiegelZeros.W10.rootField a b) :=
  deltaIntegral (adjoinIntegralGenerators a b d ha hb)
    (actualSigma a b d hd hd1 hd2 ha hb) (actualSigmaTau a b d hd hd1 hd2 ha hb)
    orders (fun c i => exponents c i)

theorem coe_concreteDelta {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (exponents : ι → Fin 4 →₀ ℕ) (orders : ι → Fin 3 → ℕ) :
    (concreteDelta a b d hd hd1 hd2 ha hb exponents orders :
        SiegelZeros.W10.rootField a b) =
      (WeightedTorusJets.W28.derivativeMatrix
        (concreteDirections a b d hd hd1 hd2 ha hb) exponents orders).det :=
  coe_deltaIntegral_eq_derivativeMatrix_det _ _ _ _ _

theorem concreteDelta_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (exponents : ι → Fin 4 →₀ ℕ) (orders : ι → Fin 3 → ℕ)
    (hdet : (WeightedTorusJets.W28.derivativeMatrix
      (concreteDirections a b d hd hd1 hd2 ha hb) exponents orders).det ≠ 0) :
    concreteDelta a b d hd hd1 hd2 ha hb exponents orders ≠ 0 := by
  intro h
  apply hdet
  rw [← coe_concreteDelta, h]
  exact map_zero (algebraMap _ _)

end SiegelZerosAwei.W37

end


namespace SiegelZerosAwei.W37

open scoped NumberField BigOperators
variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

def integralRootA (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    𝓞 (SiegelZeros.W10.rootField a b) := adjoinIntegralGenerators a b d ha hb 1

def integralRootB (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    𝓞 (SiegelZeros.W10.rootField a b) := adjoinIntegralGenerators a b d ha hb 2

omit [CharZero K] in
theorem integralRootA_sq (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    integralRootA a b d ha hb ^ 2 = (d : 𝓞 (SiegelZeros.W10.rootField a b)) := by
  apply NumberField.RingOfIntegers.ext
  apply Subtype.ext
  change a ^ 2 = (d : K)
  exact ha

omit [CharZero K] in
theorem integralRootB_sq (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    integralRootB a b d ha hb ^ 2 = 2 := by
  apply NumberField.RingOfIntegers.ext
  apply Subtype.ext
  change b ^ 2 = (2 : K)
  exact hb

omit [CharZero K] in
theorem adjoinIntegralGenerators_eq (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    adjoinIntegralGenerators a b d ha hb =
      ![1, integralRootA a b d ha hb, integralRootB a b d ha hb,
        integralRootA a b d ha hb * integralRootB a b d ha hb] := by
  funext i
  fin_cases i <;> rfl

omit [CharZero K] in
theorem thetaIntegral_eq_coordinateTheta (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) (n : Fin 4 → ℕ) :
    thetaIntegral (adjoinIntegralGenerators a b d ha hb) n =
      Awei.W39.theta (integralRootA a b d ha hb) (integralRootB a b d ha hb)
        (fun i => (n i : ℤ)) := by
  unfold thetaIntegral
  rw [adjoinIntegralGenerators_eq]
  simp [Awei.W39.theta, Fin.sum_univ_succ]
  ring

theorem integralSigma_rootA (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    NumberField.RingOfIntegers.mapRingHom (actualSigma a b d hd hd1 hd2 ha hb)
      (integralRootA a b d ha hb) = -integralRootA a b d ha hb := by
  apply NumberField.RingOfIntegers.ext
  change WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb
    true false (SiegelZeros.W10.adjoinGenerators a b 1) =
      -SiegelZeros.W10.adjoinGenerators a b 1
  exact WeightedTorusJets.W11.squarefreeSigma_a a b d hd hd1 hd2 ha hb

theorem integralSigma_rootB (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    NumberField.RingOfIntegers.mapRingHom (actualSigma a b d hd hd1 hd2 ha hb)
      (integralRootB a b d ha hb) = integralRootB a b d ha hb := by
  apply NumberField.RingOfIntegers.ext
  change WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb
    true false (SiegelZeros.W10.adjoinGenerators a b 2) =
      SiegelZeros.W10.adjoinGenerators a b 2
  exact WeightedTorusJets.W11.squarefreeSigma_b a b d hd hd1 hd2 ha hb

theorem integralSigmaTau_rootA (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    NumberField.RingOfIntegers.mapRingHom (actualSigmaTau a b d hd hd1 hd2 ha hb)
      (integralRootA a b d ha hb) = -integralRootA a b d ha hb := by
  apply NumberField.RingOfIntegers.ext
  change WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb
    true true (SiegelZeros.W10.adjoinGenerators a b 1) =
      -SiegelZeros.W10.adjoinGenerators a b 1
  exact WeightedTorusJets.W11.squarefreeSigmaTau_a a b d hd hd1 hd2 ha hb

theorem integralSigmaTau_rootB (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    NumberField.RingOfIntegers.mapRingHom (actualSigmaTau a b d hd hd1 hd2 ha hb)
      (integralRootB a b d ha hb) = -integralRootB a b d ha hb := by
  apply NumberField.RingOfIntegers.ext
  change WeightedTorusJets.W11.squarefreeFieldSignAction a b d hd hd1 hd2 ha hb
    true true (SiegelZeros.W10.adjoinGenerators a b 2) =
      -SiegelZeros.W10.adjoinGenerators a b 2
  exact WeightedTorusJets.W11.squarefreeSigmaTau_b a b d hd hd1 hd2 ha hb

theorem rowIntegral_eq_coordinateRow (a b : K) (d : ℤ)
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (orders : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    rowIntegral (adjoinIntegralGenerators a b d ha hb)
      (actualSigma a b d hd hd1 hd2 ha hb) (actualSigmaTau a b d hd hd1 hd2 ha hb)
      orders n =
      WeightedTorusJets.W40.rowEntry
        (Awei.W39.theta (integralRootA a b d ha hb) (integralRootB a b d ha hb)
          (fun j => (n j : ℤ)))
        (Awei.W39.theta (-integralRootA a b d ha hb) (integralRootB a b d ha hb)
          (fun j => (n j : ℤ)))
        (Awei.W39.theta (-integralRootA a b d ha hb) (-integralRootB a b d ha hb)
          (fun j => (n j : ℤ))) (orders 0) (orders 1) (orders 2) := by
  simp only [rowIntegral, thetaIntegral_eq_coordinateTheta, W60.map_theta,
    integralSigma_rootA, integralSigma_rootB, integralSigmaTau_rootA,
    integralSigmaTau_rootB, WeightedTorusJets.W40.rowEntry]

theorem concreteDelta_eq_coordinateRows_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (exponents : ι → Fin 4 →₀ ℕ) (orders : ι → Fin 3 → ℕ) :
    concreteDelta a b d hd hd1 hd2 ha hb exponents orders =
      (W60.rows
        (fun j => Awei.W39.theta (integralRootA a b d ha hb) (integralRootB a b d ha hb)
          (fun k => (exponents j k : ℤ)))
        (fun j => Awei.W39.theta (-integralRootA a b d ha hb) (integralRootB a b d ha hb)
          (fun k => (exponents j k : ℤ)))
        (fun j => Awei.W39.theta (-integralRootA a b d ha hb) (-integralRootB a b d ha hb)
          (fun k => (exponents j k : ℤ)))
        (fun i => orders i 0) (fun i => orders i 1) (fun i => orders i 2)).det := by
  unfold concreteDelta deltaIntegral
  congr 1
  funext i j
  exact rowIntegral_eq_coordinateRow a b d hd hd1 hd2 ha hb (orders i)
    (fun k => exponents j k)

end SiegelZerosAwei.W37



namespace SiegelZerosAwei.W60

open scoped BigOperators NumberField
open WeightedTorusJets

variable {R K : Type*} [CommRing R] [Field K] {M H : ℕ}

def weightedRow (f : R →+* K) (x y z : Fin M → R) (a : W62.Index H) : Fin M → K :=
  fun j => W40.rowEntry (f (x j)) (f (y j)) (f (z j))
    (a.coords 0) (a.coords 1) (a.coords 2)

noncomputable def greedySet (f : R →+* K) (H C : ℕ) (x y z : Fin M → R) :
    Finset (W62.Index H) :=
  W62.selected (K := K) H C (weightedRow (H := H) f x y z)

noncomputable def greedyIndex (f : R →+* K) (H C : ℕ) (x y z : Fin M → R)
    (hcard : (greedySet f H C x y z).card = M) : Fin M ↪o W62.Index H :=
  W62.orderedSelected (K := K) (H := H) (C := C) (M := M)
    (weightedRow (H := H) f x y z) hcard

theorem greedy_card_of_spanning (f : R →+* K) (H C : ℕ) (x y z : Fin M → R)
    (hspan : W29.rowSpan (K := K) (weightedRow f x y z) (W62.cutoff H C) = ⊤) :
    (greedySet f H C x y z).card = M := by
  change (W62.selected (K := K) H C (weightedRow (H := H) f x y z)).card = M
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    (W62.selected_card_of_spanning (K := K) H C
      (weightedRow (H := H) f x y z) hspan)

theorem greedy_earlierSpan (f : R →+* K) (H C : ℕ) (hH : 0 < H)
    (x y z : Fin M → R) (hcard : (greedySet f H C x y z).card = M) :
    EarlierSpan f H x y z
      (fun i => (greedyIndex f H C x y z hcard i).coords 0)
      (fun i => (greedyIndex f H C x y z hcard i).coords 1)
      (fun i => (greedyIndex f H C x y z hcard i).coords 2) := by
  intro i a b c hw
  let candidate : W62.Index H := ⟨![a, b, c]⟩
  let idx := greedyIndex f H C x y z hcard
  have hweight : W62.weight candidate < W62.weight (idx i) := by
    simpa only [candidate, W62.weight, W40.weight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using hw
  have hv' := W62.lower_weight_ordered_span (K := K) (H := H) (C := C) (M := M)
    hH (weightedRow (H := H) f x y z) hcard i candidate hweight
  have hmatrix :
      (rows x y z (fun j => (idx j).coords 0) (fun j => (idx j).coords 1)
        (fun j => (idx j).coords 2)).map f =
      fun j => weightedRow f x y z (idx j) := by
    ext j k
    change f (x k ^ (idx j).coords 0 * y k ^ (idx j).coords 1 *
      z k ^ (idx j).coords 2) =
      f (x k) ^ (idx j).coords 0 * f (y k) ^ (idx j).coords 1 *
        f (z k) ^ (idx j).coords 2
    simp only [map_mul, map_pow]
  have hset : (↑(Finset.univ.filter fun j : Fin M => j < i) : Set (Fin M)) =
      Set.Iio i := by ext j; simp
  change weightedRow f x y z candidate ∈ Submodule.span K
    (((rows x y z (fun j => (idx j).coords 0) (fun j => (idx j).coords 1)
      (fun j => (idx j).coords 2)).map f) ''
      (↑(Finset.univ.filter fun j : Fin M => j < i) : Set (Fin M)))
  rw [hmatrix, hset]
  exact hv'

theorem greedy_det_ne_zero (f : R →+* K) (_hf : Function.Injective f)
    (H C : ℕ) (x y z : Fin M → R)
    (hcard : (greedySet f H C x y z).card = M) :
    (rows x y z
      (fun i => (greedyIndex f H C x y z hcard i).coords 0)
      (fun i => (greedyIndex f H C x y z hcard i).coords 1)
      (fun i => (greedyIndex f H C x y z hcard i).coords 2)).det ≠ 0 := by
  let idx := greedyIndex f H C x y z hcard
  have hlin : LinearIndepOn K (weightedRow (H := H) f x y z)
      (greedySet f H C x y z : Set (W62.Index H)) :=
    W62.selected_independent (K := K) H C (weightedRow (H := H) f x y z)
  have hdet : Matrix.det (fun i j => weightedRow f x y z (idx i) j) ≠ 0 :=
    W30.ordered_rows_det_ne_zero (K := K) (weightedRow (H := H) f x y z)
      (greedySet f H C x y z) hcard hlin
  have hmatrix :
      (rows x y z (fun i => (idx i).coords 0) (fun i => (idx i).coords 1)
        (fun i => (idx i).coords 2)).map f =
      fun i j => weightedRow f x y z (idx i) j := by
    ext i j
    change f (x j ^ (idx i).coords 0 * y j ^ (idx i).coords 1 *
      z j ^ (idx i).coords 2) =
      f (x j) ^ (idx i).coords 0 * f (y j) ^ (idx i).coords 1 *
        f (z j) ^ (idx i).coords 2
    simp only [map_mul, map_pow]
  intro hz
  apply hdet
  rw [← hmatrix]
  change Matrix.det (f.mapMatrix
    (rows x y z (fun i => (idx i).coords 0) (fun i => (idx i).coords 1)
      (fun i => (idx i).coords 2))) = 0
  rw [← f.map_det, hz, map_zero]

theorem greedy_determinant_dvd (f : R →+* K) (hf : Function.Injective f)
    (H C p : ℕ) (hH : 0 < H) (hpH : H < p) (x y z : Fin M → R)
    (hcard : (greedySet f H C x y z).card = M)
    (hfrob : (∀ j, (p : R) ∣ x j ^ p - y j) ∨
      (∀ j, (p : R) ∣ x j ^ p - z j)) :
    (p : R) ^ (∑ i, (greedyIndex f H C x y z hcard i).coords 0 / p) ∣
      (rows x y z
        (fun i => (greedyIndex f H C x y z hcard i).coords 0)
        (fun i => (greedyIndex f H C x y z hcard i).coords 1)
        (fun i => (greedyIndex f H C x y z hcard i).coords 2)).det :=
  determinant_dvd_either f hf H p hpH x y z _ _ _
    (greedy_earlierSpan f H C hH x y z hcard) hfrob

theorem greedy_theta_determinant_dvd (f : R →+* K) (hf : Function.Injective f)
    (H C p : ℕ) [Fact p.Prime] (hH : 0 < H) (hpH : H < p) (hp2 : p ≠ 2)
    (u v : R) (d : ℤ) (hu : u ^ 2 = (d : R)) (hv : v ^ 2 = 2)
    (hd : legendreSym p d = -1) (n : Fin M → Fin 4 → ℤ)
    (hcard : (greedySet f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j))).card = M) :
    let idx := greedyIndex f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)) hcard
    (p : R) ^ (∑ i, (idx i).coords 0 / p) ∣
      (rows (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j))
        (fun i => (idx i).coords 0) (fun i => (idx i).coords 1)
        (fun i => (idx i).coords 2)).det := by
  dsimp only
  apply theta_determinant_dvd f hf H p hpH hp2 u v d hu hv hd n
  exact greedy_earlierSpan f H C hH _ _ _ hcard

theorem exists_greedy_theta_divisibility (f : R →+* K) (hf : Function.Injective f)
    (H C : ℕ) (hH : 0 < H) (u v : R) (d : ℤ)
    (hu : u ^ 2 = (d : R)) (hv : v ^ 2 = 2) (n : Fin M → Fin 4 → ℤ)
    (hspan : W29.rowSpan (K := K)
      (weightedRow f (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j))) (W62.cutoff H C) = ⊤) :
    ∃ hcard : (greedySet f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j))).card = M,
    let idx := greedyIndex f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)) hcard
    let Δ := (rows (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j))
      (fun i => (idx i).coords 0) (fun i => (idx i).coords 1)
      (fun i => (idx i).coords 2)).det
    Δ ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime), H < p → p ≠ 2 → @legendreSym p ⟨hp⟩ d = -1 →
      (p : R) ^ (∑ i, (idx i).coords 0 / p) ∣ Δ := by
  let hcard := greedy_card_of_spanning f H C _ _ _ hspan
  refine ⟨hcard, ?_⟩
  dsimp only
  constructor
  · exact greedy_det_ne_zero f hf H C _ _ _ hcard
  · intro p hp hpH hp2 hd
    let : Fact p.Prime := ⟨hp⟩
    exact greedy_theta_determinant_dvd f hf H C p hH hpH hp2 u v d hu hv hd n hcard

end SiegelZerosAwei.W60



namespace SiegelZerosAwei.W60

open scoped BigOperators NumberField
open WeightedTorusJets

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]

def generatedRootA (a b : K) (d : ℤ) (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    𝓞 (SiegelZeros.W10.rootField a b) := W37.integralRootA a b d ha hb

def generatedRootB (a b : K) (d : ℤ) (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    𝓞 (SiegelZeros.W10.rootField a b) := W37.integralRootB a b d ha hb

omit [CharZero K] in
@[simp] theorem generatedRootA_sq (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    generatedRootA a b d ha hb ^ 2 = (d : 𝓞 (SiegelZeros.W10.rootField a b)) := W37.integralRootA_sq a b d ha hb

omit [CharZero K] in
@[simp] theorem generatedRootB_sq (a b : K) (d : ℤ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2) :
    generatedRootB a b d ha hb ^ 2 = (2 : 𝓞 (SiegelZeros.W10.rootField a b)) := W37.integralRootB_sq a b d ha hb

omit [CharZero K] in
theorem exists_generated_greedy_divisibility {M : ℕ}
    (a b : K) (d : ℤ) (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (H C : ℕ) (hH : 0 < H) (n : Fin M → Fin 4 → ℤ) :
    let L := SiegelZeros.W10.rootField a b
    let f := algebraMap (𝓞 L) L
    let u := generatedRootA a b d ha hb
    let v := generatedRootB a b d ha hb
    W29.rowSpan (K := L)
      (weightedRow f (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j))) (W62.cutoff H C) = ⊤ →
    ∃ hcard : (greedySet f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j))).card = M,
    let idx := greedyIndex f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)) hcard
    let Δ := (rows (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j))
      (fun i => (idx i).coords 0) (fun i => (idx i).coords 1)
      (fun i => (idx i).coords 2)).det
    Δ ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime), H < p → p ≠ 2 → @legendreSym p ⟨hp⟩ d = -1 →
      (p : 𝓞 L) ^ (∑ i, (idx i).coords 0 / p) ∣ Δ := by
  dsimp only
  intro hspan
  exact exists_greedy_theta_divisibility _ NumberField.RingOfIntegers.coe_injective
    H C hH _ _ d (generatedRootA_sq a b d ha hb) (generatedRootB_sq a b d ha hb) n hspan

theorem exists_concrete_greedy_divisibility {M : ℕ}
    (a b : K) (d : ℤ) (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (H C : ℕ) (hH : 0 < H) (exponents : Fin M → Fin 4 →₀ ℕ) :
    let L := SiegelZeros.W10.rootField a b
    let f := algebraMap (𝓞 L) L
    let u := W37.integralRootA a b d ha hb
    let v := W37.integralRootB a b d ha hb
    let n : Fin M → Fin 4 → ℤ := fun j i => (exponents j i : ℤ)
    W29.rowSpan (K := L)
      (weightedRow f (fun j => Awei.W39.theta u v (n j))
        (fun j => Awei.W39.theta (-u) v (n j))
        (fun j => Awei.W39.theta (-u) (-v) (n j))) (W62.cutoff H C) = ⊤ →
    ∃ hcard : (greedySet f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j))).card = M,
    let idx := greedyIndex f H C
      (fun j => Awei.W39.theta u v (n j))
      (fun j => Awei.W39.theta (-u) v (n j))
      (fun j => Awei.W39.theta (-u) (-v) (n j)) hcard
    let Δ := W37.concreteDelta a b d hd hd1 hd2 ha hb exponents
      (fun i => (idx i).coords)
    Δ ≠ 0 ∧ ∀ (p : ℕ) (hp : p.Prime), H < p → p ≠ 2 → @legendreSym p ⟨hp⟩ d = -1 →
      (p : 𝓞 L) ^ (∑ i, (idx i).coords 0 / p) ∣ Δ := by
  dsimp only
  intro hspan
  obtain ⟨hcard, h⟩ := exists_generated_greedy_divisibility a b d ha hb H C hH
    (fun j i => (exponents j i : ℤ)) hspan
  refine ⟨hcard, ?_⟩
  dsimp only at h ⊢
  simpa only [W37.concreteDelta_eq_coordinateRows_det, generatedRootA,
    generatedRootB] using h

end SiegelZerosAwei.W60


end SiegelZeros

end OAI
