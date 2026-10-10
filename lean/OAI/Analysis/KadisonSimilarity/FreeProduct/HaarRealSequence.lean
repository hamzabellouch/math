import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialCompression

namespace OAI

/-!
# Real orthonormal tracial sequences from a Haar unitary

The normalized cosine combinations of the positive and negative powers of a
Haar unitary are selfadjoint, trace zero, and orthonormal. Haar existence is not
assumed to have been proved by this construction.
-/

noncomputable section
namespace KadisonSimilarity

/-- This real scalar equals `1 / sqrt 2`. The equivalent form is convenient for
proving normalization without dividing by a square root. -/
def haarCosineCoefficient : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

@[simp] theorem star_haarCosineCoefficient :
    star haarCosineCoefficient = haarCosineCoefficient := by
  simp [haarCosineCoefficient]

theorem haarCosineCoefficient_normalization :
    haarCosineCoefficient * haarCosineCoefficient * 2 = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * 2 = (1 : ℝ) := by
    nlinarith
  unfold haarCosineCoefficient
  exact_mod_cast hc

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

/-- The `(n+1)`-st normalized cosine of the algebraic Haar unitary. -/
def haarCosineVector (w : Rˣ) (n : ℕ) : R :=
  haarCosineCoefficient •
    ((↑(w ^ ((n : ℤ) + 1)) : R) + (↑(w ^ (-((n : ℤ) + 1))) : R))

theorem haarCosineVector_selfadjoint (w : Rˣ) (hw : star w = w⁻¹) (n : ℕ) :
    star (haarCosineVector w n) = haarCosineVector w n := by
  simp only [haarCosineVector, star_smul, star_haarCosineCoefficient, star_add,
    star_unitary_zpow w hw, neg_neg]
  rw [add_comm]

variable (τ : R →ₗ[ℂ] ℂ) (w : Rˣ)
  (hhaar : ∀ k : ℤ, τ (↑(w ^ k) : R) = if k = 0 then 1 else 0)

include hhaar in
omit [StarRing R] [StarModule ℂ R] in
/-- Multiplying integer powers turns the moment condition into a Kronecker
delta for the sum of their exponents. -/
theorem haar_power_product_moment (j k : ℤ) :
    τ ((↑(w ^ j) : R) * (↑(w ^ k) : R)) = if j + k = 0 then 1 else 0 := by
  rw [← Units.val_mul, ← zpow_add, hhaar]

include hhaar in
omit [StarRing R] [StarModule ℂ R] in
theorem haarCosineVector_trace_zero (n : ℕ) : τ (haarCosineVector w n) = 0 := by
  have hp : (n : ℤ) + 1 ≠ 0 := by omega
  have hm : -((n : ℤ) + 1) ≠ 0 := by omega
  simp only [haarCosineVector, map_smul, map_add, hhaar, hp, hm, ↓reduceIte,
    add_zero, smul_zero]

include hhaar in
/-- Distinct positive cosine frequencies are orthogonal. The two mixed terms
survive exactly when the frequencies coincide. -/
theorem haarCosineVector_inner (hw : star w = w⁻¹) (i j : ℕ) :
    τ (star (haarCosineVector w i) * haarCosineVector w j) =
      if i = j then 1 else 0 := by
  rw [haarCosineVector_selfadjoint w hw]
  simp only [haarCosineVector, smul_mul_smul, map_smul, add_mul, mul_add, map_add,
    haar_power_product_moment τ w hhaar, smul_eq_mul]
  have hpp : (i : ℤ) + 1 + ((j : ℤ) + 1) ≠ 0 := by omega
  have hmm : -((i : ℤ) + 1) + -((j : ℤ) + 1) ≠ 0 := by omega
  by_cases hij : i = j
  · subst j
    have hpm : (i : ℤ) + 1 + -((i : ℤ) + 1) = 0 := by omega
    have hmp : -((i : ℤ) + 1) + ((i : ℤ) + 1) = 0 := by omega
    simp only [hpp, hmm, hpm, hmp, ↓reduceIte]
    convert haarCosineCoefficient_normalization using 1
    ring
  · have hpm : (i : ℤ) + 1 + -((j : ℤ) + 1) ≠ 0 := by omega
    have hmp : -((i : ℤ) + 1) + ((j : ℤ) + 1) ≠ 0 := by omega
    simp only [hpp, hmm, hpm, hmp, hij, ↓reduceIte, add_zero, mul_zero]

/-- The algebraic real orthonormal sequence required by the tracial matrix
tower is constructed from the Haar unitary. -/
def realTracialSequenceOfHaar (hw : star w = w⁻¹) : RealTracialSequence τ where
  vector := haarCosineVector w
  trace_zero := haarCosineVector_trace_zero τ w hhaar
  selfadjoint := haarCosineVector_selfadjoint w hw
  inner := haarCosineVector_inner τ w hhaar hw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- A Haar unitary removes the independent real-orthonormal-sequence input
from the tracial matrix tower construction. -/
def tracialMatrixTowerOfHaar
    (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a b, τ (a * b) = τ (b * a))
    (M : NestedTracialMatrices (A := A) τ V) (hw : star w = w⁻¹)
    (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop) :
    TracialMatrixTower (E := E) (F := centeredSubspace (V 1)) (A := A) :=
  tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace
    (realTracialSequenceOfHaar τ w hhaar hw) hsize

end KadisonSimilarity

end

end OAI
