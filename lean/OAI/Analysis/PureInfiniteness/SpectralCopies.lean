import OAI.Analysis.PureInfiniteness.CutSampleReturn

namespace OAI

/-! Disjoint copies of a spectral return column. These encode the finite
amplification in KR02 Lemmas 7.8 and 7.10. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

section Nonunital

variable {D M J : Type*} [NonUnitalCStarAlgebra D] [Fintype M] [DecidableEq M] [Fintype J]

def supportedSpectralCopy (g : J → D) (i : M) (p : M × J) : D :=
  if p.1 = i then g p.2 else 0

lemma sum_supportedSpectralCopy (g : J → D) (i : M) :
    ∑ p, supportedSpectralCopy g i p = ∑ j, g j := by
  simp [supportedSpectralCopy, Fintype.sum_prod_type]

lemma sum_smul_supportedSpectralCopy (g : J → D) (t : J → ℂ) (i : M) :
    ∑ p, t p.2 • supportedSpectralCopy g i p = ∑ j, t j • g j := by
  simp [supportedSpectralCopy, Fintype.sum_prod_type]

omit [Fintype M] [Fintype J] in
lemma supportedSpectralCopy_support (f g : J → D) (hfg : ∀ j, f j * g j = g j)
    (i : M) (p : M × J) : f p.2 * supportedSpectralCopy g i p = supportedSpectralCopy g i p := by
  by_cases h : p.1 = i <;> simp [supportedSpectralCopy, h, hfg]

omit [Fintype M] [Fintype J] in
lemma supportedSpectralCopy_disjoint (g : J → D) (i k : M) (hik : i ≠ k) (p : M × J) :
    supportedSpectralCopy g i p = 0 ∨ supportedSpectralCopy g k p = 0 := by
  by_cases hi : p.1 = i
  · right
    have hk : p.1 ≠ k := fun hk => hik (hi.symm.trans hk)
    simp [supportedSpectralCopy, hk]
  · left
    simp [supportedSpectralCopy, hi]

variable [PartialOrder D] [StarOrderedRing D]

omit [Fintype M] [Fintype J] [StarOrderedRing D] in
lemma supportedSpectralCopy_nonneg (g : J → D) (hg : ∀ j, 0 ≤ g j) (i : M) (p : M × J) :
    0 ≤ supportedSpectralCopy g i p := by
  by_cases h : p.1 = i <;> simp [supportedSpectralCopy, h, hg]

omit [Fintype M] [Fintype J] in
lemma sqrt_supportedSpectralCopy (g : J → D) (i : M) (p : M × J) :
    CFC.sqrt (supportedSpectralCopy g i p) = if p.1 = i then CFC.sqrt (g p.2) else 0 := by
  by_cases h : p.1 = i <;> simp [supportedSpectralCopy, h]

end Nonunital

section Unital

variable {D M J : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Fintype M] [DecidableEq M] [Fintype J] [DecidableEq J]

lemma spectralCopies_cross_diagonal_zero (g : J → D) (c : M × J → D)
    (i k : M) (hik : i ≠ k) :
    (sqrtColumn (supportedSpectralCopy g i)).conjTranspose *
      NonunitalGamma.diagonalHom c * sqrtColumn (supportedSpectralCopy g k) = 0 := by
  rw [rectangular_mul_assoc]
  apply CStarMatrix.ext
  intro r s
  change (∑ p, star (CFC.sqrt (supportedSpectralCopy g i p)) *
    (NonunitalGamma.diagonalHom c * sqrtColumn (supportedSpectralCopy g k)) p s) = 0
  simp only [diagonal_mul_sqrtColumn, sqrt_supportedSpectralCopy]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hi : p.1 = i
  · simp [hi, hik]
  · simp [hi]

end Unital

end WeakPureInfiniteness

end

end OAI
