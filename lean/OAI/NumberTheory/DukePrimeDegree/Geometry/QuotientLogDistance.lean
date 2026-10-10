import OAI.NumberTheory.DukePrimeDegree.Geometry.MatrixLogLength
import OAI.NumberTheory.PrimePackets.ZetaResidues

namespace OAI

/-! # Logarithmic displacement distance on the lattice quotient

Taking the infimum over actual right translations gives a distance
independent of a representative. Its triangle inequality and translation
bound provide uniformly controlled real observables on the quotient.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_rightAction_eq {n : ℕ} (x y : X n) : ∃ g : G n, rightAction x g=y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      refine ⟨a⁻¹*b,?_⟩
      change Quotient.mk _ (a*(a⁻¹*b))=Quotient.mk _ b
      simp

def rightDisplacementLengths {n : ℕ} (x y : X n) : Set ℝ :=
  {r | ∃ g : G n, rightAction x g=y ∧ matrixLogLength g=r}

lemma rightDisplacementLengths_nonempty {n : ℕ} (x y : X n) :
    (rightDisplacementLengths x y).Nonempty := by
  obtain ⟨g,hg⟩ := exists_rightAction_eq x y
  exact ⟨matrixLogLength g,g,hg,rfl⟩

lemma rightDisplacementLengths_bddBelow {n : ℕ} (x y : X n) :
    BddBelow (rightDisplacementLengths x y) := by
  refine ⟨0,?_⟩
  rintro r ⟨g,_,rfl⟩
  exact matrixLogLength_nonneg g

def quotientLogDistance {n : ℕ} (x y : X n) : ℝ := sInf (rightDisplacementLengths x y)

lemma quotientLogDistance_nonneg {n : ℕ} (x y : X n) : 0 ≤ quotientLogDistance x y := by
  apply le_csInf (rightDisplacementLengths_nonempty x y)
  rintro r ⟨g,_,rfl⟩
  exact matrixLogLength_nonneg g

lemma quotientLogDistance_le_length {n : ℕ} (x y : X n) (g : G n)
    (hg : rightAction x g=y) : quotientLogDistance x y ≤ matrixLogLength g :=
  csInf_le (rightDisplacementLengths_bddBelow x y) ⟨g,hg,rfl⟩

lemma quotientLogDistance_self {n : ℕ} (x : X n) : quotientLogDistance x x=0 := by
  apply le_antisymm _ (quotientLogDistance_nonneg x x)
  simpa only [matrixLogLength_one] using quotientLogDistance_le_length x x 1 (rightAction_one x)

lemma quotientLogDistance_triangle {n : ℕ} (x y z : X n) :
    quotientLogDistance x z ≤ quotientLogDistance x y+quotientLogDistance y z := by
  have H (g : G n) (hg : rightAction x g=y) :
      quotientLogDistance x z ≤ matrixLogLength g+quotientLogDistance y z := by
    have hle : quotientLogDistance x z-matrixLogLength g ≤ quotientLogDistance y z := by
      apply le_csInf (rightDisplacementLengths_nonempty y z)
      rintro r ⟨h,hh,rfl⟩
      have hpath : rightAction x (g*h)=z := by rw [←rightAction_mul,hg,hh]
      have h₁ := quotientLogDistance_le_length x z (g*h) hpath
      have h₂ := matrixLogLength_mul_le g h
      linarith
    linarith
  have hle : quotientLogDistance x z-quotientLogDistance y z ≤ quotientLogDistance x y := by
    apply le_csInf (rightDisplacementLengths_nonempty x y)
    rintro r ⟨g,hg,rfl⟩
    linarith [H g hg]
  linarith

lemma quotientLogDistance_symm {n : ℕ} (x y : X n) : quotientLogDistance x y=quotientLogDistance y x := by
  suffices H : ∀ x y : X n, quotientLogDistance y x ≤ quotientLogDistance x y from
    le_antisymm (H y x) (H x y)
  intro x y
  apply le_csInf (rightDisplacementLengths_nonempty x y)
  rintro r ⟨g,hg,rfl⟩
  have hback : rightAction y g⁻¹=x := by rw [←hg,rightAction_mul,mul_inv_cancel,rightAction_one]
  simpa only [matrixLogLength_inv] using quotientLogDistance_le_length y x g⁻¹ hback

/-- The distance from a fixed point changes by at most the length of a
right translation, uniformly in the point being translated. -/
theorem quotientLogDistance_right_bound {n : ℕ} (x y : X n) (g : G n) :
    |quotientLogDistance x (rightAction y g)-quotientLogDistance x y| ≤ matrixLogLength g := by
  have h₁ := quotientLogDistance_triangle x y (rightAction y g)
  have h₂ := quotientLogDistance_triangle x (rightAction y g) y
  have h₃ := quotientLogDistance_le_length y (rightAction y g) g rfl
  rw [quotientLogDistance_symm (rightAction y g) y] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma exists_rightAction_length_lt {n : ℕ} (x y : X n) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : G n, rightAction x g=y ∧ matrixLogLength g < quotientLogDistance x y+ε := by
  obtain ⟨r,⟨g,hg,hgr⟩,hr⟩ := exists_lt_of_csInf_lt (rightDisplacementLengths_nonempty x y)
    (show sInf (rightDisplacementLengths x y) < quotientLogDistance x y+ε by
      exact lt_add_of_pos_right _ hε)
  exact ⟨g,hg,by rwa [hgr]⟩

end DukePrimeDegree

end

end OAI
