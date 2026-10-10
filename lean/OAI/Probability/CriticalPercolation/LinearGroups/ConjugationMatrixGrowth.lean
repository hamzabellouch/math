import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.ExpandingCharacterGrowth

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Matrix

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def latticeCharacter (w : ι → ℂ) : Multiplicative (ι → ℤ) →* Multiplicative ℂ where
  toFun x := Multiplicative.ofAdd (w ⬝ᵥ fun i => ((Multiplicative.toAdd x i : ℤ) : ℂ))
  map_one' := by change Multiplicative.ofAdd _ = Multiplicative.ofAdd 0; congr 1; simp
  map_mul' x y := by
    change Multiplicative.ofAdd (w ⬝ᵥ fun i => (((Multiplicative.toAdd x i +
      Multiplicative.toAdd y i) : ℤ) : ℂ)) = Multiplicative.ofAdd (_+_)
    congr 1
    simp [dotProduct,Finset.sum_add_distrib,mul_add]

omit [DecidableEq ι] in
lemma latticeCharacter_mulVec (w : ι → ℂ) (M : Matrix ι ι ℤ) (v : ι → ℤ) :
    Multiplicative.toAdd (latticeCharacter w (Multiplicative.ofAdd (M.mulVec v))) =
      (Matrix.vecMul w (M.map (Int.castRingHom ℂ))) ⬝ᵥ (fun i => (v i : ℂ)) := by
  change (w ⬝ᵥ fun i => ((M.mulVec v i : ℤ) : ℂ)) = _
  have he : (fun i => ((M.mulVec v i : ℤ) : ℂ)) =
      (M.map (Int.castRingHom ℂ)).mulVec (fun i => (v i : ℂ)) := by
    funext i
    exact (Int.castRingHom ℂ).map_mulVec M v i
  rw [he,Matrix.dotProduct_mulVec]

lemma latticeCharacter_single (w : ι → ℂ) (i : ι) :
    Multiplicative.toAdd (latticeCharacter w (Multiplicative.ofAdd (Pi.single i 1)))=w i := by
  change (w ⬝ᵥ fun j => (((Pi.single i (1:ℤ) : ι → ℤ) j : ℤ) : ℂ))=w i
  have he : (fun j => (((Pi.single i (1:ℤ) : ι → ℤ) j : ℤ) : ℂ)) = Pi.single i (1:ℂ) := by
    funext j
    by_cases h : i=j
    · subst j; simp
    · simp [Ne.symm h]
  rw [he,dotProduct_single,mul_one]

theorem HasPolynomialDegree.conjugationMatrix_roots_norm_le_one {d : ℕ}
    (hg : HasPolynomialDegree A d) (H : Subgroup A) [H.Normal] (a : A)
    (p : H →* Multiplicative (ι → ℤ)) (hp : Surjective p)
    (M : Matrix ι ι ℤ)
    (hM : ∀ x : H, Multiplicative.toAdd (p ((MulAut.conjNormal a) x)) =
      M.mulVec (Multiplicative.toAdd (p x))) :
    ∀ z∈(M.map (Int.castRingHom ℂ)).charpoly.roots, ‖z‖≤1 := by
  intro z hz
  let C := M.map (Int.castRingHom ℂ)
  have hroot : (C.transpose.mulVecLin.charpoly).IsRoot z := by
    rw [Matrix.charpoly_mulVecLin,Matrix.charpoly_transpose]
    exact (Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero).mp hz
  have heig := (Module.End.hasEigenvalue_iff_isRoot_charpoly C.transpose.mulVecLin z).mpr hroot
  obtain ⟨w,hw⟩ := heig.exists_hasUnifEigenvector
  have hweq : Matrix.vecMul w C = z • w := by
    simpa only [Matrix.mulVecLin_apply,Matrix.mulVec_transpose] using hw.apply_eq_smul
  have hwn := hw.2
  have hex : ∃ i, w i ≠ 0 := by
    by_contra! h
    exact hwn (funext h)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨b,hb⟩ := hp (Multiplicative.ofAdd (Pi.single i 1))
  let φ := (latticeCharacter w).comp p
  have hφ : ∀ x : H, Multiplicative.toAdd (φ ((MulAut.conjNormal a) x)) =
      z * Multiplicative.toAdd (φ x) := by
    intro x
    change Multiplicative.toAdd (latticeCharacter w (p ((MulAut.conjNormal a) x))) =
      z * Multiplicative.toAdd (latticeCharacter w (p x))
    have hpx : p ((MulAut.conjNormal a) x) =
      Multiplicative.ofAdd (M.mulVec (Multiplicative.toAdd (p x))) := by
      exact congrArg Multiplicative.ofAdd (hM x)
    rw [hpx,latticeCharacter_mulVec]
    change (Matrix.vecMul w C) ⬝ᵥ (fun i => ((Multiplicative.toAdd (p x) i : ℤ) : ℂ)) = _
    rw [hweq,smul_dotProduct]
    rfl
  have hφb : Multiplicative.toAdd (φ b) ≠ 0 := by
    change Multiplicative.toAdd (latticeCharacter w (p b)) ≠ 0
    rw [hb,latticeCharacter_single]
    exact hi
  exact hg.norm_conj_eigencharacter_le_one H a φ z hφ b hφb

end CriticalPercolation.SparseGrowth
end
end

end OAI
