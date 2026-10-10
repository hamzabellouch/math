import OAI.Analysis.Laughlin.FourBody.RetainedComparison
import OAI.Analysis.Laughlin.FourBody.TargetResolution

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix ComplexOrder

theorem castSpinColumns_mul_adjoint {I : Type*} (m n : ℕ) (h : m=n)
    (W : Matrix I (Fin (m+1)) ℂ) :
    castSpinColumns m n h W * (castSpinColumns m n h W)ᴴ = W*Wᴴ := by
  subst n
  rfl

theorem fourWedgeProjector_congr (Q r D E : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hA' : E-r ≤ 2*Q-2) (hB' : E-r ≤ genericCoupledWeight Q Q r) (h : D=E) :
    fourWedgeInclusion Q r D hr hA hB*(fourWedgeInclusion Q r D hr hA hB)ᴴ =
      fourWedgeInclusion Q r E hr hA' hB'*(fourWedgeInclusion Q r E hr hA' hB')ᴴ := by
  subst E
  rfl

theorem retainedFirst_projector (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) :
    retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ =
    fourWedgeInclusion Q 1 D (by omega) (by omega) (by unfold genericCoupledWeight; omega) *
      (fourWedgeInclusion Q 1 D (by omega) (by omega) (by unfold genericCoupledWeight; omega))ᴴ := by
  unfold retainedFourInclusion
  rw [castSpinColumns_mul_adjoint]
  rfl

theorem contractionForm_projector_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (W : Matrix I J ℂ) (x : Space Q) :
    0 ≤ (contractionForm Q L (W*Wᴴ) x).re :=
  occupation_matrix_quadratic_positive Q _ (Matrix.posSemidef_self_mul_conjTranspose W) _

theorem sum_fin_castLE_le (m n : ℕ) (hmn : m ≤ n) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∑ i : Fin m, f (Fin.castLE hmn i)) ≤ ∑ i : Fin n, f i := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image (Fin.castLE hmn), f i := by
      rw [Finset.sum_image]
      intro i hi j hj he
      exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i hi hnot => hf i)

theorem retainedFourTarget_le_full (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourTarget Q hQ x ≤
      (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q (by omega)) x).re := by
  let f (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q 1)+1)) : ℝ :=
    (contractionForm Q (sourceFourFamilyEnd Q)
      (fourWedgeInclusion Q 1 (1+z.val) (by omega) (by omega) (by omega) *
        (fourWedgeInclusion Q 1 (1+z.val) (by omega) (by omega) (by omega))ᴴ) x).re
  have hn : 23 ≤ min (2*Q-2) (genericCoupledWeight Q Q 1)+1 := by
    unfold genericCoupledWeight
    omega
  have hs := sum_fin_castLE_le 23 _ hn f (fun z => contractionForm_projector_nonneg Q _ _ x)
  have hl : (∑ d : Fin 23, f (Fin.castLE hn d)) = retainedFourTarget Q hQ x := by
    unfold retainedFourTarget
    apply Finset.sum_congr rfl
    intro d hd
    rw [retainedFirst_projector]
    dsimp only [f,Fin.val_castLE]
    exact congrArg (fun M => (contractionForm Q (sourceFourFamilyEnd Q) M x).re)
      (fourWedgeProjector_congr Q 1 (1+d.val) (d.val+1) (by omega)
        (by omega) (by unfold genericCoupledWeight; omega)
        (by omega) (by unfold genericCoupledWeight; omega) (Nat.add_comm 1 d.val))
  have hr : (∑ z, f z) =
      (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q (by omega)) x).re := by
    rw [fourPairTargetMatrix,fourPairEmbedding_resolution,contractionForm_sum,Complex.re_sum]
  rwa [hl,hr] at hs

end Laughlin.Fock

end OAI
