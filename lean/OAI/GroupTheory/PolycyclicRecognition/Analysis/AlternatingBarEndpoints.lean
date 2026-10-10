import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingBarFaces

namespace OAI

/-! # The two endpoint faces cancel in a signed abelian bar chain -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem alternatingBar_endpoints_cancel {n : ℕ} (v : Fin (n + 1) → A) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
      Finsupp.single (fun i : Fin n => v (σ i.succ)) (1 : ℤ)) +
    (-1 : ℤ) ^ (n + 1) •
      (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        Finsupp.single (fun i : Fin n => v (σ i.castSucc)) (1 : ℤ)) = 0 := by
  classical
  let r := finRotate (n + 1)
  let H (σ : Equiv.Perm (Fin (n + 1))) :=
    Finsupp.single (fun i : Fin n => v (σ i.castSucc)) (1 : ℤ)
  let T (σ : Equiv.Perm (Fin (n + 1))) :=
    Finsupp.single (fun i : Fin n => v (σ i.succ)) (1 : ℤ)
  have hvec (σ : Equiv.Perm (Fin (n + 1))) : H (σ * r) = T σ := by
    dsimp only [H, T]
    congr 1
    funext i
    change v (σ (finRotate (n + 1) i.castSucc)) = v (σ i.succ)
    exact congrArg (v ∘ σ) (finRotate_of_lt (show i.val < n from i.isLt))
  have hr : (Equiv.Perm.sign r : ℤ) = (-1 : ℤ) ^ n := by
    simp [r, sign_finRotate]
  have hsign (σ : Equiv.Perm (Fin (n + 1))) :
      (Equiv.Perm.sign (σ * r) : ℤ) = (-1 : ℤ) ^ n * (Equiv.Perm.sign σ : ℤ) := by
    rw [map_mul, Units.val_mul, hr, mul_comm]
  have hsum : (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • H σ) =
      (-1 : ℤ) ^ n • (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • T σ) := by
    calc
      _ = ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign (σ * r) : ℤ) • H (σ * r) :=
        (Equiv.sum_comp (Equiv.mulRight r) (fun σ => (Equiv.Perm.sign σ : ℤ) • H σ)).symm
      _ = ∑ σ : Equiv.Perm (Fin (n + 1)), (-1 : ℤ) ^ n • ((Equiv.Perm.sign σ : ℤ) • T σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [hsign, hvec, mul_smul]
      _ = _ := Finset.smul_sum.symm
  have hcoef : (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ n = -1 := by
    calc
      _ = -(((-1 : ℤ) * -1) ^ n) := by rw [mul_pow, pow_succ]; ring
      _ = -1 := by simp
  change (∑ σ, (Equiv.Perm.sign σ : ℤ) • T σ) +
    (-1 : ℤ) ^ (n + 1) • (∑ σ, (Equiv.Perm.sign σ : ℤ) • H σ) = 0
  rw [hsum, smul_smul, hcoef, neg_one_smul, add_neg_cancel]

end PolycyclicRecognition

end

end OAI
