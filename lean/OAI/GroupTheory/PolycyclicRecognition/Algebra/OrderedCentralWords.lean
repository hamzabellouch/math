import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralWordCollection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace OAI

/-! # Ordered integral coordinates and their central collection factor -/

namespace PolycyclicRecognition
open scoped commutatorElement
variable {G A : Type*} [Group G] [CommGroup A] {d : ℕ}

def orderedWord (a : Fin d → G) (x : Fin d → ℤ) : G :=
  (List.ofFn (fun i => a i ^ x i)).prod

@[simp] theorem orderedWord_zero (a : Fin d → G) : orderedWord a 0 = 1 := by
  simp [orderedWord]

theorem orderedWord_succ (a : Fin (d + 1) → G) (x : Fin (d + 1) → ℤ) :
    orderedWord a x = a 0 ^ x 0 * orderedWord (fun i => a i.succ) (fun i => x i.succ) := by
  simp [orderedWord, List.ofFn_succ]

def triangularFactor (c : Fin d → Fin d → A) (x y : Fin d → ℤ) : A :=
  ∏ i, ∏ j, if j < i then c i j ^ (x i * y j) else 1

theorem triangularFactor_succ (c : Fin (d + 1) → Fin (d + 1) → A)
    (x y : Fin (d + 1) → ℤ) :
    triangularFactor c x y =
      (∏ i : Fin d, c i.succ 0 ^ (x i.succ * y 0)) *
        triangularFactor (fun i j => c i.succ j.succ)
          (fun i => x i.succ) (fun i => y i.succ) := by
  simp [triangularFactor, Fin.prod_univ_succ, Finset.prod_mul_distrib]

theorem orderedWord_right_power (z : A →* G)
    (hz : ∀ v, z v ∈ Subgroup.center G) (a : Fin d → G) (b : G)
    (c : Fin d → A) (hc : ∀ i, ⁅a i, b⁆ = z (c i)) (x : Fin d → ℤ) (n : ℤ) :
    orderedWord a x * b ^ n =
      z (∏ i, c i ^ (x i * n)) * b ^ n * orderedWord a x := by
  have h := central_word_powers_collection z hz (List.ofFn (fun i : Fin d => i))
    a b c (fun i _ => hc i) x n
  simpa [orderedWord, List.map_ofFn, List.prod_ofFn, Function.comp_def] using h

theorem orderedWord_mul (z : A →* G) (hz : ∀ v, z v ∈ Subgroup.center G)
    (a : Fin d → G) (c : Fin d → Fin d → A)
    (hc : ∀ i j, ⁅a i, a j⁆ = z (c i j)) (x y : Fin d → ℤ) :
    orderedWord a x * orderedWord a y =
      z (triangularFactor c x y) * orderedWord a (x + y) := by
  induction d with
  | zero => simp [orderedWord, triangularFactor]
  | succ d ih =>
    let tailA := fun i : Fin d => a i.succ
    let ct := fun i j : Fin d => c i.succ j.succ
    let xt := fun i : Fin d => x i.succ
    let yt := fun i : Fin d => y i.succ
    let F := ∏ i : Fin d, c i.succ 0 ^ (x i.succ * y 0)
    let T := triangularFactor ct xt yt
    have ht : orderedWord tailA xt * a 0 ^ y 0 =
        z F * a 0 ^ y 0 * orderedWord tailA xt :=
      orderedWord_right_power z hz tailA (a 0) (fun i => c i.succ 0)
        (fun i => hc i.succ 0) xt (y 0)
    have hi : orderedWord tailA xt * orderedWord tailA yt =
        z T * orderedWord tailA (xt + yt) :=
      ih tailA ct (fun i j => hc i.succ j.succ) xt yt
    have hF : a 0 ^ x 0 * z F = z F * a 0 ^ x 0 :=
      Subgroup.mem_center_iff.mp (hz F) _
    have hT : a 0 ^ (x 0 + y 0) * z T = z T * a 0 ^ (x 0 + y 0) :=
      Subgroup.mem_center_iff.mp (hz T) _
    calc
      orderedWord a x * orderedWord a y =
          (a 0 ^ x 0 * orderedWord tailA xt) * (a 0 ^ y 0 * orderedWord tailA yt) := by
        rw [orderedWord_succ, orderedWord_succ]
      _ = a 0 ^ x 0 * (orderedWord tailA xt * a 0 ^ y 0) * orderedWord tailA yt := by
        simp only [mul_assoc]
      _ = a 0 ^ x 0 * (z F * a 0 ^ y 0 * orderedWord tailA xt) * orderedWord tailA yt := by
        rw [ht]
      _ = (a 0 ^ x 0 * z F) * (a 0 ^ y 0 *
          (orderedWord tailA xt * orderedWord tailA yt)) := by simp only [mul_assoc]
      _ = (z F * a 0 ^ x 0) * (a 0 ^ y 0 *
          (orderedWord tailA xt * orderedWord tailA yt)) := by rw [hF]
      _ = z F * (a 0 ^ x 0 * a 0 ^ y 0) *
          (orderedWord tailA xt * orderedWord tailA yt) := by simp only [mul_assoc]
      _ = z F * a 0 ^ (x 0 + y 0) * (z T * orderedWord tailA (xt + yt)) := by
        rw [← zpow_add, hi]
      _ = z F * (a 0 ^ (x 0 + y 0) * z T) * orderedWord tailA (xt + yt) := by
        simp only [mul_assoc]
      _ = z F * (z T * a 0 ^ (x 0 + y 0)) * orderedWord tailA (xt + yt) := by rw [hT]
      _ = z (F * T) * (a 0 ^ (x 0 + y 0) * orderedWord tailA (xt + yt)) := by
        rw [map_mul]
        simp only [mul_assoc]
      _ = z (triangularFactor c x y) * orderedWord a (x + y) := by
        rw [triangularFactor_succ, orderedWord_succ]
        rfl

end PolycyclicRecognition

end OAI
