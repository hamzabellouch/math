import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Feasible

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

def searchStep (n : ℕ) (r : ℚ) : ℚ := r/(n+1)
def searchMesh (n : ℕ) (r R : ℚ) : ℚ :=
  (searchStep n r)^2/(16*(n+1)*(R+searchStep n r+1))
def searchFuel (n : ℕ) (r R : ℚ) : ℕ :=
  ⌈4*R^2/(searchStep n r)^2⌉₊+1

def Pencil.search (B : Pencil n m) (r R : ℚ) (y : Fin n → ℚ) : Fin n → ℚ :=
  (B.next (searchStep n r) (searchMesh n r R))^[searchFuel n r R] y

lemma searchStep_pos {r : ℚ} (hr : 0 < r) : 0 < searchStep n r := by
  unfold searchStep
  positivity

lemma searchMesh_pos {r R : ℚ} (hr : 0 < r) (hR : 0 ≤ R) : 0 < searchMesh n r R := by
  have hs := searchStep_pos (n := n) hr
  unfold searchMesh
  positivity

lemma mesh_error_small {s R : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) (hR : 0 ≤ R) :
    2*(R+s)*(s^2/(16*(R+s+1)))+(s^2/(16*(R+s+1)))^2 ≤ s^2/2 := by
  have hden : 0 < 16*(R+s+1) := by positivity
  have hδ : 0 ≤ s^2/(16*(R+s+1)) := by positivity
  have hfirst : 2*(R+s)*(s^2/(16*(R+s+1))) ≤ s^2/8 := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<8)).mpr
    nlinarith [sq_nonneg s]
  have hδs : s^2/(16*(R+s+1)) ≤ s/16 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<16)).mpr
    nlinarith [mul_nonneg hs.le hR]
  have hδsq := pow_le_pow_left₀ hδ hδs 2
  nlinarith [sq_nonneg s]

lemma searchMesh_small {r R : ℚ} (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) :
    2*((R : ℝ)+searchStep n r)*((n+1)*(searchMesh n r R : ℝ))+
      ((n+1)*(searchMesh n r R : ℝ))^2 ≤ (searchStep n r : ℝ)^2/2 := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hs : 0 < (searchStep n r : ℝ) := by exact_mod_cast searchStep_pos (n := n) hr
  have hs1' : searchStep n r ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℚ)<n+1)).mpr
    exact hr1.trans (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hs1 : (searchStep n r : ℝ) ≤ 1 := by exact_mod_cast hs1'
  have hR' : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have he : (n+1)*(searchMesh n r R : ℝ) =
      (searchStep n r : ℝ)^2/(16*((R:ℝ)+searchStep n r+1)) := by
    simp only [searchMesh,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one]
    field_simp
  rw [he]
  exact mesh_error_small hs hs1 hR'

lemma searchFuel_suffices {r R : ℚ} (hr : 0 < r) (_hR : 0 ≤ R) :
    (R:ℝ)^2 < (searchFuel n r R : ℝ)*(searchStep n r : ℝ)^2/2 := by
  have hs : 0 < searchStep n r := searchStep_pos hr
  have hc := Nat.le_ceil (4*R^2/(searchStep n r)^2)
  have hh : 2*R^2/(searchStep n r)^2 < (searchFuel n r R : ℚ) := by
    unfold searchFuel
    push_cast
    have := div_nonneg (sq_nonneg R) (sq_nonneg (searchStep n r))
    simp only [mul_div_assoc] at hc ⊢
    linarith
  have hmul := (div_lt_iff₀ (pow_pos hs 2)).mp hh
  have hcast : 2*(R:ℝ)^2 < (searchFuel n r R : ℝ)*(searchStep n r : ℝ)^2 := by
    exact_mod_cast hmul
  linarith

theorem Pencil.search_accepts (B : Pencil n m) (r R : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R)
    (hball : Metric.closedBall c (r:ℝ) ⊆ B.feasible)
    (hy : ‖realVector y-c‖ ≤ (R:ℝ)) :
    B.witness (B.search r R y)=none := by
  apply B.search_feasible (searchStep n r) (searchMesh n r R) y c
    (by exact_mod_cast hr) (by exact_mod_cast hR) (searchMesh_pos hr hR)
    (by simp [searchStep]) hball (searchMesh_small hr hr1 hR) hy
    (searchFuel n r R) (searchFuel_suffices hr hR)

lemma roundVector_on_mesh (mesh : ℚ) (y : Fin n → ℚ) :
    ∀ i, ∃ v : ℤ, roundVector mesh y i = mesh*v := by
  intro i
  exact ⟨⌊y i/mesh⌋,rfl⟩

lemma Pencil.next_on_mesh (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hy : ∀ i, ∃ v : ℤ, y i=mesh*v) :
    ∀ i, ∃ v : ℤ, B.next step mesh y i=mesh*v := by
  cases hv : B.witness y with
  | none => simpa only [Pencil.next,hv] using hy
  | some v => simpa only [Pencil.next,hv] using
      roundVector_on_mesh mesh (fun i => y i-step*B.normal v i/l1 (B.normal v))

lemma Pencil.iterate_on_mesh (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hy : ∀ i, ∃ v : ℤ, y i=mesh*v) (k : ℕ) :
    ∀ i, ∃ v : ℤ, ((B.next step mesh)^[k] y) i=mesh*v := by
  induction k with
  | zero => exact hy
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact B.next_on_mesh step mesh _ ih
end CurrentKS.RationalSDP

end OAI
