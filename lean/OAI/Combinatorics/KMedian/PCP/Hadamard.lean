import Mathlib
import OAI.Combinatorics.KMedian.PCP.FiniteTest

namespace OAI

section Inline_PCPHadamard

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

abbrev Bit := ZMod 2
abbrev BitVector (V : Type) := V → Bit

theorem bit_cases (b : Bit) : b = 0 ∨ b = 1 := by
  have hlt := ZMod.val_lt b
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  rcases hb with hb | hb
  · left; apply ZMod.val_injective 2; simpa using hb
  · right; apply ZMod.val_injective 2; change b.val = 1; exact hb

theorem bit_add_one_ne_zero (b : Bit) : b + 1 ≠ 0 ↔ b = 0 := by
  rcases bit_cases b with rfl | rfl <;> decide

section Balance
variable {G : Type} [AddCommGroup G] [Fintype G]

theorem linear_nonzero_rate (g : G →+ Bit) (z : G) (hz : g z ≠ 0) :
    testRate (fun x => g x ≠ 0) = 1/2 := by
  have hg : g z = 1 := (bit_cases (g z)).resolve_left hz
  have he := testRate_equiv (Equiv.addRight z) (fun x => g x ≠ 0)
  have hc : testRate (fun x => g (x + z) ≠ 0) =
      testRate (fun x => ¬ (g x ≠ 0)) := by
    apply testRate_congr
    intro x
    simp only [map_add, hg, bit_add_one_ne_zero, not_not]
  have hcomp := testRate_complement (fun x => g x ≠ 0)
  change testRate (fun x => g (x + z) ≠ 0) = _ at he
  linarith

end Balance

section Bilinear
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

theorem bilinear_nonzero_rate (b : G →+ (H →+ Bit)) (x : G) (y : H)
    (h : b x y ≠ 0) :
    1/4 ≤ testRate (fun p : G × H => b p.1 p.2 ≠ 0) := by
  classical
  let gy : G →+ Bit :=
    { toFun := fun z => b z y
      map_zero' := by simp
      map_add' := by intros; simp }
  have hg : testRate (fun z => b z y ≠ 0) = 1/2 := linear_nonzero_rate gy x h
  rw [testRate_prod (fun z w => b z w ≠ 0)]
  have hh : (𝔼 z : G, if b z y ≠ 0 then (1/2 : ℝ) else 0) ≤
      𝔼 z : G, testRate (fun w => b z w ≠ 0) := by
    apply expect_le_expect
    intro z _
    by_cases hz : b z y ≠ 0
    · simp only [ite_eq_left hz]
      exact le_of_eq (linear_nonzero_rate (b z) y hz).symm
    · simp only [ite_eq_right hz]
      exact testRate_nonneg _
  have hi : (𝔼 z : G, if b z y ≠ 0 then (1/2 : ℝ) else 0) =
      (1/2) * testRate (fun z => b z y ≠ 0) := by
    unfold testRate
    rw [mul_expect]
    apply expect_congr rfl
    intro z _
    split_ifs <;> norm_num
  rw [hi, hg] at hh
  norm_num at hh ⊢
  exact hh
end Bilinear

section Vectors
variable {V W : Type} [Fintype V] [Fintype W]

def dot (x y : BitVector V) : Bit := ∑ i, x i * y i

def tensor (x : BitVector V) (y : BitVector W) : BitVector (V × W) :=
  fun p => x p.1 * y p.2

@[simp] theorem dot_add_left (x y z : BitVector V) : dot (x+y) z = dot x z + dot y z := by
  simp [dot, add_mul, sum_add_distrib]
@[simp] theorem dot_add_right (x y z : BitVector V) : dot x (y+z) = dot x y + dot x z := by
  simp [dot, mul_add, sum_add_distrib]
@[simp] theorem dot_zero_left (x : BitVector V) : dot 0 x = 0 := by simp [dot]
@[simp] theorem dot_zero_right (x : BitVector V) : dot x 0 = 0 := by simp [dot]

def dotHom (x : BitVector V) : BitVector V →+ Bit where
  toFun := dot x
  map_zero' := dot_zero_right x
  map_add' := dot_add_right x

omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_add_left (x y : BitVector V) (z : BitVector W) :
    tensor (x+y) z = tensor x z + tensor y z := by ext; simp [tensor, add_mul]
omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_add_right (x : BitVector V) (y z : BitVector W) :
    tensor x (y+z) = tensor x y + tensor x z := by ext; simp [tensor, mul_add]
omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_zero_left (x : BitVector W) : tensor (0 : BitVector V) x = 0 := by
  ext; simp [tensor]
omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_zero_right (x : BitVector V) : tensor x (0 : BitVector W) = 0 := by
  ext; simp [tensor]

theorem dot_tensor (a x : BitVector V) (b y : BitVector W) :
    dot (tensor a b) (tensor x y) = dot a x * dot b y := by
  simp only [dot, tensor, Fintype.sum_prod_type, sum_mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

noncomputable def coordinates (f : BitVector V →+ Bit) : BitVector V := by
  classical
  exact fun i => f (Pi.single i 1)

theorem linear_representation (f : BitVector V →+ Bit) (x : BitVector V) :
    f x = dot (coordinates f) x := by
  classical
  have hdecomp := congrArg f (univ_sum_single x)
  rw [map_sum] at hdecomp
  rw [← hdecomp]
  unfold dot
  apply sum_congr rfl
  intro i _
  have hs : Pi.single i (x i) = x i • (Pi.single i (1 : Bit)) := by
    rw [← Pi.single_smul]
    simp
  rw [hs, ZMod.map_smul]
  simp only [smul_eq_mul, coordinates]
  ring

def multiplicationDiscrepancy (f : BitVector V →+ Bit) (g : BitVector W →+ Bit)
    (h : BitVector (V × W) →+ Bit) : BitVector V →+ (BitVector W →+ Bit) where
  toFun x :=
    { toFun := fun y => h (tensor x y) - f x * g y
      map_zero' := by simp
      map_add' := by intros; simp [mul_add]; ring }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp [add_mul]; ring

omit [Fintype V] [Fintype W] in
theorem multiplication_identifies_tensor (f : BitVector V →+ Bit)
    (g : BitVector W →+ Bit) (h : BitVector (V × W) →+ Bit)
    (hm : ∀ x y, h (tensor x y) = f x * g y) :
    coordinates h = tensor (coordinates f) (coordinates g) := by
  classical
  ext p
  obtain ⟨i,j⟩ := p
  unfold coordinates tensor
  convert hm (Pi.single i 1) (Pi.single j 1) using 1
  congr 1
  ext ⟨u,v⟩
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [tensor, hi, hj]

end Vectors
end MetricKMedian.PCP

end Inline_PCPHadamard

end OAI
