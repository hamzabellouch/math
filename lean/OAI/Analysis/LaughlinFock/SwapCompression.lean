import Mathlib
import OAI.Analysis.LaughlinFock.ScalarAction

namespace OAI

/-! Swap Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

abbrev CubeVector := ℕ → ℕ → ℕ → ℝ

def CubeLayer (T : ℕ) (f : CubeVector) : Prop :=
  ∀ i j k, i+j+k ≠ T → f i j k = 0

def cubeLower (Q : ℕ) (f : CubeVector) : CubeVector := fun i j k =>
  spinStep Q i * f (i-1) j k + spinStep Q j * f i (j-1) k +
    spinStep Q k * f i j (k-1)

def cubeRaise (Q : ℕ) (f : CubeVector) : CubeVector := fun i j k =>
  spinStep Q (i+1) * f (i+1) j k + spinStep Q (j+1) * f i (j+1) k +
    spinStep Q (k+1) * f i j (k+1)

 

def pairTensorEmbed (Q : ℕ) : GridVector →ₗ[ℝ] CubeVector where
  toFun f i j k := ∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p k
  map_add' f g := by
    funext i j k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

 

def pairTensorProject (Q : ℕ) : CubeVector →ₗ[ℝ] GridVector where
  toFun f p k := gridInner Q Q (coupledVector Q Q 1 p) (fun i j => f i j k)
  map_add' f g := by
    funext p k
    simp only [gridInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext p k
    simp only [gridInner, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

 
def swap23 : CubeVector →ₗ[ℝ] CubeVector where
  toFun f i j k := f i k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 
def pairSwapCompression (Q : ℕ) : GridVector →ₗ[ℝ] GridVector :=
  (pairTensorProject Q).comp (swap23.comp (pairTensorEmbed Q))

theorem pairCoupled_lower {Q : ℕ} (hQ : 1 ≤ Q) (p : ℕ) :
    gridLower Q Q (coupledVector Q Q 1 p) =
      spinStep (2*Q-2) (p+1) • coupledVector Q Q 1 (p+1) := by
  simpa only [two_mul, mul_one] using coupledVector_lower_all hQ hQ p

theorem pairCoupled_raise {Q : ℕ} (hQ : 1 ≤ Q) (p : ℕ) :
    gridRaise Q Q (coupledVector Q Q 1 p) =
      spinStep (2*Q-2) p • coupledVector Q Q 1 (p-1) := by
  simpa only [two_mul, mul_one] using coupledVector_raise_all hQ hQ p

theorem gridInner_add_right (n m : ℕ) (f g h : GridVector) :
    gridInner n m f (g+h) = gridInner n m f g + gridInner n m f h := by
  simp only [gridInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem grid_raise_adjoint (n m : ℕ) (f g : GridVector) :
    gridInner n m (gridRaise n m f) g = gridInner n m f (gridLower n m g) := by
  rw [gridInner_comm, ← grid_adjoint, gridInner_comm]

theorem pairTensorProject_lower {Q : ℕ} (hQ : 1 ≤ Q) (f : CubeVector) :
    pairTensorProject Q (cubeLower Q f) = gridLower (2*Q-2) Q (pairTensorProject Q f) := by
  funext p k
  change gridInner Q Q (coupledVector Q Q 1 p)
      (gridLower Q Q (fun i j => f i j k) + spinStep Q k • (fun i j => f i j (k-1))) = _
  rw [gridInner_add_right, gridInner_smul_right, ← grid_raise_adjoint,
    pairCoupled_raise hQ, gridInner_smul_left]
  rfl

theorem pairTensorProject_raise {Q : ℕ} (hQ : 1 ≤ Q) (f : CubeVector) :
    pairTensorProject Q (cubeRaise Q f) = gridRaise (2*Q-2) Q (pairTensorProject Q f) := by
  funext p k
  change gridInner Q Q (coupledVector Q Q 1 p)
      (gridRaise Q Q (fun i j => f i j k) + spinStep Q (k+1) • (fun i j => f i j (k+1))) = _
  rw [gridInner_add_right, gridInner_smul_right, ← grid_adjoint,
    pairCoupled_lower hQ, gridInner_smul_left]
  rfl

theorem pairTensorEmbed_lower {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairTensorEmbed Q (gridLower (2*Q-2) Q f) = cubeLower Q (pairTensorEmbed Q f) := by
  funext i j k
  have hp (p : ℕ) : gridLower Q Q (coupledVector Q Q 1 p) i j =
      spinStep (2*Q-2) (p+1) * coupledVector Q Q 1 (p+1) i j :=
    congrArg (fun g : GridVector => g i j) (pairCoupled_lower hQ p)
  calc
    _ = (∑ p ∈ Finset.range (2*Q-2+1),
        (spinStep (2*Q-2) p * f (p-1) k) * coupledVector Q Q 1 p i j) +
        spinStep Q k * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k-1)) := by
      simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk, gridLower,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring
    _ = (∑ p ∈ Finset.range (2*Q-2+1), f p k *
        (spinStep (2*Q-2) (p+1) * coupledVector Q Q 1 (p+1) i j)) +
        spinStep Q k * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k-1)) := by
      rw [spinStep_sum_adjoint (2*Q-2) (fun p => f p k) (fun p => coupledVector Q Q 1 p i j)]
    _ = (∑ p ∈ Finset.range (2*Q-2+1), f p k * gridLower Q Q (coupledVector Q Q 1 p) i j) +
        spinStep Q k * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k-1)) := by
      simp only [hp]
    _ = _ := by
      simp only [cubeLower, pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk,
        gridLower, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring

theorem pairTensorEmbed_raise {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairTensorEmbed Q (gridRaise (2*Q-2) Q f) = cubeRaise Q (pairTensorEmbed Q f) := by
  funext i j k
  have hp (p : ℕ) : gridRaise Q Q (coupledVector Q Q 1 p) i j =
      spinStep (2*Q-2) p * coupledVector Q Q 1 (p-1) i j :=
    congrArg (fun g : GridVector => g i j) (pairCoupled_raise hQ p)
  calc
    _ = (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j *
        (spinStep (2*Q-2) (p+1) * f (p+1) k)) +
        spinStep Q (k+1) * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k+1)) := by
      simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk, gridRaise,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = (∑ p ∈ Finset.range (2*Q-2+1),
        (spinStep (2*Q-2) p * coupledVector Q Q 1 (p-1) i j) * f p k) +
        spinStep Q (k+1) * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k+1)) := by
      rw [spinStep_sum_adjoint (2*Q-2) (fun p => coupledVector Q Q 1 p i j) (fun p => f p k)]
    _ = (∑ p ∈ Finset.range (2*Q-2+1), gridRaise Q Q (coupledVector Q Q 1 p) i j * f p k) +
        spinStep Q (k+1) * (∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p (k+1)) := by
      simp only [hp]
    _ = _ := by
      simp only [cubeRaise, pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk,
        gridRaise, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring

theorem swap23_lower (Q : ℕ) (f : CubeVector) :
    swap23 (cubeLower Q f) = cubeLower Q (swap23 f) := by
  funext i j k
  simp only [swap23, cubeLower, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem swap23_raise (Q : ℕ) (f : CubeVector) :
    swap23 (cubeRaise Q f) = cubeRaise Q (swap23 f) := by
  funext i j k
  simp only [swap23, cubeRaise, LinearMap.coe_mk, AddHom.coe_mk]
  ring

 

theorem pairSwapCompression_lower {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairSwapCompression Q (gridLower (2*Q-2) Q f) =
      gridLower (2*Q-2) Q (pairSwapCompression Q f) := by
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorEmbed_lower hQ,
    swap23_lower, pairTensorProject_lower hQ]

theorem pairSwapCompression_raise {Q : ℕ} (hQ : 1 ≤ Q) (f : GridVector) :
    pairSwapCompression Q (gridRaise (2*Q-2) Q f) =
      gridRaise (2*Q-2) Q (pairSwapCompression Q f) := by
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorEmbed_raise hQ,
    swap23_raise, pairTensorProject_raise hQ]

theorem pairTensorEmbed_layer {Q T : ℕ} {f : GridVector} (hf : GridLayer T f) :
    CubeLayer (T+1) (pairTensorEmbed Q f) := by
  intro i j k hijk
  simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hij : i+j=1+p
  · rw [hf p k (by omega), mul_zero]
  · rw [coupledVector_layer Q Q 1 p i j hij, zero_mul]

theorem swap23_layer {T : ℕ} {f : CubeVector} (hf : CubeLayer T f) :
    CubeLayer T (swap23 f) := by
  intro i j k h
  exact hf i k j (by omega)

theorem pairTensorProject_layer {Q T : ℕ} {f : CubeVector} (hf : CubeLayer (T+1) f) :
    GridLayer T (pairTensorProject Q f) := by
  intro p k hpk
  simp only [pairTensorProject, LinearMap.coe_mk, AddHom.coe_mk, gridInner]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i+j=1+p
  · rw [hf i j k (by omega), mul_zero]
  · rw [coupledVector_layer Q Q 1 p i j hij, zero_mul]

theorem pairSwapCompression_layer (Q T : ℕ) (f : GridVector) (hf : GridLayer T f) :
    GridLayer T (pairSwapCompression Q f) :=
  pairTensorProject_layer (swap23_layer (pairTensorEmbed_layer hf))

 

theorem pairSwapCompression_coupled {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (k : ℕ) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z k) =
      (pairSwapCompression Q (coupledVector (2*Q-2) Q z 0) 0 z /
        highestCoefficient (2*Q-2) Q z 0) • coupledVector (2*Q-2) Q z k := by
  exact coupledVector_intertwiner (by omega) hz _
    (pairSwapCompression_lower (by omega)) (pairSwapCompression_raise (by omega))
    (pairSwapCompression_layer Q) k

end LaughlinFock
end

end OAI
