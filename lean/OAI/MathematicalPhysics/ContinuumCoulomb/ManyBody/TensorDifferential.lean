import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalTensor
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakComplexLaplacian

namespace OAI

/-! Exact coordinate derivatives of tensor products. Cross-coordinate
factors remain constant when differentiating a second time in one slot. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

def coordinateProduct {n : ℕ} (f : Fin n → Position → ℂ) (x : Configuration n) : ℂ :=
  ∏ i, f i (Coulomb.position x i)

def positionComplexPartial (f : Position → ℂ) (b : Fin 3) (x : Position) : ℂ :=
  fderiv ℝ f x (EuclideanSpace.single b 1)

def positionComplexLaplacian (f : Position → ℂ) (x : Position) : ℂ :=
  ∑ b, positionComplexPartial (fun y => positionComplexPartial f b y) b x

theorem coordinateProduct_C1 {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) : ContDiff ℝ 1 (coordinateProduct f) := by
  apply contDiff_prod
  intro i _
  exact (hf i).comp (Coulomb.positionCLM i).contDiff

theorem coordinateProduct_C2 {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (coordinateProduct f) := by
  apply contDiff_prod
  intro i _
  exact (hf i).comp (Coulomb.positionCLM i).contDiff

theorem coordinateProduct_partial {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : Fin n) (b : Fin 3) (x : Configuration n) :
    configurationComplexPartial (coordinateProduct f) (i,b) x =
      positionComplexPartial (f i) b (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  exact tensorOrbital_C1_fderiv (fun j y _ => f j y) (fun j _ => hf j) id
    (fun _ => 0) x i b

theorem coordinateProduct_partial_product {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (i : Fin n) (b : Fin 3) :
    configurationComplexPartial (coordinateProduct f) (i,b) =
      coordinateProduct (fun j y => if j=i then positionComplexPartial (f j) b y else f j y) := by
  funext x
  rw [coordinateProduct_partial f hf i b x]
  change _ = Coulomb.slotTensor f (fun j => positionComplexPartial (f j) b) 1 i
    (fun j => Coulomb.position x j)
  rw [Coulomb.slotTensor_factor]
  rfl

theorem positionComplexPartial_C1 (f : Position → ℂ) (hf : ContDiff ℝ 2 f) (b : Fin 3) :
    ContDiff ℝ 1 (positionComplexPartial f b) :=
  (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem coordinateProduct_second {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (i : Fin n) (b : Fin 3) (x : Configuration n) :
    configurationComplexPartial (configurationComplexPartial (coordinateProduct f) (i,b)) (i,b) x =
      positionComplexPartial (positionComplexPartial (f i) b) b (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  let g : Fin n → Position → ℂ := fun j y => if j=i then positionComplexPartial (f j) b y else f j y
  have hg (j : Fin n) : ContDiff ℝ 1 (g j) := by
    by_cases hj : j=i
    · simpa only [g,hj,ite_true] using positionComplexPartial_C1 (f j) (hf j) b
    · simpa only [g,hj,ite_false] using (hf j).of_le (by norm_num)
  rw [coordinateProduct_partial_product f (fun j => (hf j).of_le (by norm_num)) i b]
  rw [coordinateProduct_partial _ hg i b x]
  change positionComplexPartial (g i) b (Coulomb.position x i)*_ = _
  have hgi : g i = positionComplexPartial (f i) b := by funext y; simp only [g,ite_true]
  rw [hgi]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [g,ite_eq_right (Finset.mem_erase.mp hj).1]

theorem coordinateProduct_laplacian {n : ℕ} (f : Fin n → Position → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : Configuration n) :
    configurationComplexLaplacian (coordinateProduct f) x =
      ∑ i, positionComplexLaplacian (f i) (Coulomb.position x i)*
        ∏ j ∈ Finset.univ.erase i, f j (Coulomb.position x j) := by
  unfold configurationComplexLaplacian
  rw [Fintype.sum_prod_type]
  simp_rw [coordinateProduct_second f hf]
  simp only [positionComplexLaplacian,Finset.sum_mul]

end ContinuumCoulomb

end

end OAI
