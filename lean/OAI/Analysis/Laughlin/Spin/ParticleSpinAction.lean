import OAI.Analysis.Laughlin.EnergyNonnegative
import OAI.Analysis.Laughlin.Spin.Representation

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorPowerMatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ := fun a b => ∏ i, A (a i) (b i)

theorem tensorPowerMatrix_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A B : Matrix κ κ ℂ) :
    tensorPowerMatrix (ι := ι) (A*B) = tensorPowerMatrix (ι := ι) A * tensorPowerMatrix (ι := ι) B := by
  ext a c
  simp only [tensorPowerMatrix,Matrix.mul_apply,← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i b => A (a i) b*B b (c i))

theorem tensorPowerMatrix_one {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] :
    tensorPowerMatrix (ι := ι) (1 : Matrix κ κ ℂ) = 1 := by
  classical
  ext a b
  simp only [tensorPowerMatrix,Matrix.one_apply]
  by_cases h : a=b
  · subst b; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem tensorPowerMatrix_conjTranspose {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ κ ℂ) : tensorPowerMatrix (ι := ι) Aᴴ = (tensorPowerMatrix A)ᴴ := by
  ext a b
  simp [tensorPowerMatrix,Matrix.conjTranspose_apply]

theorem tensorPowerMatrix_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (hA : A ∈ Matrix.unitaryGroup κ ℂ) :
    tensorPowerMatrix (ι := ι) A ∈ Matrix.unitaryGroup (ι → κ) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose,← tensorPowerMatrix_conjTranspose,← tensorPowerMatrix_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h,tensorPowerMatrix_one]

noncomputable def sourceParticleRepresentation (N Q : ℕ) : SourceSU2 →*
    Matrix (Configuration N Q) (Configuration N Q) ℂ where
  toFun g := tensorPowerMatrix (sourceSpinRepresentation Q g)
  map_one' := by rw [map_one, tensorPowerMatrix_one]
  map_mul' g h := by rw [map_mul, tensorPowerMatrix_mul]

theorem sourceParticleRepresentation_unitary (N Q : ℕ) (g : SourceSU2) :
    sourceParticleRepresentation N Q g ∈ Matrix.unitaryGroup (Configuration N Q) ℂ :=
  tensorPowerMatrix_unitary _ (sourceSpinRepresentation_unitary Q g)

theorem sourceParticleRepresentation_continuous (N Q : ℕ)
    (a b : Configuration N Q) : Continuous (fun g => sourceParticleRepresentation N Q g a b) := by
  change Continuous (fun g => ∏ k, sourceSpinRepresentation Q g (a k) (b k))
  exact continuous_finsetProd _ (fun k hk => sourceSpinRepresentation_continuous Q _ _)

end Laughlin.Rotation

end OAI
