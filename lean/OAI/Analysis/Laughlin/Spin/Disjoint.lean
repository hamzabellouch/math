import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import OAI.Analysis.Laughlin.Spin.Schur

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix ComplexOrder

 theorem sourceSpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    sourceSpinRepresentation Q g⁻¹=(sourceSpinRepresentation Q g)ᴴ := by
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  calc
    _ = 1*sourceSpinRepresentation Q g⁻¹ := by rw [Matrix.one_mul]
    _ = ((sourceSpinRepresentation Q g)ᴴ*sourceSpinRepresentation Q g)*sourceSpinRepresentation Q g⁻¹ := by rw [hu]
    _ = _ := by rw [Matrix.mul_assoc,← map_mul,mul_inv_cancel,map_one,Matrix.mul_one]

 theorem source_spin_intertwiner_adjoint (m n : ℕ)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ)
    (hM : ∀ g : SourceSU2, sourceSpinRepresentation m g*M=M*sourceSpinRepresentation n g) :
    ∀ g : SourceSU2, sourceSpinRepresentation n g*Mᴴ=Mᴴ*sourceSpinRepresentation m g := by
  intro g
  have h := congrArg Matrix.conjTranspose (hM g⁻¹)
  simpa only [Matrix.conjTranspose_mul,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using h.symm

theorem source_spin_intertwiner_zero (m n : ℕ) (hmn : m ≠ n)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ)
    (hM : ∀ g : SourceSU2, sourceSpinRepresentation m g*M=M*sourceSpinRepresentation n g) : M=0 := by
  have hA := source_spin_intertwiner_adjoint m n M hM
  have hl := source_spin_commutant_scalar m (M*Mᴴ) (by
    intro g
    rw [← Matrix.mul_assoc,hM,Matrix.mul_assoc,hA,← Matrix.mul_assoc])
  have hr := source_spin_commutant_scalar n (Mᴴ*M) (by
    intro g
    rw [← Matrix.mul_assoc,hA,Matrix.mul_assoc,hM,← Matrix.mul_assoc])
  by_contra h0
  obtain ⟨i,j,hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    apply h0
    ext i j
    simpa using not_exists.mp (not_exists.mp h i) j
  let c := (M*Mᴴ) 0 0
  let d := (Mᴴ*M) 0 0
  have hc : c ≠ 0 := by
    intro hc
    have hz : M*Mᴴ=0 := by rw [hl]; change c • _=0; rw [hc,zero_smul]
    exact h0 (Matrix.self_mul_conjTranspose_eq_zero.mp hz)
  have hd : c=d := by
    have h := Matrix.mul_assoc M Mᴴ M
    rw [hl,hr,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one] at h
    have he := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply,smul_eq_mul] at he
    exact mul_right_cancel₀ hij he
  have ht := Matrix.trace_mul_comm M Mᴴ
  rw [hl,hr] at ht
  simp only [Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  change c*((m+1 : ℕ) : ℂ)=d*((n+1 : ℕ) : ℂ) at ht
  rw [← hd] at ht
  have he : m+1=n+1 := by exact_mod_cast mul_left_cancel₀ hc ht
  omega

end Laughlin.Rotation

end OAI
