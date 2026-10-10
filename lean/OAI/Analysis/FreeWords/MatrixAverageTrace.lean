import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageBasic
import OAI.Analysis.FreeWords.ProjectionRound

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKUltraTrace

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {M : VonNeumannAlgebra H}

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] ConcreteAlgebra M) (τ : FaithfulNormalTrace M)

omit [Nonempty ι] in
theorem matrixAverage_star (x : ConcreteAlgebra M) :
    star (matrixAverage ρ x)=matrixAverage ρ (star x) := by
  change star ((Fintype.card ι:ℂ)⁻¹ • ∑ i, ∑ j, matrixUnit ρ i j*x*matrixUnit ρ j i)=_
  simp only [star_smul,star_sum,star_mul,matrixUnit_star]
  simp only [matrixAverage,matrixUnit,mul_assoc]
  congr 1
  simp

omit [Nonempty ι] in
theorem matrixAverage_trace_symm (x y : ConcreteAlgebra M) :
    τ.map (matrixAverage ρ x*y)=τ.map (x*matrixAverage ρ y) := by
  change τ.map (((Fintype.card ι:ℂ)⁻¹ • ∑ i,∑ j,matrixUnit ρ i j*x*matrixUnit ρ j i)*y)=
    τ.map (x*((Fintype.card ι:ℂ)⁻¹ • ∑ i,∑ j,matrixUnit ρ i j*y*matrixUnit ρ j i))
  simp only [smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,map_smul,map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_assoc]
  rw [τ.tracial (matrixUnit ρ j i)]
  simp only [mul_assoc]

theorem matrixAverage_one : matrixAverage ρ 1=1 :=
  matrixAverage_fixed ρ 1 (fun _ _ => Commute.one_left _)

theorem matrixAverage_trace (x : ConcreteAlgebra M) : τ.map (matrixAverage ρ x)=τ.map x := by
  have hh := matrixAverage_trace_symm ρ τ x 1
  simpa only [mul_one,matrixAverage_one] using hh

omit [Nonempty ι] in
theorem matrixAverage_inner (x y : ConcreteAlgebra M) :
    (tracePositive τ) (star (matrixAverage ρ x)*y)=
    (tracePositive τ) (star x*matrixAverage ρ y) := by
  change τ.map (star (matrixAverage ρ x)*y)=τ.map (star x*matrixAverage ρ y)
  rw [matrixAverage_star,matrixAverage_trace_symm]

theorem matrixAverage_traceNorm_le (x : ConcreteAlgebra M) :
    traceNorm τ (matrixAverage ρ x) ≤ traceNorm τ x := by
  let v := gnsVector (tracePositive τ) x
  let z := gnsVector (tracePositive τ) (matrixAverage ρ x)
  have hin : ⟪v,z⟫_ℂ=⟪z,z⟫_ℂ := by
    simp only [v,z,gnsVector_inner,matrixAverage_inner,matrixAverage_idempotent]
  have hh := norm_inner_le_norm (𝕜 := ℂ) v z
  rw [hin,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_norm] at hh
  simp only [traceNorm_eq_gns]
  by_cases hz : ‖z‖=0
  · change ‖z‖ ≤ ‖v‖
    rw [hz]; exact norm_nonneg _
  · have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖z‖ ≤ ‖v‖
    nlinarith

theorem traceNorm_smul (c : ℂ) (x : ConcreteAlgebra M) :
    traceNorm τ (c • x)=‖c‖*traceNorm τ x := by
  simp only [traceNorm_eq_gns,map_smul,norm_smul]

theorem traceNorm_star (x : ConcreteAlgebra M) : traceNorm τ (star x)=traceNorm τ x := by
  simp only [traceNorm,star_star]
  rw [τ.tracial]

theorem traceNorm_mul_right_le (x y : ConcreteAlgebra M) :
    traceNorm τ (x*y) ≤ traceNorm τ x*‖y‖ := by
  rw [← traceNorm_star τ (x*y),star_mul]
  simpa only [norm_star,traceNorm_star,mul_comm] using traceNorm_mul_le τ (star y) (star x)

end

end KKMatrixQuantization
end

end OAI
