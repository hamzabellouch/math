import Mathlib
import OAI.Analysis.FreeWords.DyadicPhases
import OAI.Analysis.FreeWords.PartitionHom

namespace OAI

noncomputable section

namespace KKProjectionSupport

noncomputable section

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]

variable [StarRing A] [StarModule ℂ A]

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance haarGridElementConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance haarGridElementConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance haarGridElementConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance haarGridElementConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKProjectionSupport

namespace KKProjectionSupport

noncomputable section

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hD : IsDiffuse M)

def gridHom (n : ℕ) : (BitWords n → ℂ) →⋆ₐ[ℂ] ConcreteAlgebra M :=
  partitionHom (dyadicGrid M τ hD n).p (dyadicGrid M τ hD n).proj
    (dyadicGrid M τ hD n).orth (dyadicGrid M τ hD n).sum

def gridElement (n : ℕ) : ConcreteAlgebra M := gridHom M τ hD n (dyadicPhase n)

theorem gridElement_unitary (n : ℕ) : gridElement M τ hD n ∈ unitary (ConcreteAlgebra M) := by
  change (gridHom M τ hD n) (dyadicPhase n) ∈ unitary (ConcreteAlgebra M)
  apply Unitary.map_mem (gridHom M τ hD n)
  rw [Unitary.mem_iff]
  constructor <;> ext w
  · change star (dyadicPhase n w)*dyadicPhase n w=1
    rw [RCLike.star_def,mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,dyadicPhase_norm]
    norm_num
  · change dyadicPhase n w*star (dyadicPhase n w)=1
    rw [RCLike.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,dyadicPhase_norm]
    norm_num

theorem gridElement_refine (n : ℕ) :
    gridElement M τ hD n=gridHom M τ hD (n+1) (fun w => dyadicPhase n w.1) := by
  change (∑ w, dyadicPhase n w • (dyadicGrid M τ hD n).p w)=
    ∑ w : BitWords n × Bool, dyadicPhase n w.1 • (dyadicGrid M τ hD (n+1)).p w
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,← smul_add,dyadicGrid_refine]

theorem gridElement_step (n : ℕ) :
    ‖gridElement M τ hD (n+1)-gridElement M τ hD n‖ ≤ 2*Real.pi/(2:ℝ)^(n+1) := by
  rw [gridElement_refine M τ hD n]
  change ‖gridHom M τ hD (n+1) (dyadicPhase (n+1))-
    gridHom M τ hD (n+1) (fun w => dyadicPhase n w.1)‖ ≤ _
  rw [← map_sub]
  refine (NonUnitalStarAlgHom.norm_apply_le (gridHom M τ hD (n+1)) _).trans ?_
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro w
  rcases w with ⟨w,b⟩
  cases b
  · change ‖dyadicPhase n w*1-dyadicPhase n w‖ ≤ _
    rw [mul_one,sub_self,norm_zero]
    positivity
  · change ‖dyadicPhase n w*dyadicRoot (n+1)-dyadicPhase n w‖ ≤ _
    have he : dyadicPhase n w*dyadicRoot (n+1)-dyadicPhase n w=
        dyadicPhase n w*(dyadicRoot (n+1)-1) := by ring
    rw [he,norm_mul,dyadicPhase_norm,one_mul]
    exact dyadicRoot_sub_one (n+1)

theorem gridElement_moment (n k : ℕ) :
    τ.map (gridElement M τ hD n^k)=phaseMoment n k := by
  change τ.map ((partitionHom _ _ _ _) _ ^ k)=_
  rw [partitionHom_pow,map_sum]
  simp only [map_smul,(dyadicGrid M τ hD n).trace,smul_eq_mul]
  simp only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  rw [← Finset.sum_mul,mul_comm]
  rfl

end

end KKProjectionSupport
end

end OAI
