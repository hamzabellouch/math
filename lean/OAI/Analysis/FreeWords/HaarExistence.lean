import Mathlib
import OAI.Analysis.FreeWords.HaarGridElement

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

local instance haarExistencePartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance haarExistencePreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance haarExistenceLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance haarExistenceStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

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

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier Filter Topology

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance haarExistencePartialOrder_1 (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance haarExistencePreorder_1 (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance haarExistenceLE_1 (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance haarExistenceStarOrderedRing_1 (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem gridElement_cauchy (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) : CauchySeq (gridElement M τ hD) := by
  apply cauchySeq_of_dist_le_of_summable (fun n => 2*Real.pi/(2:ℝ)^(n+1))
  · intro n
    rw [dist_comm,dist_eq_norm]
    exact gridElement_step M τ hD n
  · have hs : Summable (fun n : ℕ => Real.pi * (1/2:ℝ)^n) :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_left _
    convert hs using 1
    ext n
    rw [div_pow,one_pow,pow_succ]
    field_simp

theorem exists_haar_unitary (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hD : IsDiffuse M) : ∃ u : unitary (ConcreteAlgebra M),
      ∀ k : ℤ, k ≠ 0 → τ.map (u ^ k).val = 0 := by
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete (gridElement_cauchy M τ hD)
  have hmem : u ∈ unitary (ConcreteAlgebra M) :=
    isClosed_unitary.mem_of_tendsto hu (Eventually.of_forall (gridElement_unitary M τ hD))
  have hm (k : ℕ) (hk : 0<k) : τ.map (u^k)=0 := by
    have ht : Tendsto (fun n => τ.map (gridElement M τ hD n^k)) atTop (𝓝 (τ.map (u^k))) :=
      (map_continuous (tracePositive τ)).continuousAt.tendsto.comp (hu.pow k)
    have he : (fun n => τ.map (gridElement M τ hD n^k)) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [eventually_ge_atTop k] with n hn
      rw [gridElement_moment M τ hD n k]
      exact phaseMoment_eq_zero n k hk (hn.trans_lt (Nat.lt_two_pow_self))
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)
  refine ⟨⟨u,hmem⟩,?_⟩
  intro k hk
  cases k with
  | ofNat k =>
    have he := zpow_natCast (⟨u,hmem⟩ : unitary (ConcreteAlgebra M)) k
    have hτ := congrArg (fun v : unitary (ConcreteAlgebra M) => τ.map v.val) he
    exact hτ.trans (by simpa only [SubmonoidClass.coe_pow] using hm k (Nat.pos_of_ne_zero (by intro h; subst k; exact hk rfl)))
  | negSucc k =>
    rw [zpow_negSucc,← Unitary.star_eq_inv,Unitary.coe_star,SubmonoidClass.coe_pow]
    change τ.map (star (u^(k+1)))=0
    change (tracePositive τ) (star (u^(k+1)))=0
    rw [map_star,show (tracePositive τ) (u^(k+1))=0 from hm _ (by omega),star_zero]

end

end KKProjectionSupport
end

end OAI
