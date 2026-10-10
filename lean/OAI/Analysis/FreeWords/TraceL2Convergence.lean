import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageTrace

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

open Filter Topology

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {I : Type*} {l : Filter I} {x y : I → ConcreteAlgebra M} {a b : ConcreteAlgebra M}

theorem tendsto_gns_iff :
    Tendsto (fun i => gnsVector (tracePositive τ) (x i)) l (𝓝 (gnsVector (tracePositive τ) a)) ↔
      Tendsto (fun i => traceNorm τ (x i-a)) l (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [traceNorm_eq_gns,map_sub]

theorem tendsto_gns_star
    (hx : Tendsto (fun i => gnsVector (tracePositive τ) (x i)) l (𝓝 (gnsVector (tracePositive τ) a))) :
    Tendsto (fun i => gnsVector (tracePositive τ) (star (x i))) l (𝓝 (gnsVector (tracePositive τ) (star a))) := by
  apply (tendsto_gns_iff τ).mpr
  have he (i:I) : traceNorm τ (star (x i)-star a)=traceNorm τ (x i-a) := by rw [← star_sub,traceNorm_star]
  simpa only [he] using (tendsto_gns_iff τ).mp hx

theorem tendsto_gns_mul (C : ℝ) (_ : 0≤C) (hb : ∀ i, ‖x i‖≤C)
    (hx : Tendsto (fun i => gnsVector (tracePositive τ) (x i)) l (𝓝 (gnsVector (tracePositive τ) a)))
    (hy : Tendsto (fun i => gnsVector (tracePositive τ) (y i)) l (𝓝 (gnsVector (tracePositive τ) b))) :
    Tendsto (fun i => gnsVector (tracePositive τ) (x i*y i)) l (𝓝 (gnsVector (tracePositive τ) (a*b))) := by
  apply (tendsto_gns_iff τ).mpr
  have hh (i:I) : traceNorm τ (x i*y i-a*b)≤C*traceNorm τ (y i-b)+traceNorm τ (x i-a)*‖b‖ := by
    have he : x i*y i-a*b=x i*(y i-b)+(x i-a)*b := by noncomm_ring
    rw [he]
    exact (traceNorm_add_le τ _ _).trans (add_le_add
      ((traceNorm_mul_le τ _ _).trans (mul_le_mul_of_nonneg_right (hb i) (traceNorm_nonneg τ _)))
      (traceNorm_mul_right_le τ _ _))
  have ht := (((tendsto_gns_iff τ).mp hy).const_mul C).add
    (((tendsto_gns_iff τ).mp hx).mul_const ‖b‖)
  simp only [mul_zero,zero_mul,zero_add] at ht
  exact squeeze_zero (fun i => traceNorm_nonneg τ _) hh ht

theorem tendsto_gns_trace
    (hx : Tendsto (fun i => gnsVector (tracePositive τ) (x i)) l (𝓝 (gnsVector (tracePositive τ) a))) :
    Tendsto (fun i => τ.map (x i)) l (𝓝 (τ.map a)) := by
  have hh : Tendsto (fun i => ⟪gnsVector (tracePositive τ) (1:ConcreteAlgebra M),
      gnsVector (tracePositive τ) (x i)⟫_ℂ) l
      (𝓝 ⟪gnsVector (tracePositive τ) (1:ConcreteAlgebra M),gnsVector (tracePositive τ) a⟫_ℂ) :=
    tendsto_const_nhds.inner hx
  simp only [gnsVector_inner,star_one,one_mul] at hh
  exact hh

end

end KKLocalPatching
end

end OAI
