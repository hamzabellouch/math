import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageTrace
import OAI.Analysis.FreeWords.PartialUnitaryAlgebra
import OAI.Analysis.FreeWords.PartialUnitaryNorm

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance patchTracePartialOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance patchTracePreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance patchTraceLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance patchTraceStarOrderedRing : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem trace_mul_cs (a b : ConcreteAlgebra M) :
    ‖τ.map (a*b)‖ ≤ traceNorm τ a*traceNorm τ b := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (gnsVector (tracePositive τ) (star a))
    (gnsVector (tracePositive τ) b)
  simp only [gnsVector_inner,star_star,← traceNorm_eq_gns,traceNorm_star] at h
  change ‖τ.map (a*b)‖ ≤ _ at h
  exact h

theorem traceNorm_power (v : PartialUnitary (ConcreteAlgebra M)) (k:ℤ) :
    traceNorm τ (v.power k)=traceNorm τ v.support := by
  simp only [traceNorm,v.star_power_mul,v.projection.isSelfAdjoint.star_eq,
    v.projection.isIdempotentElem.eq]

theorem trace_supported_le (q a : ConcreteAlgebra M) (hq : IsStarProjection q)
    (ha : q*a=a) : ‖τ.map a‖ ≤ traceNorm τ q^2*‖a‖ := by
  have he : τ.map a=τ.map (q*a*q) := by
    rw [τ.tracial (q*a) q,← mul_assoc,hq.isIdempotentElem.eq,ha]
  rw [he]
  calc
    _ ≤ traceNorm τ q*traceNorm τ (a*q) := by
      simpa only [mul_assoc] using trace_mul_cs τ q (a*q)
    _ ≤ traceNorm τ q*(‖a‖*traceNorm τ q) :=
      mul_le_mul_of_nonneg_left (traceNorm_mul_le τ a q) (traceNorm_nonneg τ q)
    _ = _ := by ring

theorem gap_trace_bound (v : PartialUnitary (ConcreteAlgebra M))
    (k l : ℤ) (Y Z : ConcreteAlgebra M) (c : ℂ) :
    ‖τ.map (v.power k*Y*v.power l*Z)‖ ≤
      (traceNorm τ (v.support*Y*v.support-c • v.support)+‖c‖*traceNorm τ v.support)*
        traceNorm τ v.support*‖Z‖ := by
  let q := v.support
  let A := q*Y*q
  have hj : v.power k*Y*v.power l*Z=v.power k*A*v.power l*Z := by
    dsimp only [A,q]
    simp only [← mul_assoc,v.mul_support]
    rw [mul_assoc (v.power k*Y) v.support (v.power l),v.support_mul]
  rw [hj,τ.tracial (v.power k*A*v.power l) Z]
  have he : Z*(v.power k*A*v.power l)=(Z*v.power k)*A*v.power l := by noncomm_ring
  rw [he,τ.tracial ((Z*v.power k)*A) (v.power l)]
  have he : v.power l*((Z*v.power k)*A)=(v.power l*Z*v.power k)*A := by noncomm_ring
  rw [he,τ.tracial (v.power l*Z*v.power k) A]
  have hA : traceNorm τ A≤traceNorm τ (A-c • q)+‖c‖*traceNorm τ q := by
    calc
      _ = traceNorm τ ((A-c • q)+c • q) := by rw [sub_add_cancel]
      _ ≤ _ := by simpa only [traceNorm_smul] using traceNorm_add_le τ (A-c • q) (c • q)
  have hZ : traceNorm τ (v.power l*Z*v.power k)≤traceNorm τ q*‖Z‖ := by
    calc
      _ ≤ ‖v.power l‖*traceNorm τ (Z*v.power k) := by
        simpa only [mul_assoc] using traceNorm_mul_le τ (v.power l) (Z*v.power k)
      _ ≤ 1*traceNorm τ (Z*v.power k) := mul_le_mul_of_nonneg_right (v.norm_power_le_one l) (traceNorm_nonneg τ _)
      _ ≤ ‖Z‖*traceNorm τ (v.power k) := by simpa only [one_mul] using traceNorm_mul_le τ Z (v.power k)
      _ = traceNorm τ q*‖Z‖ := by rw [traceNorm_power]; ring
  calc
    _ ≤ traceNorm τ A*traceNorm τ (v.power l*Z*v.power k) := trace_mul_cs τ _ _
    _ ≤ (traceNorm τ (A-c • q)+‖c‖*traceNorm τ q)*(traceNorm τ q*‖Z‖) :=
      mul_le_mul hA hZ (traceNorm_nonneg τ _) (add_nonneg (traceNorm_nonneg τ _) (mul_nonneg (norm_nonneg _) (traceNorm_nonneg τ _)))
    _ = _ := by ring

end

end KKLocalPatching
end

end OAI
