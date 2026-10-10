import Mathlib
import OAI.Analysis.FreeWords.PatchTraceBounds

namespace OAI

noncomputable section

namespace KKLocalPatching

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport KKMatrixQuantization

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance patchCornerPartialOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance patchCornerPreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance patchCornerLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance patchCornerStarOrderedRing : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem corner_scalar_bound (e Y : ConcreteAlgebra M) (he : IsStarProjection e)
    {b η : ℝ} (hη : 0<η) (ht : (τ.map e).re≤1-η)
    (hY : ‖τ.map Y‖≤b) (heY : ‖τ.map (e*Y)‖≤b) :
    ‖(τ.map (1-e))⁻¹*τ.map ((1-e)*Y*(1-e))‖≤2*b/η := by
  have hp : IsStarProjection (1-e) := he.one_sub
  have hr : τ.map (1-e)=((1-(τ.map e).re:ℝ):ℂ) := by
    rw [map_sub,τ.normalized]
    have hre : τ.map e=((τ.map e).re:ℂ) := by
      apply Complex.ext
      · rfl
      · exact (Complex.nonneg_iff.mp (trace_projection_nonneg τ he)).2.symm
    rw [hre]
    push_cast
    rfl
  have htpos : 0<1-(τ.map e).re := by linarith
  have hc : τ.map ((1-e)*Y*(1-e))=τ.map Y-τ.map (e*Y) := by
    rw [τ.tracial ((1-e)*Y) (1-e),← mul_assoc,hp.isIdempotentElem.eq,sub_mul,one_mul,map_sub]
  rw [hr,hc,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htpos]
  have heB : 0≤2*b := by linarith [norm_nonneg (τ.map Y)]
  have hnum : ‖τ.map Y-τ.map (e*Y)‖≤2*b := (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ (1-(τ.map e).re)⁻¹*(2*b) := mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr htpos.le)
    _ ≤ η⁻¹*(2*b) := mul_le_mul_of_nonneg_right (inv_anti₀ hη (by linarith)) heB
    _ = _ := by ring

theorem gap_trace_small (v : PartialUnitary (ConcreteAlgebra M))
    (k l : ℤ) (Y Z : ConcreteAlgebra M) (c : ℂ) {a b : ℝ}
    (ha : 0≤a) (hb : ‖c‖≤b) (hZ : ‖Z‖≤1)
    (hcomp : (traceNorm τ (v.support*Y*v.support-c • v.support))^2≤a*(τ.map v.support).re) :
    ‖τ.map (v.power k*Y*v.power l*Z)‖≤(Real.sqrt a+b)*(τ.map v.support).re := by
  let q := traceNorm τ v.support
  let e := traceNorm τ (v.support*Y*v.support-c • v.support)
  have hq : 0≤q := traceNorm_nonneg τ _
  have he : 0≤e := traceNorm_nonneg τ _
  have hsq : q^2=(τ.map v.support).re := traceNorm_projection_sq τ v.projection
  have hs : (Real.sqrt a)^2=a := Real.sq_sqrt ha
  have hsn := Real.sqrt_nonneg a
  have herr : e≤Real.sqrt a*q := by
    change e^2≤a*(τ.map v.support).re at hcomp
    rw [← hsq] at hcomp
    have hn := mul_nonneg hsn hq
    nlinarith [sq_nonneg (e-Real.sqrt a*q)]
  have hbound := gap_trace_bound τ v k l Y Z c
  change _≤(e+‖c‖*q)*q*‖Z‖ at hbound
  calc
    _ ≤ (e+‖c‖*q)*q*1 := hbound.trans (mul_le_mul_of_nonneg_left hZ
        (mul_nonneg (add_nonneg he (mul_nonneg (norm_nonneg _) hq)) hq))
    _ ≤ (Real.sqrt a*q+b*q)*q := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right (add_le_add herr (mul_le_mul_of_nonneg_right hb hq)) hq
    _ = (Real.sqrt a+b)*(τ.map v.support).re := by rw [← hsq]; ring

end

end KKLocalPatching
end

end OAI
