import Mathlib
import OAI.Analysis.FreeWords.MatrixCommutant
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : VonNeumannAlgebra H}

variable (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)

def commutantTrace (τ : FaithfulNormalTrace M) : FaithfulNormalTrace (matrixCommutant ρ) where
  map := τ.map.comp (commutantInclusion ρ).toLinearMap
  positive x hx := τ.positive _ hx
  normalized := τ.normalized
  tracial x y := by
    change τ.map (commutantInclusion ρ x*commutantInclusion ρ y)=
      τ.map (commutantInclusion ρ y*commutantInclusion ρ x)
    exact τ.tracial _ _
  faithful x hx hτ := commutantInclusion_injective ρ (τ.faithful _ hx hτ)
  normal r := by
    let f : WeakAlgebra (matrixCommutant ρ) → WeakAlgebra M :=
      fun T => ⟨T.val,((mem_matrixCommutant ρ _).mp T.property).1⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    exact (τ.normal r).comp hf.continuousOn (fun T hT => hT)

@[simp] theorem commutantTrace_apply (τ : FaithfulNormalTrace M) (x : ConcreteAlgebra (matrixCommutant ρ)) :
    (commutantTrace ρ τ).map x=τ.map (commutantInclusion ρ x) := rfl

@[simp] theorem commutantTrace_norm (τ : FaithfulNormalTrace M) (x : ConcreteAlgebra (matrixCommutant ρ)) :
    traceNorm (commutantTrace ρ τ) x=traceNorm τ (commutantInclusion ρ x) := by
  simp only [traceNorm,commutantTrace_apply,map_mul,map_star]

theorem cornerLift_zero (o : ι) : cornerLift ρ o 0=0 := by simp [cornerLift]

theorem matrixCommutant_diffuse [Nonempty ι] (hD : IsDiffuse M) : IsDiffuse (matrixCommutant ρ) := by
  intro p hp hp0
  let o : ι := Classical.choice inferInstance
  let b := commutantInclusion ρ p
  let e := matrixUnit ρ o o
  have hb : IsStarProjection b := hp.map _
  have he : IsStarProjection e := ⟨matrixUnit_mul_same ρ o o o,matrixUnit_star ρ o o⟩
  have hbe : Commute b e := inclusion_commute ρ p o o
  let a := e*b*e
  have haeq : a=e*b := by
    change e*b*e=e*b
    rw [mul_assoc,hbe.eq,← mul_assoc,he.isIdempotentElem.eq]
  have ha : IsStarProjection a := by rw [haeq]; exact he.mul hb hbe.symm
  have hab : cornerLift ρ o a=b := cornerLift_fixed ρ o b (inclusion_commute ρ p)
  have ha0 : a≠0 := by
    intro hh
    have hh' : b=0 := by rw [← hab,hh,cornerLift_zero]
    exact hp0 (commutantInclusion_injective ρ hh')
  obtain ⟨q,hq,hq0,hqa,hqq⟩ := hD a ha ha0
  have hae : a*e=a := by dsimp [a]; rw [mul_assoc,he.isIdempotentElem.eq]
  have hqe : q*e=q := by rw [← hqq,mul_assoc,hae,hqq]
  have heq : e*q=q := by
    simpa only [star_mul,he.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq] using congrArg star hqe
  let c := cornerLift ρ o q
  have hc : IsStarProjection c := by
    constructor
    · change cornerLift ρ o q*cornerLift ρ o q=cornerLift ρ o q
      rw [cornerLift_mul_cornerLift,hqe,hq.isIdempotentElem.eq]
    · change star (cornerLift ρ o q)=cornerLift ρ o q
      rw [cornerLift_star,hq.isSelfAdjoint.star_eq]
  have hcompress : e*c*e=q := by
    change matrixUnit ρ o o*cornerLift ρ o q*matrixUnit ρ o o=q
    rw [cornerLift_compression]
    change e*q*e=q
    rw [heq,hqe]
  let Q := inCommutant ρ c (cornerLift_commute ρ o q)
  refine ⟨Q,?_,?_,?_,?_⟩
  · constructor
    · apply (commutantInclusion_injective ρ)
      simpa only [map_mul,Q,inclusion_inCommutant] using hc.isIdempotentElem.eq
    · apply (commutantInclusion_injective ρ)
      simpa only [map_star,Q,inclusion_inCommutant] using hc.isSelfAdjoint.star_eq
  · intro hh
    have hcz : c=0 := congrArg (commutantInclusion ρ) hh
    exact hq0 (by simpa only [hcz,mul_zero,zero_mul] using hcompress.symm)
  · intro hh
    have hcb : c=b := congrArg (commutantInclusion ρ) hh
    exact hqa (by rw [← hcompress,hcb])
  · apply commutantInclusion_injective ρ
    change c*b=c
    rw [← hab]
    change cornerLift ρ o q*cornerLift ρ o a=cornerLift ρ o q
    rw [cornerLift_mul_cornerLift,hqe,hqq]

end

end KKMatrixQuantization
end

end OAI
