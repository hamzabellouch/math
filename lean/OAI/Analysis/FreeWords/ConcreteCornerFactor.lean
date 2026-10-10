import Mathlib
import OAI.Analysis.FreeWords.ConcreteCornerAlgebra
import OAI.Analysis.FreeWords.CornerCentralScalar
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKConcreteCorner

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : Submodule ℂ H) [CompleteSpace S]

variable (M : VonNeumannAlgebra H) (hp : S.starProjection ∈ M)

theorem cornerAlgebra_factor (τ : FaithfulNormalTrace M) (hF : IsFactor M)
    (hp0 : projection S M hp ≠ 0) : IsFactor (cornerAlgebra S M) := by
  intro x hx
  let p := projection S M hp
  let a := liftLinear S M hp x
  have hpa : p*a=a := (lift_supported S M hp x).1
  have hap : a*p=a := (lift_supported S M hp x).2
  have hco : ∀ y : ConcreteAlgebra M, a*y*p=p*y*a := by
    intro y
    have hh := congrArg (liftLinear S M hp) (hx (restrict S M hp y)).eq
    rw [lift_mul,lift_mul,lift_restrict] at hh
    change a*(p*y*p)=(p*y*p)*a at hh
    calc
      a*y*p = (a*p)*y*p := by rw [hap]
      _ = a*(p*y*p) := by simp only [mul_assoc]
      _ = (p*y*p)*a := hh
      _ = p*y*(p*a) := by simp only [mul_assoc]
      _ = p*y*a := by rw [hpa]
  obtain ⟨c,hc⟩ := corner_central_scalar τ hF p a (projection_isStar' S M hp) hp0 hco
  refine ⟨c,lift_injective S M hp ?_⟩
  simpa only [map_smul,lift_one] using hc

include hp in
theorem cornerAlgebra_diffuse (hD : IsDiffuse M) : IsDiffuse (cornerAlgebra S M) := by
  intro q hq hq0
  let p := projection S M hp
  let a := liftLinear S M hp q
  have ha : IsStarProjection a := lift_projection S M hp q hq
  have ha0 : a≠0 := by
    intro hh
    exact hq0 (lift_injective S M hp (hh.trans (map_zero _).symm))
  obtain ⟨b,hb,hb0,hba,hbb⟩ := hD a ha ha0
  have hap : a*p=a := (lift_supported S M hp q).2
  have hbp : b*p=b := by rw [← hbb,mul_assoc,hap,hbb]
  have hps : star p=p := (projection_isStar' S M hp).isSelfAdjoint.star_eq
  have hpb : p*b=b := by
    simpa only [star_mul,hps,hb.isSelfAdjoint.star_eq] using congrArg star hbp
  let B := restrict S M hp b
  have hB : liftLinear S M hp B=b := by
    change liftLinear S M hp (restrict S M hp b)=b
    rw [lift_restrict,hpb,hbp]
  refine ⟨B,?_,?_,?_,?_⟩
  · constructor
    · change B*B=B
      apply lift_injective S M hp
      rw [lift_mul,hB,hb.isIdempotentElem.eq]
    · change star B=B
      apply lift_injective S M hp
      rw [lift_star,hB,hb.isSelfAdjoint.star_eq]
  · intro hh
    exact hb0 (by rw [← hB,hh,map_zero])
  · intro hh
    exact hba (by rw [← hB,hh])
  · apply lift_injective S M hp
    rw [lift_mul,hB]
    exact hbb

end

end KKConcreteCorner
end

end OAI
