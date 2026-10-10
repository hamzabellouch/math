import Mathlib
import OAI.Analysis.FreeWords.ProjectionStructure

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

end KKProjectionSupport

namespace KKProjectionSupport

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem partial_of_initial_projection {v : A} (hp : IsStarProjection (star v*v)) : Partial v := by
  let p := star v*v
  have hp2 : p*p=p := hp.isIdempotentElem.eq
  have hsp : star p=p := hp.isSelfAdjoint.star_eq
  have hz : star (v*p-v)*(v*p-v)=0 := by
    calc
      star (v*p-v)*(v*p-v) = p*p*p-p*p-p*p+p := by
        simp only [star_sub, star_mul, hsp, p]
        noncomm_ring
      _ = 0 := by simp only [hp2, sub_self, zero_sub, neg_add_cancel]
  have he := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  simpa only [Partial, sub_eq_zero, p, mul_assoc] using he

theorem polar_initial_support {v S a : A} (hv : Partial v) (hS : IsSelfAdjoint S)
    (hva : v*S=a) (hSS : S*S=star a*a) : (star v*v)*S=S := by
  let p := star v*v
  have hp := partial_initial hv
  have hep := projection_sub (IsStarProjection.one A) hp (mul_one _)
  have he2 : (1-p)*(1-p)=1-p := hep.isIdempotentElem.eq
  have hsp : star p=p := hp.isSelfAdjoint.star_eq
  have hSpS : S*p*S=S*S := by
    calc
      S*p*S=star (v*S)*(v*S) := by rw [star_mul,hS.star_eq]; simp only [p,mul_assoc]
      _=star a*a := by rw [hva]
      _=S*S := hSS.symm
  have hz : star ((1-p)*S)*((1-p)*S)=0 := by
    calc
      star ((1-p)*S)*((1-p)*S)=S*((1-p)*(1-p))*S := by
        simp only [star_mul,star_sub,star_one,hS.star_eq,hsp,mul_assoc]
      _=S*(1-p)*S := by rw [he2]
      _=S*S-S*p*S := by noncomm_ring
      _=0 := by rw [hSpS,sub_self]
  have he := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [sub_mul,one_mul] at he
  exact (sub_eq_zero.mp he).symm

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partial_unitary_extension (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hM : IsFactor M) (v : ConcreteAlgebra M) (hv : Partial v) :
    ∃ u : unitary (ConcreteAlgebra M), (u : ConcreteAlgebra M)*(star v*v)=v := by
  have hp := partial_initial hv
  have hq := partial_final hv
  have hpc := projection_sub (IsStarProjection.one _) hp (mul_one _)
  have hqc := projection_sub (IsStarProjection.one _) hq (mul_one _)
  have hτ : τ.map (1-star v*v)=τ.map (1-v*star v) := by rw [map_sub,map_sub,τ.tracial]
  obtain ⟨w,hwp,hqw⟩ := projection_equivalent_of_trace M τ hM _ _ hpc hqc hτ
  have hw : Partial w := partial_of_initial_projection (hwp.symm ▸ hpc)
  have hwpc : w*(1-star v*v)=w := by rw [← hwp,←mul_assoc]; exact hw
  have hqcw : (1-v*star v)*w=w := by rw [← hqw]; exact hw
  have hc := orthogonal_of_residual hv (IsStarProjection.one _) (IsStarProjection.one _)
    (mul_one _) (one_mul _) hwpc hqcw
  have hcw : star w*v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hc.1
  have hcs : w*star v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hc.2
  have hunit : v+w ∈ unitary (ConcreteAlgebra M) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [star_add,add_mul,mul_add,mul_add,hc.1,hcw,add_zero,zero_add,hwp]
      abel
    · rw [star_add,mul_add,add_mul,add_mul,hc.2,hcs,add_zero,zero_add,hqw]
      abel
  refine ⟨⟨v+w,hunit⟩,?_⟩
  change (v+w)*(star v*v)=v
  rw [add_mul,←mul_assoc,←mul_assoc,hv,hcs,zero_mul,add_zero]

end

end KKProjectionSupport
end

end OAI
