import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingEquality
import OAI.Combinatorics.Chromatic.Walls.MutationSimpleIncoming

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma literalIncomingRay_eq_one_of_none (l : List (WallUnitDatum M)) (r : M)
    (hn : ∀u∈l,¬OnPositiveRay r u.root) : literalIncomingRay Ω l r=1 := by
  classical
  unfold literalIncomingRay
  have hf : l.filter (fun u=>OnPositiveRay r u.root)=[]:=by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro u hu
    have H:=List.mem_filter.mp hu
    exact hn u H.1 (of_decide_eq_true H.2)
  rw [hf,List.map_nil,List.prod_nil]
lemma literalIncoming_simple_nonsimple (r : M)
    (hn : ∀i,¬OnPositiveRay r (simpleRoot C i)) : literalIncomingRay Ω (simpleIncomingList C) r=1 := by
  apply literalIncomingRay_eq_one_of_none
  intro u hu
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hu
  exact hn i

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
lemma nonsimple_incoming_at_far_through (N d : ℕ) (r : M) (hd : 0<d) (hr : HasRootDegree C d r)
    (hn : ∀i,¬OnPositiveRay r (simpleRoot C i)) (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) (e r) (B.flip (e r)) k)
    (b : ℝ) (hb : ∀a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k,a<b) :
    ∀n≤N,coeff n (chartZero LaurentRay.vUnit Ω C
      ((k+b • B.flip (e r)).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val=coeff n 1 := by
  have HE:=literal_incoming_at_far_through Ω C e he B hB hcomp L hdeg
    (simpleIncomingList C) (simpleIncomingList_allowed C) N d r hd hr k H b hb
  rw [literalIncoming_simple_nonsimple Ω C r hn] at HE
  exact HE

variable (hΩ : ∀m,Ω m m=0) (coord : M →+ (I → ℤ)) (pc : I) (pos : Bool)
include he hB hcomp hdeg in
lemma pushed_nonsimple_incoming_at_far (d dr : ℕ) (r : M) (hdr : 0<dr) (hr : HasRootDegree C dr r)
    (hn : ∀i,¬OnPositiveRay r (simpleRoot C i)) (k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C ((mutationSize Ω C pc+1)*d)) (e r) (B.flip (e r)) k)
    (b : ℝ) (hb : ∀a∈lineEvents (realRootsThrough e C ((mutationSize Ω C pc+1)*d)) (B.flip (e r)) k,a<b) :
    coeff d (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
      (chartZero LaurentRay.vUnit Ω C ((k+b • B.flip (e r)).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val)=coeff d 1 := by
  rw [←mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit]
  exact mutationCompletion_congr_through Ω hΩ C coord pc pos LaurentRay.vUnit _ _ d _ le_rfl
    (nonsimple_incoming_at_far_through Ω C e he B hB hcomp L hdeg _ dr r hdr hr hn k H b hb)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : M) (hp : Ω p p=0)
lemma mutationIncomingLabel_nsmul (a : ℕ) (m : M) :
    mutationIncomingLabel Ω p (a • m)=a • mutationIncomingLabel Ω p m := by
  by_cases hm : 0≤Ω p m
  · rw [mutationIncomingLabel_nonnegative Ω p m hm,
      mutationIncomingLabel_nonnegative Ω p (a • m)]
    rw [map_nsmul,nsmul_eq_mul]
    exact mul_nonneg (Int.natCast_nonneg _) hm
  · have hm' : Ω p m≤0:=le_of_lt (lt_of_not_ge hm)
    rw [mutationIncomingLabel_nonpositive Ω p m hm',
      mutationIncomingLabel_nonpositive Ω p (a • m),map_nsmul]
    rw [map_nsmul,nsmul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hm'
include hp in
lemma mutationIncomingLabel_positive_ray_iff (r m : M) :
    OnPositiveRay (mutationIncomingLabel Ω p r) (mutationIncomingLabel Ω p m)↔OnPositiveRay r m := by
  constructor
  · rintro ⟨a,b,ha,hb,he⟩
    refine ⟨a,b,ha,hb,?_⟩
    apply (mutationIncomingLabelEquiv Ω p hp).injective
    change mutationIncomingLabel Ω p (a • m)=mutationIncomingLabel Ω p (b • r)
    simpa only [mutationIncomingLabel_nsmul] using he
  · rintro ⟨a,b,ha,hb,he⟩
    exact ⟨a,b,ha,hb,by simpa only [mutationIncomingLabel_nsmul] using congrArg (mutationIncomingLabel Ω p) he⟩

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (pc : I)
lemma mutationIncomingLabel_simple (i : I) (hi : i≠pc) :
    mutationIncomingLabel Ω (simpleRoot C pc) (simpleRoot C i)=simpleRoot (mutatedRoots Ω C pc) i := by
  rw [mutatedRoot_off Ω C pc i hi]
  rfl
lemma mutationIncomingLabel_simple_ray_iff (hΩ : ∀m,Ω m m=0)
    (i : I) (hi : i≠pc) (r : M) :
    OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r) (simpleRoot (mutatedRoots Ω C pc) i)↔
      OnPositiveRay r (simpleRoot C i) := by
  rw [←mutationIncomingLabel_simple Ω C pc i hi]
  exact mutationIncomingLabel_positive_ray_iff Ω (simpleRoot C pc) (hΩ _) r (simpleRoot C i)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
