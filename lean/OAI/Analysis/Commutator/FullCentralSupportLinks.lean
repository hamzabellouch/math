import Mathlib
import OAI.Analysis.Commutator.OrthogonalLinkFamily

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_nonzero_corner_of_full_support (M : VonNeumannAlgebra H)
    {e f : H →L[ℂ] H} (hsupport : (supportSpace M e).starProjection=1) (hff : f≠0) :
    ∃ a∈M, f*a*e≠0 := by
  by_contra! h
  have hz : ∀ x∈supportSpace M e, f x=0 := by
    intro x hx
    apply closure_minimal (t := {x | f x=0}) ?_
      (isClosed_eq f.continuous continuous_const) hx
    have hspan : Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x} ≤ LinearMap.ker f.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨a,ha,ξ,rfl⟩
      exact congrArg (fun T : H →L[ℂ] H => T ξ) (h a ha)
    exact hspan
  apply hff
  ext x
  have hm := (supportSpace M e).starProjection_apply_mem x
  rw [hsupport] at hm
  exact hz x hm

theorem exists_linking_partialIsometry_of_full_support (M : VonNeumannAlgebra H)
    {e f : H →L[ℂ] H} (he : e∈M) (hfM : f∈M)
    (hpe : IsStarProjection e) (hpf : IsStarProjection f)
    (hsupport : (supportSpace M e).starProjection=1) (hnf : f≠0) :
    ∃ v∈M, v≠0 ∧ v*star v*v=v ∧ star v*v≤e ∧ v*star v≤f := by
  obtain ⟨a,ha,hna⟩ := exists_nonzero_corner_of_full_support M hsupport hnf
  let x := f*a*e
  have hx : x∈M := M.mul_mem (M.mul_mem hfM ha) he
  have hfx : f*x=x := by dsimp only [x]; rw [←mul_assoc,←mul_assoc,hpf.isIdempotentElem.eq]
  have hxe : x*e=x := by dsimp only [x]; rw [mul_assoc,hpe.isIdempotentElem.eq]
  refine ⟨Polar.partialIsometry x,Polar.partialIsometry_mem_vonNeumann M hx,?_,
    Polar.partialIsometry_triple x,?_,?_⟩
  · intro hzero
    apply hna
    have hfact := Polar.factorization x
    rw [hzero,zero_mul] at hfact
    exact hfact.symm
  · rw [Polar.partialIsometry_initial]
    exact Polar.rightSupport_le x e hpe hxe
  · exact Polar.leftSupport_le x f hpf hfx

end Kadison.FactorCorner

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

theorem maximal_family_spans_of_full_support
    (hsupport : (FactorCorner.supportSpace M e).starProjection=1)
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (S : Set (Link M e f)) (hS : Maximal (OrthogonalLinks M e f) S) :
    (familySpace M e f S).starProjection=f := by
  let q := (familySpace M e f S).starProjection
  have hq : IsStarProjection q := isStarProjection_starProjection
  have hqM : q∈M := familySpace_projection_mem M e f S
  have hfq : f*q=q := familySpace_target_mul M e f S hf
  have hqf : q*f=q := by simpa only [star_mul,hq.isSelfAdjoint.star_eq,hf.isSelfAdjoint.star_eq] using congrArg star hfq
  have hr : IsStarProjection (f-q) := hq.sub_of_mul_eq_left hf hqf
  by_contra hqne
  have hrne : f-q≠0 := by
    intro hz
    exact hqne (sub_eq_zero.mp hz).symm
  obtain ⟨w,hwM,hwne,hwtr,hwsrc,hwtgt⟩ :=
    FactorCorner.exists_linking_partialIsometry_of_full_support M heM (M.sub_mem hfM hqM) he hr hsupport hrne
  let w' : Link M e (f-q) := ⟨w,hwM,hwtr,hwsrc,hwtgt⟩
  have hrw : (f-q)*w=w := w'.target_mul hr
  have hwf : w*star w≤f := hwtgt.trans (sub_le_self _ hq.nonneg)
  let v : Link M e f := ⟨w,hwM,hwtr,hwsrc,hwf⟩
  have hvorth (u : Link M e f) (hu : u∈S) : star u.val*w=0 := by
    have hqu : q*u.val=u.val := familySpace_projection_mul M e f S hu
    have hsuq : star u.val*q=star u.val := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq] using congrArg star hqu
    have huf : star u.val*f=star u.val := by
      simpa only [star_mul,hf.isSelfAdjoint.star_eq] using congrArg star (u.target_mul hf)
    calc
      _=star u.val*((f-q)*w) := by rw [hrw]
      _=0 := by rw [←mul_assoc,mul_sub,huf,hsuq,sub_self,zero_mul]
  have hins : OrthogonalLinks M e f (insert v S) := by
    intro a ha b hb hne'
    rcases ha with rfl|ha <;> rcases hb with rfl|hb
    · exact (hne' rfl).elim
    · simpa only [star_mul,star_star,star_zero] using congrArg star (hvorth b hb)
    · exact hvorth a ha
    · exact hS.1 ha hb hne'
  have hvS : v∈S := hS.2 hins (Set.subset_insert v S) (Set.mem_insert v S)
  have hqw : q*w=w := familySpace_projection_mul M e f S hvS
  have hqr : q*(f-q)=0 := by rw [mul_sub,hqf,hq.isIdempotentElem.eq,sub_self]
  have : q*w=0 := by calc
    _=q*((f-q)*w) := by rw [hrw]
    _=0 := by rw [←mul_assoc,hqr,zero_mul]
  exact hwne (hqw.symm.trans this)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
