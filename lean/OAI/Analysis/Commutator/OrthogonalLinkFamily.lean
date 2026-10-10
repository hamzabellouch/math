import Mathlib
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.PartialIsometryOrder

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

def OrthogonalLinks (S : Set (Link M e f)) : Prop :=
  S.Pairwise (fun v w => star v.val*w.val=0)

lemma exists_maximal_orthogonalLinks :
    ∃ S : Set (Link M e f),Maximal (OrthogonalLinks M e f) S := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c,?_,fun s hs => Set.subset_sUnion_of_mem hs⟩
  intro v hv w hw hne
  obtain ⟨s,hs,hvs⟩ := hv
  obtain ⟨t,ht,hwt⟩ := hw
  rcases hchain.total hs ht with hst|hts
  · exact hc ht (hst hvs) hwt hne
  · exact hc hs hvs (hts hwt) hne

def familySpace (S : Set (Link M e f)) : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x}).topologicalClosure

instance (S : Set (Link M e f)) : CompleteSpace (familySpace M e f S) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

lemma familySpace_generator (S : Set (Link M e f)) {v : Link M e f} (hv : v∈S) (ξ : H) :
    v.val ξ∈familySpace M e f S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v,hv,ξ,rfl⟩)

lemma familySpace_invariant (S : Set (Link M e f)) {a : H →L[ℂ] H}
    (ha : a∈Set.centralizer (M : Set (H →L[ℂ] H))) :
    ∀ x∈familySpace M e f S,a x∈familySpace M e f S := by
  intro x hx
  apply closure_minimal (t:={x | a x∈familySpace M e f S}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage a.continuous) hx
  change Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x} ≤
    (familySpace M e f S).comap a.toLinearMap
  apply Submodule.span_le.mpr
  rintro y ⟨v,hv,ξ,rfl⟩
  have he : a (v.val ξ)=v.val (a ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (ha v.val v.mem).symm
  change a (v.val ξ)∈familySpace M e f S
  rw [he]
  exact familySpace_generator M e f S hv _

lemma familySpace_projection_mem (S : Set (Link M e f)) :
    (familySpace M e f S).starProjection∈M := by
  change (familySpace M e f S).starProjection∈M.carrier
  rw [←M.centralizer_centralizer']
  intro a ha
  have hsa : star a∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
    intro b hb
    simpa only [star_mul,star_star] using congrArg star (ha (star b) (M.star_mem' hb)).symm
  exact (projection_commutes_of_invariant _ a (familySpace_invariant M e f S ha)
    (familySpace_invariant M e f S hsa)).symm

lemma familySpace_projection_mul (S : Set (Link M e f)) {v : Link M e f} (hv : v∈S) :
    (familySpace M e f S).starProjection*v.val=v.val := by
  ext ξ
  exact Submodule.starProjection_eq_self_iff.mpr (familySpace_generator M e f S hv ξ)

lemma familySpace_target_mul (S : Set (Link M e f)) (hf : IsStarProjection f) :
    f*(familySpace M e f S).starProjection=(familySpace M e f S).starProjection := by
  have hfix : ∀ x∈familySpace M e f S,f x=x := by
    intro x hx
    apply closure_minimal (t:={x | f x=x}) ?_
      (isClosed_eq f.continuous continuous_id) hx
    have hspan : Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x} ≤
        LinearMap.ker (f-1).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨v,hv,ξ,rfl⟩
      change f (v.val ξ)-v.val ξ=0
      rw [show f (v.val ξ)=v.val ξ from congrArg (fun T : H →L[ℂ] H => T ξ) (v.target_mul hf),sub_self]
    intro y hy
    have he := hspan hy
    exact sub_eq_zero.mp he
  ext x
  exact hfix _ ((familySpace M e f S).starProjection_apply_mem x)

theorem maximal_family_spans (hM : FactorCorner.IsFactor M)
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f) (hne : e≠0)
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
    FactorCorner.exists_linking_partialIsometry M hM heM (M.sub_mem hfM hqM) he hr hne hrne
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
