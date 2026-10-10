import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.OrthogonalLinkSums

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.CyclicDecomposition

open PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : StarSubalgebra ℂ (H →L[ℂ] H))

def full : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' := by
    apply Set.eq_univ_of_univ_subset
    exact (Set.subset_centralizer_centralizer (S := (Set.univ : Set (H →L[ℂ] H))))

abbrev ProjLink := Link (full (H:=H)) 1 1

def cyclicLink (ξ : H) : ProjLink (H:=H) where
  val := (cyclicSubspace A ξ).starProjection
  mem := by trivial
  triple := by
    have hp : IsStarProjection (cyclicSubspace A ξ).starProjection := isStarProjection_starProjection
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq]
  source_le := by
    have hp : IsStarProjection (cyclicSubspace A ξ).starProjection := isStarProjection_starProjection
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
    exact hp.le_one
  target_le := by
    have hp : IsStarProjection (cyclicSubspace A ξ).starProjection := isStarProjection_starProjection
    rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
    exact hp.le_one

def Good (S : Set (ProjLink (H:=H))) : Prop :=
  OrthogonalLinks (full (H:=H)) 1 1 S ∧ ∀ v∈S, ∃ ξ : H,ξ≠0 ∧ v=cyclicLink A ξ

lemma exists_maximal_good : ∃ S : Set (ProjLink (H:=H)),Maximal (Good A) S := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c,⟨?_,?_⟩,fun s hs => Set.subset_sUnion_of_mem hs⟩
  · intro v hv w hw hne
    obtain ⟨s,hs,hvs⟩ := hv
    obtain ⟨t,ht,hwt⟩ := hw
    rcases hchain.total hs ht with hst|hts
    · exact (hc ht).1 (hst hvs) hwt hne
    · exact (hc hs).1 hvs (hts hwt) hne
  · rintro v ⟨s,hs,hvs⟩
    exact (hc hs).2 v hvs

variable {A}

lemma good_projection {S : Set (ProjLink (H:=H))} (hS : Good A S) {v : ProjLink (H:=H)} (hv : v∈S) :
    IsStarProjection v.val := by
  obtain ⟨ξ,_,rfl⟩ := hS.2 v hv
  exact isStarProjection_starProjection

lemma good_commutes {S : Set (ProjLink (H:=H))} (hS : Good A S) {v : ProjLink (H:=H)} (hv : v∈S)
    {a : H →L[ℂ] H} (ha : a∈A) : a*v.val=v.val*a := by
  obtain ⟨ξ,_,rfl⟩ := hS.2 v hv
  exact cyclic_projection_mem_commutant A ξ a ha

lemma family_invariant {S : Set (ProjLink (H:=H))} (hS : Good A S)
    {a : H →L[ℂ] H} (ha : a∈A) :
    ∀ x∈familySpace (full (H:=H)) 1 1 S,a x∈familySpace (full (H:=H)) 1 1 S := by
  let K := familySpace (full (H:=H)) 1 1 S
  intro x hx
  apply closure_minimal (t:={x | a x∈K}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage a.continuous) hx
  change Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x} ≤ K.comap a.toLinearMap
  apply Submodule.span_le.mpr
  rintro y ⟨v,hv,ξ,rfl⟩
  have he : a (v.val ξ)=v.val (a ξ) := congrArg (fun T : H →L[ℂ] H => T ξ) (good_commutes hS hv ha)
  change a (v.val ξ)∈K
  rw [he]
  exact familySpace_generator _ _ _ S hv _

theorem maximal_spans {S : Set (ProjLink (H:=H))} (hS : Maximal (Good A) S) :
    (familySpace (full (H:=H)) 1 1 S).starProjection=1 := by
  classical
  let K := familySpace (full (H:=H)) 1 1 S
  let q := K.starProjection
  have hq : IsStarProjection q := isStarProjection_starProjection
  have hqcomm {a : H →L[ℂ] H} (ha : a∈A) : q*a=a*q :=
    projection_commutes_of_invariant K a (family_invariant hS.1 ha)
      (family_invariant hS.1 (A.star_mem' ha))
  by_contra hneq
  have hx : ∃ x : H,q x≠x := by
    by_contra! h
    exact hneq (ContinuousLinearMap.ext h)
  obtain ⟨x,hx⟩ := hx
  let ξ := x-q x
  have hξ : ξ≠0 := by intro h; exact hx (sub_eq_zero.mp h).symm
  have hqξ : q ξ=0 := by
    change q (x-q x)=0
    rw [map_sub,show q (q x)=q x from congrArg (fun T : H →L[ℂ] H => T x) hq.isIdempotentElem.eq,sub_self]
  have hker : cyclicSubspace A ξ ≤ q.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨a,ha,rfl⟩
      change q (a ξ)=0
      rw [show q (a ξ)=a (q ξ) from congrArg (fun T : H →L[ℂ] H => T ξ) (hqcomm ha),hqξ,map_zero]
    · exact q.isClosed_ker
  let v := cyclicLink A ξ
  have hvp : IsStarProjection v.val := isStarProjection_starProjection
  have hqv : q*v.val=0 := by
    ext y
    exact hker ((cyclicSubspace A ξ).starProjection_apply_mem y)
  have hvne : v.val≠0 := by
    intro hz
    have ht := Submodule.starProjection_eq_self_iff.mpr (mem_cyclicSubspace_self A ξ)
    change v.val ξ=ξ at ht
    rw [hz,zero_apply] at ht
    exact hξ ht.symm
  have hort {w : ProjLink (H:=H)} (hw : w∈S) : star w.val*v.val=0 := by
    have hqw : q*w.val=w.val := familySpace_projection_mul _ _ _ S hw
    have hwq : star w.val*q=star w.val := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq] using congrArg star hqw
    calc
      _=(star w.val*q)*v.val := by rw [hwq]
      _=0 := by rw [mul_assoc,hqv,mul_zero]
  have hgood : Good A (insert v S) := by
    refine ⟨?_,?_⟩
    · intro a ha b hb hne
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · exact (hne rfl).elim
      · simpa only [star_mul,star_star,star_zero] using congrArg star (hort hb)
      · exact hort ha
      · exact hS.1.1 ha hb hne
    · intro w hw
      rcases hw with rfl|hw
      · exact ⟨ξ,hξ,rfl⟩
      · exact hS.1.2 w hw
  have hvS : v∈S := hS.2 hgood (Set.subset_insert _ _) (Set.mem_insert _ _)
  have he : q*v.val=v.val := familySpace_projection_mul _ _ _ S hvS
  exact hvne (he.symm.trans hqv)

structure Decomposition (A : StarSubalgebra ℂ (H →L[ℂ] H)) where
  I : Type u
  ξ : I → H
  nonzero : ∀ i,ξ i≠0
  cross : ∀ i j,i≠j → (cyclicSubspace A (ξ i)).starProjection*(cyclicSubspace A (ξ j)).starProjection=0
  strong : ∀ x : H,Tendsto (fun s : Finset I => (∑ i∈s,(cyclicSubspace A (ξ i)).starProjection) x) atTop (𝓝 x)

variable (A)

theorem exists_decomposition : Nonempty (Decomposition A) := by
  classical
  obtain ⟨S,hS⟩ := exists_maximal_good A
  choose ξ hξ he using fun v : S => hS.1.2 v.val v.property
  have hval (v : S) : v.val.val=(cyclicSubspace A (ξ v)).starProjection := congrArg Link.val (he v)
  have hfin (v : S) : v.val.final=(cyclicSubspace A (ξ v)).starProjection := by
    rw [Link.final,(good_projection hS.1 v.property).isSelfAdjoint.star_eq,
      (good_projection hS.1 v.property).isIdempotentElem.eq,hval]
  refine ⟨⟨S,ξ,hξ,?_,?_⟩⟩
  · intro v w hne
    have ht := family_cross _ _ _ S hS.1.1 hne
    rw [(good_projection hS.1 v.property).isSelfAdjoint.star_eq,hval,hval] at ht
    exact ht
  · intro x
    have ht := finiteProjection_tendsto _ _ _ S hS.1.1 (IsStarProjection.one _) (maximal_spans hS) x
    simpa only [finiteProjection,hfin,one_apply_eq_self] using ht

end Kadison.CyclicDecomposition

end

end
end

end OAI
