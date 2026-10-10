import OAI.Analysis.CircleDomains.Uniformization.ConformalComposition
import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletion

namespace OAI

/-!
# The published finite circle-uniformization input

Conway, *Functions of One Complex Variable II*, GTM 159 (1995),
Theorem 15.7.9, p. 106, gives circle uniformization of nondegenerate
finitely connected regions. `FiniteCircleUniformization` records only
its existence conclusion on the sphere, omitting normalization and
uniqueness. It is an explicit proposition parameter, not an axiom.

The complement components of a finite family of disjoint closed
connected sets are identified below. This checks the finiteness and
nondegeneracy hypotheses for completed surfaces, also after an arbitrary
sphere homeomorphism such as compact metric uniformization.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def FiniteNondegenerateComplement (U : Set Sphere) : Prop :=
  (connectedComponentIn Uᶜ '' Uᶜ).Finite ∧
    ∀ p ∈ Uᶜ, (connectedComponentIn Uᶜ p).Nontrivial

def FiniteCircleUniformization : Prop :=
  ∀ U : Set Sphere, IsOpen U → IsConnected U → Uᶜ.Nonempty →
    FiniteNondegenerateComplement U →
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V

theorem connectedComponentIn_finite_disjoint_closed
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    {i : I} {p : X} (hp : p ∈ C i) :
    connectedComponentIn (⋃ j, C j) p = C i := by
  classical
  let R : Set X := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover : (⋃ j, C j) ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hsub : connectedComponentIn (⋃ j, C j) p ⊆ C i := by
    have hs := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := ⋃ j, C j) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hCR.inter_eq, inter_empty])
    rcases hs with h | h
    · exact h
    · exact fun x hx => (Set.disjoint_left.mp hCR hp
        (h (mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hp⟩)))).elim
  exact hsub.antisymm ((hconn i).subset_connectedComponentIn hp (subset_iUnion C i))

theorem finite_nondegenerate_complement_of_disjoint_closed
    {I : Type*} [Finite I] {U : Set Sphere}
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    (hneq : ∀ i, (C i).Nontrivial) (hcomp : Uᶜ = ⋃ i, C i) :
    FiniteNondegenerateComplement U := by
  have hcomponent {p : Sphere} (hp : p ∈ Uᶜ) :
      ∃ i, connectedComponentIn Uᶜ p = C i := by
    rw [hcomp] at hp ⊢
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨i, connectedComponentIn_finite_disjoint_closed C hC hconn hdisj hi⟩
  refine ⟨(finite_range C).subset ?_, ?_⟩
  · rintro B ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := hcomponent hp
    exact ⟨i, hi.symm⟩
  · intro p hp
    obtain ⟨i, hi⟩ := hcomponent hp
    simpa only [hi] using hneq i

theorem circle_model_of_finite_disjoint_complement
    (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] {U : Set Sphere} (hU : IsOpen U) (hconnU : IsConnected U)
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    (hneq : ∀ i, (C i).Nontrivial) (hcomp : Uᶜ = ⋃ i, C i) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V := by
  by_cases hne : Uᶜ.Nonempty
  · exact hfinite U hU hconnU hne
      (finite_nondegenerate_complement_of_disjoint_closed C hC hconn hdisj hneq hcomp)
  · have hUniv : U = univ := by
      apply eq_univ_of_forall
      intro x
      by_contra hx
      exact hne ⟨x, hx⟩
    subst U
    exact circleDomainModel_univ

/-- After compact metric uniformization, the finite circle theorem gives
an actual bijection to a circle domain. It is conformal in every region
where the metric uniformization retained the original complex structure. -/
theorem circle_model_after_homeomorphism
    (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] {U W : Set Sphere} (hU : IsOpen U) (hconnU : IsConnected U)
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    (hneq : ∀ i, (C i).Nontrivial) (hcomp : Uᶜ = ⋃ i, C i)
    (e : Sphere ≃ₜ Sphere) (hW : W ⊆ U) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f U V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' U) V := by
  have hcomp' : (e '' U)ᶜ = ⋃ i, e '' C i := by
    rw [← e.image_compl, hcomp, image_iUnion]
  have hdisj' : Pairwise (Disjoint on fun i => e '' C i) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hzx : z = x := e.injective heq
    exact Set.disjoint_left.mp (hdisj hij) hx (hzx ▸ hz)
  obtain ⟨V, g, hV, hg⟩ := circle_model_of_finite_disjoint_complement hfinite
    (e.isOpenMap _ hU) (hconnU.image e e.continuous.continuousOn)
    (fun i => e '' C i) (fun i => e.isClosedMap _ (hC i))
    (fun i => (hconn i).image e e.continuous.continuousOn) hdisj'
    (fun i => (hneq i).image e.injective) hcomp'
  refine ⟨V, g ∘ e, hV, hg.bijOn.comp e.injective.bijOn_image,
    hg.1.comp he (fun p hp => ⟨p, hW hp, rfl⟩), ?_⟩
  have heq : (g ∘ e) ∘ e.symm = g := by funext p; simp only [Function.comp_apply, e.apply_symm_apply]
  simpa only [heq] using hg

end CircleDomainRigidity

end

end OAI
