import OAI.CategoryTheory.Thomason.Chains.FiniteChainMesh
import OAI.CategoryTheory.Thomason.Transfer.FiniteCosieveAttachmentCover
import OAI.CategoryTheory.Thomason.Transfer.FiniteStreetSievePushouts
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing

namespace OAI

section

/-! # The weak comparison for attachments of finite face-chain posets -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory PartialOrder

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Face-chain attachments satisfy the actual Street comparison, including
the empty old face set. No retraction of the whole chain poset is used. -/
theorem finite_chain_attachment_comparison
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (S : Set P)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve (ChainSieve.old S)) ⟶ X}
    {b : h.categorification.obj (nerve (NonemptyFiniteChains P)) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion (ChainSieve.old S))) a b j) :
    realizationWeakEquivalences (nervePushoutComparison h.streetNerve hp) := by
  let : Finite (NonemptyFiniteChains P) := finite_nonemptyFiniteChains P
  exact h.finite_dwyer_attachment_comparison G aw s g kq
    (ChainSieve.old S) (ChainSieve.upper S) (ChainSieve.old_lower S)
    (ChainSieve.upper_upper S) (ChainSieve.old_subset_upper S) (ChainSieve.retraction S) hp

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # The actual finite-dimensional Dwyer attachment comparison -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory PartialOrder

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Couniversality on a containing cosieve controls the actual attachment
comparison, with all pushouts taken in the finite category. -/
theorem containing_cosieve_attachment_comparison
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (A Z C : Set P)
    (hZ : IsUpperSet Z) (hC : IsUpperSet C) (hAZ : A ⊆ Z)
    (hAC : ∀ x ∈ A, x ∉ C) (cover : ∀ x, x ∈ Z ∨ x ∈ C)
    (wZ : h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ))))
    [Mono ((h.finiteStreetNerve (n+1)).map
      (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ))))]
    {X Y : Truncated.{0} (n+1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    realizationWeakEquivalences (nervePushoutComparison (h.finiteStreetNerve (n+1)) hp) := by
  obtain ⟨p, hbp, hjp⟩ := r.cosieve_piece_label h A Z hZ hAZ hp
  obtain ⟨q, hbq, hjq⟩ := r.disjoint_cosieve_piece_label h A C hC hAC hp
  let d := (r.posetCosieveIso h Z hZ).hom ≫
    finiteLabelFiberMap (r.membershipLabel h Zᶜ hZ.compl) p 1 b hbp
  let e := (finiteConstantFiberIso X 1).inv ≫
    finiteLabelFiberMap (finiteConstantLabel X 1) p 1 j hjp
  have hz : IsPushout (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ))) a d e :=
    r.cosieve_piece_pushout h A Z hZ hAZ hp p hbp hjp
  have hi : IsPushout (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ)))
      (𝟙 _) (𝟙 _) (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ))) :=
    IsPushout.of_id_snd
  have wz := nervePushoutComparison_weakEquivalence (h.finiteStreetNerve (n+1)) kq
    hz (wZ hi) (wZ hz)
  have hk : d ≫ finiteLabelFiberInclusion p 1 =
      r.reflect.map (h.posetMap (subposetInclusion Z)) ≫ b :=
    EndpointFiber.finite_piece_inclusion 1 _ _ b hbp _ (r.posetCosieveIso h Z hZ)
      (r.posetCosieveIso_inclusion h Z hZ)
  have he : e ≫ finiteLabelFiberInclusion p 1 = j := by apply Hom.ext; rfl
  have : Mono ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (interRight Z C))) ≫
      (h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion C)))) := by
    rw [← Functor.map_comp, ← r.reflect.map_comp, ← h.posetMap_comp]
    exact r.posetCosieve_nerve_mono h (Z ∩ C) (hZ.inter hC)
  have : Mono ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (interRight Z C)))) :=
    mono_of_mono _ ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion C))))
  have hfac : r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ)) ≫
      r.reflect.map (h.posetMap (subposetInclusion Z)) =
      r.reflect.map (h.posetMap (subposetInclusion A)) :=
    (r.reflect.map_comp _ _).symm.trans (congrArg r.reflect.map (h.subposetInclusionWithin_fac A Z hAZ))
  have hp' : IsPushout (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ)) ≫
      r.reflect.map (h.posetMap (subposetInclusion Z))) a b j := by rw [hfac]; exact hp
  have hw := nervePushoutComparison_weak_of_cosieve_cover (h.finiteStreetNerve (n+1)) g
    (v := r.reflect.map (h.posetMap (interRight Z C))) hp' hz hk he
    (r.street_cosieve_maps_isPushout h Z C hZ hC cover)
    (r.cosieve_attachment_street_pushout h A Z C hZ hC hAC cover hp p q hbp hjp hbq hjq) wz
  exact (nervePushoutComparison_weak_iff (h.finiteStreetNerve (n+1)) hfac hp' hp).mp hw

/-- A right adjoint on the containing cosieve suffices in every positive
finite dimension; the ambient poset need not retract onto the sieve. -/
theorem finite_dwyer_attachment_comparison
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A Z : Set P)
    (hA : IsLowerSet A) (hZ : IsUpperSet Z) (hAZ : A ⊆ Z)
    (R : SieveRetraction {z : Z | z.val ∈ A})
    {X Y : Truncated.{0} (n+1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    realizationWeakEquivalences (nervePushoutComparison (h.finiteStreetNerve (n+1)) hp) := by
  have hfac : (r.reflect.mapIso (h.posetMapIso (restrictedOldIso A Z hAZ))).hom ≫
      r.reflect.map (h.posetMap (subposetInclusion {z : Z | z.val ∈ A})) =
      r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ)) :=
    (r.reflect.map_comp _ _).symm.trans (congrArg r.reflect.map (h.restrictedOldIso_fac A Z hAZ))
  have wZ : h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ))) := by
    rw [← hfac]
    exact h.finite_couniversal_precompose_iso n
      (r.reflect.mapIso (h.posetMapIso (restrictedOldIso A Z hAZ))) _
      (r.finite_poset_couniversal h G t aw s g kq _ R)
  have : Mono ((h.finiteStreetNerve (n+1)).map
      (r.reflect.map (h.posetMap (subposetInclusionWithin A Z hAZ)))) := by
    have := r.posetSieve_nerve_mono h s {z : Z | z.val ∈ A} R.lower
    rw [← hfac, Functor.map_comp]
    infer_instance
  apply r.containing_cosieve_attachment_comparison h g kq A Z Aᶜ hZ hA.compl hAZ
    (fun _ hx hxc => hxc hx) ?_ wZ hp
  intro x
  by_cases hx : x ∈ A
  · exact Or.inl (hAZ hx)
  · exact Or.inr hx

/-- Actual finite-dimensional comparison for chains on any finite face set. -/
theorem finite_chain_attachment_comparison
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (S : Set P)
    {X Y : Truncated.{0} (n+1)}
    {a : (r.categorification h).obj (nerve (ChainSieve.old S)) ⟶ X}
    {b : (r.categorification h).obj (nerve (NonemptyFiniteChains P)) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion (ChainSieve.old S)))) a b j) :
    realizationWeakEquivalences (nervePushoutComparison (h.finiteStreetNerve (n+1)) hp) := by
  let : Finite (NonemptyFiniteChains P) := finite_nonemptyFiniteChains P
  exact r.finite_dwyer_attachment_comparison h G t aw s g kq
    (ChainSieve.old S) (ChainSieve.upper S) (ChainSieve.old_lower S)
    (ChainSieve.upper_upper S) (ChainSieve.old_subset_upper S) (ChainSieve.retraction S) hp

end Thomason.Construction.FiniteReflectionInput

end

end OAI
