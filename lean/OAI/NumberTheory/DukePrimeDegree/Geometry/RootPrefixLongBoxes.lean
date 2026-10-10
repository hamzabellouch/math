import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRestrictions
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLeafMeasure

namespace OAI

/-! # Compact remaining-root time sets fit in actual prefix quotient boxes -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (g : G n)

lemma timeParam_injective_of_free (s : UpperRootTransverse n × T)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) :
    Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)) := by
  intro t u h
  let wt := c.word t
  let wu := c.word u
  have htw : wt ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hfinal t)
  have huw : wu ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hfinal u)
  have hh := congrArg (fun x => rightAction x wu⁻¹) h
  change rightAction (C.timeParam c hP hfinal g (s,t)) wu⁻¹ =
    rightAction (C.timeParam c hP hfinal g (s,u)) wu⁻¹ at hh
  rw [C.timeParam_eq_action,C.timeParam_eq_action,rightAction_mul,rightAction_mul] at hh
  have hz : rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) (wt*wu⁻¹) =
      Quotient.mk _ ((g*s.1.val)*C.base s.2) := by
    simpa only [wt,wu,mul_inv_cancel,rightAction_one] using hh
  have he := hfree (wt*wu⁻¹)
    ((positiveRootGeneratedGroup _).mul_mem htw ((positiveRootGeneratedGroup _).inv_mem huw)) hz
  apply (c.word_isEmbedding_remaining hfinal).injective
  exact mul_right_cancel (show wt*wu⁻¹=wu*wu⁻¹ from he.trans (mul_inv_cancel wu).symm)

theorem box_contains_compact_time (s : UpperRootTransverse n × T)
    (hinj : Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)))
    (K : Set c.Time) (hK : IsCompact K) :
    ∃ B : RootPrefixBox C c hP hfinal g, s ∈ B.transverse ∧ K ⊆ B.time := by
  have hf := C.timeParam_localHomeomorph c hP hfinal g
  have hi : Set.InjOn (C.timeParam c hP hfinal g) ({s} ×ˢ K) := by
    rintro ⟨s₁,t₁⟩ ⟨hs₁,_⟩ ⟨s₂,t₂⟩ ⟨hs₂,_⟩ heq
    have h₁ : s₁=s := hs₁
    have h₂ : s₂=s := hs₂
    subst s₁
    subst s₂
    exact Prod.ext rfl (hinj heq)
  obtain ⟨W,hW,hKW,hemb⟩ := compact_injective_localHomeomorph_neighborhood hf
    (isCompact_singleton.prod hK) hi
  obtain ⟨U,V,hU,hV,hsU,hKV,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set (UpperRootTransverse n × T))) hK hW hKW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U,V,hU,hV,he⟩,hsU (Set.mem_singleton s),hKV⟩

end RootPrefixCoordinates
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_injective_slice_of_ae_free (B : RootPrefixBox C c hP hfinal g)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      Function.Injective (fun t => C.timeParam c hP hfinal g (s,t)) := by
  have hf := B.ae_coordinate_of_ambient μ hfree
  have hf' : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ),
      ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
        rightAction (C.timeParam c hP hfinal g z) v = C.timeParam c hP hfinal g z → v = 1 := by
    simpa only [conditionalKernel,Measure.disintegrate] using hf
  have H := Measure.ae_ae_of_ae_compProd hf'
  filter_upwards [H] with s hs
  obtain ⟨t,ht⟩ := hs.exists
  apply C.timeParam_injective_of_free c hP hfinal g s
  apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots n))
    (Quotient.mk _ ((g*s.1.val)*C.base s.2)) (c.word t)
    (positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hfinal t))
  simpa only [C.timeParam_eq_action] using ht

end RootPrefixBox
end DukePrimeDegree

end

end OAI
