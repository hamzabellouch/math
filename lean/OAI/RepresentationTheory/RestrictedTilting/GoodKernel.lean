import OAI.RepresentationTheory.RestrictedTilting.CompatibleJets

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
variable (k : Type u) [Field k]

 
def HasGoodKernel {P A : FDRep k (SL2 k)} (g : P ⟶ A) : Prop :=
  ∃ (K : FDRep k (SL2 k)) (i : K ⟶ P) (w : i ≫ g = 0),
    (ShortComplex.mk i g w).ShortExact ∧ HasGoodFiltration k K

lemma HasGoodKernel.epi {P A : FDRep k (SL2 k)} {g : P ⟶ A}
    (h : HasGoodKernel k g) : Epi g := by
  obtain ⟨K,i,w,hs,hK⟩ := h
  exact hs.epi_g

lemma fdrepKernel_shortExact {P A : FDRep k (SL2 k)} (g : P ⟶ A)
    (hg : Function.Surjective (fdrepLinear k g)) :
    (ShortComplex.mk (fdrepKernelι k g) g (by
      apply fdrep_hom_ext k; intro x; exact x.property)).ShortExact := by
  apply fdrep_shortExact k _ Subtype.val_injective hg
  exact Submodule.range_subtype _

lemma HasGoodKernel.id (A : FDRep k (SL2 k)) : HasGoodKernel k (𝟙 A) := by
  refine ⟨fdrepKernel k (𝟙 A), fdrepKernelι k (𝟙 A), ?_, ?_, ?_⟩
  · apply fdrep_hom_ext k; intro x; exact x.property
  · exact fdrepKernel_shortExact k (𝟙 A) Function.surjective_id
  · have : Subsingleton (fdrepKernel k (𝟙 A)) := by
      apply subsingleton_of_forall_eq 0
      intro x
      apply Subtype.ext
      exact x.property
    exact .zero _ (fdrep_isZero_of_subsingleton k _)

lemma HasGoodKernel.comp {P A B : FDRep k (SL2 k)} {g : P ⟶ A} {h : A ⟶ B}
    (hg : HasGoodKernel k g) (hh : HasGoodKernel k h) : HasGoodKernel k (g ≫ h) := by
  obtain ⟨K,i,w,hS,hK⟩ := hg
  obtain ⟨L,j,v,hT,hL⟩ := hh
  obtain ⟨N,a,b,c,wab,wc,hN,hC⟩ := fdrep_splice k i g w hS j h v hT
  exact ⟨N,c,wc,hC,hK.extension k hL a b wab hN⟩

lemma HasGoodKernel.tensor_right {P A : FDRep k (SL2 k)} {g : P ⟶ A}
    (hg : HasGoodKernel k g) (B : FDRep k (SL2 k)) (hB : HasGoodFiltration k B) :
    HasGoodKernel k ((tensorRight B).map g) := by
  obtain ⟨K,i,w,hS,hK⟩ := hg
  let := tensorRight_preservesFiniteLimits B
  let := tensorRight_preservesFiniteColimits B
  exact ⟨K ⊗ B, (tensorRight B).map i, (by rw [← Functor.map_comp, w, Functor.map_zero]),
    hS.map_of_exact (tensorRight B), hK.tensor k hB⟩

lemma HasGoodKernel.split [Infinite k] {P A : FDRep k (SL2 k)} {g : P ⟶ A}
    (hg : HasGoodKernel k g) (hP : IsRational k P.ρ) (hA : IsTilting k A) :
    ∃ s : A ⟶ P, s ≫ g = 𝟙 A := by
  obtain ⟨K,i,w,hS,hK⟩ := hg
  exact good_weyl_extension_split k hK hA.2.2 P hP i g w hS

lemma HasGoodKernel.of_isIso {P A : FDRep k (SL2 k)} (g : P ⟶ A) [IsIso g] :
    HasGoodKernel k g := by
  refine ⟨fdrepKernel k g, fdrepKernelι k g, ?_, ?_, ?_⟩
  · apply fdrep_hom_ext k; intro x; exact x.property
  · exact fdrepKernel_shortExact k g (fdrep_surjective k g)
  · have : Subsingleton (fdrepKernel k g) := by
      apply subsingleton_of_forall_eq 0
      intro x
      apply Subtype.ext
      apply fdrep_injective k g
      exact x.property.trans (map_zero _).symm
    exact .zero _ (fdrep_isZero_of_subsingleton k _)

 
lemma costandardMultiply_goodKernel (a b : ℕ) : HasGoodKernel k (costandardMultiply k a b) := by
  rcases a with _ | a
  · have := costandardMultiply_isIso_of_zero k 0 b (Or.inl rfl)
    exact HasGoodKernel.of_isIso k _
  · rcases b with _ | b
    · have := costandardMultiply_isIso_of_zero k (a+1) 0 (Or.inr rfl)
      exact HasGoodKernel.of_isIso k _
    · exact ⟨_, costandardDeterminant k a b, costandardDeterminant_multiply k a b,
        costandardTensorSequence_shortExact k a b, costandard_tensor_hasGoodFiltration k a b⟩

lemma HasGoodKernel.kernel_good {P A : FDRep k (SL2 k)} {g : P ⟶ A}
    (hg : HasGoodKernel k g) : HasGoodFiltration k (fdrepKernel k g) := by
  obtain ⟨K,i,w,hS,hK⟩ := hg
  have := hS.mono_f
  let j := fdrepKernelLift k i g w
  have hj : Function.Bijective (fdrepLinear k j) := by
    constructor
    · intro x y h
      apply fdrep_injective k i
      exact congrArg Subtype.val h
    · intro x
      have hx : x.val ∈ LinearMap.range (fdrepLinear k i) := by
        rw [fdrep_exact k hS.exact]
        exact x.property
      obtain ⟨v,hv⟩ := hx
      exact ⟨v,Subtype.ext hv⟩
  have := fdrepHom_isIso_of_bijective k j hj
  exact hK.of_iso k (asIso j)
end FiberFunctorProof

end OAI
