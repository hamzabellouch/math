import OAI.RepresentationTheory.RestrictedTilting.TiltingCovers
import OAI.RepresentationTheory.RestrictedTilting.SteinbergSpan
import OAI.RepresentationTheory.RestrictedTilting.BoundedStableFaithfulness

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (p r : ℕ) [Fact p.Prime] [CharP k p]
variable (l : (Fin r → ZMod p) →+ k) (hl : Function.Injective l)

 
def StableFaithfulPair (A B : FDRep k (SL2 k)) : Prop :=
  ∀ (f : A ⟶ B), FactorsThroughProjective ((restrictElementary k p r l).map f) →
    f ∈ steinbergSpan k p r A B

omit [Infinite k] [CharP k p] in
lemma StableFaithfulPair.iso_left {A A' B : FDRep k (SL2 k)}
    (h : StableFaithfulPair k p r l A B) (e : A ≅ A') :
    StableFaithfulPair k p r l A' B := by
  intro f hf
  have hg : FactorsThroughProjective ((restrictElementary k p r l).map (e.hom ≫ f)) := by
    rw [Functor.map_comp]
    exact hf.precomp _
  have H := steinbergSpan.precomp k p r e.inv _ (h _ hg)
  simpa using H

omit [Infinite k] [CharP k p] in
lemma StableFaithfulPair.iso_right {A B B' : FDRep k (SL2 k)}
    (h : StableFaithfulPair k p r l A B) (e : B ≅ B') :
    StableFaithfulPair k p r l A B' := by
  intro f hf
  have hg : FactorsThroughProjective ((restrictElementary k p r l).map (f ≫ e.inv)) := by
    rw [Functor.map_comp]
    exact hf.postcomp _
  have H := steinbergSpan.postcomp k p r _ e.hom (h _ hg)
  simpa using H

omit [Infinite k] [CharP k p] in
lemma StableFaithfulPair.prod_left {A A' B : FDRep k (SL2 k)}
    (h : StableFaithfulPair k p r l A B) (h' : StableFaithfulPair k p r l A' B) :
    StableFaithfulPair k p r l (repProduct k A A') B := by
  intro f hf
  have h₁ : FactorsThroughProjective
      ((restrictElementary k p r l).map (repInl k A A' ≫ f)) := by
    rw [Functor.map_comp]; exact hf.precomp _
  have h₂ : FactorsThroughProjective
      ((restrictElementary k p r l).map (repInr k A A' ≫ f)) := by
    rw [Functor.map_comp]; exact hf.precomp _
  have H := (steinbergSpan k p r _ B).add_mem
    (steinbergSpan.precomp k p r (repFst k A A') _ (h _ h₁))
    (steinbergSpan.precomp k p r (repSnd k A A') _ (h' _ h₂))
  have he : (repFst k A A' ≫ repInl k A A' + repSnd k A A' ≫ repInr k A A') ≫ f = f := by
    rw [repProduct_decomposition, Category.id_comp]
  rw [Preadditive.add_comp, Category.assoc, Category.assoc] at he
  rwa [he] at H

omit [Infinite k] [CharP k p] in
lemma StableFaithfulPair.prod_right {A B B' : FDRep k (SL2 k)}
    (h : StableFaithfulPair k p r l A B) (h' : StableFaithfulPair k p r l A B') :
    StableFaithfulPair k p r l A (repProduct k B B') := by
  intro f hf
  have h₁ : FactorsThroughProjective
      ((restrictElementary k p r l).map (f ≫ repFst k B B')) := by
    rw [Functor.map_comp]; exact hf.postcomp _
  have h₂ : FactorsThroughProjective
      ((restrictElementary k p r l).map (f ≫ repSnd k B B')) := by
    rw [Functor.map_comp]; exact hf.postcomp _
  have H := (steinbergSpan k p r A _).add_mem
    (steinbergSpan.postcomp k p r _ (repInl k B B') (h _ h₁))
    (steinbergSpan.postcomp k p r _ (repInr k B B') (h' _ h₂))
  have he : f ≫ (repFst k B B' ≫ repInl k B B' + repSnd k B B' ≫ repInr k B B') = f := by
    rw [repProduct_decomposition, Category.comp_id]
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc] at he
  rwa [he] at H

include hl

omit [CharP k p] in
lemma generated_stable_kernel {A B : FDRep k (SL2 k)}
    (hA : SteinbergGenerated k p r A) (hB : SteinbergGenerated k p r B) :
    StableFaithfulPair k p r l A B := by
  induction hA generalizing B with
  | low A hA a ha hw =>
    induction hB with
    | low B hB b hb hw' =>
      intro f hf
      have hz := low_weight_projective_factor_zero p r l hl A B hA.1 hB.1 a b hw hw'
        (by omega) f hf
      rw [hz]
      exact (steinbergSpan k p r A B).zero_mem
    | high X hX => exact fun f _ => steinbergSpan_of_high_right k p r X hX f
    | of_iso hB e ih => exact ih.iso_right k p r l e
    | prod hB hB' ih ih' => exact ih.prod_right k p r l ih'
  | high X hX => exact fun f _ => steinbergSpan_of_high_left k p r X hX f
  | of_iso hA e ih => exact (ih hB).iso_left k p r l e
  | prod hA hA' ih ih' => exact (ih hB).prod_left k p r l (ih' hB)

 
theorem tilting_projective_factor_mem_steinbergSpan (hr : 1 ≤ r)
    (A B : FDRep k (SL2 k)) (hA : IsTilting k A) (hB : IsTilting k B)
    (f : A ⟶ B) (hf : FactorsThroughProjective ((restrictElementary k p r l).map f)) :
    f ∈ steinbergSpan k p r A B := by
  obtain ⟨P,a,s,ha,hP⟩ := tilting_retract_generated k p r hr A hA
  obtain ⟨Q,b,t,hb,hQ⟩ := tilting_retract_generated k p r hr B hB
  have hg : FactorsThroughProjective ((restrictElementary k p r l).map (a ≫ f ≫ t)) := by
    simp only [Functor.map_comp]
    exact (hf.precomp _).postcomp _
  have H := generated_stable_kernel k p r l hl hP hQ _ hg
  have H' := steinbergSpan.postcomp k p r _ b (steinbergSpan.precomp k p r s _ H)
  simp only [Category.assoc] at H'
  rwa [← Category.assoc s a, ha, Category.id_comp, hb, Category.comp_id] at H'
end FiberFunctorProof

end OAI
