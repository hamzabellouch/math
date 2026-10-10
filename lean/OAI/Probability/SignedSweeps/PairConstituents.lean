import OAI.Probability.SignedSweeps.AllocationSigns
import OAI.Probability.SignedSweeps.TensorMultiplicity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G H E F U V W : Type*} [Monoid G] [Monoid H]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W]

lemma tensor_isotypic_zero (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ G U) (υ : Representation ℂ H V) (L : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hL : ∀ (f : Representation.IntertwiningMap ρ τ) (g : Representation.IntertwiningMap σ υ),
      L ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap = 0) :
    L ∘ₗ TensorProduct.map
      (isotypicSubrepresentation ρ τ).toSubmodule.starProjection.toLinearMap
      (isotypicSubrepresentation σ υ).toSubmodule.starProjection.toLinearMap = 0 := by
  have hz (x : U) (hx : x ∈ (isotypicSubrepresentation ρ τ).toSubmodule)
      (y : V) (hy : y ∈ (isotypicSubrepresentation σ υ).toSubmodule) :
      L (x ⊗ₜ[ℂ] y) = 0 := by
    refine Submodule.iSup_induction (motive := fun x => L (x ⊗ₜ[ℂ] y) = 0)
      (fun f : Representation.IntertwiningMap ρ τ => f.toLinearMap.range) hx ?_ ?_ ?_
    · intro f x hx
      obtain ⟨x,rfl⟩ := hx
      refine Submodule.iSup_induction (motive := fun y => L (f x ⊗ₜ[ℂ] y) = 0)
        (fun g : Representation.IntertwiningMap σ υ => g.toLinearMap.range) hy ?_ ?_ ?_
      · intro g y hy
        obtain ⟨y,rfl⟩ := hy
        exact LinearMap.congr_fun (hL f g) (x ⊗ₜ[ℂ] y)
      · simp
      · intro y z hy hz
        simp only [TensorProduct.tmul_add, map_add, hy, hz, add_zero]
    · simp
    · intro x z hx hz
      simp only [TensorProduct.add_tmul, map_add, hx, hz, add_zero]
  apply TensorProduct.ext'
  intro x y
  exact hz _ ((isotypicSubrepresentation ρ τ).toSubmodule.starProjection_apply_mem x)
    _ ((isotypicSubrepresentation σ υ).toSubmodule.starProjection_apply_mem y)

lemma exists_tensor_isotypic_nonzero (ρ : Representation ℂ G E) (σ : Representation ℂ H F)
    (τ : Representation ℂ G U) (υ : Representation ℂ H V) (L : U ⊗[ℂ] V →ₗ[ℂ] W)
    (hL : L ∘ₗ TensorProduct.map
      (isotypicSubrepresentation ρ τ).toSubmodule.starProjection.toLinearMap
      (isotypicSubrepresentation σ υ).toSubmodule.starProjection.toLinearMap ≠ 0) :
    ∃ (f : Representation.IntertwiningMap ρ τ) (g : Representation.IntertwiningMap σ υ),
      L ∘ₗ TensorProduct.map f.toLinearMap g.toLinearMap ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hL (tensor_isotypic_zero ρ σ τ υ L hn)

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ V] in
lemma tensor_map_equiv_nonzero {F' : Type*} [AddCommGroup F'] [Module ℂ F']
    (L : U ⊗[ℂ] V →ₗ[ℂ] W) (r : E →ₗ[ℂ] U) (s : F →ₗ[ℂ] V)
    (e : F' ≃ₗ[ℂ] F) (h : L ∘ₗ TensorProduct.map r s ≠ 0) :
    L ∘ₗ TensorProduct.map r (s ∘ₗ e.toLinearMap) ≠ 0 := by
  intro hz
  apply h
  apply TensorProduct.ext'
  intro x y
  obtain ⟨z,rfl⟩ := e.surjective y
  exact LinearMap.congr_fun hz (x ⊗ₜ[ℂ] z)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def pairEmbeddingHom {u v p : ℕ} (e : Fin u ⊕ Fin v ≃ Fin p) :
    SymmetricGroup u × SymmetricGroup v →* SymmetricGroup p :=
  e.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin u) (Fin v))

lemma pair_internal_intertwining {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (S : EvenAllocation u p) (a : Partition u) (b : Partition v)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (g : SymmetricGroup u) (t : SymmetricGroup v)
    (x : Specht a ⊗[ℂ] Specht b.transpose) :
    let j := pairWordEmbedding (C:=C) (allocationEquiv h S)
    let k := j.toLinearMap ∘ₗ TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)
    k (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
      signedWordRepresentation p C (allocationBlockPermutation h S g t) (k x) := by
  dsimp only
  have he (y : Specht b.transpose) :
      e.toLinearEquiv (spechtRepresentation b.transpose t y) =
        complexSign v t • spechtRepresentation b t (e.toLinearEquiv y) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap t y
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    have hj := LinearMap.congr_fun (pairWordEmbedding_signed_internal (C:=C) h S g t)
      (r x ⊗ₜ[ℂ] s (e.toLinearEquiv y))
    change pairWordEmbedding (allocationEquiv h S)
      (r (spechtRepresentation a g x) ⊗ₜ[ℂ]
        s (e.toLinearEquiv (spechtRepresentation b.transpose t y))) = _
    rw [r.isIntertwining, he, map_smul, s.isIntertwining,
      TensorProduct.tmul_smul, map_smul]
    exact hj.symm

lemma pair_projection_detects {u v p : ℕ} {C W : Type*} [Fintype C]
    [AddCommGroup W] [Module ℂ W]
    (h : u+v=p) (a : Partition u) (b : Partition v)
    (A : WordSpace p (C ⊕ C) →ₗ[ℂ] W) (hA : A ≠ 0)
    (hAQ : A ∘ₗ pairTypeProjection h a b C = A) :
    ∃ (S : EvenAllocation u p)
      (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
      (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C)),
      (A ∘ₗ (pairWordEmbedding (C:=C) (allocationEquiv h S)).toLinearMap) ∘ₗ
        TensorProduct.map r.toLinearMap s.toLinearMap ≠ 0 := by
  have hn : (∑ S : EvenAllocation u p,
      A ∘ₗ hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C))) ≠ 0 := by
    change (∑ S : EvenAllocation u p, (LinearMap.compRight ℂ A)
      (hilbertBlock (pairWordEmbedding (C:=C) (allocationEquiv h S))
        (TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C)))) ≠ 0
    rw [← map_sum]
    change A ∘ₗ pairTypeProjection h a b C ≠ 0
    rw [hAQ]
    exact hA
  obtain ⟨S,_,hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  let j := pairWordEmbedding (C:=C) (allocationEquiv h S)
  let L := A ∘ₗ j.toLinearMap
  have hL : L ∘ₗ TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C) ≠ 0 := by
    intro hz
    apply hS
    change A ∘ₗ (j.toLinearMap ∘ₗ _ ∘ₗ j.toLinearMap.adjoint) = 0
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    change (L ∘ₗ _) ∘ₗ j.toLinearMap.adjoint = 0
    rw [hz, LinearMap.zero_comp]
  obtain ⟨r,s,hrs⟩ := exists_tensor_isotypic_nonzero (spechtRepresentation a) (spechtRepresentation b)
    (wordRepresentation u C) (wordRepresentation v C) L hL
  exact ⟨S,r,s,hrs⟩

lemma pair_sector_adjoint_nonzero {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (mu : Partition p)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (signedWordRepresentation p C))
    (hf : f ≠ 0) (hQ : ∀ x, pairTypeProjection h a b C (f x) = f x) :
    f.toLinearMap.adjoint ≠ 0 ∧
      f.toLinearMap.adjoint ∘ₗ pairTypeProjection h a b C = f.toLinearMap.adjoint := by
  constructor
  · intro hz
    have he := congrArg LinearMap.adjoint hz
    rw [LinearMap.adjoint_adjoint, map_zero] at he
    exact hf (Representation.IntertwiningMap.ext he)
  · have he : pairTypeProjection h a b C ∘ₗ f.toLinearMap = f.toLinearMap := LinearMap.ext hQ
    have he' := congrArg LinearMap.adjoint he
    rw [LinearMap.adjoint_comp, (pairTypeProjection_positive h a b C).isSymmetric.adjoint_eq] at he'
    exact he'

theorem pair_sector_constituent_occurrence {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (mu : Partition p)
    (f : Representation.IntertwiningMap (spechtRepresentation mu) (signedWordRepresentation p C))
    (hf : f ≠ 0) (hQ : ∀ x, pairTypeProjection h a b C (f x) = f x) :
    ∃ (S : EvenAllocation u p)
      (k : (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] Specht mu),
      Function.Injective k ∧ ∀ (g : SymmetricGroup u) (t : SymmetricGroup v) x,
        k (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
          spechtRepresentation mu ((allocationEquiv h S).permCongr (g.sumCongr t)) (k x) := by
  let A := adjointIntertwiner (spechtRepresentation mu) (signedWordRepresentation p C)
    (spechtRepresentation_norm mu) signedWordRepresentation_norm f
  obtain ⟨hA,hAQ⟩ := pair_sector_adjoint_nonzero h a b mu f hf hQ
  obtain ⟨S,r,s,hrs⟩ := pair_projection_detects h a b A.toLinearMap hA hAQ
  let j := pairWordEmbedding (C:=C) (allocationEquiv h S)
  let L := A.toLinearMap ∘ₗ j.toLinearMap
  obtain ⟨e⟩ := specht_transpose_sign_equiv b
  let k := L ∘ₗ TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)
  have hk : k ≠ 0 := tensor_map_equiv_nonzero L r.toLinearMap s.toLinearMap e.toLinearEquiv hrs
  have hint (g : SymmetricGroup u) (t : SymmetricGroup v) (x : Specht a ⊗[ℂ] Specht b.transpose) :
      k (TensorProduct.map (spechtRepresentation a g) (spechtRepresentation b.transpose t) x) =
        spechtRepresentation mu ((allocationEquiv h S).permCongr (g.sumCongr t)) (k x) := by
    have hh := congrArg A.toLinearMap (pair_internal_intertwining h S a b r s e g t x)
    exact hh.trans (Representation.IntertwiningMap.isIntertwining _ _ A (allocationBlockPermutation h S g t) _)
  let τ := (spechtRepresentation mu).comp (pairEmbeddingHom (allocationEquiv h S))
  let k' := k.intertwiningMap_of_isIntertwiningMap
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose)) τ
      (fun ⟨g,t⟩ x => hint g t x)
  let := specht_irreducible a
  let := specht_irreducible b.transpose
  let := outerTensorRepresentation_irreducible (spechtRepresentation a) (spechtRepresentation b.transpose)
    (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose)
  have hk' : k' ≠ 0 := fun hz => hk (congrArg Representation.IntertwiningMap.toLinearMap hz)
  exact ⟨S,k,(Representation.IsIrreducible.injective_or_eq_zero k').resolve_right hk',hint⟩

end SignedSweeps
end

end OAI
