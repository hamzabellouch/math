import OAI.Probability.SignedSweeps.MarkedPairFibers
import OAI.Probability.SignedSweeps.IsometricFibers

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma wordTypeProjection_intertwiner {u : ℕ} {C : Type*} [Fintype C]
    (a : Partition u)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (x : Specht a) : wordTypeProjection a C (r x) = r x :=
  Submodule.starProjection_eq_self_iff.mpr (intertwiner_mem_isotypic _ _ r x)

lemma pairTypeProjection_embedding {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (S : EvenAllocation u p)
    (x : WordSpace u C ⊗[ℂ] WordSpace v C) :
    pairTypeProjection h a b C (pairWordEmbedding (allocationEquiv h S) x) =
      pairWordEmbedding (allocationEquiv h S)
        (TensorProduct.map (wordTypeProjection a C) (wordTypeProjection b C) x) := by
  unfold pairTypeProjection
  rw [LinearMap.sum_apply, Finset.sum_eq_single S]
  · exact hilbertBlock_on _ _ x
  · intro T _ hTS
    have hz : (pairWordEmbedding (C:=C) (allocationEquiv h T)).toLinearMap.adjoint
        (pairWordEmbedding (allocationEquiv h S) x) = 0 := by
      apply ext_inner_left ℂ
      intro y
      rw [LinearMap.adjoint_inner_right, inner_zero_right]
      exact pairWordEmbedding_orthogonal h hTS y x
    rw [hilbertBlock_apply, hz, map_zero, map_zero]
  · simp

lemma pairTypeProjection_fixes_specht_pair {u v p : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (a : Partition u) (b : Partition v) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (x : Specht a ⊗[ℂ] Specht b) :
    pairTypeProjection h a b C
      (pairWordEmbedding (allocationEquiv h S) (TensorProduct.map r.toLinearMap s.toLinearMap x)) =
      pairWordEmbedding (allocationEquiv h S) (TensorProduct.map r.toLinearMap s.toLinearMap x) := by
  rw [pairTypeProjection_embedding]
  congr 1
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp only [TensorProduct.map_tmul, Representation.IntertwiningMap.toLinearMap_apply,
      wordTypeProjection_intertwiner]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma markedTypeProjection_insertion {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (x : WordSpace p (C ⊕ C)) :
    markedTypeProjection hu h a b C (fiberInsertion z x) =
      fiberInsertion z (pairTypeProjection hu a b C x) := by
  apply PiLp.ext
  intro w
  change pairTypeProjection hu a b C ((fiberInsertion z x).ofLp w) = _
  simp only [fiberInsertion_apply]
  split_ifs <;> simp

def markedPairSpechtMap {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b))) :
    (Specht a ⊗[ℂ] Specht b.transpose) →ₗ[ℂ] MarkedWordSpace p l n C :=
  (markedPairInsertion hu h z S).toLinearMap ∘ₗ
    TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)

lemma markedPairSpechtMap_fixed {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (x : Specht a ⊗[ℂ] Specht b.transpose) :
    markedTypeProjection hu h a b C (markedPairSpechtMap hu h a b z S r s e x) =
      markedPairSpechtMap hu h a b z S r s e x := by
  change markedTypeProjection hu h a b C (fiberInsertion z (pairWordEmbedding _ _)) =
    fiberInsertion z (pairWordEmbedding _ _)
  rw [markedTypeProjection_insertion]
  apply congrArg (fiberInsertion z)
  have he : TensorProduct.map r.toLinearMap (s.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap) x =
      TensorProduct.map r.toLinearMap s.toLinearMap
        (TensorProduct.map LinearMap.id e.toLinearEquiv.toLinearMap x) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
  rw [he]
  exact pairTypeProjection_fixes_specht_pair hu a b S r s _

lemma markedPairSpechtMap_intertwines {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (g : SymmetricGroup u × SymmetricGroup v) (x : Specht a ⊗[ℂ] Specht b.transpose) :
    markedPairSpechtMap hu h a b z S r s e
        (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose) g x) =
      markedWordRepresentation h C (markedPairEmbeddingHom hu h z S g)
        (markedPairSpechtMap hu h a b z S r s e x) := by
  change fiberInsertion z (pairWordEmbedding _ _) =
    markedWordRepresentation h C ((pairEmbeddingHom (allocationEquiv hu S) g).viaEmbedding _)
      (fiberInsertion z (pairWordEmbedding _ _))
  rw [markedWordRepresentation_pointwise]
  exact congrArg (fiberInsertion z) (pair_internal_intertwining hu S a b r s e g.1 g.2 x)

lemma markedPairSpechtMap_nonzero {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (hr : Function.Injective r) (hs : Function.Injective s) :
    markedPairSpechtMap hu h a b z S r s e ≠ 0 := by
  intro hz
  have hx := LinearMap.congr_fun hz (spechtGenerator a ⊗ₜ[ℂ] spechtGenerator b.transpose)
  change markedPairInsertion hu h z S
    (r (spechtGenerator a) ⊗ₜ[ℂ] s (e.toLinearEquiv (spechtGenerator b.transpose))) = 0 at hx
  have hx' := (markedPairInsertion (C:=C) hu h z S).injective
    (hx.trans (map_zero (markedPairInsertion (C:=C) hu h z S)).symm)
  exact complex_tmul_ne_zero
    (fun he => spechtGenerator_ne_zero a (hr (he.trans (map_zero r).symm)))
    (fun he => spechtGenerator_ne_zero b.transpose
      (e.toLinearEquiv.injective ((hs (he.trans (map_zero s).symm)).trans (map_zero _).symm))) hx'

def MarkedSectorSpace {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :=
  (markedTypeSubrepresentation hu h a b C).toSubmodule

instance {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    NormedAddCommGroup (MarkedSectorSpace hu h a b C) :=
  inferInstanceAs (NormedAddCommGroup (markedTypeSubrepresentation hu h a b C).toSubmodule)

instance {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    InnerProductSpace ℂ (MarkedSectorSpace hu h a b C) :=
  inferInstanceAs (InnerProductSpace ℂ (markedTypeSubrepresentation hu h a b C).toSubmodule)

instance {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    FiniteDimensional ℂ (MarkedSectorSpace hu h a b C) :=
  inferInstanceAs (FiniteDimensional ℂ (markedTypeSubrepresentation hu h a b C).toSubmodule)

def markedSectorRepresentation {u v p l n : ℕ} (hu : u+v=p) (h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup n) (MarkedSectorSpace hu h a b C) :=
  (markedTypeSubrepresentation hu h a b C).toRepresentation

def markedSectorIntertwiner {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b))) :
    Representation.IntertwiningMap
      (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
      ((markedSectorRepresentation hu h a b C).comp (markedPairEmbeddingHom hu h z S)) :=
  ((markedPairSpechtMap hu h a b z S r s e).codRestrict
    (markedTypeSubrepresentation hu h a b C).toSubmodule
    (fun x => ⟨_, markedPairSpechtMap_fixed hu h a b z S r s e x⟩)).intertwiningMap_of_isIntertwiningMap
    _ _ (by
      intro g x
      apply Subtype.ext
      exact markedPairSpechtMap_intertwines hu h a b z S r s e g x)

lemma markedSectorIntertwiner_nonzero {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (hr : Function.Injective r) (hs : Function.Injective s) :
    markedSectorIntertwiner hu h a b z S r s e ≠ 0 := by
  intro he
  apply markedPairSpechtMap_nonzero hu h a b z S r s e hr hs
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun t => t x) he)

lemma markedSectorIntertwiner_off {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (g : SymmetricGroup n) (hg : g ∉ Set.range (markedPairEmbeddingHom hu h z S))
    (x y : Specht a ⊗[ℂ] Specht b.transpose) :
    inner ℂ (markedSectorIntertwiner hu h a b z S r s e x)
      ((markedSectorRepresentation hu h a b C) g
        (markedSectorIntertwiner hu h a b z S r s e y)) = 0 :=
  markedPairInsertion_off hu h z S g hg _ _

lemma markedTypeSubrepresentation_norm {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (g : SymmetricGroup n) (x : MarkedSectorSpace hu h a b C) :
    ‖(markedSectorRepresentation hu h a b C) g x‖ = ‖x‖ :=
  markedWordRepresentation_norm h g (x.val : MarkedWordSpace p l n C)

lemma marked_sector_isometric_fiber_from_maps {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (r : Representation.IntertwiningMap (spechtRepresentation a) (wordRepresentation u C))
    (s : Representation.IntertwiningMap (spechtRepresentation b) (wordRepresentation v C))
    (e : Representation.Equiv (spechtRepresentation b.transpose) (signTwist (spechtRepresentation b)))
    (hr : Function.Injective r) (hs : Function.Injective s) :
    ∃ j : (Specht a ⊗[ℂ] Specht b.transpose) →ₗᵢ[ℂ]
        MarkedSectorSpace hu h a b C,
      (∀ g, (markedSectorRepresentation hu h a b C) (markedPairEmbeddingHom hu h z S g) ∘ₗ j.toLinearMap =
        j.toLinearMap ∘ₗ outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose) g) ∧
      (∀ g ∉ Set.range (markedPairEmbeddingHom hu h z S), ∀ x y,
        inner ℂ (j x) ((markedSectorRepresentation hu h a b C) g (j y)) = 0) := by
  let := specht_irreducible a
  let := specht_irreducible b.transpose
  let := outerTensorRepresentation_irreducible (spechtRepresentation a) (spechtRepresentation b.transpose)
    (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose)
  apply isometric_fiber_of_intertwiner (markedPairEmbeddingHom hu h z S)
    (outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose))
    (markedSectorRepresentation hu h a b C)
    (outerTensorRepresentation_norm _ _ (spechtRepresentation_norm a) (spechtRepresentation_norm b.transpose))
    (markedTypeSubrepresentation_norm (C:=C) hu h a b)
    (markedSectorIntertwiner (C:=C) hu h a b z S r s e)
  · exact markedSectorIntertwiner_nonzero (C:=C) hu h a b z S r s e hr hs
  · exact markedSectorIntertwiner_off (C:=C) hu h a b z S r s e

theorem marked_sector_isometric_fiber {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (z : MarkedAssignment l n) (S : EvenAllocation u p) :
    let τ := outerTensorRepresentation (spechtRepresentation a) (spechtRepresentation b.transpose)
    let σ := markedSectorRepresentation hu h a b C
    ∃ j : (Specht a ⊗[ℂ] Specht b.transpose) →ₗᵢ[ℂ] (MarkedSectorSpace hu h a b C),
      (∀ g, σ (markedPairEmbeddingHom hu h z S g) ∘ₗ j.toLinearMap =
        j.toLinearMap ∘ₗ τ g) ∧
      (∀ g ∉ Set.range (markedPairEmbeddingHom hu h z S), ∀ x y,
        inner ℂ (j x) (σ g (j y)) = 0) := by
  dsimp only
  let r := spechtOrbitIntertwiner a (wordRepresentation u C)
    (EuclideanSpace.single (rowColorWord a colorA) 1)
  let s := spechtOrbitIntertwiner b (wordRepresentation v C)
    (EuclideanSpace.single (rowColorWord b colorB) 1)
  obtain ⟨e⟩ := specht_transpose_sign_equiv b
  exact marked_sector_isometric_fiber_from_maps hu h a b z S r s e
    (specht_occurs_word a colorA) (specht_occurs_word b colorB)

end SignedSweeps
end

end OAI
