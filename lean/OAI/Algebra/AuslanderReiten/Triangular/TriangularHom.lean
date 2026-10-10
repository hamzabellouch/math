import OAI.Algebra.AuslanderReiten.Triangular.TriangularModule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctor

namespace OAI

namespace ArExplicit.TriangularModule

variable {k R F M N M' N' : Type*} [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module k M'] [Module R M']
variable [AddCommGroup N'] [Module R N']
variable {φ : BalancedTensor k R F M →ₗ[R] N}
variable {ψ : BalancedTensor k R F M' →ₗ[R] N'}

def hom (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (h : ∀ f m, b (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (a m))) :
    TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ where
  toFun x := ⟨a x.top, b x.bottom⟩
  map_add' x y := by ext <;> simp
  map_smul' t x := by
    ext
    · exact a.map_smul t.top x.top
    · simp only [bottom_smul, map_add, h, map_smul, RingHom.id_apply]

@[simp] theorem hom_top (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (h : ∀ f m, b (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (a m)))
    (x : TriangularModule k R F M N φ) : (hom a b h x).top = a x.top := rfl

@[simp] theorem hom_bottom (a : M →ₗ[R] M') (b : N →ₗ[R] N')
    (h : ∀ f m, b (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (a m)))
    (x : TriangularModule k R F M N φ) : (hom a b h x).bottom = b x.bottom := rfl

variable (g : TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ)

theorem top_of_map (x : TriangularModule k R F M N φ) :
    (g ⟨x.top, 0⟩).top = (g x).top := by
  have h := congrArg TriangularModule.top (g.map_smul (⟨1, 0, 0⟩ : Triangular R F) x)
  have he : (⟨1, 0, 0⟩ : Triangular R F) • x = ⟨x.top, 0⟩ := by ext <;> simp
  rw [he] at h
  simpa using h

theorem bottom_of_map (x : TriangularModule k R F M N φ) :
    (g ⟨0, x.bottom⟩).bottom = (g x).bottom := by
  have h := congrArg TriangularModule.bottom (g.map_smul (⟨0, 1, 0⟩ : Triangular R F) x)
  have he : (⟨0, 1, 0⟩ : Triangular R F) • x = ⟨0, x.bottom⟩ := by ext <;> simp
  rw [he] at h
  simpa using h

def topMap : M →ₗ[R] M' where
  toFun m := (g ⟨m, 0⟩).top
  map_add' m n := by
    have h : (⟨m + n, 0⟩ : TriangularModule k R F M N φ) = ⟨m, 0⟩ + ⟨n, 0⟩ := by
      ext <;> simp
    rw [h]
    rw [g.map_add]
    rfl
  map_smul' r m := by
    have h := congrArg TriangularModule.top
      (g.map_smul (⟨r, 0, 0⟩ : Triangular R F) ⟨m, 0⟩)
    have he : (⟨r, 0, 0⟩ : Triangular R F) •
        (⟨m, 0⟩ : TriangularModule k R F M N φ) = ⟨r • m, 0⟩ := by ext <;> simp
    rw [he] at h
    exact h

def bottomMap : N →ₗ[R] N' where
  toFun n := (g ⟨0, n⟩).bottom
  map_add' m n := by
    have h : (⟨0, m + n⟩ : TriangularModule k R F M N φ) = ⟨0, m⟩ + ⟨0, n⟩ := by
      ext <;> simp
    rw [h]
    rw [g.map_add]
    rfl
  map_smul' r n := by
    have h := congrArg TriangularModule.bottom
      (g.map_smul (⟨0, r, 0⟩ : Triangular R F) ⟨0, n⟩)
    have he : (⟨0, r, 0⟩ : Triangular R F) •
        (⟨0, n⟩ : TriangularModule k R F M N φ) = ⟨0, r • n⟩ := by ext <;> simp
    rw [he] at h
    simpa using h

@[simp] theorem topMap_apply (m : M) : topMap g m = (g ⟨m, 0⟩).top := rfl
@[simp] theorem bottomMap_apply (n : N) : bottomMap g n = (g ⟨0, n⟩).bottom := rfl

theorem compatibility (f : F) (m : M) :
    bottomMap g (φ (BalancedTensor.tmul f m)) = ψ (BalancedTensor.tmul f (topMap g m)) := by
  have h := congrArg TriangularModule.bottom
    (g.map_smul (⟨0, 0, f⟩ : Triangular R F) ⟨m, 0⟩)
  have he : (⟨0, 0, f⟩ : Triangular R F) •
      (⟨m, 0⟩ : TriangularModule k R F M N φ) = ⟨0, φ (BalancedTensor.tmul f m)⟩ := by
    ext <;> simp
  rw [he] at h
  simpa using h

theorem hom_topMap_bottomMap : hom (topMap g) (bottomMap g) (compatibility g) = g := by
  apply LinearMap.ext
  intro x
  ext
  · exact top_of_map g x
  · exact bottom_of_map g x

@[ext] theorem hom_ext
    (g' : TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ)
    (ht : topMap g = topMap g') (hb : bottomMap g = bottomMap g') : g = g' := by
  apply LinearMap.ext
  intro x
  ext
  · rw [← top_of_map g x, ← top_of_map g' x]
    exact congrArg (fun a : M →ₗ[R] M' => a x.top) ht
  · rw [← bottom_of_map g x, ← bottom_of_map g' x]
    exact congrArg (fun b : N →ₗ[R] N' => b x.bottom) hb

end ArExplicit.TriangularModule

end OAI
