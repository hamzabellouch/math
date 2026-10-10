import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

noncomputable section

open scoped BigOperators
open Matrix

namespace Problem336.IncidenceCirculation

variable {V E R : Type*} [DecidableEq V] [Fintype V] [Fintype E] [CommRing R]

def incidence (src dst : E → V) : Matrix V E R :=
  fun v e => (if v = src e then 1 else 0) - (if v = dst e then 1 else 0)

def reducedIncidence (src dst : E → V) (root : V) : Matrix {v : V // v ≠ root} E R :=
  fun v e => incidence src dst v.1 e

omit [Fintype E] in
@[simp] theorem sum_incidence_column (src dst : E → V) (e : E) :
    ∑ v, incidence (R := R) src dst v e = 0 := by
  simp [incidence, Finset.sum_sub_distrib]

theorem sum_divergence (src dst : E → V) (x : E → R) :
    ∑ v, (incidence src dst *ᵥ x) v = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_incidence_column, zero_mul]
  exact Finset.sum_const_zero

theorem divergence_eq_zero_of_off_root (src dst : E → V) (root : V) (x : E → R)
    (h : ∀ v, v ≠ root → (incidence src dst *ᵥ x) v = 0) :
    incidence src dst *ᵥ x = 0 := by
  have hroot : (incidence src dst *ᵥ x) root = 0 := by
    have hsum := sum_divergence src dst x
    rwa [Finset.sum_eq_single root (fun v _ hv => h v hv) (by simp)] at hsum
  funext v
  by_cases hv : v = root
  · simpa [hv] using hroot
  · exact h v hv

theorem reduced_mulVec_eq_zero_iff (src dst : E → V) (root : V) (x : E → R) :
    reducedIncidence src dst root *ᵥ x = 0 ↔ incidence src dst *ᵥ x = 0 := by
  constructor
  · intro h
    apply divergence_eq_zero_of_off_root src dst root x
    intro v hv
    exact congrFun h ⟨v, hv⟩
  · intro h
    funext v
    exact congrFun h v.1

theorem reduced_mulVec_eq_zero_iff_root (src dst : E → V) (root root' : V) (x : E → R) :
    reducedIncidence src dst root *ᵥ x = 0 ↔
      reducedIncidence src dst root' *ᵥ x = 0 := by
  rw [reduced_mulVec_eq_zero_iff, reduced_mulVec_eq_zero_iff]

def pushMatrix {A B : Type*} [DecidableEq B] (f : A → B) : Matrix B A R :=
  fun b a => if f a = b then 1 else 0

variable {V' E' : Type*} [DecidableEq V'] [DecidableEq E'] [finiteTargetVertices : Fintype V'] [Fintype E']

omit [Fintype E] [Fintype V'] in

theorem incidence_naturality (src dst : E → V) (src' dst' : E' → V')
    (f : E → E') (g : V → V')
    (hsrc : ∀ e, src' (f e) = g (src e)) (hdst : ∀ e, dst' (f e) = g (dst e)) :
    (incidence (R := R) src' dst' * pushMatrix f : Matrix V' E R) =
      pushMatrix g * incidence src dst := by
  ext v e
  simp only [Matrix.mul_apply, incidence, pushMatrix]
  simp [mul_sub, Finset.sum_sub_distrib, hsrc, hdst, eq_comm]

omit [Fintype V'] in

theorem circulation_pushForward (src dst : E → V) (src' dst' : E' → V')
    (f : E → E') (g : V → V')
    (hsrc : ∀ e, src' (f e) = g (src e)) (hdst : ∀ e, dst' (f e) = g (dst e))
    (x : E → R) (hx : incidence src dst *ᵥ x = 0) :
    incidence src' dst' *ᵥ (pushMatrix f *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, incidence_naturality src dst src' dst' f g hsrc hdst,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

theorem reduced_circulation_pushForward (src dst : E → V) (src' dst' : E' → V')
    (root : V) (root' : V') (f : E → E') (g : V → V')
    (hsrc : ∀ e, src' (f e) = g (src e)) (hdst : ∀ e, dst' (f e) = g (dst e))
    (x : E → R) (hx : reducedIncidence src dst root *ᵥ x = 0) :
    reducedIncidence src' dst' root' *ᵥ (pushMatrix f *ᵥ x) = 0 := by
  apply (reduced_mulVec_eq_zero_iff src' dst' root' _).2
  exact circulation_pushForward src dst src' dst' f g hsrc hdst x
    ((reduced_mulVec_eq_zero_iff src dst root x).1 hx)

omit [Fintype E'] in

theorem pushMatrix_mulVec_apply (f : E → E') (hf : Function.Injective f) (x : E → R) (e : E) :
    (pushMatrix f *ᵥ x) (f e) = x e := by
  classical
  simp [Matrix.mulVec, dotProduct, pushMatrix, hf.eq_iff]

omit [Fintype E'] in

theorem pushMatrix_mulVec_apply_of_not_mem_range (f : E → E') (x : E → R) (e' : E')
    (he' : e' ∉ Set.range f) : (pushMatrix f *ᵥ x) e' = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  have hne : f e ≠ e' := fun h => he' ⟨e, h⟩
  simp [pushMatrix, hne]

def circulationSpace (src dst : E → V) : Submodule R (E → R) :=
  LinearMap.ker (incidence src dst).mulVecLin

theorem reduced_circulationSpace_eq (src dst : E → V) (root : V) :
    LinearMap.ker (reducedIncidence (R := R) src dst root).mulVecLin =
      circulationSpace src dst := by
  ext x
  exact reduced_mulVec_eq_zero_iff src dst root x

omit finiteTargetVertices in
theorem circulationSpace_map_le [Fintype V'] (src dst : E → V) (src' dst' : E' → V')
    (f : E → E') (g : V → V')
    (hsrc : ∀ e, src' (f e) = g (src e)) (hdst : ∀ e, dst' (f e) = g (dst e)) :
    (circulationSpace (R := R) src dst).map (pushMatrix f).mulVecLin ≤
      circulationSpace src' dst' := by
  rintro y ⟨x, hx, rfl⟩
  exact circulation_pushForward src dst src' dst' f g hsrc hdst x hx

end Problem336.IncidenceCirculation

end

end OAI
