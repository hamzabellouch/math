import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteColumnComplex

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)

/-- The vertical differential on the finite direct sum of the columns. -/
def diagonal (n : ℤ) : term K n →ₗ[R] term K (n+1) :=
  LinearMap.pi (fun i => ((K i).d n (n+1)).hom.comp (LinearMap.proj i))

@[simp] theorem diagonal_apply (n : ℤ) (z : term K n) (i : Fin l) :
    diagonal K n z i = ((K i).d n (n+1)).hom (z i) := rfl

theorem diagonal_square (n : ℤ) : (diagonal K (n+1)).comp (diagonal K n) = 0 := by
  apply LinearMap.ext
  intro z
  funext i
  exact congrArg (fun f => f.hom (z i)) ((K i).d_comp_d n (n+1) ((n+1)+1))

/-- A horizontal differential on signed columns, with its actual square and mixed relation. -/
structure Horizontal where
  d : ∀ n : ℤ, term K n →ₗ[R] term K (n+1)
  square : ∀ n, (d (n+1)).comp (d n) = 0
  mixed : ∀ n, (diagonal K (n+1)).comp (d n) + (d (n+1)).comp (diagonal K n) = 0
  strictUpper : ∀ (n : ℤ) (i : Fin l) (z : term K n),
    (∀ j : Fin l, j.val < i.val → z j = 0) → d n z i = 0

variable (H : Horizontal K)

/-- The full differential is the sum of the signed vertical and horizontal differentials. -/
def totalDifferential : Differential K where
  d n := diagonal K n + H.d n
  square n := by
    apply LinearMap.ext
    intro z
    funext i
    have hv := congrArg (fun f : term K n →ₗ[R] term K ((n+1)+1) => f z i) (diagonal_square K n)
    have hh := congrArg (fun f : term K n →ₗ[R] term K ((n+1)+1) => f z i) (H.square n)
    have hm := congrArg (fun f : term K n →ₗ[R] term K ((n+1)+1) => f z i) (H.mixed n)
    simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.zero_apply,Pi.add_apply,Pi.zero_apply] at hv hh hm ⊢
    simp only [map_add,Pi.add_apply]
    simp only [diagonal_apply] at hv hh hm ⊢
    rw [hv,hh]
    simpa only [zero_add,add_zero] using hm
  triangular n i z hz := by
    change diagonal K n z i + H.d n z i = _
    rw [H.strictUpper n i z hz,add_zero]
    rfl

def total : CochainComplex (ModuleCat.{u} R) ℤ := complex K (totalDifferential K H)

theorem total_acyclic (hK : ∀ i, (K i).Acyclic) : (total K H).Acyclic :=
  acyclic K (totalDifferential K H) hK
end LittleFinitistic.FiniteColumnComplex

end

end OAI
