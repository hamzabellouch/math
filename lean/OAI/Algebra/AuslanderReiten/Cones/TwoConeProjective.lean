import OAI.Algebra.AuslanderReiten.Cones.ConeCokernel
import OAI.Algebra.AuslanderReiten.Modules.SplitModules
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)

abbrev BaseCokernel (n : ℕ) := D.term n ⧸ LinearMap.range (D.d n)
abbrev FirstCokernel (n : ℕ) := firstTerm D n ⧸ LinearMap.range (firstD D n)

def baseSuccessorEquiv (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    BaseCokernel D (n+1) ≃ₗ[R] LinearMap.ker (LinearMap.range (D.d n)).mkQ :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp (hex n)).symm).trans
    ((D.d n).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ (LinearMap.range (D.d n))).symm))

theorem baseCokernel_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (D.term n))
    [Module.Projective R (BaseCokernel D 0)] (n : ℕ) :
    Module.Projective R (BaseCokernel D n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let := ih
    let := hp n
    let := projective_kernel_of_surjective (LinearMap.range (D.d n)).mkQ
      (Submodule.mkQ_surjective _)
    exact Module.Projective.of_equiv (baseSuccessorEquiv D hex n).symm

theorem firstCokernel_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (BaseCokernel D n)) (n : ℕ) :
    Module.Projective R (FirstCokernel D n) := by
  let := hp n
  let := hp (n+2)
  exact ConeCokernel.projective (D.d n) (D.d (n+2)) (D.first n)
    (D.d (n+3)) (D.first (n+1)) (hex (n+2)) (D.first_comm n)

theorem cokernel_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (BaseCokernel D n)) (n : ℕ) :
    Module.Projective R (Cokernel D n) := by
  let := firstCokernel_projective D hex hp n
  let := firstCokernel_projective D hex hp (n+2)
  exact ConeCokernel.projective (firstD D n) (firstD D (n+2)) (secondOnFirst D n)
    (firstD D (n+3)) (secondOnFirst D (n+1)) (firstD_exact D hex (n+2))
    (secondOnFirst_comm D n)

theorem C₁_projective
    (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
    (hp : ∀ n, Module.Projective R (D.term n))
    [Module.Projective R (BaseCokernel D 0)] : Module.Projective R (C₁ D) :=
  cokernel_projective D hex (baseCokernel_projective D hex hp) 1

end ArExplicit.TwoCone

end

end OAI
