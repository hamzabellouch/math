import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialParameterExtension

namespace OAI

/-! # Extending lattice automorphisms through ordered polynomial coordinates

The extension is constructed by replacing each integral generator power by
the corresponding real one-parameter subgroup. Polynomial identities prove
both multiplicativity and the inverse identities.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold ContDiff
variable {L H : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group H] {d : ℕ}
  (b : Basis (Fin d) ℝ L) (p : L ≃ L) (e : H →* L) (X : Fin d → H)

def latticeWordMap (a : H →* H) : L → L :=
  fun x => orderedRealWord b (fun i => e (a (X i))) (p.symm x)

theorem latticeWordMap_polynomial (hq : IsPolynomialInBasis b b p.symm) (a : H →* H) :
    IsPolynomialInBasis b b (latticeWordMap b p e X a) :=
  (orderedRealWord_polynomial b _).comp hq

theorem latticeWordMap_on_lattice
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : H →* H) (x : H) :
    latticeWordMap b p e X a (e x) = e (a x) := by
  obtain ⟨z, rfl⟩ := hX x
  rw [← hparam z]
  change orderedRealWord b (fun i => e (a (X i)))
    (p.symm (p (b.equivFun.symm (fun i => (z i : ℝ))))) = _
  rw [p.symm_apply_apply, orderedRealWord_integer]
  exact orderedWord_map (e.comp a) X z

def latticeWordAut (hp : IsPolynomialInBasis b b p) (hq : IsPolynomialInBasis b b p.symm)
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : MulAut H) : MulAut L := by
  let f := latticeWordMap b p e X a.toMonoidHom
  let g := latticeWordMap b p e X a.symm.toMonoidHom
  have hf := latticeWordMap_polynomial b p e X hq a.toMonoidHom
  have hg := latticeWordMap_polynomial b p e X hq a.symm.toMonoidHom
  have hF (x : H) : f (e x) = e (a x) :=
    latticeWordMap_on_lattice b p e X hparam hX a.toMonoidHom x
  have hG (x : H) : g (e x) = e (a.symm x) :=
    latticeWordMap_on_lattice b p e X hparam hX a.symm.toMonoidHom x
  refine polynomialGroupEquivFromParameter b hf hg hp p.surjective ?_ ?_ ?_
  · intro z w
    rw [hparam z, hparam w]
    calc
      f (e (orderedWord X z) * e (orderedWord X w)) =
          e (a (orderedWord X z * orderedWord X w)) := by rw [← map_mul, hF]
      _ = e (a (orderedWord X z)) * e (a (orderedWord X w)) := by rw [map_mul, map_mul]
      _ = f (e (orderedWord X z)) * f (e (orderedWord X w)) := by rw [hF, hF]
  · intro z
    change g (f (p (b.equivFun.symm (fun i => (z i : ℝ))))) =
      p (b.equivFun.symm (fun i => (z i : ℝ)))
    rw [hparam z, hF, hG, a.symm_apply_apply]
  · intro z
    change f (g (p (b.equivFun.symm (fun i => (z i : ℝ))))) =
      p (b.equivFun.symm (fun i => (z i : ℝ)))
    rw [hparam z, hG, hF, a.apply_symm_apply]

theorem latticeWordAut_on_lattice (hp : IsPolynomialInBasis b b p)
    (hq : IsPolynomialInBasis b b p.symm)
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : MulAut H) (x : H) :
    latticeWordAut b p e X hp hq hparam hX a (e x) = e (a x) :=
  latticeWordMap_on_lattice b p e X hparam hX a.toMonoidHom x

theorem contMDiff_latticeWordAut (hp : IsPolynomialInBasis b b p)
    (hq : IsPolynomialInBasis b b p.symm)
    (hparam : ∀ z : Fin d → ℤ,
      p (b.equivFun.symm (fun i => (z i : ℝ))) = e (orderedWord X z))
    (hX : Function.Surjective (orderedWord X)) (a : MulAut H) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (latticeWordAut b p e X hp hq hparam hX a) := by
  have h : ContDiff ℝ ∞ (latticeWordMap b p e X a.toMonoidHom) :=
    (latticeWordMap_polynomial b p e X hq a.toMonoidHom).contDiff.of_le le_top
  exact h.contMDiff

end PolycyclicRecognition

end

end OAI
