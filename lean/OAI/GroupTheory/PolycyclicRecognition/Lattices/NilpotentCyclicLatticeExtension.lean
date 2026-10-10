import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeAutomorphismFlow
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice
import OAI.GroupTheory.PolycyclicRecognition.Lattices.DerivationSolvableModel

namespace OAI

/-! # The cyclic step in nilpotent lattice realization

Given a polynomial lattice model for the kernel and the smooth extension of
its conjugation automorphism, nilpotence supplies the real flow and the
resulting cyclic extension is a uniform lattice in a constructed solvable
Lie group.
-/

noncomputable section
namespace PolycyclicRecognition
open Module
open scoped Manifold ContDiff
attribute [local instance] semidirectProductTopology
variable {H L : Type} [Group H] [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]

theorem nilpotent_cyclic_lattice_extension (a : MulAut H)
    [Group.IsNilpotent (H ⋊[integerPowerAction a] Multiplicative ℤ)]
    {d : ℕ} (b : Basis (Fin d) ℝ L) (p : L → L)
    (hp : IsPolynomialInBasis b b p) (hsurj : Function.Surjective p)
    (Λ : Subgroup L) (hΛ : IsUniformLattice Λ) (e : H ≃* Λ)
    (hgrid : ∀ z : Fin d → ℤ, ∃ x : H,
      (e x : L) = p (b.equivFun.symm (fun i => (z i : ℝ))))
    (F : L ≃* L) (hF : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ F)
    (he : ∀ x, F (e x) = (e (a x) : L)) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧
        Nonempty ((H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  let G := H ⋊[integerPowerAction a] Multiplicative ℤ
  let j : H →* G := SemidirectProduct.inl
  let t : G := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
  have ha (x : H) : j (a x) = t * j x * t⁻¹ := by
    have h := SemidirectProduct.inl_aut (φ := integerPowerAction a)
      (Multiplicative.ofAdd (1 : ℤ)) x
    rw [map_inv] at h
    change j ((a ^ (1 : ℤ)) x) = t * j x * t⁻¹ at h
    simpa only [zpow_one] using h
  let q : H →* L := Λ.subtype.comp e.toMonoidHom
  obtain ⟨D, hD, htime⟩ := exists_nilpotent_lattice_automorphism_log b p hp hsurj
    q hgrid j SemidirectProduct.inl_injective a t ha F hF he
  let φ := P.derivationAction D hD
  have hstep (x : H) : (e (a x) : L) = φ (Multiplicative.ofAdd 1) (e x) := by
    change (e (a x) : L) = nilpotentDerivationFlow D hD 1 (e x)
    rw [htime, he]
  obtain ⟨Γ, hΓ, ⟨f⟩⟩ := integer_semidirect_lattice_realization φ a Λ hΛ e hstep
  let S := derivationSolvableLieModel D hD
  let E := derivationModelEquiv D hD
  refine ⟨S, Γ.comap E.toMonoidHom, ?_, ⟨f.trans (comapSubgroupEquiv E Γ).symm⟩⟩
  exact hΓ.comap_mulEquiv E (continuous_derivationModelEquiv D hD)
    (continuous_derivationModelEquiv_symm D hD)

end PolycyclicRecognition

end

end OAI
