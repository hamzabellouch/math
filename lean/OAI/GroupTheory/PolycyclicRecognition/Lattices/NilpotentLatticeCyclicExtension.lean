import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeDerivationExtension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeWordExtension
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeAutomorphismFlow

namespace OAI

/-! # The iterative nilpotent lattice step

Ordered real generator powers extend conjugation; the finite logarithm of
its differential supplies the flow. The output retains the lattice parameter.
-/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H]

theorem NilpotentLatticeCoordinates.cyclic_extension
    (C : NilpotentLatticeCoordinates H) (a : MulAut H)
    [Group.IsNilpotent (H ⋊[integerPowerAction a] Multiplicative ℤ)] :
    Nonempty (NilpotentLatticeCoordinates
      (H ⋊[integerPowerAction a] Multiplicative ℤ)) := by
  let G := H ⋊[integerPowerAction a] Multiplicative ℤ
  let j : H →* G := SemidirectProduct.inl
  let t : G := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ℤ))
  have ha (x : H) : j (a x) = t * j x * t⁻¹ := by
    have h := SemidirectProduct.inl_aut (φ := integerPowerAction a)
      (Multiplicative.ofAdd (1 : ℤ)) x
    rw [map_inv] at h
    change j ((a ^ (1 : ℤ)) x) = t * j x * t⁻¹ at h
    simpa only [zpow_one] using h
  let q := C.lattice.subtype.comp C.equiv.toMonoidHom
  let F := latticeWordAut C.basis C.parameter q C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a
  obtain ⟨D, hD, htime⟩ := exists_nilpotent_lattice_automorphism_log
    C.basis C.parameter C.polynomial C.parameter.surjective q
    (fun z => ⟨orderedWord C.generators z, (C.integer_parameter z).symm⟩)
    j SemidirectProduct.inl_injective a t ha F
    (contMDiff_latticeWordAut C.basis C.parameter q C.generators
      C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a)
    (latticeWordAut_on_lattice C.basis C.parameter q C.generators
      C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a)
  apply C.derivation_extension a D hD
  intro x
  rw [htime]
  exact (latticeWordAut_on_lattice C.basis C.parameter q C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a x).symm

end PolycyclicRecognition

end

end OAI
