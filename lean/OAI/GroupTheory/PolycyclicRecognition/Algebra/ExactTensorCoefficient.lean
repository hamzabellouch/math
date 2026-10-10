import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveTensorCoefficient
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

namespace OAI

/-! # Exact tensoring by the flat integral coefficient

This uses flatness of the underlying integer module; no equivariant splitting
is claimed for the constant-functions sequence.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem representation_tensorLeft_map_exact (A : Rep.{0} ℤ G) [Module.Flat ℤ A]
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.Exact) :
    (S.map (tensorLeft A)).Exact := by
  have hs := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (S.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))).mp
      (hS.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))
  have he := Module.Flat.lTensor_exact A (f := S.f.hom.toLinearMap)
    (g := S.g.hom.toLinearMap) hs
  apply (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact he

theorem representation_tensorLeft_preserves_homology (A : Rep.{0} ℤ G) [Module.Flat ℤ A] :
    (tensorLeft A).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (representation_tensorLeft_map_exact A)

theorem representation_tensorLeft_map_shortExact (A : Rep.{0} ℤ G) [Module.Flat ℤ A]
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (S.map (tensorLeft A)).ShortExact := by
  let := representation_tensorLeft_preserves_homology A
  let := Functor.preservesMonomorphisms_of_map_exact (tensorLeft A)
    (representation_tensorLeft_map_exact A)
  let := Functor.preservesEpimorphisms_of_map_exact (tensorLeft A)
    (representation_tensorLeft_map_exact A)
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map (tensorLeft A)

end PolycyclicRecognition

end

end OAI
