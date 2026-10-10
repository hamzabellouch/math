import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalAcyclicKernelHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalNilpotentHomologyVanishing

namespace OAI

/-! # Removing a countable locally finite normal subgroup in rational homology

Finite-support representatives lie in finite subgroups, where transfer from
the trivial subgroup kills positive rational homology. The normal-extension
comparison then identifies ambient and quotient rational homology.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem locallyFinite_rational_homology_isZero [Countable G]
    (hG : ∀ H : Subgroup G, H.FG → Finite H)
    (A : Rep ℤ G) (i : ℕ) (hi : 0 < i) :
    IsZero (rationalModuleFunctor.obj (groupHomology A i)) := by
  obtain ⟨S, hS, hSfg, hcover⟩ := exists_fg_subgroup_exhaustion (G := G)
  have hindex (n : ℕ) : ((⊥ : Subgroup G).subgroupOf (S n)).FiniteIndex := by
    let : Finite (S n) := hG (S n) (hSfg n)
    infer_instance
  let := (poincareDuality_zero_of_subsingleton (⊥ : Subgroup G)).cohomologicalDimension
  exact rational_homology_isZero_of_surjective A (Rep.res (⊥ : Subgroup G).subtype A) i
    ((subgroupHomologyInclusion ⊥ A i).hom.baseChange ℚ)
    (rational_homology_core_surjective ⊥ S hS hcover (fun _ => bot_le) hindex A i)
    (rationalModuleFunctor.map_isZero (groupHomology_isZero_above_dimension 0 _ i hi))

def locallyFiniteKernelRationalHomologyIso (N : Subgroup G) [N.Normal] [Countable N]
    (hN : ∀ H : Subgroup N, H.FG → Finite H) (n : ℕ) :
    rationalModuleFunctor.obj (groupHomology (trivialIntegral G) n) ≅
      rationalModuleFunctor.obj (groupHomology (trivialIntegral (G ⧸ N)) n) :=
  rationalAcyclicKernelHomologyIso N
    (fun i hi => locallyFinite_rational_homology_isZero hN (trivialIntegral N) i hi) n

def torsionNilpotentKernelRationalHomologyIso (N : Subgroup G) [N.Normal]
    [Countable N] [Group.IsNilpotent N] (ht : ∀ g : N, IsOfFinOrder g) (n : ℕ) :
    rationalModuleFunctor.obj (groupHomology (trivialIntegral G) n) ≅
      rationalModuleFunctor.obj (groupHomology (trivialIntegral (G ⧸ N)) n) :=
  rationalAcyclicKernelHomologyIso N
    (fun i hi => torsion_nilpotent_rational_homology_isZero ht (trivialIntegral N) i hi) n

end PolycyclicRecognition

end

end OAI
