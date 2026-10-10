import OAI.GroupTheory.PolycyclicRecognition.Algebra.FreeCoefficientCoinvariants

namespace OAI

/-! # Positive group homology vanishes for projective coefficients

Free coefficients reduce to finite-support sums of an exact bar resolution.
Projective coefficients are handled by an actual split free cover.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Finsupp.module
variable {G : Type} [Group G]

instance freeCoefficientCoinvariants_preservesHomology (ι : Type) :
    ((Rep.coinvariantsTensor ℤ G).obj (Rep.free ℤ G ι)).PreservesHomology := by
  classical
  let F := forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ) ⋙ moduleFinsuppFunctor ℤ ι
  let : PreservesFiniteLimits (moduleFinsuppFunctor ℤ ι) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (moduleFinsuppFunctor ℤ ι) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  let : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let : PreservesFiniteLimits ((Rep.coinvariantsTensor ℤ G).obj (Rep.free ℤ G ι)) :=
    preservesFiniteLimits_of_natIso (freeCoefficientCoinvariantsIso (G := G) ι).symm
  let : PreservesFiniteColimits ((Rep.coinvariantsTensor ℤ G).obj (Rep.free ℤ G ι)) :=
    preservesFiniteColimits_of_natIso (freeCoefficientCoinvariantsIso (G := G) ι).symm
  infer_instance

theorem freeCoefficient_groupHomology_succ_isZero (ι : Type) (n : ℕ) :
    IsZero (groupHomology (Rep.free ℤ G ι) (n + 1)) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj (Rep.free ℤ G ι)
  have he : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex ℤ G)).ExactAt (n + 1) :=
    ((Rep.barResolution ℤ G).complex_exactAt_succ n).map F
  exact he.isZero_homology.of_iso
    (groupHomologyIso (Rep.free ℤ G ι) (n + 1) (Rep.barResolution ℤ G))

theorem projectiveCoefficient_groupHomology_succ_isZero (A : Rep.{0} ℤ G)
    [Projective A] (n : ℕ) : IsZero (groupHomology A (n + 1)) := by
  classical
  let f : Rep.free ℤ G A.V ⟶ A := Rep.freeLift ℤ G A (fun a => a)
  have hf : Function.Surjective f := by
    intro a
    refine ⟨Finsupp.single a (MonoidAlgebra.single 1 1), ?_⟩
    change Representation.freeLift A.ρ (fun a => a)
      (Finsupp.single a (MonoidAlgebra.single 1 1)) = a
    rw [Representation.freeLift_single_single, map_one]
    exact @one_smul ℤ A.V _ A.hV2.toMulAction a
  let : Epi f := (Rep.epi_iff_surjective f).mpr hf
  let s := Projective.factorThru (𝟙 A) f
  have hs : s ≫ f = 𝟙 A := Projective.factorThru_comp _ _
  have hz := freeCoefficient_groupHomology_succ_isZero (G := G) A.V n
  have hm := groupHomology.map_id_comp s f (n + 1)
  rw [hs, groupHomology.map_id] at hm
  have hzero : groupHomology.map (MonoidHom.id G) s (n + 1) = 0 := hz.eq_of_tgt _ _
  rw [hzero, zero_comp] at hm
  exact (IsZero.iff_id_eq_zero _).mpr hm

theorem normalExtensionRowHomology_succ_isZero (N : Subgroup G) [N.Normal]
    (P : ProjectiveResolution (trivialIntegral G)) (i j : ℕ) :
    IsZero (((normalExtensionBicomplex N P).X i).homology (j + 1)) :=
  (projectiveCoefficient_groupHomology_succ_isZero
    ((normalQuotientResolutionComplex N P).X i) j).of_iso
      (normalExtensionRowHomologyIso N P i (j + 1))

end PolycyclicRecognition

end

end OAI
