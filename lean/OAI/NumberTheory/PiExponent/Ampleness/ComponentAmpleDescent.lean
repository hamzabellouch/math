import OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentCover
import OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentLocal
import OAI.NumberTheory.PiExponent.Ampleness.ComponentAmpleDescentSupported
import OAI.NumberTheory.PiExponent.Approximation.ClosedUnitKernel
import OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem exists_complementary_ideal_descent
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤) :
    ∃ N : J.subscheme.Modules, N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj N ≅ closedModule I) := by
  have : (closedModule I).IsFinitePresentation := closedModule_isFinitePresentation I
  apply ClosedAnnihilatedDescent.exists_closed_coherent_descent J.subschemeι (closedModule I)
  intro U
  exact closedModule_restrict_annihilated hcover U

theorem eventual_restriction_surjective_of_complement_ample
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (K L : LineBundle X) (I J : X.IdealSheafData)
    (hcover : I.support ⊔ J.support = ⊤) (hJ : (L.pullback J.subschemeι).IsAmple) :
    ∃ B : ℕ, ∀ n ≥ B, Function.Surjective
      (fun s : GlobalSections X (K.tensor (L.pow n)).sheaf => pullbackSection I.subschemeι s) := by
  obtain ⟨N,hN,⟨e⟩⟩ := exists_complementary_ideal_descent I J hcover
  let : N.IsFinitePresentation := hN
  obtain ⟨B,hB⟩ := eventual_tensor_cohomology_zero_of_closed_pushforward p J.subschemeι
    (closedModule I) N e K L hJ
  refine ⟨B,fun n hn => ?_⟩
  exact pullbackSection_surjective_of_idealTensor_cohomology_zero I.subschemeι
    (K.tensor (L.pow n)) (hB n hn 1 (by decide))

theorem isAmple_of_reduced_closed_cover
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤)
    (hI : (L.pullback I.subschemeι).IsAmple) (hJ : (L.pullback J.subschemeι).IsAmple) :
    L.IsAmple := by
  let : NoetherianSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : NoetherianSpace J.subscheme :=
    J.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  have hc : Set.range I.subschemeι ∪ Set.range J.subschemeι = Set.univ := by
    rw [I.range_subschemeι,J.range_subschemeι]
    exact congrArg (fun Z : Closeds X => (Z : Set X)) hcover
  exact isAmple_of_eventual_restriction_surjective I.subschemeι J.subschemeι L H hH hc hI hJ
    (eventual_restriction_surjective_of_complement_ample p H.inverse L I J hcover hJ)
    (eventual_restriction_surjective_of_complement_ample p H.inverse L J I
      (by simpa only [sup_comm] using hcover) hI)

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
