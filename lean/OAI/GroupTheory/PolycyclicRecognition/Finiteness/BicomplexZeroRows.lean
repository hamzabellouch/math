import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainZeroProjection

namespace OAI

/-! # Replacing acyclic positive rows by their degree-zero homology -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex

abbrev bicomplexZeroRows (K : NatBicomplex) : NatBicomplex :=
  (integralChainZeroFunctor.mapHomologicalComplex (ComplexShape.down ℕ)).obj K

def bicomplexZeroRowsProjection (K : NatBicomplex) : K ⟶ bicomplexZeroRows K where
  f i := integralChainZeroProjection (K.X i)
  comm' i j _ := (integralChainZeroNatTrans.naturality (K.d i j)).symm

theorem bicomplexZeroRows_total_quasiIso (K : NatBicomplex)
    (hex : ∀ i j, (K.X i).ExactAt (j + 1)) :
    QuasiIso (HomologicalComplex₂.total.map (bicomplexZeroRowsProjection K)
      (ComplexShape.down ℕ)) :=
  bicomplex_total_of_row_epi_quasiIso (bicomplexZeroRowsProjection K)
    (fun i => show Epi (integralChainZeroProjection (K.X i)) from inferInstance) (fun i => integralChainZeroProjection_quasiIso (K.X i) (hex i))

theorem normalExtension_zeroRows_total_quasiIso {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] (P : ProjectiveResolution (trivialIntegral G)) :
    QuasiIso (HomologicalComplex₂.total.map
      (bicomplexZeroRowsProjection (normalExtensionBicomplex N P)) (ComplexShape.down ℕ)) := by
  apply bicomplexZeroRows_total_quasiIso
  intro i j
  exact ((normalExtensionBicomplex N P).X i).exactAt_iff_isZero_homology (j + 1) |>.mpr
    (normalExtensionRowHomology_succ_isZero N P i j)

end PolycyclicRecognition

end

end OAI
