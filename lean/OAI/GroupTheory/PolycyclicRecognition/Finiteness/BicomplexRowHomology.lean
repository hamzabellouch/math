import OAI.GroupTheory.PolycyclicRecognition.Algebra.SingleRowsTotal

namespace OAI

/-! # Total homology after eliminating the positive rows -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex

abbrev rowOpcyclesComplex (K : NatBicomplex) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((opcyclesFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K

def zeroRowsTotalIso (K : NatBicomplex) :
    (bicomplexZeroRows K).total (ComplexShape.down ℕ) ≅ rowOpcyclesComplex K := by
  exact singleRowsTotalIso (rowOpcyclesComplex K)

def totalRowZeroHomologyIso (K : NatBicomplex)
    (hex : ∀ i j, (K.X i).ExactAt (j + 1)) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).homology n ≅ (rowOpcyclesComplex K).homology n := by
  have := bicomplexZeroRows_total_quasiIso K hex
  exact asIso (homologyMap
      (HomologicalComplex₂.total.map (bicomplexZeroRowsProjection K) (ComplexShape.down ℕ)) n) ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso (zeroRowsTotalIso K)

def normalExtensionTotalRowZeroHomologyIso {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ) :
    ((normalExtensionBicomplex N P).total (ComplexShape.down ℕ)).homology n ≅
      (rowOpcyclesComplex (normalExtensionBicomplex N P)).homology n := by
  apply totalRowZeroHomologyIso
  intro i j
  exact (((normalExtensionBicomplex N P).X i).exactAt_iff_isZero_homology (j + 1)).mpr
    (normalExtensionRowHomology_succ_isZero N P i j)

end PolycyclicRecognition

end

end OAI
