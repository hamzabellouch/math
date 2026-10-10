import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalBicomplexHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalZeroCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexRowHomology

namespace OAI

/-! # Rational total comparison for the actual integral bicomplex

Exact rationalization allows the row kernel to be rationally acyclic. The
integral rows themselves need not be exact.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

abbrev rationalChainFunctor :=
  rationalModuleFunctor.mapHomologicalComplex (ComplexShape.down ℕ)

instance rationalModuleFunctor_preservesFiniteLimits :
    PreservesFiniteLimits rationalModuleFunctor :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance rationalModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits rationalModuleFunctor :=
  Functor.preservesFiniteColimits_of_preservesHomology _

theorem rational_total_homology_isZero_of_rows (K : NatBicomplex)
    (hz : ∀ i j, IsZero (rationalModuleFunctor.obj ((K.X i).homology j)))
    (n : ℕ) : IsZero (rationalModuleFunctor.obj
      ((K.total (ComplexShape.down ℕ)).homology n)) := by
  apply rational_total_homology_isZero_of_secondPage K n
  intro p j _
  apply rational_homology_isZero_of_term (rowHomologyComplex K j) p
  exact hz p j

theorem rational_bicomplex_total_of_row_epi_quasiIso {K L : NatBicomplex} (f : K ⟶ L)
    (hepi : ∀ i, Epi (f.f i))
    (hquasi : ∀ i, QuasiIso (rationalChainFunctor.map (f.f i))) :
    QuasiIso (rationalChainFunctor.map
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ))) := by
  let S : ShortComplex NatBicomplex :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let : Epi f := HomologicalComplex.epi_of_epi_f f hepi
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
  have hz : ∀ i j, IsZero (rationalModuleFunctor.obj ((S.X₁.X i).homology j)) := by
    intro i j
    have hSi := (hS.map (HomologicalComplex.eval _ _ i)).map_of_exact rationalChainFunctor
    exact (hSi.acyclic_X₁ (hquasi i) j).isZero_homology.of_iso
      (rationalModuleHomologyIso (S.X₁.X i) j).symm
  let : PreservesFiniteLimits integralFirstQuadrantTotal :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits integralFirstQuadrantTotal :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  have hT := (hS.map_of_exact integralFirstQuadrantTotal).map_of_exact rationalChainFunctor
  apply integral_shortExact_quasiIso_g _ hT
  intro n
  exact (rational_total_homology_isZero_of_rows S.X₁ hz n).of_iso
    (rationalModuleHomologyIso (S.X₁.total (ComplexShape.down ℕ)) n)

theorem rational_chainZeroProjection_quasiIso (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (hz : ∀ n, IsZero (rationalModuleFunctor.obj (K.homology (n + 1)))) :
    QuasiIso (rationalChainFunctor.map (integralChainZeroProjection K)) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    let := integralChainZeroProjection_quasiIsoAt_zero K
    infer_instance
  | succ n =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    apply IsZero.isIso
    · exact (hz n).of_iso (rationalModuleHomologyIso K (n + 1))
    · have he := exactAt_single_obj (ComplexShape.down ℕ) 0 (K.opcycles 0)
        (n + 1) (by omega)
      exact (rationalModuleFunctor.map_isZero he.isZero_homology).of_iso
        (rationalModuleHomologyIso (integralChainZeroFunctor.obj K) (n + 1))

theorem rational_bicomplexZeroRows_total_quasiIso (K : NatBicomplex)
    (hz : ∀ i j, IsZero (rationalModuleFunctor.obj ((K.X i).homology (j + 1)))) :
    QuasiIso (rationalChainFunctor.map
      (HomologicalComplex₂.total.map (bicomplexZeroRowsProjection K) (ComplexShape.down ℕ))) :=
  rational_bicomplex_total_of_row_epi_quasiIso (bicomplexZeroRowsProjection K)
    (fun i => show Epi (integralChainZeroProjection (K.X i)) from inferInstance)
    (fun i => rational_chainZeroProjection_quasiIso (K.X i) (hz i))

def rational_totalRowZeroHomologyIso (K : NatBicomplex)
    (hz : ∀ i j, IsZero (rationalModuleFunctor.obj ((K.X i).homology (j + 1)))) (n : ℕ) :
    rationalModuleFunctor.obj ((K.total (ComplexShape.down ℕ)).homology n) ≅
      rationalModuleFunctor.obj ((rowOpcyclesComplex K).homology n) := by
  let := rational_bicomplexZeroRows_total_quasiIso K hz
  exact (rationalModuleHomologyIso (K.total (ComplexShape.down ℕ)) n).symm ≪≫
    asIso (homologyMap (rationalChainFunctor.map
      (HomologicalComplex₂.total.map (bicomplexZeroRowsProjection K) (ComplexShape.down ℕ))) n) ≪≫
    rationalModuleHomologyIso ((bicomplexZeroRows K).total (ComplexShape.down ℕ)) n ≪≫
    rationalModuleFunctor.mapIso
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso (zeroRowsTotalIso K))

end PolycyclicRecognition

end

end OAI
