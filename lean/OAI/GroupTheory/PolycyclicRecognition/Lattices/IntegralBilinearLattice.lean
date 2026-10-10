import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralBilinearExtension

namespace OAI

/-! # The Lie lattice attached to an integral bilinear group law -/

noncomputable section
namespace PolycyclicRecognition

variable {d e : ℕ} (a : Fin e → Fin d → Fin d → ℤ)

def integralBilinearEmbedding : BilinearCentralGroup (coefficientBilinear a) →*
    (bilinearCentralLieModel (realCoefficientBilinear a)).carrier where
  toFun x := (integerVectorMap d x.1, integerVectorMap e x.2)
  map_one' := by apply Prod.ext <;> exact map_zero _
  map_mul' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · change integerVectorMap e (x.2 + y.2 + coefficientBilinear a x.1 y.1) =
        integerVectorMap e x.2 + integerVectorMap e y.2 +
          realCoefficientBilinear a (integerVectorMap d x.1) (integerVectorMap d y.1)
      rw [map_add, map_add, realCoefficientBilinear_cast]

theorem integralBilinearEmbedding_injective : Function.Injective (integralBilinearEmbedding a) := by
  intro x y h
  exact Prod.ext (integerVectorMap_injective d (congrArg Prod.fst h))
    (integerVectorMap_injective e (congrArg Prod.snd h))

def integralBilinearLattice :
    Subgroup (bilinearCentralLieModel (realCoefficientBilinear a)).carrier :=
  bilinearCentralLattice (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin e))
    (realCoefficientBilinear a) (realCoefficientBilinear_integral a)

theorem integralBilinearLattice_uniform : IsUniformLattice (integralBilinearLattice a) :=
  bilinearCentralLattice_uniform _ _ _ _

def integralBilinearLatticeEquiv :
    BilinearCentralGroup (coefficientBilinear a) ≃* integralBilinearLattice a := by
  let f : BilinearCentralGroup (coefficientBilinear a) →* integralBilinearLattice a :=
    (integralBilinearEmbedding a).codRestrict _ (fun x =>
      ⟨integerVectorMap_mem d x.1, integerVectorMap_mem e x.2⟩)
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    exact integralBilinearEmbedding_injective a (congrArg Subtype.val h)
  · intro x
    obtain ⟨u, hu⟩ := exists_integerVectorMap_of_mem d x.val.1 x.property.1
    obtain ⟨v, hv⟩ := exists_integerVectorMap_of_mem e x.val.2 x.property.2
    refine ⟨(u, v), ?_⟩
    apply Subtype.ext
    exact Prod.ext hu hv

theorem integralBilinear_solvable_realization :
    ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
      IsUniformLattice Λ ∧ Nonempty (BilinearCentralGroup (coefficientBilinear a) ≃* Λ) :=
  ⟨bilinearCentralLieModel (realCoefficientBilinear a), integralBilinearLattice a,
    integralBilinearLattice_uniform a, ⟨integralBilinearLatticeEquiv a⟩⟩

end PolycyclicRecognition

end

end OAI
