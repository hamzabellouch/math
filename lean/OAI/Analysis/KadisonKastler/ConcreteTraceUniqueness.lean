import OAI.Analysis.KadisonKastler.ConcreteFiniteTrace

namespace OAI

/-! # Uniqueness of the normalized faithful factor trace

Projection dimension identifies any positive normalized tracial
functional on a finite diffuse factor. In particular, the explicit
matrix trace agrees with the canonical ultrapower trace.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

def FaithfulTracialState.toContinuousLinearMap (τ : FaithfulTracialState B) : B →L[ℂ] ℂ :=
  τ.toLinearMap.mkContinuous 1 (fun x => by simpa only [one_mul] using τ.norm_apply_le_norm x)

theorem FaithfulTracialState.norm_toContinuousLinearMap_le (τ : FaithfulTracialState B) :
    ‖τ.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound τ.toContinuousLinearMap zero_le_one
  intro x
  change ‖τ.toLinearMap x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using τ.norm_apply_le_norm x

section Positive

variable [PartialOrder B] [StarOrderedRing B]

theorem FaithfulTracialState.nonneg (τ : FaithfulTracialState B) {x : B} (hx : 0 ≤ x) :
    0 ≤ (τ.toLinearMap x).re := by
  have h := τ.positive (CFC.sqrt x)
  rwa [(CFC.sqrt_nonneg x).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self x hx] at h

end Positive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance uniquenessOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance uniquenessPreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance uniquenessLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance uniquenessStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

private theorem scalarCenter (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (c : Algebra M) (hc : ∀ a : Algebra M, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra M) := by
  obtain ⟨z, hz⟩ := hM.factor c hc
  exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩

private theorem one_ne_zero (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    (1 : Algebra M) ≠ 0 := fun h => hM.nonzero (congrArg Subtype.val h).symm

private theorem trace_on_selfAdjoint
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (τ : FaithfulTracialState (Algebra M))
    (x : Algebra M) (hx : IsSelfAdjoint x) :
    τ.toLinearMap x = Generator.Tracial.dimensionSpectralValue
      (scalarCenter hM) hM.diffuse hM.finite (one_ne_zero hM) x hx := by
  apply Generator.Tracial.functional_eq_dimensionSpectralValue
    (scalarCenter hM) hM.diffuse hM.finite (one_ne_zero hM)
    τ.toContinuousLinearMap τ.norm_toContinuousLinearMap_le
  intro p
  exact Generator.Tracial.tracialFunctional_projection_dimension
    (scalarCenter hM) hM.diffuse hM.finite (one_ne_zero hM)
    τ.toContinuousLinearMap τ.map_one (fun _ hx => τ.nonneg hx) τ.map_star τ.tracial p

/-- Any two normalized faithful tracial states on a concrete II1 factor
agree. Normality is not an extra premise. -/
theorem faithfulTracialState_unique
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ σ : FaithfulTracialState (Algebra M)) (x : Algebra M) :
    τ.toLinearMap x = σ.toLinearMap x := by
  have hsa (y : Algebra M) (hy : IsSelfAdjoint y) : τ.toLinearMap y = σ.toLinearMap y :=
    (trace_on_selfAdjoint hM τ y hy).trans (trace_on_selfAdjoint hM σ y hy).symm
  rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_add, map_smul, map_smul,
    hsa _ (selfAdjoint.mem_iff.mp (realPart x).property),
    hsa _ (selfAdjoint.mem_iff.mp (imaginaryPart x).property)]

/-- The explicit normalized matrix trace therefore equals the canonical
trace selected by the concrete factor construction. -/
theorem faithfulTracialState_eq_concreteFactorTrace
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τ : FaithfulTracialState (Algebra M)) (x : Algebra M) :
    τ.toLinearMap x = (concreteFactorTrace hM).toLinearMap x :=
  faithfulTracialState_unique hM τ (concreteFactorTrace hM) x

end

end KadisonKastler

end OAI
