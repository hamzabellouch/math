import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusCoefficients

namespace OAI

/-! # The physical L² realization of the frequency lattice

Reindexing the existing torus Fourier Hilbert basis gives an exact isometry
from the Euclidean lattice model into physical torus L².
-/

open MeasureTheory Set

namespace DefocusingNLS

local notation "T" => UnitAddTorus (Fin 12)

noncomputable local instance torusFourierIsometryMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusFourierIsometryProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def torusLatticeBasis : HilbertBasis frequencyLattice ℂ (Lp ℂ 2 (volume : Measure T)) :=
  HilbertBasis.mk
    (UnitAddTorus.mFourierBasis.orthonormal.comp frequencyCoordinatesEquiv
      frequencyCoordinatesEquiv.injective)
    (by
      have he : range (⇑(UnitAddTorus.mFourierBasis (d := Fin 12)) ∘
          ⇑frequencyCoordinatesEquiv) =
            range (UnitAddTorus.mFourierBasis (d := Fin 12)) :=
        frequencyCoordinatesEquiv.surjective.range_comp _
      rw [he]
      exact UnitAddTorus.mFourierBasis.dense_span.ge)

@[simp] theorem torusLatticeBasis_apply (n : frequencyLattice) :
    torusLatticeBasis n = UnitAddTorus.mFourierLp 2 (frequencyCoordinates n) := by
  rw [torusLatticeBasis, HilbertBasis.coe_mk, UnitAddTorus.coe_mFourierBasis]
  rfl

noncomputable def torusFourierIsometry : FourierL2 ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure T) :=
  torusLatticeBasis.repr.symm

theorem torusFourierIsometry_coefficient (f : FourierL2) (n : frequencyLattice) :
    UnitAddTorus.mFourierCoeff (torusFourierIsometry f) (frequencyCoordinates n) = f n := by
  rw [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply,
    UnitAddTorus.coe_mFourierBasis, ← torusLatticeBasis_apply,
    ← HilbertBasis.repr_apply_apply]
  exact congrArg (fun u : FourierL2 => u n) (torusLatticeBasis.repr.apply_symm_apply f)

theorem torusFourierIsometry_eq_continuous (f : FourierL2) (g : C(T, ℂ))
    (hfg : ∀ n : frequencyLattice, unitTorusCoefficient (frequencyCoordinates n) g = f n) :
    torusFourierIsometry f = g.toLp 2 volume ℂ := by
  apply torusLatticeBasis.repr.injective
  ext n
  simp only [HilbertBasis.repr_apply_apply, torusLatticeBasis_apply]
  change inner ℂ (UnitAddTorus.mFourierLp 2 (frequencyCoordinates n))
      (torusFourierIsometry f) = unitTorusCoefficient (frequencyCoordinates n) g
  rw [hfg, ← torusLatticeBasis_apply, ← HilbertBasis.repr_apply_apply]
  exact congrArg (fun u : FourierL2 => u n) (torusLatticeBasis.repr.apply_symm_apply f)

end DefocusingNLS

end OAI
