import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.TracialInclusion

namespace OAI

/-! # Transporting a scalar relative commutant through common representations -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M R : VonNeumannAlgebra H} {P S : VonNeumannAlgebra K}

theorem relative_scalar_of_common_equivs (hRM : R ≤ M) (hSP : S ≤ P)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra R ≃⋆ₐ[ℂ] Algebra S)
    (hcompat : ∀ r, e (coordinateInclusion hRM r) = coordinateInclusion hSP (f r))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (x : Algebra P)
    (hx : ∀ s : Algebra S, coordinateInclusion hSP s * x = x * coordinateInclusion hSP s) :
    ∃ c : ℂ, x = c • (1 : Algebra P) := by
  have hc (r : Algebra R) : coordinateInclusion hRM r * e.symm x =
      e.symm x * coordinateInclusion hRM r := by
    apply e.injective
    rw [map_mul, map_mul]
    change e (coordinateInclusion hRM r) * e (e.symm x) =
      e (e.symm x) * e (coordinateInclusion hRM r)
    rw [hcompat, e.apply_symm_apply]
    exact hx (f r)
  obtain ⟨c, hc⟩ := hirr (e.symm x) hc
  refine ⟨c, ?_⟩
  calc
    x = e (e.symm x) := (e.apply_symm_apply x).symm
    _ = e (c • (1 : Algebra M)) := congrArg e hc
    _ = c • (1 : Algebra P) := by
      change e.toAlgEquiv.toLinearMap (c • 1) = _
      rw [e.toAlgEquiv.toLinearMap.map_smul]
      congr 1
      exact e.map_one

theorem relative_ambient_scalar_of_common_equivs (hRM : R ≤ M) (hSP : S ≤ P)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra R ≃⋆ₐ[ℂ] Algebra S)
    (hcompat : ∀ r, e (coordinateInclusion hRM r) = coordinateInclusion hSP (f r))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (T : K →L[ℂ] K) (hT : T ∈ P) (hc : ∀ s ∈ S, s * T = T * s) :
    ∃ c : ℂ, T = c • (1 : K →L[ℂ] K) := by
  obtain ⟨c, he⟩ := relative_scalar_of_common_equivs hRM hSP e f hcompat hirr
    ⟨T, hT⟩ (fun s => Subtype.ext (hc s.val s.property))
  exact ⟨c, congrArg (fun a : Algebra P => a.val) he⟩

end

end KadisonKastler

end OAI
