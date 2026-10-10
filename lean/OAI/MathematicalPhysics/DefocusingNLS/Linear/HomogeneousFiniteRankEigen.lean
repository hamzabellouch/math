import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankCriterion
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace OAI

/-! # Actual eigenvectors for the finite-rank spectral obstruction

Outside the spectrum of the bounded remainder, a zero of the Schur
determinant produces a nonzero eigenvector. Its eigenspace injects into
the finite-dimensional factor of the perturbation.
-/

namespace DefocusingNLS

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [CompleteSpace E] in
theorem finiteRank_exists_eigenvector_of_det_zero (B : E →L[ℂ] E)
    (U : F →L[ℂ] E) (V : E →L[ℂ] F) (z : ℂ)
    (hz : z ∈ resolventSet ℂ B)
    (hdet : (ContinuousLinearMap.id ℂ F - V.comp ((resolvent B z).comp U)).det = 0) :
    ∃ x : E, x ≠ 0 ∧ (B + U.comp V) x = z • x := by
  let A : E →L[ℂ] E := algebraMap ℂ (E →L[ℂ] E) z - B
  let R := resolvent B z
  let D : F →L[ℂ] F := ContinuousLinearMap.id ℂ F - V.comp (R.comp U)
  have hker : LinearMap.ker D.toLinearMap ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  obtain ⟨c, hc, hc0⟩ := (LinearMap.ker D.toLinearMap).ne_bot_iff.mp hker
  change c - V (R (U c)) = 0 at hc
  have hDc : c = V (R (U c)) := sub_eq_zero.mp hc
  have hAR : A.comp R = ContinuousLinearMap.id ℂ E :=
    Ring.mul_inverse_cancel A hz
  have hAx : A (R (U c)) = U c :=
    congrArg (fun L : E →L[ℂ] E => L (U c)) hAR
  refine ⟨R (U c), ?_, ?_⟩
  · intro hx
    exact hc0 (hDc.trans (by rw [hx, map_zero]))
  · change z • R (U c) - B (R (U c)) = U c at hAx
    change B (R (U c)) + U (V (R (U c))) = z • R (U c)
    rw [← hDc]
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hAx).symm

theorem finiteRank_spectrum_iff_exists_eigenvector (B : E →L[ℂ] E)
    (U : F →L[ℂ] E) (V : E →L[ℂ] F) (z : ℂ)
    (hz : z ∈ resolventSet ℂ B) :
    z ∈ spectrum ℂ (B + U.comp V) ↔
      ∃ x : E, x ≠ 0 ∧ (B + U.comp V) x = z • x := by
  constructor
  · intro hs
    exact finiteRank_exists_eigenvector_of_det_zero B U V z hz
      ((finiteRank_spectrum_iff_det_zero B U V z hz).mp hs)
  · rintro ⟨x, hx, he⟩
    rw [spectrum.mem_iff]
    intro hunit
    have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    have hzero : (algebraMap ℂ (E →L[ℂ] E) z - (B + U.comp V)) x = 0 := by
      change z • x - (B + U.comp V) x = 0
      rw [he, sub_self]
    exact hx (hinj (hzero.trans (map_zero _).symm))

theorem finiteRank_finiteDimensional_eigenspace (B : E →L[ℂ] E)
    (U : F →L[ℂ] E) (V : E →L[ℂ] F) (z : ℂ)
    (hz : z ∈ resolventSet ℂ B) :
    FiniteDimensional ℂ (Module.End.eigenspace (B + U.comp V).toLinearMap z) := by
  let A : E →L[ℂ] E := algebraMap ℂ (E →L[ℂ] E) z - B
  let G := Module.End.eigenspace (B + U.comp V).toLinearMap z
  let W : G →ₗ[ℂ] F := V.toLinearMap.comp G.subtype
  have hA (x : G) : A x = U (V x) := by
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change B x + U (V x) = z • (x : E) at hx
    change z • (x : E) - B x = U (V x)
    rw [← hx]
    abel
  have hinjA := (ContinuousLinearMap.isUnit_iff_bijective.mp hz).1
  apply FiniteDimensional.of_injective W
  intro x y hxy
  apply Subtype.ext
  apply hinjA
  rw [hA x, hA y]
  exact congrArg U hxy

end

end DefocusingNLS

end OAI
