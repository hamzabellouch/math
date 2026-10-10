import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap LineDeriv
open scoped LineDeriv

abbrev JetCoordinateIndex (d N : ℕ) := Σ i : Fin (N + 1), Fin i.val → Fin d

def schwartzJetCoordinates (d N : ℕ) :
    𝓢(Ambient d, ℂ) →ₗ[ℂ] (JetCoordinateIndex d N → ℂ) :=
  LinearMap.pi fun i => (TemperedDistribution.delta (0 : Ambient d)).toLinearMap.comp
    (iteratedLineDerivOpCLM ℂ 𝓢(Ambient d, ℂ)
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j))).toLinearMap

theorem schwartzJetCoordinates_apply (d N : ℕ) (g : 𝓢(Ambient d, ℂ))
    (i : JetCoordinateIndex d N) :
    schwartzJetCoordinates d N g i =
      iteratedFDeriv ℝ i.1.val g 0 (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) := by
  change (∂^{fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)} g) 0 = _
  exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv

theorem schwartzJetCoordinates_eq_iff (d N : ℕ) (g h : 𝓢(Ambient d, ℂ)) :
    schwartzJetCoordinates d N g = schwartzJetCoordinates d N h ↔
      ∀ i, i ≤ N → iteratedFDeriv ℝ i g 0 = iteratedFDeriv ℝ i h 0 := by
  constructor
  · intro heq i hi
    have hm : (iteratedFDeriv ℝ i g 0).toMultilinearMap =
        (iteratedFDeriv ℝ i h 0).toMultilinearMap := by
      apply Module.Basis.ext_multilinear (fun _ : Fin i => (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      intro v
      have hv := congrFun heq (⟨⟨i, by omega⟩, v⟩ : JetCoordinateIndex d N)
      simpa only [schwartzJetCoordinates_apply] using! hv
    ext v
    exact congrArg (fun f => f v) hm
  · intro heq
    funext i
    rw [schwartzJetCoordinates_apply, schwartzJetCoordinates_apply,
      heq i.1.val (by omega)]

end

end RieszRectifiability

end OAI
