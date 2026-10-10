import OAI.Analysis.KadisonKastler.HilbertPairRepresentation
import OAI.Analysis.KadisonKastler.NormalRepresentationRange

namespace OAI

/-! # A normal representation and the original algebra on their Hilbert sum -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))

def normalPairHom : Algebra M →⋆ₐ[ℂ] (WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K)) :=
  hilbertPairRepresentation M.toStarSubalgebra.subtype φ

theorem normalPairHom_injective : Function.Injective (normalPairHom M φ) := by
  intro a b hab
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) =>
    (T (WithLp.toLp 2 (x, 0))).fst) hab

theorem normalPairHom_boundedWeakNormal (hφ : BoundedWeakNormal M φ) :
    BoundedWeakNormal M (normalPairHom M φ) := by
  intro ι l a b C hn hw x y
  have hφw := hφ a b C hn hw x.snd y.snd
  have hMw := hw x.fst y.fst
  exact hMw.add hφw

def normalPairAlgebra : VonNeumannAlgebra (WithLp 2 (H × K)) :=
  generatedVonNeumannAlgebra (normalPairHom M φ).range

def normalPairEquiv (hφ : BoundedWeakNormal M φ) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (normalPairAlgebra M φ) :=
  boundedWeakNormalEquiv M (normalPairHom M φ) (normalPairHom_injective M φ)
    (normalPairHom_boundedWeakNormal M φ hφ)

@[simp] theorem normalPairEquiv_coe (hφ : BoundedWeakNormal M φ) (a : Algebra M) :
    (normalPairEquiv M φ hφ a).val = normalPairHom M φ a := rfl

end

end KadisonKastler

end OAI
