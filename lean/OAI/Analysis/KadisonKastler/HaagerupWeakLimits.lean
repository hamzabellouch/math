import OAI.Analysis.KadisonKastler.CompleteWeakLimits
import OAI.Analysis.KadisonKastler.Haagerup

namespace OAI

/-! Haagerup bounds are closed under pointwise weak operator limits. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance haagerupWeakOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance haagerupWeakOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance haagerupWeakAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance haagerupWeakAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem haagerupBound_of_weak_operator_ultralimit (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι)
    (F : ι → Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M)
    (L : Algebra M →ₗ[ℂ] Algebra M →ₗ[ℂ] Algebra M) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, HaagerupBound (F i) c)
    (ht : ∀ a b ξ η, Tendsto (fun i => inner ℂ η ((F i a b : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((L a b : H →L[ℂ] H) ξ)))) :
    HaagerupBound L c := by
  let e := M.toStarSubalgebra.subtype
  have he := injective_starAlgHom_completelyIsometric e Subtype.val_injective
  intro p r q X Y
  have h := rectangular_matrix_ultralimit_norm_le ω
    (fun i => CStarMatrix.mapₗ e.toAlgHom.toLinearMap (bilinearProduct (F i) X Y))
    (CStarMatrix.mapₗ e.toAlgHom.toLinearMap (bilinearProduct L X Y))
    (mul_nonneg (mul_nonneg hc (norm_nonneg X)) (norm_nonneg Y))
    (fun i => by rw [he]; exact hF i p r q X Y) ?_
  · rwa [he] at h
  · intro a b ξ η
    change Tendsto (fun i => inner ℂ η (((∑ k, F i (X a k) (Y k b) : Algebra M) :
      H →L[ℂ] H) ξ)) (ω : Filter ι)
      (𝓝 (inner ℂ η (((∑ k, L (X a k) (Y k b) : Algebra M) : H →L[ℂ] H) ξ)))
    simpa [inner_sum] using
      (tendsto_finsetSum Finset.univ (fun k _ => ht (X a k) (Y k b) ξ η))

end

end KadisonKastler

end OAI
