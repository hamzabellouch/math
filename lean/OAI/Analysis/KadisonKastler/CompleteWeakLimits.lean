import OAI.Analysis.KadisonKastler.WeakMatrixLimits
import OAI.Analysis.KadisonKastler.CompleteLinearLimits
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! Completely bounded maps into a concrete von Neumann algebra have weak ultralimits. -/

namespace KadisonKastler

noncomputable section

open Filter Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance completeWeakOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance completeWeakOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance completeWeakAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance completeWeakAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem completelyBoundedBy_of_weak_operator_ultralimit (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    (L : Algebra M →ₗ[ℂ] Algebra M) {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ i, CompletelyBoundedBy (F i) c)
    (ht : ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
      (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ)))) :
    CompletelyBoundedBy L c := by
  let e := M.toStarSubalgebra.subtype
  have he := injective_starAlgHom_completelyIsometric e Subtype.val_injective
  intro p q X
  have h := rectangular_matrix_ultralimit_norm_le ω
    (fun i => CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ (F i) X))
    (CStarMatrix.mapₗ e.toAlgHom.toLinearMap (CStarMatrix.mapₗ L X))
    (mul_nonneg hc (norm_nonneg X))
    (fun i => by rw [he]; exact hF i p q X)
    (fun a b ξ η => ht (X a b) ξ η)
  rwa [he] at h

/-- Pointwise weak compactness preserves the full matrix norm bound. -/
theorem exists_completelyBounded_weak_ultralimit (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (F : ι → Algebra M →ₗ[ℂ] Algebra M)
    {c : ℝ} (hc : 0 ≤ c) (hF : ∀ i, CompletelyBoundedBy (F i) c) :
    ∃ L : Algebra M →ₗ[ℂ] Algebra M, CompletelyBoundedBy L c ∧
      ∀ a ξ η, Tendsto (fun i => inner ℂ η ((F i a : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η ((L a : H →L[ℂ] H) ξ))) := by
  choose E hE ht using fun a : Algebra M => Tracial.exists_weak_operator_ultralimit ω
    (fun i => (F i a : H →L[ℂ] H)) (c * ‖a‖) (mul_nonneg hc (norm_nonneg a))
    (fun i => (hF i).apply_norm_le a)
  have hmem (a : Algebra M) : E a ∈ M :=
    Tracial.weak_operator_limit_mem M (fun i => F i a) (E a) (ht a)
  have hadd (a b : Algebra M) : E (a + b) = E a + E b := by
    ext ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (a + b) ξ η)
    simpa [inner_add_right] using (ht a ξ η).add (ht b ξ η)
  have hsmul (z : ℂ) (a : Algebra M) : E (z • a) = z • E a := by
    ext ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • a) ξ η)
    simpa [inner_smul_right] using (ht a ξ η).const_mul z
  let L : Algebra M →ₗ[ℂ] Algebra M :=
    { toFun := fun a => ⟨E a, hmem a⟩
      map_add' := fun a b => Subtype.ext (hadd a b)
      map_smul' := fun z a => Subtype.ext (hsmul z a) }
  exact ⟨L, completelyBoundedBy_of_weak_operator_ultralimit M ω F L hc hF ht, ht⟩

end

end KadisonKastler

end OAI
