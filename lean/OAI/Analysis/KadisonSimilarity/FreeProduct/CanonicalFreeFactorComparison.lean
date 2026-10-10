import OAI.Analysis.KadisonSimilarity.FreeProduct.CanonicalFreeCornerCore
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeFactorCenter
import OAI.Analysis.KadisonSimilarity.Representation.NormalOrthogonalUnitaries
import OAI.Analysis.KadisonSimilarity.FreeProduct.GeneratedWordDensity

namespace OAI

/-! Projection comparison for the actual canonical generated free product.
The source normality and its dense matrix tower construct the orthogonal
unitaries; freeness proves scalar center; the normal range gives comparison. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
  (hφ : Function.Injective φ) (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τ htr φ ψ
local notation "G" => canonicalGeneratedGeometry τ htr φ ψ
local notation "A₀" => StarAlgHom.range (canonicalGeneratedFirst τ htr φ ψ)
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τ htr φ ψ)

variable (τR : R →ₚ[ℂ] ℂ) (hψτ : ∀ r, τ (ψ r) = τR r)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
  (h1 : τ 1 = 1) (hfτ : ∀ a : P, τ (star a * a) = 0 → a = 0)

include hφ hψ hψτ M h1 hfτ in
/-- Projection comparison follows from the faithful normal source,
freeness and normality of the generated model. -/
theorem canonicalFreeFactorComparison
    (hfree : ScalarFree τ.toLinearMap φ.range ψ.range)
    (hsource : τR.gnsStarAlgHom.range =
      (representationVonNeumannAlgebra τR.gnsStarAlgHom).toStarSubalgebra)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (hnormal : ∃ N : VonNeumannAlgebra (canonicalGeneratedTrace τ htr φ ψ).GNS,
      (G).left.range = N.toStarSubalgebra) : (G).LocalFreeCornerPublishedInputs := by
  let : IsClosed (A₀ : Set L) := canonicalFirstRange_closed τ htr φ ψ hφ
  let : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τ htr φ ψ hψ
  have hsψ (r : R) : ψ (star r) = star (ψ r) := ψ.map_star' r
  have hmψ (r s : R) : ψ (r * s) = ψ r * ψ s := ψ.map_mul' r s
  have hR : τR 1 = 1 := by
    rw [← hψτ, map_one, h1]
  have hfR (r : R) (hr : τR (star r * r) = 0) : r = 0 := by
    apply hψ
    rw [map_zero]
    apply hfτ
    rw [← hsψ r, ← hmψ (star r) r, hψτ, hr]
  have trR (r s : R) : τR (r * s) = τR (s * r) := by
    rw [← hψτ, ← hψτ, hmψ r s, hmψ s r, htr]
  obtain ⟨u, hu0, huv⟩ :=
    (gnsTracialGeometry τR trR).exists_orthogonal_unitaries_of_normal_matrix_tower
      M hR (gnsTracialVector_injective τR hfR) _ hsource hsize
  let f := canonicalGeneratedSecond τ htr φ ψ
  let v : ℕ → unitary L := fun n => Unitary.map (StarMonoidHom.ofClass f) (u n)
  have hv (n : ℕ) : (v n : L) ∈ D₀ := ⟨(u n : R), rfl⟩
  have hv0 (n : ℕ) : (G).trace (v n : L) = 0 := by
    change τ (ψ (u n : R)) = 0
    rw [hψτ]
    exact hu0 n
  have hvv (i j : ℕ) : (G).trace ((v i : L) * star (v j : L)) =
      if i = j then 1 else 0 := by
    change τ (ψ (u i : R) * star (ψ (u j : R))) = _
    rw [← hsψ (u j : R), ← hmψ (u i : R) (star (u j : R)), hψτ]
    exact huv i j
  have hG1 : (G).trace 1 = 1 := h1
  have hGf := canonicalGenerated_faithful τ htr φ ψ hfτ
  let M₀ : NestedTracialMatrices (A := I) ((G).baseGeometry D₀).trace
      ((G).baseGeometry D₀).vector := canonicalGeneratedMatrices τ htr φ ψ τR hψτ M
  have hcenter := (G).scalar_center_of_free_matrix_factor (A := A₀) (D := D₀)
    M₀ hG1 hGf
    (canonicalGenerated_freeness τ htr φ ψ hfree)
    ((G).reducedWordGenerated_of_factorsTraciallyGenerate A₀ D₀ hG1
      (canonicalGenerated_generation τ htr φ ψ)) v hv hv0 hvv
  obtain ⟨N, hN⟩ := hnormal
  exact ⟨(G).projectionComparison_of_normal_range hG1 hGf N hN hcenter⟩

end KadisonSimilarity

end

end OAI
