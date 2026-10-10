import OAI.Geometry.NodalSets.Coefficients.PlacedEnvelopeResidualWaves
import OAI.Geometry.NodalSets.Coefficients.SeedResidualBounds

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem PlacedEnvelopeData.seed_residual {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T)
    (ha : 0 ≤ a) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x) (k K' : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ K,
      DerivativeBound k (fun z ↦ sourceWeightedOperator g w
        (fun y ↦ (seedCoordinateField N y:ℂ)) z+
          (seedEigenvalue N:ℂ)*(seedCoordinateField N z:ℂ)) x
        (ε*(N:ℝ)^(-(K':ℝ))*Real.exp ((N:ℝ)*d.S x)) := by
  have hKV : K ⊆ d.V := fun x hx ↦
    d.closure_U_V (subset_closure (d.C_U (d.inner_C (Or.inr hx))))
  have h0 : (0 : Coord) ∈ seedCoordCube a := by
    constructor <;> intro i <;> simp only [Pi.zero_apply] <;> linarith
  have h0V : (0 : Coord) ∈ d.V :=
    d.closure_U_V (subset_closure (d.C_U (d.inner_C (Or.inl h0))))
  exact seedCoordinateField_residual_gap_bound hK (hKV.trans d.V_branch)
    d.open_V hKV ⟨0,h0V⟩ g (hg.mono d.V_branch)
    (fun x hx ↦ hs x (d.V_branch hx)) (fun x hx ↦ hp x (d.V_branch hx))
    w (hw.mono d.V_branch) (fun x hx ↦ hwp x (d.V_branch hx)) d.S d.gap_pos
    (fun x hx ↦ d.inner_gap x (Or.inr hx)) k K' hε

end
end Yau.Target

end OAI
