import OAI.Geometry.NodalSets.Elliptic.PlacedEnvelopeDomains
import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma PlacedEnvelopeData.closure_U_branch {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.U ⊆ seedCoordBranch :=
  d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans
    (subset_closure.trans (d.patch_V.trans d.V_branch))))

lemma PlacedEnvelopeData.closure_U_V {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.U ⊆ d.V :=
  d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans
    (subset_closure.trans d.patch_V)))

theorem PlacedEnvelopeData.waves {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) (ha : 0 ≤ a)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x) (k0 K' : ℕ) :
    Nonempty (LocalCompactWaveData g w d.S (closure d.U)
      (3*K'+4*k0+6) (K'+k0+1) K' k0) := by
  have h0 : (0 : Coord) ∈ seedCoordCube a := by
    constructor <;> intro i <;> simp only [Pi.zero_apply] <;> linarith
  have h0U : (0 : Coord) ∈ d.U := d.C_U (d.inner_C (Or.inl h0))
  have h0V : (0 : Coord) ∈ d.V := d.closure_U_V (subset_closure h0U)
  apply construct_local_compact_waves d.compact_closure_U d.open_V d.closure_U_V ⟨0,h0V⟩
    g (hg.mono d.V_branch) (fun x hx ↦ hs x (d.V_branch hx))
    (fun x hx ↦ hp x (d.V_branch hx)) w d.S (hw.mono d.V_branch)
    (d.smooth.mono d.V_branch) (fun x hx ↦ hwp x (d.V_branch hx))
    (fun x hx ↦ (d.admissible x (d.closure_U_V hx)).1)
  · intro x hx
    obtain ⟨hn,v,hv,hpv,hstr⟩ := d.admissible x (d.closure_U_V hx)
    exact ⟨v,hpv,hv,hstr⟩
  · omega
  · omega

end
end Yau.Target

end OAI
