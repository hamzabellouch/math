import OAI.Geometry.NodalSets.Coefficients.SeedCoefficientPlacement
import OAI.Geometry.NodalSets.Elliptic.EnvelopeRegion
import OAI.Geometry.NodalSets.Elliptic.LocalEnvelopeDomains

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

structure PlacedEnvelopeData (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (r a : ℝ) (K : Set Coord) (T : ℝ) where
  S : Coord → ℝ
  gap : ℝ
  U : Set Coord
  Ω : Set Coord
  V : Set Coord
  C : Set Coord
  gap_pos : 0 < gap
  smooth : ContDiffOn ℝ ∞ S seedCoordBranch
  compact_C : IsCompact C
  C_patch : C ⊆ seedCoordPatch r
  inner_C : seedCoordCube a ∪ K ⊆ C
  inner_gap : ∀ x ∈ seedCoordCube a ∪ K, seedCoordReal x+gap ≤ S x
  outer_gap : ∀ x ∉ C, S x ≤ seedCoordReal x-gap
  open_V : IsOpen V
  patch_V : closure (seedCoordPatch r) ⊆ V
  V_branch : V ⊆ seedCoordBranch
  admissible : sourceDirectionalAdmissibleOn g S V
  gain : T < ∫ x in seedCoordCube a, corrugationOldSlope g S x
  open_U : IsOpen U
  open_Ω : IsOpen Ω
  C_U : C ⊆ U
  compact_closure_U : IsCompact (closure U)
  closure_U_Ω : closure U ⊆ Ω
  compact_closure_Ω : IsCompact (closure Ω)
  closure_Ω_patch : closure Ω ⊆ seedCoordPatch r
  compact_high : IsCompact {x | x ∈ seedCoordPatch r ∧ seedCoordReal x-gap/2 ≤ S x}
  high_U : {x | x ∈ seedCoordPatch r ∧ seedCoordReal x-gap/2 ≤ S x} ⊆ U

theorem SeedEnvelopePlaced.domains {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ}
    (h : SeedEnvelopePlaced g r a K T) : Nonempty (PlacedEnvelopeData g r a K T) := by
  obtain ⟨S,d,C,V,hd,hS,hC,hCP,hinner,hig,hog,hV,hPV,hVB,had,hgain⟩ := h
  have hPB := hPV.trans hVB
  obtain ⟨U,Ω,hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP,hQ,hQU,hout⟩ :=
    local_envelope_nested_domains S seedCoordReal (seedCoordPatch_open r)
      (seedCoordPatch_compactClosure r) seedCoordBranch_open hPB hS seedCoordReal_smoothOn
      hC hCP hd (fun x _ hx ↦ hog x hx)
  exact ⟨⟨S,d,U,Ω,V,C,hd,hS,hC,hCP,hinner,hig,hog,hV,hPV,hVB,had,hgain,
    hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP,hQ,hQU⟩⟩

theorem PlacedEnvelopeData.high_region {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    ∃ Q : Set Coord, IsCompact Q ∧ Q ⊆ d.U ∧
      (∃ ε > 0, Metric.cthickening ε Q ⊆ d.U) ∧
      ∀ᶠ n : ℕ in atTop, highEnvelopeRegion (closure d.Ω) d.S seedCoordReal n ⊆ Q := by
  let Q := {x | x ∈ seedCoordPatch r ∧ seedCoordReal x-d.gap/2 ≤ d.S x}
  refine ⟨Q,d.compact_high,d.high_U,
    d.compact_high.exists_cthickening_subset_open d.open_U d.high_U,?_⟩
  have ht : Tendsto (fun n : ℕ ↦ -8*Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [div_eq_mul_inv,mul_assoc] using hh.const_mul (-8)
  filter_upwards [ht.eventually (lt_mem_nhds (by linarith [d.gap_pos] : -d.gap/2 < (0:ℝ)))] with n hn
  intro x hx
  refine ⟨d.closure_Ω_patch hx.1,?_⟩
  have hh := hn.le.trans hx.2
  linarith

end
end Yau.Target

end OAI
