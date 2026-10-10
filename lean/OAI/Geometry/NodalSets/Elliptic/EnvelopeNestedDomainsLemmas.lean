import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set
open scoped Topology

theorem envelope_nested_domains {C P : Set Coord} (hC : IsCompact C)
    (hP : IsOpen P) (hCP : C ⊆ P) :
    ∃ U Ω : Set Coord, IsOpen U ∧ IsOpen Ω ∧ C ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      IsCompact (closure Ω) ∧ closure Ω ⊆ P := by
  obtain ⟨L,hL,hCL,hLP⟩ := exists_compact_between hC hP hCP
  obtain ⟨M,hM,hLM,hMP⟩ := exists_compact_between hL hP hLP
  have hUL : closure (interior L) ⊆ L := closure_minimal interior_subset hL.isClosed
  have hΩM : closure (interior M) ⊆ M := closure_minimal interior_subset hM.isClosed
  exact ⟨interior L,interior M,isOpen_interior,isOpen_interior,hCL,
    hL.of_isClosed_subset isClosed_closure hUL,hUL.trans hLM,
    hM.of_isClosed_subset isClosed_closure hΩM,hΩM.trans hMP⟩

theorem compact_high_envelope_set (S S0 : Coord → ℝ) (hS : Continuous S) (hS0 : Continuous S0)
    {C P : Set Coord} (hC : IsCompact C) (hCP : C ⊆ P) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ P, x ∉ C → S x ≤ S0 x-d) :
    IsCompact {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ∧
      {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ⊆ C := by
  have hsub : {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ⊆ C := by
    intro x hx
    by_contra hc
    have hh := hgap x hx.1 hc
    have hl := hx.2
    linarith
  have he : {x | x ∈ P ∧ S0 x-d/2 ≤ S x} = C ∩ {x | S0 x-d/2 ≤ S x} := by
    ext x
    exact ⟨fun hx ↦ ⟨hsub hx,hx.2⟩,fun hx ↦ ⟨hCP hx.1,hx.2⟩⟩
  refine ⟨?_,hsub⟩
  rw [he]
  exact hC.inter_right (isClosed_le (hS0.sub continuous_const) hS)

open Yau.Jets Set Filter
open scoped ContDiff Topology

theorem exists_signed_envelope_offset {K P : Set Coord} (hK : IsCompact K)
    (hP : IsOpen P) (hKP : K ⊆ P) :
    ∃ f : Coord → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, |f x| ≤ 1) ∧
      (∀ x ∈ K, f =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∃ C : Set Coord, IsCompact C ∧ C ⊆ P ∧ K ⊆ C ∧
        ∀ x ∉ C, f x = -1 := by
  obtain ⟨b,hb,hbc,hbP,hbr,hb1⟩ := compact_smooth_cutoff hK hP hKP
  refine ⟨fun x ↦ 2*b x-1,(contDiff_const.mul hb).sub contDiff_const,?_,?_,
    tsupport b,hbc,hbP,?_,?_⟩
  · intro x
    rw [abs_le]
    constructor <;> nlinarith [(hbr x).1,(hbr x).2]
  · intro x hx
    filter_upwards [hb1 x hx] with y hy
    norm_num [hy]
  · intro x hx
    apply subset_tsupport
    have hh := (hb1 x hx).eq_of_nhds
    change b x ≠ 0
    rw [hh]
    norm_num
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]

end Yau.Geometry

end

end OAI
