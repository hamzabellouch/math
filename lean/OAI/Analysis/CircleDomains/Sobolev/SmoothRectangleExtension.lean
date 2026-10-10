import OAI.Analysis.CircleDomains.Rigidity.TraceMaskRectangle
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! A smooth function on a neighborhood of a closed rectangle has a
compactly supported smooth extension agreeing there on an open set. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_rectangle_cutoff_one_near {K Ω : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (η : (ℝ × ℝ) → ℝ) (V : Set (ℝ × ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
      IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, η x = 1 := by
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨η,hη,_,hsupp,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    isOpen_thickening isClosed_cthickening
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K) (n := (⊤ : ℕ∞))
  have hs : tsupport η ⊆ cthickening δ K := by
    rw [tsupport,hsupp]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨η,thickening (δ/2) K,hη,
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure hs,
    hs.trans hδΩ,isOpen_thickening,self_subset_thickening (half_pos hδ) K,?_⟩
  intro x hx
  exact (hone x).1 (thickening_subset_cthickening (δ/2) K hx)

 theorem exists_smooth_rectangle_extension {Ω K : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {b : (ℝ × ℝ) → ℝ} (hb : ContDiffOn ℝ 1 b Ω) :
    ∃ (g : (ℝ × ℝ) → ℝ) (V : Set (ℝ × ℝ)), ContDiff ℝ 1 g ∧
      HasCompactSupport g ∧ IsOpen V ∧ K ⊆ V ∧ EqOn g b V ∧
      EqOn (fderiv ℝ g) (fderiv ℝ b) V := by
  obtain ⟨η,V,hη,hηs,hηΩ,hV,hKV,hη1⟩ := exists_rectangle_cutoff_one_near hK hΩ hKΩ
  let g : (ℝ × ℝ) → ℝ := fun x => η x*b x
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · exact (hη.of_le (by simp)).contDiffAt.mul (hb.contDiffAt (hΩ.mem_nhds hx))
    · have hx' : x ∉ tsupport η := fun hh => hx (hηΩ hh)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx'] with y hy
      change η y*b y = 0
      rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
  have he : EqOn g b V := fun x hx => by change η x*b x = b x; rw [hη1 x hx,one_mul]
  refine ⟨g,V,hg,hηs.mul_right,hV,hKV,he,?_⟩
  intro x hx
  exact (he.eventuallyEq_of_mem (hV.mem_nhds hx)).fderiv_eq

end CircleDomainRigidity

end

end OAI
