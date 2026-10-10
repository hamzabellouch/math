import OAI.Geometry.SurfaceImmersion.Geometry.NormalInterpolation
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

/-! Glue the local adjusted normal to the exterior projected normal.
The cutoff support conditions remove every use of an unavailable chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma first_contMDiffAt {a b : M → Vec} {t : M → ℝ} {p : M}
    (ha : ContMDiffAt planeModel 𝓘(ℝ,Vec) ∞ a p)
    (hb : ContMDiffAt planeModel 𝓘(ℝ,Vec) ∞ b p)
    (ht : ContMDiffAt planeModel 𝓘(ℝ) ∞ t p)
    (ha1 : a p ⬝ᵥ a p = 1) (hb1 : b p ⬝ᵥ b p = 1)
    (hne : a p ≠ -b p) (htr : t p ∈ Icc (0 : ℝ) 1) :
    ContMDiffAt planeModel 𝓘(ℝ,Vec) ∞ (fun x => first (a x) (b x) (t x)) p := by
  let H : Vec × (Vec × ℝ) → Vec := fun x => first x.1 x.2.1 x.2.2
  have hH : ContDiffAt ℝ ∞ H (a p,b p,t p) :=
    first_smoothAt contDiffAt_fst (contDiffAt_snd.fst) (contDiffAt_snd.snd)
      ha1 hb1 (dot_gt_neg_one_of_ne_antipode ha1 hb1 hne) htr
  have hm : ContMDiffAt 𝓘(ℝ,Vec × (Vec × ℝ)) 𝓘(ℝ,Vec) ∞ H (a p,b p,t p) :=
    hH.contMDiffAt
  have hout := hm.comp (g := H) p (ha.prodMk_space (hb.prodMk_space ht))
  exact hout

theorem normal_collar_gluing {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {a b : M → Vec} {chi : M → ℝ}
    (ha : ContMDiffOn planeModel 𝓘(ℝ,Vec) ∞ a U)
    (hb : ContMDiffOn planeModel 𝓘(ℝ,Vec) ∞ b V)
    (hchi : ContMDiff planeModel 𝓘(ℝ) ∞ chi)
    (hchiu : tsupport chi ⊆ U) (hchiv : tsupport (fun x => 1-chi x) ⊆ V)
    (hchi01 : ∀ x, chi x ∈ Icc (0 : ℝ) 1)
    (ha1 : ∀ x ∈ U, a x ⬝ᵥ a x = 1) (hb1 : ∀ x ∈ V, b x ⬝ᵥ b x = 1)
    (hne : ∀ x ∈ U ∩ V, b x ≠ -a x) :
    let g := fun x => first (b x) (a x) (chi x)
    ContMDiff planeModel 𝓘(ℝ,Vec) ∞ g ∧ (∀ x, g x ⬝ᵥ g x = 1) ∧
      (∀ x, chi x = 1 → g x = a x) ∧ (∀ x, chi x = 0 → g x = b x) ∧
      (∀ x (w : Vec), (x ∈ U → w ⬝ᵥ a x = 0) →
        (x ∈ V → w ⬝ᵥ b x = 0) → w ⬝ᵥ g x = 0) ∧
      (∀ x (w : Vec), (x ∈ U → 0 < w ⬝ᵥ a x) →
        (x ∈ V → 0 < w ⬝ᵥ b x) → 0 < w ⬝ᵥ g x) := by
  dsimp only
  have ha_mem (x : M) (hx : chi x ≠ 0) : x ∈ U :=
    hchiu (subset_tsupport chi hx)
  have hb_mem (x : M) (hx : chi x ≠ 1) : x ∈ V := by
    apply hchiv
    apply subset_tsupport
    change 1-chi x ≠ 0
    exact sub_ne_zero.mpr (Ne.symm hx)
  have ha_eq (x : M) (hx : chi x = 1) : first (b x) (a x) (chi x) = a x := by
    rw [hx,first_one (ha1 x (ha_mem x (by simpa only [hx] using one_ne_zero)))]
  have hb_eq (x : M) (hx : chi x = 0) : first (b x) (a x) (chi x) = b x := by
    rw [hx,first_zero (hb1 x (hb_mem x (by simpa only [hx] using zero_ne_one)))]
  refine ⟨?_,?_,ha_eq,hb_eq,?_,?_⟩
  · intro x
    by_cases hxU : x ∈ U
    · by_cases hxV : x ∈ V
      · exact first_contMDiffAt (hb.contMDiffAt (hV.mem_nhds hxV))
          (ha.contMDiffAt (hU.mem_nhds hxU)) (hchi x) (hb1 x hxV) (ha1 x hxU)
          (hne x ⟨hxU,hxV⟩) (hchi01 x)
      · have hz : (fun y => 1-chi y) =ᶠ[𝓝 x] 0 :=
          notMem_tsupport_iff_eventuallyEq.mp (fun hs => hxV (hchiv hs))
        apply (ha.contMDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
        filter_upwards [hz] with y hy
        exact ha_eq y (sub_eq_zero.mp hy).symm
    · have hz : chi =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hs => hxU (hchiu hs))
      have hxV : x ∈ V := hb_mem x (by rw [hz.eq_of_nhds]; exact zero_ne_one)
      apply (hb.contMDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      exact hb_eq y hy
  · intro x
    by_cases h0 : chi x = 0
    · rw [hb_eq x h0]; exact hb1 x (hb_mem x (by rw [h0]; exact zero_ne_one))
    by_cases h1 : chi x = 1
    · rw [ha_eq x h1]; exact ha1 x (ha_mem x h0)
    exact first_unit (hb1 x (hb_mem x h1)) (ha1 x (ha_mem x h0))
      (dot_gt_neg_one_of_ne_antipode (hb1 x (hb_mem x h1)) (ha1 x (ha_mem x h0))
        (hne x ⟨ha_mem x h0,hb_mem x h1⟩)) (hchi01 x)
  · intro x w hwa hwb
    by_cases h0 : chi x = 0
    · rw [hb_eq x h0]; exact hwb (hb_mem x (by rw [h0]; exact zero_ne_one))
    by_cases h1 : chi x = 1
    · rw [ha_eq x h1]; exact hwa (ha_mem x h0)
    exact first_perp (hwb (hb_mem x h1)) (hwa (ha_mem x h0)) _
  · intro x w hwa hwb
    by_cases h0 : chi x = 0
    · rw [hb_eq x h0]; exact hwb (hb_mem x (by rw [h0]; exact zero_ne_one))
    by_cases h1 : chi x = 1
    · rw [ha_eq x h1]; exact hwa (ha_mem x h0)
    exact first_pairing_pos (hchi01 x) (hwb (hb_mem x h1)) (hwa (ha_mem x h0))

end ClosedSurfaceR4.VelocityFrame

end

end OAI
