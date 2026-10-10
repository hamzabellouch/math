import OAI.Analysis.CircleDomains.Selection.RayProjection
import OAI.Analysis.CircleDomains.Topology.PathImageCount

namespace OAI

/-! Every integer between two index values forces a distinct intersection.
Injectivity of the projected test path makes these physical intersections distinct. -/

open Set Function Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem HalfPlaneRay.cayley_mem_crosscut_iff (R : HalfPlaneRay) {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z ∈ range R.crosscut ↔ z ∈ range R.curve := by
  constructor
  · rintro ⟨t, ht⟩
    have hlt : t < ⊤ := by
      by_contra hn
      have he : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
      subst t
      change R.compactify ⊤ = halfPlaneDisk z at ht
      rw [R.compactify_top] at ht
      exact halfPlaneDisk_ne_one hz ht.symm
    refine ⟨⟨t, hlt⟩, ?_⟩
    change R.compactify t = halfPlaneDisk z at ht
    rw [HalfPlaneRay.compactify, dite_eq_left hlt] at ht
    exact halfPlaneDisk_injOn (R.nonneg _) hz ht
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, by change R.compactify t.val = _; rw [HalfPlaneRay.compactify, dite_eq_left t.property]⟩

theorem translated_ray_hit_between_indices (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (k : ℤ) (h0 : geometricRayIndex hsch γ hγ (δ 0) < k)
    (h1 : k ≤ geometricRayIndex hsch γ hγ (δ 1)) :
    ∃ s : PathTime, ∃ t : DiskRayTime, δ s = (translatedHalfPlaneRay γ hγ k).curve t := by
  let R := translatedHalfPlaneRay γ hγ k
  let H := rayJordan hsch γ hγ k
  have ha : halfPlaneDisk (δ 0) ∈ closure (jordanInterior H) := by
    by_contra hn
    have hm : k ∈ rayRightIndices hsch γ hγ (δ 0) := hn
    exact (not_le_of_gt h0) ((mem_rayRightIndices_iff_le hsch hsep γ hγ (δ 0) (hδ 0) k).mp hm)
  have hb : halfPlaneDisk (δ 1) ∉ closure (jordanInterior H) :=
    (mem_rayRightIndices_iff_le hsch hsep γ hγ (δ 1) (hδ 1) k).mpr h1
  by_contra hn
  have hmiss : ∀ s, halfPlaneDisk (δ s) ∉ range R.crosscut := by
    intro s hs
    obtain ⟨t, ht⟩ := (R.cayley_mem_crosscut_iff (hδ s)).mp hs
    exact hn ⟨s, t, ht.symm⟩
  let f : PathTime → R.CutDomain := fun s => ⟨halfPlaneDisk (δ s),
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le (hδ s)), hmiss s⟩
  have hc : Continuous f := (continuousOn_halfPlaneDisk.comp_continuous δ.continuous hδ).subtype_mk _
  have he := ((R.isLocallyConstant_side (rayJordan_spec hsch γ hγ k)).comp_continuous hc).apply_eq_of_preconnectedSpace
    (0 : PathTime) 1
  change (if halfPlaneDisk (δ 0) ∈ closure (jordanInterior H) then false else true) =
    (if halfPlaneDisk (δ 1) ∈ closure (jordanInterior H) then false else true) at he
  rw [ite_eq_left ha, ite_eq_right hb] at he
  cases he

theorem geometric_index_interval_count (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ((Finset.Ioc (geometricRayIndex hsch γ hγ (δ 0))
      (geometricRayIndex hsch γ hγ (δ 1))).card : ℝ≥0∞) ≤
      pathImageCount (diskRayProjection '' range δ) γ := by
  let F := Finset.Ioc (geometricRayIndex hsch γ hγ (δ 0)) (geometricRayIndex hsch γ hγ (δ 1))
  have hex : ∀ k : F, ∃ s : PathTime, ∃ t : DiskRayTime,
      δ s = (translatedHalfPlaneRay γ hγ k.val).curve t := by
    intro k
    have hk := Finset.mem_Ioc.mp k.property
    exact translated_ray_hit_between_indices hsch hsep γ hγ δ hδ k.val hk.1 hk.2
  choose s t ht using hex
  let x : F → ℂ := fun k => diskRayProjection (δ (s k))
  have hx (k : F) : x k ∈ range γ ∩ diskRayProjection '' range δ := by
    refine ⟨⟨(t k).val, ?_⟩, δ (s k), mem_range_self _, rfl⟩
    dsimp [x]
    rw [ht k, diskRayProjection_translated]
  have hxi : Injective x := by
    intro k l hkl
    have hs : s k = s l := hinj hkl
    have hh : (translatedHalfPlaneRay γ hγ k.val).curve (t k) =
        (translatedHalfPlaneRay γ hγ l.val).curve (t l) := (ht k).symm.trans (hs ▸ ht l)
    exact Subtype.ext ((translatedHalfPlaneRay_meet_iff γ hγ k.val l.val (t k) (t l)).mp hh).1
  calc
    (F.card : ℝ≥0∞) = ∑' k : F, if x k ∈ range γ ∩ diskRayProjection '' range δ then (1 : ℝ≥0∞) else 0 := by
      simp only [hx, ite_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, mul_one]
    _ ≤ pathImageCount (diskRayProjection '' range δ) γ :=
      ENNReal.tsum_comp_le_tsum_of_injective hxi
        (fun z => if z ∈ range γ ∩ diskRayProjection '' range δ then (1 : ℝ≥0∞) else 0)

theorem geometric_index_difference_le_intersections (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ENNReal.ofReal |(geometricRayIndex hsch γ hγ (δ 1) : ℝ) -
      (geometricRayIndex hsch γ hγ (δ 0) : ℝ)| ≤
      pathImageCount (diskRayProjection '' range δ) γ := by
  have hforward (ε : C(PathTime, ℂ)) (hε : ∀ t, 0 ≤ (ε t).im)
      (hi : Injective (diskRayProjection ∘ ε))
      (hle : geometricRayIndex hsch γ hγ (ε 0) ≤ geometricRayIndex hsch γ hγ (ε 1)) :
      ENNReal.ofReal ((geometricRayIndex hsch γ hγ (ε 1) : ℝ) -
        (geometricRayIndex hsch γ hγ (ε 0) : ℝ)) ≤
        pathImageCount (diskRayProjection '' range ε) γ := by
    have hcard := Int.card_Ioc_of_le _ _ hle
    have hr : ((Finset.Ioc (geometricRayIndex hsch γ hγ (ε 0))
        (geometricRayIndex hsch γ hγ (ε 1))).card : ℝ) =
        (geometricRayIndex hsch γ hγ (ε 1) : ℝ) -
        (geometricRayIndex hsch γ hγ (ε 0) : ℝ) := by exact_mod_cast hcard
    rw [← hr, ENNReal.ofReal_natCast]
    exact geometric_index_interval_count hsch hsep γ hγ ε hε hi
  by_cases hle : geometricRayIndex hsch γ hγ (δ 0) ≤ geometricRayIndex hsch γ hγ (δ 1)
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))]
    exact hforward δ hδ hinj hle
  · let ε : C(PathTime, ℂ) := ⟨δ ∘ unitInterval.symm, δ.continuous.comp unitInterval.continuous_symm⟩
    have hε0 : ε 0 = δ 1 := congrArg δ unitInterval.symm_zero
    have hε1 : ε 1 = δ 0 := congrArg δ unitInterval.symm_one
    have hrange : range ε = range δ := unitInterval.symmHomeomorph.surjective.range_comp δ
    have hi : Injective (diskRayProjection ∘ ε) := hinj.comp unitInterval.symmHomeomorph.injective
    have hh := hforward ε (fun t => hδ _) hi (by rw [hε0, hε1]; exact le_of_not_ge hle)
    rw [hε0, hε1, hrange] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hle))), neg_sub]
    exact hh

end CircleDomainRigidity

end

end OAI
