import OAI.Geometry.Convex.GeneralMahler.Lift

namespace OAI
/-! Polar bodies, translations, and slices. -/
noncomputable section
open Set MeasureTheory Real WithLp Metric Filter
open scoped ENNReal NNReal Topology Pointwise RealInnerProductSpace
namespace GeneralMahler
variable {n : ℕ}

/-- (K-z)^o from the manuscript. -/
def polarAt (K : Set (Rn n)) (z : Rn n) : Set (Rn n) :=
  {y | ∀ x ∈ K, ⟪y,x-z⟫ ≤ 1}

namespace Body

/-- K translated by -z. -/
def off (K : Body n) (z : Rn n) : Body n where
  carrier := (fun x => z + x) ⁻¹' (K : Set (Rn n))
  convex' := by
    intro x hx y hy a b ha hb hab
    have H := K.convex hx hy ha hb hab
    change z + (a • x + b • y) ∈ K
    change a • (z+x) + b • (z+y) ∈ K at H
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at H
    exact H
  isCompact' := (Homeomorph.addLeft z).isCompact_preimage.mpr K.isCompact
  nonempty' := by
    obtain ⟨x,hx⟩ := K.nonempty
    refine ⟨-z+x,?_⟩
    simpa using hx
  solid := by
    obtain ⟨x,hx⟩ := K.has_interior
    refine ⟨-z+x,?_⟩
    change _ ∈ interior ((Homeomorph.addLeft z) ⁻¹' _)
    rw [← Homeomorph.preimage_interior]
    simpa using hx

@[simp] theorem mem_off {K : Body n} (z x : Rn n) :
    x ∈ K.off z ↔ z+x ∈ K := Iff.rfl

theorem off_interior {K : Body n} {z : Rn n} (hz : z ∈ interior (K:Set (Rn n))) :
    0 ∈ interior (K.off z : Set (Rn n)) := by
  change _ ∈ interior ((Homeomorph.addLeft z) ⁻¹' _)
  rw [← Homeomorph.preimage_interior]
  simp
  exact hz

theorem polar_off (K : Body n) (z : Rn n) :
    polarAt K z = polarAt (K.off z) 0 := by
  ext y
  constructor
  · intro hy x hx
    simpa using hy (z+x) hx
  · intro hy x hx
    have hm : x-z ∈ K.off z := by
      simpa [sub_eq_add_neg, add_left_comm] using hx
    simpa using hy _ hm

/-- Uniform lower bound for height in the dual cone to K with 0 interior. -/
lemma dual_height {K : Body n} (hk : 0 ∈ interior (K:Set (Rn n))) :
    ∃ c > 0, ∀ p ∈ posDual K.cone, c * ‖p‖ ≤ hgt p := by
  have heq : posDual (posDual K.cone) = K.cone := ProperCone.innerDual_innerDual _
  have H : pair 1 0 ∈ interior (posDual (posDual K.cone) : Set (LiftSpace n)) := by
    rw [heq]
    simpa using (pair_mem_interior_cone_iff K 1 (by norm_num) 0).mpr hk
  obtain ⟨c,hc,hb⟩ := interior_dual_bound H
  refine ⟨c,hc,fun p hp => ?_⟩
  have h := hb p hp
  conv at h =>
    rhs
    rw [← hgt_horiz_pair p, pair_inner, inner_zero_left, add_zero, mul_one]
  exact h

lemma dual_head {K : Body n} (x : Rn n) :
    pair 1 x ∈ posDual K.cone ↔ -x ∈ polarAt (K : Set (Rn n)) 0 := by
  rw [mem_posDual]
  constructor
  · intro h y hy
    change y ∈ K at hy
    have H := h (show pair 1 y ∈ K.cone by simp [hy])
    rw [pair_inner, mul_one] at H
    change ⟪-x,y-0⟫ ≤ 1
    rw [inner_neg_left, sub_zero, real_inner_comm]
    linarith
  · intro h p hp
    rw [← hgt_horiz_pair p] at hp ⊢
    obtain ⟨hu,a,ha,he⟩ := (pair_mem_cone ..).mp hp
    have H := h _ ha
    rw [inner_neg_left, sub_zero, real_inner_comm] at H
    rw [pair_inner, he, real_inner_smul_left]
    nlinarith

/-- Slice t=1 of the dual, a reflected polar. -/
def polarSlice (K : Body n) (hk : 0 ∈ interior (K:Set (Rn n))) : Body n where
  carrier := {x | pair 1 x ∈ posDual K.cone}
  convex' := by
    intro x hx y hy a b ha hb hab
    have H := (posDual K.cone).convex hx hy ha hb hab
    change pair 1 (a • x + b • y) ∈ posDual K.cone
    change a • pair 1 x + b • pair 1 y ∈ posDual K.cone at H
    have he : a • pair 1 x + b • pair 1 y = pair 1 (a • x + b • y) := calc
      _ = pair (a * 1+b*1) (a • x+b • y) := rfl
      _ = _ := by rw [mul_one,mul_one,hab]
    rwa [he] at H
  isCompact' := by
    have hcl : IsClosed {x | pair 1 x ∈ posDual K.cone} :=
      (posDual K.cone).isClosed.preimage (show Continuous (fun x : Rn n => pair 1 x) by fun_prop)
    apply (Metric.isCompact_iff_isClosed_bounded).mpr
    obtain ⟨c,hc,hcw⟩ := dual_height hk
    refine ⟨hcl,(isBounded_closedBall (x := (0:Rn n)) (r := 1/c)).subset ?_⟩
    intro x hx
    rw [mem_closedBall, dist_zero_right, le_div_iff₀ hc, mul_comm]
    have H := hcw (pair 1 x) hx
    have hn := WithLp.prod_norm_sq_eq_of_L2 (pair 1 x)
    change ‖pair 1 x‖ ^ 2 = ‖(1:ℝ)‖ ^ 2 + ‖x‖^2 at hn
    have hp : ‖x‖ ≤ ‖pair 1 x‖ := by nlinarith [norm_nonneg (pair 1 x)]
    exact le_trans (mul_le_mul_of_nonneg_left hp hc.le) H
  nonempty' :=
    ⟨0, show pair 1 0 ∈ posDual K.cone from interior_subset (axis_dual_interior K 1 zero_lt_one)⟩
  solid := by
    refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    have h : Continuous (fun x : Rn n => pair 1 x) := by fun_prop
    exact (h.tendsto 0) (mem_interior_iff_mem_nhds.mp (axis_dual_interior K 1 zero_lt_one))

theorem cone_polarSlice (K : Body n) (hk : 0 ∈ interior (K:Set (Rn n))) :
    (polarSlice K hk).cone = posDual K.cone := by
  ext p
  rw [← hgt_horiz_pair p, pair_mem_cone]
  constructor
  · rintro ⟨ht,x,hx,he⟩
    change pair 1 x ∈ posDual K.cone at hx
    have H := (posDual K.cone).smul_mem hx ht
    simpa only [smul_pair,mul_one,he] using H
  · rw [hgt_horiz_pair]
    intro hp
    obtain ⟨c,hc,hcw⟩ := dual_height hk
    have H := hcw p hp
    by_cases hz : p = 0
    · subst p
      obtain ⟨x,hx⟩ := (K.polarSlice hk).nonempty
      refine ⟨le_refl _,x,hx,?_⟩
      change 0 = (0:ℝ) • x
      simp
    · have hr : 0 < hgt p := lt_of_lt_of_le (mul_pos hc (norm_pos_iff.mpr hz)) H
      refine ⟨hr.le,(hgt p)⁻¹ • horiz p, ?_, by simp [hr.ne']⟩
      change pair 1 _ ∈ posDual _
      have he := (posDual K.cone).smul_mem hp (inv_nonneg.mpr hr.le)
      have hpair : (hgt p)⁻¹ • p = pair 1 ((hgt p)⁻¹ • horiz p) := calc
        _ = pair ((hgt p)⁻¹ * hgt p) ((hgt p)⁻¹ • horiz p) := rfl
        _ = _ := by rw [inv_mul_cancel₀ hr.ne']
      rwa [hpair] at he

theorem polarSlice_volume (K : Body n) (hk : 0 ∈ interior (K:Set (Rn n))) :
    volume (K.polarSlice hk : Set (Rn n)) = volume (polarAt (K : Set (Rn n)) 0) := by
  have he : (K.polarSlice hk : Set (Rn n)) = (fun x => -x) ⁻¹' polarAt (K : Set (Rn n)) 0 := by
    ext; exact dual_head _
  rw [he]; simp

end Body
end GeneralMahler

end

end OAI
