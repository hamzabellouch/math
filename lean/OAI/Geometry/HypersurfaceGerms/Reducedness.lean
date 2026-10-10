import Mathlib

namespace OAI

/-! Reduced analytic germs from isolation of the critical locus. -/

namespace AmbientMultiplicity.ReducedIsolation
noncomputable section
open Filter Topology Set Metric
abbrev C4 := Fin 4 → ℂ

def insertPlane : (ℂ × ℂ) →L[ℂ] C4 :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℂ ℂ ℂ,
    ContinuousLinearMap.snd ℂ ℂ ℂ, 0, 0]

@[simp] lemma insertPlane_zero : insertPlane (0, 0) = 0 := map_zero insertPlane

lemma insertPlane_mem {r : ℝ} (hr : 0 ≤ r) {t w : ℂ}
    (ht : t ∈ closedBall 0 r) (hw : w ∈ closedBall 0 r) :
    insertPlane (t, w) ∈ closedBall 0 r := by
  rw [mem_closedBall_zero_iff] at ht hw ⊢
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  fin_cases i
  · exact ht
  · exact hw
  all_goals simpa [insertPlane] using hr

lemma insertPlane_ne_left {t w : ℂ} (ht : t ≠ 0) : insertPlane (t, w) ≠ 0 := by
  intro h
  exact ht (congr_fun h 0)
lemma insertPlane_ne_right {t w : ℂ} (hw : w ≠ 0) : insertPlane (t, w) ≠ 0 := by
  intro h
  exact hw (congr_fun h 1)

 
theorem nonzero_of_isolated_zero {g : C4 → ℂ} (hg : AnalyticAt ℂ g 0)
    (hi : ∀ᶠ z in 𝓝 (0 : C4), g z = 0 → z = 0) : g 0 ≠ 0 := by
  intro hg0
  obtain ⟨r, hr, hh⟩ := nhds_basis_closedBall.eventually_iff.mp
    (hg.eventually_analyticAt.and hi)
  have hga : ∀ z ∈ closedBall (0 : C4) r, AnalyticAt ℂ g z := fun z hz => (hh hz).1
  have hgz : ∀ z ∈ closedBall (0 : C4) r, z ≠ 0 → g z ≠ 0 := by
    intro z hz hn he
    exact hn ((hh hz).2 he)
  let K : Set (ℂ × ℂ) := sphere 0 r ×ˢ closedBall 0 r
  have hKi : IsCompact K := (isCompact_sphere (0 : ℂ) r).prod (isCompact_closedBall (0 : ℂ) r)
  have hKmem : ∀ p ∈ K, insertPlane p ∈ closedBall 0 r := by
    intro p hp
    exact insertPlane_mem hr.le (sphere_subset_closedBall hp.1) hp.2
  have hKn : ∀ p ∈ K, g (insertPlane p) ≠ 0 := by
    intro p hp
    apply hgz _ (hKmem p hp)
    apply insertPlane_ne_left
    exact ne_of_mem_sphere hp.1 hr.ne'
  have hKc : ContinuousOn (fun p => (g (insertPlane p))⁻¹) K := by
    apply ContinuousOn.inv₀
    · intro p hp
      exact ((hga _ (hKmem p hp)).continuousAt.comp insertPlane.continuous.continuousAt).continuousWithinAt
    · exact hKn
  obtain ⟨C, hC⟩ := hKi.exists_bound_of_continuousOn hKc
  have hbound (w : ℂ) (hw : w ∈ closedBall 0 r) (hw0 : w ≠ 0) :
      ‖(g (insertPlane (0, w)))⁻¹‖ ≤ C := by
    have ha (t : ℂ) (ht : t ∈ closedBall 0 r) :
        AnalyticAt ℂ (fun t => (g (insertPlane (t, w)))⁻¹) t := by
      have hm := insertPlane_mem hr.le ht hw
      have han : AnalyticAt ℂ (fun t : ℂ => insertPlane (t, w)) t :=
        insertPlane.analyticAt _ |>.comp (analyticAt_id.prod analyticAt_const)
      exact ((hga _ hm).comp (f := fun t : ℂ => insertPlane (t, w)) han).inv (hgz _ hm (insertPlane_ne_right hw0))
    have hd : DiffContOnCl ℂ (fun t => (g (insertPlane (t, w)))⁻¹) (ball 0 r) := by
      constructor
      · intro t ht
        exact (ha t (ball_subset_closedBall ht)).differentiableAt.differentiableWithinAt
      · rw [closure_ball 0 hr.ne']
        exact fun t ht => (ha t ht).continuousAt.continuousWithinAt
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    · intro t ht
      rw [frontier_ball 0 hr.ne'] at ht
      exact hC (t, w) ⟨ht, hw⟩
    · exact subset_closure (mem_ball_self hr)
  have hgc : ContinuousAt (fun w : ℂ => g (insertPlane (0, w))) 0 := by
    have hh : ContinuousAt (fun w : ℂ => insertPlane (0, w)) 0 := by fun_prop
    have hg' : ContinuousAt g (insertPlane (0, (0 : ℂ))) := by simpa using hg.continuousAt
    exact hg'.comp (f := fun w : ℂ => insertPlane (0, w)) hh
  have hsmall : ∀ᶠ w : ℂ in 𝓝 0, ‖g (insertPlane (0, w))‖ * (max C 0 + 1) < 1 := by
    have hc := hgc.norm.mul_const (max C 0 + 1)
    exact hc.eventually (eventually_lt_nhds (by simp [hg0]))
  have he : ∃ w : ℂ, ‖g (insertPlane (0, w))‖ * (max C 0 + 1) < 1 ∧
      w ∈ closedBall 0 r ∧ w ≠ 0 := by
    have h1 := hsmall.filter_mono (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    have hb : ∀ᶠ w : ℂ in 𝓝 0, w ∈ closedBall 0 r := closedBall_mem_nhds (0 : ℂ) hr
    have h2 := hb.filter_mono (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    have h3 : ∀ᶠ w : ℂ in 𝓝[≠] 0, w ≠ 0 := by
      exact self_mem_nhdsWithin
    exact (h1.and (h2.and h3)).exists
  obtain ⟨w, hwsmall, hw, hwn⟩ := he
  have hgwn := hgz _ (insertPlane_mem hr.le (mem_closedBall_self hr.le) hw)
    (insertPlane_ne_right hwn)
  have hn : 1 = ‖g (insertPlane (0, w))‖ * ‖(g (insertPlane (0, w)))⁻¹‖ := by
    rw [← norm_mul, mul_inv_cancel₀ hgwn, norm_one]
  have hmul := mul_le_mul_of_nonneg_left (hbound w hw hwn) (norm_nonneg (g (insertPlane (0, w))))
  have hC0 : C ≤ max C 0 + 1 := by linarith [le_max_left C 0]
  have hmul' := mul_le_mul_of_nonneg_left hC0 (norm_nonneg (g (insertPlane (0, w))))
  linarith

 
theorem no_square_factor {f : C4 → ℂ}
    (hi : ∀ᶠ z in 𝓝 (0 : C4), fderiv ℂ f z = 0 → z = 0)
    (g k : C4 → ℂ) (hg : AnalyticAt ℂ g 0) (hk : AnalyticAt ℂ k 0)
    (heq : f =ᶠ[𝓝 (0 : C4)] (fun z => g z ^ 2 * k z)) : g 0 ≠ 0 := by
  apply nonzero_of_isolated_zero hg
  filter_upwards [hi, hg.eventually_analyticAt, hk.eventually_analyticAt,
    heq.eventuallyEq_nhds] with z hiz hgz hkz hez
  intro hz
  apply hiz
  have hd0 := ((hgz.differentiableAt.hasFDerivAt.pow 2).mul hkz.differentiableAt.hasFDerivAt)
  have hd := hd0.congr_of_eventuallyEq hez
  convert hd.fderiv using 1
  ext v
  simp [hz, smul_eq_mul]

end
end AmbientMultiplicity.ReducedIsolation

end OAI
