import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyPilot

namespace OAI

noncomputable section

namespace UniformKServer.HeavyEditRamp

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- The clipped ramp on [9,10]. -/
def ramp (v : ℝ) : ℝ := max 0 (min 1 (v-9))

/-- The source's ramp of distance to the center set, equal to one for the empty set. -/
def parameter (r : ℝ) (H : Finset X) (p : X) : ℝ :=
  (insert 1 (H.image (fun c => ramp (dist p c/r)))).min' (by simp)

end

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem ramp_bounds (v : ℝ) : ramp v ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

omit [MetricSpace X] in
theorem ramp_zero {v : ℝ} (h : v ≤ 9) : ramp v = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [MetricSpace X] in
theorem ramp_one {v : ℝ} (h : 10 ≤ v) : ramp v = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

omit [MetricSpace X] in
theorem ramp_lip (v w : ℝ) : |ramp v-ramp w| ≤ |v-w| := by
  have h₁ := abs_max_sub_max_le_max (0:ℝ) (min 1 (v-9)) 0 (min 1 (w-9))
  have h₂ := abs_min_sub_min_le_max (1:ℝ) (v-9) 1 (w-9)
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 (v-9)-min 1 (w-9)))] at h₁
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (v-9-(w-9)))] at h₂
  simpa only [sub_sub_sub_cancel_right,ramp] using h₁.trans h₂

theorem parameter_bounds (r : ℝ) (H : Finset X) (p : X) :
    parameter r H p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.le_min'
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · norm_num
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ha
      exact (ramp_bounds _).1
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem parameter_le_center (r : ℝ) (H : Finset X) (p c : X) (hc : c ∈ H) :
    parameter r H p ≤ ramp (dist p c/r) :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c,hc,rfl⟩))

theorem le_parameter (r : ℝ) (H : Finset X) (p : X) (a : ℝ) (h1 : a ≤ 1)
    (hc : ∀ c ∈ H, a ≤ ramp (dist p c/r)) : a ≤ parameter r H p := by
  apply Finset.le_min'
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact h1
  · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hb
    exact hc c hc'

theorem parameter_lip (r : ℝ) (hr : 0 < r) (H : Finset X) (p q : X) :
    |parameter r H p-parameter r H q| ≤ dist p q/r := by
  suffices h : ∀ p q : X, parameter r H p-parameter r H q ≤ dist p q/r by
    apply abs_le.mpr
    constructor
    · have hh := h q p
      rw [dist_comm q p] at hh
      linarith
    · exact h p q
  intro p q
  have hm := Finset.min'_mem (insert 1 (H.image (fun c => ramp (dist q c/r)))) (by simp)
  change parameter r H q ∈ insert 1 (H.image (fun c => ramp (dist q c/r))) at hm
  rcases Finset.mem_insert.mp hm with hq | hq
  · rw [hq]
    have := (parameter_bounds r H p).2
    exact (sub_nonpos.mpr this).trans (div_nonneg dist_nonneg hr.le)
  · obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hq
    have h₁ := parameter_le_center r H p c hc
    have h₂ := (le_abs_self (ramp (dist p c/r)-ramp (dist q c/r))).trans (ramp_lip _ _)
    have h₃ : |dist p c/r-dist q c/r| ≤ dist p q/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
      exact div_le_div_of_nonneg_right (abs_dist_sub_le p q c) hr.le
    rw [he] at h₂
    linarith

end
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

theorem center_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (p c : X)
    (hc : c ∈ H) (hd : dist p c ≤ 9*r) : parameter r H p=0 := by
  have he := parameter_le_center r H p c hc
  rw [ramp_zero ((div_le_iff₀ hr).mpr hd)] at he
  linarith [(parameter_bounds r H p).1]

theorem far_one (r : ℝ) (hr : 0 < r) (H : Finset X) (p : X)
    (hd : ∀ c ∈ H, 10*r ≤ dist p c) : parameter r H p=1 := by
  apply le_antisymm (parameter_bounds r H p).2
  apply le_parameter r H p 1 le_rfl
  intro c hc
  rw [ramp_one ((le_div_iff₀ hr).mpr (hd c hc))]

theorem update_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : dist p x ≤ 9*r) : parameter r (HeavyPilot.updateCenters r H x) p=0 :=
  center_zero r hr _ p x (Finset.mem_insert_self _ _) hp

theorem update_far (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : 110*r < dist p x) : parameter r (HeavyPilot.updateCenters r H x) p ≤ parameter r H p := by
  apply le_parameter r H p _ (parameter_bounds r (HeavyPilot.updateCenters r H x) p).2
  intro c hc
  by_cases hfar : 100*r < dist x c
  · exact parameter_le_center r (HeavyPilot.updateCenters r H x) p c (by simp [HeavyPilot.updateCenters,hc,hfar])
  · have hpc : 10 ≤ dist p c/r := by
      have ht := dist_triangle p c x
      rw [dist_comm c x] at ht
      apply (le_div_iff₀ hr).mpr
      push Not at hfar
      linarith
    rw [ramp_one hpc]
    exact (parameter_bounds r (HeavyPilot.updateCenters r H x) p).2

end UniformKServer.HeavyEditRamp

end

end OAI
