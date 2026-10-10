import Mathlib
import OAI.Combinatorics.UniformKServer.PilotDrift
import OAI.Combinatorics.UniformKServer.PilotFiltering

namespace OAI

noncomputable section

namespace UniformKServer.HeavyPilot

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- The clipped ramp on [3,4]. -/
def ramp (v : ℝ) : ℝ := max 0 (min 1 (v-3))

/-- The source's ramp of distance to the center set, equal to one for the empty set. -/
def parameter (r : ℝ) (H : Finset X) (p : X) : ℝ :=
  (insert 1 (H.image (fun c => ramp (dist p c/r)))).min' (by simp)

/-- The heavy update deletes all centers at distance at most 100r, then inserts x. -/
def updateCenters (r : ℝ) (H : Finset X) (x : X) : Finset X :=
  insert x (H.filter fun c => 100*r < dist x c)

def annulusMass (r : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ p, if 3*r < dist p x ∧ dist p x ≤ 120*r then μ p else 0

end

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem ramp_bounds (v : ℝ) : ramp v ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

omit [MetricSpace X] in
theorem ramp_zero {v : ℝ} (h : v ≤ 3) : ramp v = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [MetricSpace X] in
theorem ramp_one {v : ℝ} (h : 4 ≤ v) : ramp v = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

omit [MetricSpace X] in
theorem ramp_lip (v w : ℝ) : |ramp v-ramp w| ≤ |v-w| := by
  have h₁ := abs_max_sub_max_le_max (0:ℝ) (min 1 (v-3)) 0 (min 1 (w-3))
  have h₂ := abs_min_sub_min_le_max (1:ℝ) (v-3) 1 (w-3)
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 (v-3)-min 1 (w-3)))] at h₁
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (v-3-(w-3)))] at h₂
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

theorem update_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : dist p x ≤ 3*r) : parameter r (updateCenters r H x) p = 0 := by
  have hc := parameter_le_center r (updateCenters r H x) p x (by simp [updateCenters])
  rw [ramp_zero ((div_le_iff₀ hr).mpr hp)] at hc
  linarith [(parameter_bounds r (updateCenters r H x) p).1]

theorem update_far (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : 104*r < dist p x) : parameter r (updateCenters r H x) p ≤ parameter r H p := by
  apply le_parameter r H p _ (parameter_bounds r (updateCenters r H x) p).2
  intro c hc
  by_cases hfar : 100*r < dist x c
  · exact parameter_le_center r (updateCenters r H x) p c (by simp [updateCenters,hc,hfar])
  · have hpc : 4 ≤ dist p c/r := by
      have ht := dist_triangle p c x
      rw [dist_comm c x] at ht
      apply (le_div_iff₀ hr).mpr
      push Not at hfar
      linarith
    rw [ramp_one hpc]
    exact (parameter_bounds r (updateCenters r H x) p).2

theorem increase_support (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hinc : parameter r H p < parameter r (updateCenters r H x) p) :
    3*r < dist p x ∧ dist p x ≤ 104*r := by
  constructor
  · by_contra h
    have he := update_zero r hr H x p (le_of_not_gt h)
    rw [he] at hinc
    linarith [(parameter_bounds r H p).1]
  · by_contra h
    exact (not_lt_of_ge (update_far r hr H x p (lt_of_not_ge h))) hinc

theorem near_old_one (r : ℝ) (hr : 0 < r) (H : Finset X) (x s : X)
    (hfar : ∀ c ∈ H, 8*r < dist x c) (hs : dist s x/r < 1/4) :
    parameter r H s = 1 := by
  apply le_antisymm (parameter_bounds r H s).2
  apply le_parameter r H s 1 le_rfl
  intro c hc
  have hsc : 4 ≤ dist s c/r := by
    have ht := dist_triangle x s c
    rw [dist_comm x s] at ht
    have hds := (div_lt_iff₀ hr).mp hs
    apply (le_div_iff₀ hr).mpr
    linarith [hfar c hc]
  rw [ramp_one hsc]

theorem near_new_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (x s : X)
    (hs : dist s x/r < 1/4) : parameter r (updateCenters r H x) s = 0 := by
  apply update_zero r hr H x s
  have hds := (div_lt_iff₀ hr).mp hs
  linarith

theorem annulus_surcharge (r : ℝ) (hr : 0 < r) (x s p : X)
    (hs : dist s x/r < 1/4) (hp : 3*r < dist p x ∧ dist p x ≤ 120*r) :
    PilotCompact.bumpA 1 512 (dist s p/r) = 1 := by
  have hds := (div_lt_iff₀ hr).mp hs
  have hlow : 1 ≤ dist s p/r := by
    apply (le_div_iff₀ hr).mpr
    have ht := dist_triangle p s x
    rw [dist_comm p s] at ht
    linarith [hp.1]
  have hhigh : dist s p/r ≤ 512 := by
    apply (div_le_iff₀ hr).mpr
    have ht := dist_triangle s x p
    rw [dist_comm x p] at ht
    linarith [hp.2]
  simp only [PilotCompact.bumpA,ite_eq_left hhigh,one_pow,div_one]
  exact min_eq_right (by nlinarith)

end

section
attribute [local instance] Classical.propDecidable
open PilotCompact
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem integrand_gain (r : ℝ) (hr : 0 < r) (H : Finset X) (x s : X)
    (hfar : ∀ c ∈ H, 8*r < dist x c) (hs : dist s x/r < 1/4)
    (z : X → ℝ) (hz : feasible r 1 512 z) (hweight : (1:ℝ)/2 ≤ z s)
    (hzero : ∀ c, 1/4 ≤ dist c x/r → dist c x/r ≤ 256 → z c = 0) (p : X) :
    (if 3*r < dist p x ∧ dist p x ≤ 120*r then 127 else 0) ≤
      integrand r 1 512 (parameter r H) z p -
        integrand r 1 512 (parameter r (updateCenters r H x)) z p := by
  let go := parameter r H
  let gn := parameter r (updateCenters r H x)
  let B := 1-∑ c, z c*bumpB 1 (dist c p/r)
  let A := fun c => z c*(go c-gn c)*bumpA 1 512 (dist c p/r)
  have hB : B ∈ Set.Icc (0:ℝ) 1 := by
    have h := weighted_bumpB_sum r 1 512 (by norm_num) (by norm_num) (by norm_num) z hz p
    dsimp [B]
    constructor <;> linarith [h.1,h.2]
  have hA : ∀ c, 0 ≤ A c := by
    intro c
    by_cases hc : go c < gn c
    · have hsup := increase_support r hr H x c hc
      have he : z c = 0 := hzero c (by
          apply (le_div_iff₀ hr).mpr
          linarith [hsup.1]) (by
          apply (div_le_iff₀ hr).mpr
          linarith [hsup.2])
      simp [A,he]
    · exact mul_nonneg (mul_nonneg (hz.1 c) (sub_nonneg.mpr (le_of_not_gt hc)))
        (bumpA_bounds 1 512 _ (by norm_num)).1
  have hid : integrand r 1 512 go z p-integrand r 1 512 gn z p =
      (go p-gn p)*B+256*∑ c, A c := by
    simp only [integrand,A,B,mul_add,add_mul,mul_sub,sub_mul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
    ring
  change _ ≤ integrand r 1 512 go z p-integrand r 1 512 gn z p
  rw [hid]
  by_cases hp : 3*r < dist p x ∧ dist p x ≤ 120*r
  · rw [ite_eq_left hp]
    have hsingle : z s ≤ ∑ c, A c := by
      have hh := Finset.single_le_sum (f := A) (fun c _ => hA c) (Finset.mem_univ s)
      have hsA : A s = z s := by
        dsimp [A,go,gn]
        rw [near_old_one r hr H x s hfar hs,near_new_zero r hr H x s hs,
          annulus_surcharge r hr x s p hs hp]
        ring
      rw [hsA] at hh
      exact hh
    have hres : -1 ≤ (go p-gn p)*B := by
      have hg : -1 ≤ go p-gn p := by
        dsimp [go,gn]
        linarith [(parameter_bounds r H p).1,(parameter_bounds r (updateCenters r H x) p).2]
      have hh := mul_le_mul_of_nonneg_right hg hB.1
      nlinarith [hB.2]
    linarith
  · rw [ite_eq_right hp]
    have hgn : gn p ≤ go p := by
      by_contra h
      have hsup := increase_support r hr H x p (lt_of_not_ge h)
      exact hp ⟨hsup.1,by linarith [hsup.2]⟩
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hgn) hB.1)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun c _ => hA c)))

end
open PilotCompact
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Exact heavy-center pilot gain, companion §07 heavy annulus budget. -/
theorem heavy_gain (r γ δ : ℝ) (hr : 0 < r)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1/64) (hδ : 0 < δ) (hδsmall : δ ≤ 1/4112)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (H : Finset X) (x : X)
    (hfar : ∀ c ∈ H, 8*r < dist x c)
    (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*512) μ x ≤ (1+δ)*ballMass r γ μ x) :
    127*r*annulusMass r μ x ≤
      value r 1 512 μ (parameter r H) -
        value r 1 512 μ (parameter r (updateCenters r H x))
 := by
  classical
  obtain ⟨z,hz,hmin,_⟩ := minimum_exists r 1 512 μ (parameter r H)
  obtain ⟨s,hs,hw,_,_⟩ := near_site_exists r 1 512 γ δ hr (by norm_num) (by norm_num)
    (by norm_num) hγ (by simpa using hγsmall) hδ hδsmall μ (parameter r H) z hμ
    (parameter_bounds r H) x hM hconc hz hmin
  have hzero : ∀ c, 1/4 ≤ dist c x/r → dist c x/r ≤ 256 → z c = 0 := by
    intro c hnear hfar
    exact middle_site_zero r 1 512 γ δ hr (by norm_num) (by norm_num) (by norm_num)
      hγ (by simpa using hγsmall) hδ hδsmall μ (parameter r H) z hμ (parameter_bounds r H)
      x hM hconc hz hmin c (by simpa using hnear) (by norm_num; exact hfar)
  have hg : ∀ p, (if 3*r < dist p x ∧ dist p x ≤ 120*r then 127 else 0) ≤
      integrand r 1 512 (parameter r H) z p -
        integrand r 1 512 (parameter r (updateCenters r H x)) z p :=
    fun p => integrand_gain r hr H x s hfar hs z hz (by linarith) hzero p
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hg p) (hμ p))
  have hh := mul_le_mul_of_nonneg_left hsum hr.le
  have hleft : r*(∑ p, μ p*(if 3*r < dist p x ∧ dist p x ≤ 120*r then 127 else 0)) =
      127*r*annulusMass r μ x := by
    unfold annulusMass
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  have hright : r*(∑ p, μ p*(integrand r 1 512 (parameter r H) z p -
        integrand r 1 512 (parameter r (updateCenters r H x)) z p)) =
      objective r 1 512 μ (parameter r H) z -
        objective r 1 512 μ (parameter r (updateCenters r H x)) z := by
    simp only [objective,mul_sub,Finset.sum_sub_distrib]
  rw [hleft,hright,hmin] at hh
  have hv := value_le r 1 512 μ (parameter r (updateCenters r H x)) z hz
  linarith

end UniformKServer.HeavyPilot

end

end OAI
