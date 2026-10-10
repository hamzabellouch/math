import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.RoutingArrayTrace
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartRouting

namespace OAI

noncomputable section
namespace VelocityDetection.ChartTrace
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open ChartRouting CenterPaths
variable (A : RoutingData) (tr : RoutingArray.Trace A) (N : ℕ)

def height (n : ℕ) : ℝ := if tr.stopped n then -(7/16:ℝ) else -scale A N

def vertex (n : ℕ) : Coord 2 :=
  origin + ![scale A N * tr.address n, height A tr N n]

def segment (n : ℕ) (s : ℝ) : Coord 2 :=
  origin + signedCenter (n:ℝ) 1 (scale A N) (scale A N)
    (height A tr N n / scale A N) (height A tr N (n+1) / scale A N)
    (tr.address n) (tr.address (n+1)) s

@[fun_prop] theorem contDiff_segment (n : ℕ) : ContDiff ℝ ∞ (segment A tr N n) := by
  unfold segment
  fun_prop

theorem segment_source_collar (n : ℕ) {s : ℝ} (hs : 3*(s-n) ≤ 1/4) :
    segment A tr N n s = vertex A tr N n := by
  have ht : theta (n:ℝ) 1 0 s = 0 := by
    apply ramp_zero
    norm_num only [div_one,Nat.cast_zero]
    linarith
  unfold segment signedCenter
  rw [center_source_collar _ _ (by norm_num only [div_one]; exact hs),ht]
  unfold vertex
  congr 1
  ext i
  fin_cases i
  · simp
  · change -scale A N + (1-0)*(height A tr N n / scale A N + 1)*scale A N = height A tr N n
    rw [sub_zero,one_mul,add_mul,div_mul_cancel₀ _ (ne_of_gt (scale_pos A N))]
    ring

theorem segment_target_collar (n : ℕ) {s : ℝ} (hs : 11/4 ≤ 3*(s-n)) :
    segment A tr N n s = vertex A tr N (n+1) := by
  have ht : theta (n:ℝ) 1 0 s = 1 := by
    apply ramp_one
    norm_num only [div_one,Nat.cast_zero]
    linarith
  unfold segment signedCenter
  rw [center_target_collar _ _ (by norm_num only [div_one]; exact hs),ht]
  simp only [sub_self,zero_mul,div_mul_cancel₀ _ (ne_of_gt (scale_pos A N))]
  ext i
  fin_cases i <;> simp [vertex]

theorem segment_before (n : ℕ) {s : ℝ} (hs : s ≤ n) :
    segment A tr N n s = vertex A tr N n :=
  segment_source_collar A tr N n (by linarith)

theorem segment_after (n : ℕ) {s : ℝ} (hs : n+1 ≤ s) :
    segment A tr N n s = vertex A tr N (n+1) :=
  segment_target_collar A tr N n (by linarith)

theorem velocity_before (n : ℕ) {s : ℝ} (hs : s ≤ n) :
    deriv (segment A tr N n) s = 0 := by
  have hv : ∀ᶠ r : ℝ in 𝓝 s, 3*(r-n) < 1/4 :=
    (isOpen_lt (by fun_prop : Continuous (fun r : ℝ => 3*(r-n))) continuous_const).mem_nhds
      (show 3*(s-(n:ℝ)) < (1/4:ℝ) by linarith)
  have he : segment A tr N n =ᶠ[𝓝 s] fun _ => vertex A tr N n :=
    hv.mono (fun r hr => segment_source_collar A tr N n hr.le)
  rw [he.deriv_eq,deriv_const]

theorem velocity_after (n : ℕ) {s : ℝ} (hs : n+1 ≤ s) :
    deriv (segment A tr N n) s = 0 := by
  have hv : ∀ᶠ r : ℝ in 𝓝 s, 11/4 < 3*(r-n) :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun r : ℝ => 3*(r-n)))).mem_nhds
      (show (11/4:ℝ) < 3*(s-(n:ℝ)) by linarith)
  have he : segment A tr N n =ᶠ[𝓝 s] fun _ => vertex A tr N (n+1) :=
    hv.mono (fun r hr => segment_target_collar A tr N n hr.le)
  rw [he.deriv_eq,deriv_const]

def route (s : ℝ) : Coord 2 := vertex A tr N 0 +
  ∑ k ∈ Finset.range N, (segment A tr N k s - vertex A tr N k)

@[fun_prop] theorem contDiff_route : ContDiff ℝ ∞ (route A tr N) := by
  unfold route
  exact contDiff_const.add (ContDiff.sum (fun k _ => (contDiff_segment A tr N k).sub contDiff_const))

theorem route_before {s : ℝ} (hs : s ≤ 0) : route A tr N s = vertex A tr N 0 := by
  unfold route
  have hz : ∀ k ∈ Finset.range N, segment A tr N k s - vertex A tr N k = 0 := by
    intro k _
    rw [segment_before A tr N k (hs.trans (Nat.cast_nonneg _)),sub_self]
  rw [Finset.sum_eq_zero hz,add_zero]

theorem route_after {s : ℝ} (hs : N ≤ s) : route A tr N s = vertex A tr N N := by
  unfold route
  have he : ∀ k ∈ Finset.range N, segment A tr N k s = vertex A tr N (k+1) := by
    intro k hk
    apply segment_after
    have hh : (k:ℝ)+1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    exact hh.trans hs
  rw [Finset.sum_congr rfl (fun k hk => congrArg (fun v => v-vertex A tr N k) (he k hk)),
    Finset.sum_range_sub]
  abel

theorem route_eq_segment (n : ℕ) (hn : n < N) {s : ℝ} (hs : s ∈ Icc (n:ℝ) (n+1)) :
    route A tr N s = segment A tr N n s := by
  classical
  have he := Finset.sum_subset (Finset.range_mono (show n+1 ≤ N by omega))
    (f := fun k => segment A tr N k s-vertex A tr N k) (by
      intro k _ hk
      have hnk : n+1 ≤ k := by simpa using hk
      have hh : (n:ℝ)+1 ≤ k := by exact_mod_cast hnk
      rw [segment_before A tr N k (hs.2.trans hh),sub_self])
  unfold route
  rw [← he,Finset.sum_range_succ]
  have hprev : ∀ k ∈ Finset.range n, segment A tr N k s = vertex A tr N (k+1) := by
    intro k hk
    apply segment_after
    have hh : (k:ℝ)+1 ≤ n := by exact_mod_cast Finset.mem_range.mp hk
    exact hh.trans hs.1
  rw [Finset.sum_congr rfl (fun k hk => congrArg (fun v => v-vertex A tr N k) (hprev k hk)),
    Finset.sum_range_sub]
  abel

theorem deriv_route (s : ℝ) : deriv (route A tr N) s =
    ∑ k ∈ Finset.range N, deriv (segment A tr N k) s := by
  have hh := (HasDerivAt.sum (u := Finset.range N) (fun k _ =>
    (((contDiff_segment A tr N k).differentiable (by simp) s).hasDerivAt.sub_const
      (vertex A tr N k)))).const_add (vertex A tr N 0)
  change deriv (fun r => vertex A tr N 0 +
    ∑ k ∈ Finset.range N, (segment A tr N k r - vertex A tr N k)) s = _
  simpa only [Finset.sum_apply] using hh.deriv

theorem route_velocity_before {s : ℝ} (hs : s ≤ 0) : deriv (route A tr N) s = 0 := by
  rw [deriv_route]
  exact Finset.sum_eq_zero (fun k _ => velocity_before A tr N k (hs.trans (Nat.cast_nonneg _)))

theorem route_velocity_after {s : ℝ} (hs : N ≤ s) : deriv (route A tr N) s = 0 := by
  rw [deriv_route]
  apply Finset.sum_eq_zero
  intro k hk
  apply velocity_after
  have hh : (k:ℝ)+1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
  exact hh.trans hs

theorem route_velocity (n : ℕ) (hn : n < N) {s : ℝ} (hs : s ∈ Icc (n:ℝ) (n+1)) :
    deriv (route A tr N) s = deriv (segment A tr N n) s := by
  rw [deriv_route]
  apply Finset.sum_eq_single n
  · intro k _ hkn
    rcases lt_or_gt_of_ne hkn with h | h
    · apply velocity_after
      have hh : (k:ℝ)+1 ≤ n := by exact_mod_cast h
      exact hh.trans hs.1
    · apply velocity_before
      have hh : (n:ℝ)+1 ≤ k := by exact_mod_cast h
      exact hs.2.trans hh
  · exact fun h => (h (Finset.mem_range.mpr hn)).elim

theorem segment_eq_installed (n : ℕ) (h : tr.stopped n = false) :
    segment A tr N n = path A N n (tr.instruction n h) := by
  have hh : height A tr N n / scale A N = -1 := by
    simp [height,h,ne_of_gt (scale_pos A N)]
  have ht : height A tr N (n+1) = targetHeight A N n (tr.instruction n h) := by
    simp only [height,targetHeight,tr.sign_eq]
    cases tr.stopped (n+1) <;> norm_num
  unfold segment path
  rw [hh,ht,signed_source_negative,tr.source_eq,tr.target_eq]

theorem route_plateau (h : ∀ n < N, tr.stopped n = false) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) N) (X : Coord 2)
    (hX : ∀ i, |X i-route A tr N s i| ≤ radius A N) :
    periodicPrefix A N s X = deriv (route A tr N) s := by
  by_cases hN : N = 0
  · subst N
    have hz : s = 0 := le_antisymm (by simpa using hs.2) hs.1
    subst s
    rw [route_velocity_before A tr 0 le_rfl]
    change Periodization.extend (finiteField A 0) 0 X = 0
    simp [Periodization.extend,finiteField]
  by_cases he : s = N
  · subst s
    rw [route_velocity_after A tr N le_rfl]
    have hz : finiteField A N (N:ℝ) = 0 := funext (prefix_zero_after A N le_rfl)
    change Periodization.extend (finiteField A N) N X = 0
    simp [Periodization.extend,hz]
  have hn : ⌊s⌋₊ < N := (Nat.floor_lt hs.1).mpr (lt_of_le_of_ne hs.2 he)
  have hsn : s ∈ Icc (⌊s⌋₊:ℝ) (⌊s⌋₊+1) := ⟨Nat.floor_le hs.1,(Nat.lt_floor_add_one s).le⟩
  rw [route_eq_segment A tr N _ hn hsn,segment_eq_installed A tr N _ (h _ hn)] at hX
  rw [route_velocity A tr N _ hn hsn,segment_eq_installed A tr N _ (h _ hn)]
  exact periodicPrefix_plateau A N _ (tr.instruction _ (h _ hn)) hn hsn X hX

end VelocityDetection.ChartTrace
end

end OAI
