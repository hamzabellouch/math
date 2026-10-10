import Mathlib
import OAI.Combinatorics.UniformKServer.PilotConcentration

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Capacity controls all radii whose support meets either of two nearby points.
This is a weighted finite-sum statement, not an assumed HST drift estimate. -/
theorem weighted_radial_lipschitz (r R a C B : ℝ) (hr : 0 < r) (hR : 256 ≤ R)
    (ha : a ≤ 2*R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hfzero : ∀ u, a ≤ u → f u = 0)
    (hfLip : ∀ u v, 0 ≤ u → 0 ≤ v → |f u-f v| ≤ C*|u-v|)
    (z θ : X → ℝ) (hz : ∀ s, 0 ≤ z s) (hθ : ∀ s, θ s ∈ Set.Icc (0:ℝ) B)
    (x y : X) (hcap : (∑ s, max (z s-gate R (dist s x/r)) 0) ≤ 1)
    (hxy : dist x y/r ≤ 1) :
    |(∑ s, z s*θ s*f (dist s x/r))-(∑ s, z s*θ s*f (dist s y/r))| ≤
      B*C*(dist x y/r) := by
  have hd : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hs : ∀ s, |z s*θ s*(f (dist s x/r)-f (dist s y/r))| ≤
      max (z s-gate R (dist s x/r)) 0*(B*C*(dist x y/r)) := by
    intro s
    by_cases hx : dist s x/r ≤ 2*R+1
    · have hg : gate R (dist s x/r) = 0 := gate_eq_zero R _ (by linarith) (by linarith)
      rw [hg, sub_zero, max_eq_left (hz s), abs_mul, abs_mul,
        abs_of_nonneg (hz s), abs_of_nonneg (hθ s).1]
      have hdist : |dist s x/r-dist s y/r| ≤ dist x y/r := by
        rw [←sub_div, abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right (by simpa only [dist_comm] using abs_dist_sub_le x y s) hr.le
      have hf := (hfLip _ _ (div_nonneg dist_nonneg hr.le)
        (div_nonneg dist_nonneg hr.le)).trans (mul_le_mul_of_nonneg_left hdist hC)
      calc
        _ ≤ z s*θ s*(C*(dist x y/r)) :=
          mul_le_mul_of_nonneg_left hf (mul_nonneg (hz s) (hθ s).1)
        _ ≤ z s*B*(C*(dist x y/r)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hθ s).2 (hz s))
            (mul_nonneg hC hd)
        _ = _ := by ring
    · have htri := normalized_triangle r hr s y x
      rw [dist_comm y x] at htri
      have hfx := hfzero (dist s x/r) (by linarith)
      have hfy := hfzero (dist s y/r) (by linarith)
      rw [hfx, hfy, sub_self, mul_zero, abs_zero]
      exact mul_nonneg (le_max_right _ _) (by positivity)
  calc
    _ = |∑ s, z s*θ s*(f (dist s x/r)-f (dist s y/r))| := by
      rw [←Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ ∑ s, |z s*θ s*(f (dist s x/r)-f (dist s y/r))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, max (z s-gate R (dist s x/r)) 0*(B*C*(dist x y/r)) :=
      Finset.sum_le_sum fun s _ => hs s
    _ = (∑ s, max (z s-gate R (dist s x/r)) 0)*(B*C*(dist x y/r)) :=
      (Finset.sum_mul ..).symm
    _ ≤ 1*(B*C*(dist x y/r)) := mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := one_mul _

theorem integrand_global_lipschitz (r σ R L : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r))
    (hz : feasible r σ R z) (x y : X) :
    |integrand r σ R g z x-integrand r σ R g z y| ≤ (L+1026/σ)*(dist x y/r) := by
  have hd : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  by_cases hxy : dist x y/r ≤ 1
  · have hA := weighted_radial_lipschitz r R (2*R) (2/σ) 2 hr hR le_rfl
      (by positivity) (by norm_num) (bumpA σ R)
      (fun u hu => bumpA_zero σ R u (by linarith) hu)
      (fun u v hu hv => bumpA_lipschitz σ R u v hσ hσ1 hR hu hv)
      z (fun s => 1+g s) hz.1 (fun s => ⟨by linarith [(hg s).1], by linarith [(hg s).2]⟩)
      x y (hz.2.1 x) hxy
    have hB := weighted_radial_lipschitz r R (2*σ) (1/σ) 1 hr hR (by linarith)
      (by positivity) (by norm_num) (bumpB σ)
      (fun u hu => bumpB_zero σ u hσ hu)
      (fun u v _ _ => by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using bumpB_lipschitz σ u v hσ)
      z (fun _ => 1) hz.1 (fun _ => ⟨by norm_num, le_rfl⟩) x y (hz.2.1 x) hxy
    simp only [mul_one, one_mul] at hB
    let bx := ∑ s, z s*bumpB σ (dist s x/r)
    let by' := ∑ s, z s*bumpB σ (dist s y/r)
    have hbx := weighted_bumpB_sum r σ R hσ hσ1 hR z hz x
    change bx ∈ Set.Icc (0:ℝ) 1 at hbx
    have hres : |(1+g x)*(1-bx)-(1+g y)*(1-by')| ≤ (L+2/σ)*(dist x y/r) := by
      have he : (1+g x)*(1-bx)-(1+g y)*(1-by') =
          (g x-g y)*(1-bx)+(1+g y)*(by'-bx) := by ring
      rw [he]
      calc
        _ ≤ |(g x-g y)*(1-bx)|+|(1+g y)*(by'-bx)| := abs_add_le _ _
        _ = |g x-g y| *(1-bx)+(1+g y)*|bx-by'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hbx.2] : 0 ≤ 1-bx),
            abs_of_nonneg (by linarith [(hg y).1] : 0 ≤ 1+g y), abs_sub_comm by' bx]
        _ ≤ L*(dist x y/r)*1+2*((1/σ)*(dist x y/r)) := by
          apply add_le_add
          · exact mul_le_mul (hgLip x y) (by linarith [hbx.1]) (by linarith [hbx.2]) (mul_nonneg hL hd)
          · exact mul_le_mul (by linarith [(hg y).2]) hB (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have he : integrand r σ R g z x-integrand r σ R g z y =
        ((1+g x)*(1-bx)-(1+g y)*(1-by')) +
          256*((∑ s, z s*(1+g s)*bumpA σ R (dist s x/r))-
            (∑ s, z s*(1+g s)*bumpA σ R (dist s y/r))) := by
      unfold integrand bx by'
      ring
    rw [he]
    calc
      _ ≤ |(1+g x)*(1-bx)-(1+g y)*(1-by')| +
          |256*((∑ s, z s*(1+g s)*bumpA σ R (dist s x/r))-
            (∑ s, z s*(1+g s)*bumpA σ R (dist s y/r)))| := abs_add_le _ _
      _ ≤ (L+2/σ)*(dist x y/r)+256*(2*(2/σ)*(dist x y/r)) := by
        apply add_le_add hres
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 256)]
        exact mul_le_mul_of_nonneg_left hA (by norm_num)
      _ = _ := by ring
  · have hx := integrand_bounds r σ R hr hσ hσ1 hR g z hg hz x
    have hy := integrand_bounds r σ R hr hσ hσ1 hR g z hg hz y
    have hb : |integrand r σ R g z x-integrand r σ R g z y| ≤ 514 :=
      abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
    have hc : 1026 ≤ 1026/σ := (le_div_iff₀ hσ).mpr (by nlinarith)
    exact hb.trans (by nlinarith)


/-- The geometric bound is valid for an arbitrary finite selection of scales. -/
theorem radius_sum_le (r τ : ℝ) (hr : 0 ≤ r) (hτ : 2 ≤ τ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), r*τ^j) ≤ 2*(r*τ^n) := by
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hn : 0 ≤ r*τ^n := mul_nonneg hr (pow_nonneg (by linarith) n)
    have hmul := mul_le_mul_of_nonneg_left hτ hn
    nlinarith

theorem radius_subsum_le (r τ b : ℝ) (hr : 0 ≤ r) (hτ : 2 ≤ τ)
    (hb : 0 ≤ b) (s : Finset ℕ) (hs : ∀ j ∈ s, r*τ^j ≤ b) :
    (∑ j ∈ s, r*τ^j) ≤ 2*b := by
  classical
  by_cases hn : s.Nonempty
  · let m := s.max' hn
    have hm : m ∈ s := Finset.max'_mem s hn
    have hsub : s ⊆ Finset.range (m+1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s j hj))
    calc
      _ ≤ ∑ j ∈ Finset.range (m+1), r*τ^j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
      _ ≤ 2*(r*τ^m) := radius_sum_le r τ hr hτ m
      _ ≤ 2*b := by linarith [hs m hm]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty]
    positivity

/-- Domination by the old measure turns the mover's first moment into an
inner-ball mass lower bound, without a cardinality or aspect-ratio loss. -/
theorem inner_mass_half (r γ : ℝ) (hr : 0 < r) (hγ : 0 < γ)
    (μ ν : X → ℝ) (_hμ : ∀ y, 0 ≤ μ y) (hν : ∀ y, 0 ≤ ν y)
    (hν1 : ∑ y, ν y = 1) (hνμ : ∀ y, ν y ≤ μ y) (x : X)
    (he : 2*(∑ y, ν y*dist x y) ≤ γ*r) :
    1/2 ≤ ballMass r γ μ x := by
  have hp : 0 < γ*r := mul_pos hγ hr
  have hy : ∀ y, (γ*r)*ν y ≤ (γ*r)*(if dist x y ≤ γ*r then μ y else 0)+ν y*dist x y := by
    intro y
    by_cases hd : dist x y ≤ γ*r
    · rw [ite_eq_left hd]
      have hm := mul_le_mul_of_nonneg_left (hνμ y) hp.le
      have hn : 0 ≤ ν y*dist x y := mul_nonneg (hν y) dist_nonneg
      linarith
    · rw [ite_eq_right hd, mul_zero, zero_add]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge hd) (hν y)]
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset X)) => hy y)
  rw [←Finset.mul_sum, hν1, mul_one, Finset.sum_add_distrib, ←Finset.mul_sum] at hsum
  change γ*r ≤ (γ*r)*ballMass r γ μ x + ∑ y, ν y*dist x y at hsum
  nlinarith

theorem drift_nonneg_bound [DecidableEq X] (r σ R : ℝ) (hr : 0 < r)
    (μ ν g z : X → ℝ) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    (x : X) (hz : feasible r σ R z) (hmin : objective r σ R μ g z = value r σ R μ g) :
    max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g-value r σ R μ g) 0 ≤
      r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 := by
  exact max_le (candidate_drift r σ R hr μ ν g hν hν1 x z hz hmin)
    (mul_nonneg hr.le (Finset.sum_nonneg fun y _ => mul_nonneg (hν y) (le_max_right _ _)))

theorem drift_bounded [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (μ ν g : X → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (x : X)
    (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1) :
    max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g-value r σ R μ g) 0 ≤ 514*r := by
  obtain ⟨z, hz, hmin, _⟩ := minimum_exists r σ R μ g
  calc
    _ ≤ r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 :=
      drift_nonneg_bound r σ R hr μ ν g z hν hν1 x hz hmin
    _ ≤ r*∑ y, ν y*514 := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hν y)
      apply max_le _ (by norm_num)
      linarith [(integrand_bounds r σ R hr hσ hσ1 hR g z hg hz x).2,
        (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz y).1]
    _ = _ := by rw [←Finset.sum_mul,hν1]; ring

theorem drift_lipschitz [DecidableEq X] (r σ R L : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L) (μ ν g : X → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (x : X)
    (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ y z, |g y-g z| ≤ L*(dist y z/r)) :
    max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g-value r σ R μ g) 0 ≤
      (L+1026/σ)*(∑ y, ν y*dist x y) := by
  obtain ⟨z, hz, hmin, _⟩ := minimum_exists r σ R μ g
  calc
    _ ≤ r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 :=
      drift_nonneg_bound r σ R hr μ ν g z hν hν1 x hz hmin
    _ ≤ r*∑ y, ν y*((L+1026/σ)*(dist x y/r)) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hν y)
      exact (max_le (le_abs_self _) (abs_nonneg _)).trans
        (integrand_global_lipschitz r σ R L hr hσ hσ1 hR hL g z hg hgLip hz x y)
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      field_simp


end
end UniformKServer.PilotCompact


end OAI
