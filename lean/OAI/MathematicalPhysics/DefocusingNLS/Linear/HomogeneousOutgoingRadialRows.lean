import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingComparison

namespace OAI

/-! # The logarithmic derivative-row estimate in physical radius -/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

private theorem scalar_iterated_smooth (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) (Ioi 0) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

theorem homogeneousPair_iteratedDeriv (f g : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) (hg : ContDiffOn ℝ ∞ g (Ioi 0))
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    iteratedDeriv n (fun s => (f s, g s)) r = (iteratedDeriv n f r, iteratedDeriv n g r) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
      have he : iteratedDeriv n (fun s => (f s, g s)) =ᶠ[𝓝 r]
          (fun s => (iteratedDeriv n f s, iteratedDeriv n g s)) :=
        Filter.mem_of_superset (Ioi_mem_nhds hr) (fun s hs => ih s hs)
      have hfs := scalar_iterated_smooth f hf n
      have hgs := scalar_iterated_smooth g hg n
      have hfd := ((hfs r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hgd := ((hgs r hr).contDiffAt (Ioi_mem_nhds hr)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      rw [iteratedDeriv_succ, he.deriv_eq]
      simpa only [iteratedDeriv_succ] using (hfd.hasDerivAt.prodMk hgd.hasDerivAt).deriv

theorem homogeneousOutgoingRows_physical_comparison
    (U W : ℝ → V) (T R : ℝ → End) (n : ℕ) (c K M : ℝ)
    (hU : ContDiffOn ℝ ∞ U (Ioi 0)) (hc : 0 < c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hbound : ∀ r, ‖U r‖ ≤ M)
    (hrow : ∀ᶠ t in atTop, ∀ w : V,
      c * Real.exp (2 * (n : ℝ) * t) * ‖w‖ ≤ ‖T t w‖)
    (hR : ∀ᶠ t in atTop, ‖R t‖ ≤ K)
    (hid : ∀ᶠ t in atTop,
      homogeneousEulerDeriv (fun s => U (Real.exp s)) (n + 1) t =
        T t (Real.exp t • W (Real.exp t)) + R t (U (Real.exp t))) :
    ∀ᶠ r in atTop, r ^ (2 * (n : ℝ)) * homogeneousPairEnergy (W r) ≤
      (4 / c ^ 2) * homogeneousPairEnergy (iteratedDeriv (n + 1) U r) +
        (4 / c ^ 2) * (K * M) ^ 2 * r ^ (-2 * ((n + 1 : ℕ) : ℝ)) := by
  have hall := hrow.and (hR.and hid)
  have hlog := Real.tendsto_log_atTop.eventually hall
  filter_upwards [hlog, eventually_gt_atTop (0 : ℝ)] with r h hr
  have he2 : Real.exp (2 * (n : ℝ) * Real.log r) = r ^ (2 * n) := by
    rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hr]
  have heN : Real.exp (((n + 1 : ℕ) : ℝ) * Real.log r) = r ^ (n + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hr]
  have hident := h.2.2
  rw [homogeneousEulerDeriv_physical U hU, heN, Real.exp_log hr] at hident
  apply homogeneousLogRow_energy_comparison (U r) (W r)
    (iteratedDeriv (n + 1) U r) (T (Real.log r)) (R (Real.log r))
    r c K M n hr hc hK hM
  · simpa only [he2, Real.exp_log hr] using h.1 (r • W r)
  · exact hident
  · exact h.2.1
  · exact hbound r

end DefocusingNLS

end OAI
