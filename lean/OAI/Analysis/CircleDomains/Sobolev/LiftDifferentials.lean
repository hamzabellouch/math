import OAI.Analysis.CircleDomains.Topology.CircleLifts
import OAI.Analysis.CircleDomains.Modulus.ActualWedgeCost

namespace OAI

/-!
# Independence of differentials from the chosen real lift

Two continuous real lifts of one circle map differ locally by a fixed
integer. Their differentials, and those of the actual reciprocal-grid
cutoff modifications, therefore agree. These are local consequences of
the real quotient, with no additional published input.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem eventually_lifts_differ_by_integer
    {X : Type*} [TopologicalSpace X] {u v : X → ℝ} {x : X}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (v y : UnitAddCircle)) :
    ∃ m : ℤ, ∀ᶠ y in 𝓝 x, u y = v y + (m : ℝ) := by
  obtain ⟨m, hm⟩ := (addCircle_eq_iff_exists_int 1 (u x) (v x)).mp hproj.self_of_nhds
  have hnear : ∀ᶠ y in 𝓝 x, u y - v y ∈ ball (u x - v x) 1 :=
    (hu.sub hv).eventually (ball_mem_nhds _ zero_lt_one)
  refine ⟨m, ?_⟩
  filter_upwards [hproj, hnear] with y hy hdist
  obtain ⟨n, hn⟩ := (addCircle_eq_iff_exists_int 1 (u y) (v y)).mp hy
  have hmx : u x - v x = (m : ℝ) := by linarith [hm]
  have hny : u y - v y = (n : ℝ) := by linarith [hn]
  have habs : |(n : ℝ) - (m : ℝ)| < 1 := by
    simpa only [mem_ball, Real.dist_eq, hmx, hny] using hdist
  have hlo : (-1 : ℤ) < n - m := by exact_mod_cast (abs_lt.mp habs).1
  have hhi : n - m < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  have hnm : n = m := by omega
  subst n
  simpa only [mul_one] using hn

theorem fderiv_lifts_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {x : E} (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (v y : UnitAddCircle)) :
    fderiv ℝ u x = fderiv ℝ v x := by
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hu hv hproj
  have heq : u =ᶠ[𝓝 x] fun y => v y + (m : ℝ) := hm
  rw [heq.fderiv_eq (𝕜 := ℝ), fderiv_add_const]

theorem planarGradient_lifts_eq
    {u v : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ} (hu : ContinuousAt u z) (hv : ContinuousAt v z)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 z] fun y => (v y : UnitAddCircle)) :
    planarGradient u z = planarGradient v z := by
  simp only [planarGradient, fderiv_lifts_eq hu hv hproj]

theorem map_add_int_of_add_one {P : ℝ → ℝ} (hP : ∀ x, P (x + 1) = P x + 1)
    (x : ℝ) (m : ℤ) : P (x + (m : ℝ)) = P x + (m : ℝ) := by
  have hp : Periodic (fun x => P x - x) 1 := by
    intro y
    change P (y + 1) - (y + 1) = P y - y
    rw [hP]
    ring
  have hm := hp.int_mul m x
  simp only [mul_one] at hm
  linarith

theorem cutoffStaircase_add_int {X : Type*} (v χ : X → ℝ) {P : ℝ → ℝ}
    (hP : ∀ x, P (x + 1) = P x + 1) (m : ℤ) (x : X) :
    cutoffStaircase (fun y => v y + (m : ℝ)) χ P x = cutoffStaircase v χ P x + (m : ℝ) := by
  simp only [cutoffStaircase, map_add_int_of_add_one hP]
  ring

/-- Cutoff modification preserves the same local integer transition
between two lifts, not just equality of the projected circle maps. -/
theorem eventually_cutoff_lifts_differ_by_integer
    {X : Type*} [TopologicalSpace X] {u v : X → ℝ} {x : X}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (v y : UnitAddCircle))
    (χ : X → ℝ) {P : ℝ → ℝ} (hP : ∀ r, P (r + 1) = P r + 1) :
    ∃ m : ℤ, cutoffStaircase u χ P =ᶠ[𝓝 x] fun y => cutoffStaircase v χ P y + (m : ℝ) := by
  obtain ⟨m, hm⟩ := eventually_lifts_differ_by_integer hu hv hproj
  refine ⟨m, hm.mono fun y hy => ?_⟩
  simp only [cutoffStaircase, hy, map_add_int_of_add_one hP]
  ring

theorem fderiv_cutoff_lifts_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → ℝ} {x : E} (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 x] fun y => (v y : UnitAddCircle))
    (χ : E → ℝ) {P : ℝ → ℝ} (hP : ∀ r, P (r + 1) = P r + 1) :
    fderiv ℝ (cutoffStaircase u χ P) x = fderiv ℝ (cutoffStaircase v χ P) x := by
  obtain ⟨m, hm⟩ := eventually_cutoff_lifts_differ_by_integer hu hv hproj χ hP
  rw [hm.fderiv_eq (𝕜 := ℝ), fderiv_add_const]

/-- The actual selected staircase therefore defines one differential
independently of all choices of continuous real branch. -/
theorem planarGradient_reciprocal_cutoff_lifts_eq
    {u v : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ} (hu : ContinuousAt u z) (hv : ContinuousAt v z)
    (hproj : (fun y => (u y : UnitAddCircle)) =ᶠ[𝓝 z] fun y => (v y : UnitAddCircle))
    (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (δ θ : ℝ) :
    planarGradient (cutoffStaircase u χ (shiftedStaircase (reciprocalGridStep N) δ θ)) z =
      planarGradient (cutoffStaircase v χ (shiftedStaircase (reciprocalGridStep N) δ θ)) z := by
  have hP (x : ℝ) : shiftedStaircase (reciprocalGridStep N) δ θ (x + 1) =
      shiftedStaircase (reciprocalGridStep N) δ θ x + 1 := by
    simpa only [reciprocalGridStep, Nat.cast_succ] using
      shiftedStaircase_add_one (Nat.succ_pos N) δ θ x
  simp only [planarGradient, fderiv_cutoff_lifts_eq hu hv hproj χ hP]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
