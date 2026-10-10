import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import OAI.Analysis.CircleDomains.Selection.ShiftedStaircase
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

/-!
# Selecting finite terminal neighborhoods with simultaneous band control

Section 2, Step 2 of the Koebe manuscript first fixes finitely many
terminal points and then chooses their neighborhoods, before choosing
the staircase width. Here positive-radius metric balls are selected
inside prescribed neighborhoods with pairwise disjoint closed balls.
Their physical coordinate values lie in the boundary bands enlarged
by `h`; hence all shifted staircases have oscillation at most `a + 4h`
there, simultaneously for every staircase width.

For the complex plane these selected balls are actual round disks.
On a general quotient metric sphere they are only metric neighborhoods:
the separate smooth-contour construction is still needed to obtain
physical smooth Jordan boundaries around non-point fibers.
-/

open Set Filter Metric Function
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

/-- Finitely many distinct points have disjoint closed-ball
neighborhoods inside arbitrary prescribed neighborhoods, with any
prescribed positive upper bounds for their radii. -/
theorem exists_disjoint_closedBalls_in_neighborhoods
    {X I : Type*} [MetricSpace X] [Fintype I]
    (p : I → X) (hp : Injective p) (O : I → Set X)
    (hO : ∀ i, O i ∈ 𝓝 (p i)) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < ρ i) ∧
      (∀ i, closedBall (p i) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => closedBall (p i) (r i)) := by
  classical
  have hdisj : Pairwise (Disjoint on fun i => ({p i} : Set X)) := by
    intro i j hij
    exact disjoint_singleton.mpr (fun h => hij (hp h))
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ ({p i} : Set X)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_singleton isClosed_singleton (hdisj hij)
  obtain ⟨V, hV, hVd⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet ({p i} : Set X))
  have hlocal (i : I) : V i ∩ O i ∈ 𝓝 (p i) :=
    inter_mem ((hV i).1.mem_nhds ((hV i).2 (mem_singleton _))) (hO i)
  have hball (i : I) : ∃ R : ℝ, 0 < R ∧ closedBall (p i) R ⊆ V i ∩ O i :=
    nhds_basis_closedBall.mem_iff.mp (hlocal i)
  choose R hR hRV using hball
  let r : I → ℝ := fun i => min (R i / 2) (ρ i / 2)
  have hr (i : I) : 0 < r i ∧ r i < ρ i := by
    dsimp [r]
    exact ⟨lt_min (half_pos (hR i)) (half_pos (hρ i)),
      (min_le_right _ _).trans_lt (by linarith [hρ i])⟩
  have hsub (i : I) : closedBall (p i) (r i) ⊆ V i ∩ O i := by
    apply (closedBall_subset_closedBall ?_).trans (hRV i)
    exact (min_le_left _ _).trans (by linarith [hR i])
  refine ⟨r, hr, fun i x hx => (hsub i hx).2, ?_⟩
  intro i j hij
  exact (hVd hij).mono (fun _ hx => (hsub i hx).1) (fun _ hx => (hsub j hx).1)

/-- The values near a boundary point lie in its actual liminf/limsup
band enlarged by any positive margin. -/
theorem eventually_mem_enlarged_boundary_band
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ} {M : ℝ}
    (hM : ∀ y ∈ G, |f y| ≤ M) (x : X) {h : ℝ} (hh : 0 < h) :
    ∀ᶠ y in 𝓝[G] x,
      liminf f (𝓝[G] x) - h < f y ∧ f y < limsup f (𝓝[G] x) + h := by
  have hb : ∀ᶠ y in 𝓝[G] x, -M ≤ f y ∧ f y ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact abs_le.mp (hM y hy)
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_ge (hb.mono (fun _ hy => hy.1))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_le (hb.mono (fun _ hy => hy.2))
  exact (eventually_lt_of_lt_liminf (by linarith) hlo).and
    (eventually_lt_of_limsup_lt (by linarith) hhi)

/-- Actual finite-radius selection, with all nonsingular coordinate
band bounds imposed at once. `active i j` specifies which coordinates
need a real branch at terminal point `i`; the physical domain and branch
may depend on that terminal point, as for periodic coordinates. -/
theorem exists_terminal_balls_with_band_control
    {X I J : Type*} [MetricSpace X] [Fintype I] [Fintype J]
    (p : I → X) (hp : Injective p) (O : I → Set X)
    (hO : ∀ i, O i ∈ 𝓝 (p i)) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i)
    (G : I → Set X) (f : I → J → X → ℝ) (M : I → J → ℝ)
    (hM : ∀ i j y, y ∈ G i → |f i j y| ≤ M i j)
    (active : I → J → Prop) {h : ℝ} (hh : 0 < h) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < ρ i) ∧
      (∀ i, closedBall (p i) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => closedBall (p i) (r i)) ∧
      ∀ i j, active i j → ∀ y ∈ closedBall (p i) (r i) ∩ G i,
        liminf (f i j) (𝓝[G i] (p i)) - h < f i j y ∧
          f i j y < limsup (f i j) (𝓝[G i] (p i)) + h := by
  let Q : I → Set X := fun i => {y | y ∈ G i → ∀ j, active i j →
    liminf (f i j) (𝓝[G i] (p i)) - h < f i j y ∧
      f i j y < limsup (f i j) (𝓝[G i] (p i)) + h}
  have hQ (i : I) : Q i ∈ 𝓝 (p i) := by
    apply eventually_nhdsWithin_iff.mp
    apply eventually_all.mpr
    intro j
    exact (eventually_mem_enlarged_boundary_band (hM i j) (p i) hh).mono
      (fun _ hy _ => hy)
  obtain ⟨r, hr, hsub, hdisj⟩ := exists_disjoint_closedBalls_in_neighborhoods
    p hp (fun i => O i ∩ Q i) (fun i => inter_mem (hO i) (hQ i)) ρ hρ
  refine ⟨r, hr, fun i y hy => (hsub i hy).1, hdisj, ?_⟩
  intro i j hj y hy
  exact (hsub i hy.1).2 hy.2 j hj

/-- Enlarging the coordinate band by `h` at each end gives oscillation
at most its band budget plus `2h`. -/
theorem abs_sub_le_of_enlarged_boundary_band
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ}
    {s x y : X} {a h : ℝ}
    (hband : limsup f (𝓝[G] s) - liminf f (𝓝[G] s) ≤ a)
    (hx : liminf f (𝓝[G] s) - h < f x ∧ f x < limsup f (𝓝[G] s) + h)
    (hy : liminf f (𝓝[G] s) - h < f y ∧ f y < limsup f (𝓝[G] s) + h) :
    |f x - f y| ≤ a + 2 * h := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- The terminal oscillation estimate is uniform in the staircase
width. Thus disk neighborhoods can be fixed before taking that width
to zero, exactly as required in Step 2. -/
theorem terminal_staircase_oscillation_le
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ}
    {s x y : X} {a h : ℝ} (hh : 0 < h)
    (hband : limsup f (𝓝[G] s) - liminf f (𝓝[G] s) ≤ a)
    (hx : liminf f (𝓝[G] s) - h < f x ∧ f x < limsup f (𝓝[G] s) + h)
    (hy : liminf f (𝓝[G] s) - h < f y ∧ f y < limsup f (𝓝[G] s) + h)
    (δ θ : ℝ) :
    |shiftedStaircase h δ θ (f x) - shiftedStaircase h δ θ (f y)| ≤ a + 4 * h := by
  have hu := abs_sub_le_of_enlarged_boundary_band hband hx hy
  have hpx := abs_shiftedStaircase_sub_le hh δ θ (f x)
  have hpy := abs_shiftedStaircase_sub_le hh δ θ (f y)
  rw [abs_le] at hu hpx hpy ⊢
  constructor <;> linarith [hu.1, hu.2, hpx.1, hpx.2, hpy.1, hpy.2]

/-- The radii are chosen once for all staircase widths and shifts.
Any subsequently constructed physical terminal contour lying in these
closed balls inherits the paper's `a + 4h` oscillation bound. -/
theorem exists_terminal_balls_with_uniform_staircase_oscillation
    {X I J : Type*} [MetricSpace X] [Fintype I] [Fintype J]
    (p : I → X) (hp : Injective p) (O : I → Set X)
    (hO : ∀ i, O i ∈ 𝓝 (p i)) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i)
    (G : I → Set X) (f : I → J → X → ℝ) (M : I → J → ℝ)
    (hM : ∀ i j y, y ∈ G i → |f i j y| ≤ M i j)
    (active : I → J → Prop) (a : I → J → ℝ)
    (hbudget : ∀ i j, active i j →
      limsup (f i j) (𝓝[G i] (p i)) - liminf (f i j) (𝓝[G i] (p i)) ≤ a i j)
    {h : ℝ} (hh : 0 < h) :
    ∃ r : I → ℝ, (∀ i, 0 < r i ∧ r i < ρ i) ∧
      (∀ i, closedBall (p i) (r i) ⊆ O i) ∧
      Pairwise (Disjoint on fun i => closedBall (p i) (r i)) ∧
      ∀ i j, active i j → ∀ δ θ : ℝ,
        ∀ x ∈ closedBall (p i) (r i) ∩ G i,
        ∀ y ∈ closedBall (p i) (r i) ∩ G i,
          |shiftedStaircase h δ θ (f i j x) - shiftedStaircase h δ θ (f i j y)| ≤
            a i j + 4 * h := by
  obtain ⟨r, hr, hsub, hdisj, hcontrol⟩ :=
    exists_terminal_balls_with_band_control p hp O hO ρ hρ G f M hM active hh
  refine ⟨r, hr, hsub, hdisj, ?_⟩
  intro i j hj δ θ x hx y hy
  exact terminal_staircase_oscillation_le hh (hbudget i j hj)
    (hcontrol i j hj x hx) (hcontrol i j hj y hy) δ θ

end CircleDomainRigidity.FiniteTransfer

end OAI
