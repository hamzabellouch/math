import OAI.Analysis.CircleDomains.Transfer.RankOneFilling

namespace OAI

/-!
# Patching the finite family of filling disks

On pairwise disjoint open disks, replace the old coordinate by its
smooth collar extension. Equality on full boundary neighborhoods gives
smoothness across every boundary, and local equality preserves the
rank-one wedge condition inside each filling disk.
-/

open Set Filter Function
open scoped Topology ContDiff

namespace CircleDomainRigidity.FiniteTransfer

noncomputable def patchOpenRegions {X Y I : Type*}
    (D : I → Set X) (g : I → X → Y) (f : X → Y) (x : X) : Y := by
  classical
  exact if h : ∃ i, x ∈ D i then g (Classical.choose h) x else f x

theorem patchOpenRegions_eq_of_mem {X Y I : Type*}
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    (hd : Pairwise (Disjoint on D)) {i : I} {x : X} (hx : x ∈ D i) :
    patchOpenRegions D g f x = g i x := by
  classical
  have he : ∃ j, x ∈ D j := ⟨i, hx⟩
  have hi : Classical.choose he = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (Classical.choose_spec he) hx
  simp only [patchOpenRegions, dite_eq_left he, hi]

theorem patchOpenRegions_eq_of_notMem {X Y I : Type*}
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    {x : X} (hx : ∀ i, x ∉ D i) : patchOpenRegions D g f x = f x := by
  simp only [patchOpenRegions, dite_eq_right (not_exists.mpr hx)]

theorem patchOpenRegions_eventuallyEq_inside {X Y I : Type*} [TopologicalSpace X]
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    (hD : ∀ i, IsOpen (D i)) (hd : Pairwise (Disjoint on D))
    {i : I} {x : X} (hx : x ∈ D i) :
    patchOpenRegions D g f =ᶠ[𝓝 x] g i := by
  filter_upwards [(hD i).mem_nhds hx] with y hy
  exact patchOpenRegions_eq_of_mem D g f hd hy

/-- Finiteness permits simultaneous agreement near a point lying
outside all filling interiors, including a point on their boundaries. -/
theorem patchOpenRegions_eventuallyEq_outside
    {X Y I : Type*} [TopologicalSpace X] [Fintype I]
    (D : I → Set X) (g : I → X → Y) (f : X → Y)
    (hD : ∀ i, IsOpen (D i)) {x : X} (hx : ∀ i, x ∉ D i)
    (hagree : ∀ i, x ∈ frontier (D i) → g i =ᶠ[𝓝 x] f) :
    patchOpenRegions D g f =ᶠ[𝓝 x] f := by
  have hlocal i : ∀ᶠ y in 𝓝 x, y ∈ D i → g i y = f y := by
    by_cases hc : x ∈ closure (D i)
    · have hb : x ∈ frontier (D i) := by
        rw [(hD i).frontier_eq]
        exact ⟨hc, hx i⟩
      exact (hagree i hb).mono (fun _ hy _ => hy)
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy hmem
      exact (hy (subset_closure hmem)).elim
  filter_upwards [eventually_all.mpr hlocal] with y hy
  by_cases hm : ∃ i, y ∈ D i
  · simp only [patchOpenRegions, dite_eq_left hm]
    exact hy (Classical.choose hm) (Classical.choose_spec hm)
  · exact patchOpenRegions_eq_of_notMem D g f (not_exists.mp hm)

/-- Smoothness follows from smoothness of the old coordinate off the
filling interiors and of each replacement inside its own disk. -/
theorem contDiffOn_patchOpenRegions
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (D : I → Set E) (g : I → E → ℝ) (f : E → ℝ)
    (hD : ∀ i, IsOpen (D i)) (hd : Pairwise (Disjoint on D))
    {U : Set E}
    (hf : ∀ x ∈ U, (∀ i, x ∉ D i) → ContDiffAt ℝ ∞ f x)
    (hg : ∀ i, ∀ x ∈ U ∩ D i, ContDiffAt ℝ ∞ (g i) x)
    (hagree : ∀ i, ∀ x ∈ U ∩ frontier (D i), g i =ᶠ[𝓝 x] f) :
    ContDiffOn ℝ ∞ (patchOpenRegions D g f) U := by
  intro x hx
  by_cases hm : ∃ i, x ∈ D i
  · obtain ⟨i, hi⟩ := hm
    exact ((hg i x ⟨hx, hi⟩).congr_of_eventuallyEq
      (patchOpenRegions_eventuallyEq_inside D g f hD hd hi)).contDiffWithinAt
  · have hn := not_exists.mp hm
    exact ((hf x hx hn).congr_of_eventuallyEq
      (patchOpenRegions_eventuallyEq_outside D g f hD hn
        (fun i hi => hagree i x ⟨hx, hi⟩))).contDiffWithinAt

/-- The patched family inherits each filling's pointwise zero wedges.
The conclusion concerns actual derivatives of the patched functions. -/
theorem patchOpenRegions_wedges_eq_zero_inside
    {I L : Type*} (D : I → Set (ℝ × ℝ)) (g : I → L → (ℝ × ℝ) → ℝ)
    (f : L → (ℝ × ℝ) → ℝ) (hD : ∀ i, IsOpen (D i))
    (hd : Pairwise (Disjoint on D))
    (hzero : ∀ i j k, j ≠ k → ∀ x ∈ D i,
      planarWedge (planarGradient (g i j) x) (planarGradient (g i k) x) = 0)
    {i : I} {x : ℝ × ℝ} (hx : x ∈ D i) (j k : L) (hjk : j ≠ k) :
    planarWedge
      (planarGradient (patchOpenRegions D (fun i => g i j) (f j)) x)
      (planarGradient (patchOpenRegions D (fun i => g i k) (f k)) x) = 0 := by
  have heq l := (patchOpenRegions_eventuallyEq_inside D (fun i => g i l) (f l) hD hd hx).fderiv_eq
    (𝕜 := ℝ)
  simp only [planarGradient, heq]
  exact hzero i j k hjk x hx

end CircleDomainRigidity.FiniteTransfer

end OAI
