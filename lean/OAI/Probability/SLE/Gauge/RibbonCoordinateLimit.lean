import OAI.Probability.SLE.Gauge.RibbonCoordinateCompactness

namespace OAI

/-! Strict half-plane location and actual moving ribbon regions for the
compact coordinate limits. The middle region has the manuscript's fixed
longitudinal interval `(1/3,2/3)` and transverse width. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

/-- An open planar set in the closed upper half-plane cannot meet its
boundary line. -/
theorem open_nonnegative_height_subset_upperHalfPlane
    (U : Set ℂ) (hU : IsOpen U) (hheight : ∀ z ∈ U, 0 ≤ z.im) :
    U ⊆ upperHalfPlane := by
  intro z hz
  by_contra hn
  have hz0 : z.im = 0 := le_antisymm (le_of_not_gt hn) (hheight z hz)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  let w : ℂ := z - ((ε / 2 : ℝ) : ℂ) * Complex.I
  have hwsub : w - z = -(((ε / 2 : ℝ) : ℂ) * Complex.I) := by dsimp [w]; ring
  have hdist : dist w z = ε / 2 := by
    rw [dist_eq_norm, hwsub, norm_neg, norm_mul, Complex.norm_I, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  have hw : w ∈ U := hball (by rw [mem_ball, hdist]; linarith)
  have him : w.im = z.im - ε / 2 := by simp [w]
  have hh := hheight w hw
  rw [him, hz0] at hh
  linarith

/-- Uniform limits of admissible embedded ribbon patches still have
strictly positive height at every interior coordinate point. -/
theorem uniform_limit_interior_upperHalfPlane
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K : Set ℂ)
    (hP : ContinuousOn P K) (hi : InjOn P K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hheight : ∀ n z, z ∈ K → 0 ≤ (Pₙ n z).im) :
    MapsTo P (interior K) upperHalfPlane := by
  have hopen := isOpen_image_interior hpublished P K hP hi
  have hnonneg : ∀ z ∈ P '' interior K, 0 ≤ z.im := by
    rintro _ ⟨x, hx, rfl⟩
    exact ge_of_tendsto ((Complex.continuous_im.tendsto _).comp
      (hconv.tendsto_at (interior_subset hx)))
      (Eventually.of_forall (fun n => hheight n x (interior_subset hx)))
  intro x hx
  exact open_nonnegative_height_subset_upperHalfPlane _ hopen hnonneg
    (mem_image_of_mem P hx)

/-- The compactness output needed for a local ribbon patch includes
strict limiting height, without a separate positivity assumption. -/
theorem exists_bilip_halfPlane_subsequence
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ K) (C L : ℝ≥0) (R : ℝ)
    (hupper : ∀ n, LipschitzOnWith C (Pₙ n) K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (htip : ∀ n, ‖Pₙ n x₀‖ ≤ R)
    (hheight : ∀ n z, z ∈ K → 0 ≤ (Pₙ n z).im) :
    ∃ P : ℂ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => Pₙ (φ n)) P atTop K ∧
      LipschitzOnWith C P K ∧
      (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y)) ∧
      InjOn P K ∧ MapsTo P (interior K) upperHalfPlane := by
  obtain ⟨P, φ, hφ, hconv, hPu, hPl, hi⟩ :=
    exists_bilip_uniform_subsequence Pₙ K hK x₀ hx₀ C L R hupper hlower htip
  exact ⟨P, φ, hφ, hconv, hPu, hPl, hi,
    uniform_limit_interior_upperHalfPlane hpublished (fun n => Pₙ (φ n)) P K
      hPu.continuousOn hi hconv (fun n => hheight (φ n))⟩

/-- The actual physical middle strip in the source's local coordinates. -/
def physicalMiddleRegion (P : ℂ → ℂ) (K : Set ℂ) (k ε : ℝ) : Set ℂ :=
  P '' {w ∈ K | (1 / 3 : ℝ) < w.re - k ∧ w.re - k < 2 / 3 ∧ |w.im| < ε}

/-- Strict transverse margin on a compact common physical patch implies
that its moving longitudinal band is in the actual moving middle strip. -/
theorem eventual_middle_region_inclusion
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K U : Set ℂ) (L : ℝ≥0) (k ε : ℝ)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hU : IsCompact (closure U)) (hUP : closure U ⊆ P '' K)
    (hcover : ∀ᶠ n in atTop, closure U ⊆ Pₙ n '' K)
    (hwidth : ∀ z ∈ closure U, |(coordinateInverse P K z).im| < ε) :
    ∀ᶠ n in atTop,
      U ∩ {z | (1 / 3 : ℝ) < longitudinalCoordinate (Pₙ n) K k z ∧
        longitudinalCoordinate (Pₙ n) K k z < 2 / 3} ⊆
      physicalMiddleRegion (Pₙ n) K k ε := by
  have hopen : IsOpen {w : ℂ | |w.im| < ε} := isOpen_lt Complex.continuous_im.abs continuous_const
  have hcoord := eventual_compact_coordinate_region Pₙ P K (closure U)
    {w : ℂ | |w.im| < ε} L hconv hlower hU hUP hcover hopen
    (by rintro _ ⟨z, hz, rfl⟩; exact hwidth z hz)
  filter_upwards [hcoord] with n hn
  rintro z ⟨hz, hband⟩
  obtain ⟨x, hx, he⟩ := hn (subset_closure hz)
  have hi := lower_lipschitz_injOn (Pₙ n) K L (hlower n)
  have heq : coordinateInverse (Pₙ n) K z = x := by
    rw [← he]
    exact coordinateInverse_left hi hx.1
  refine ⟨x, ⟨hx.1, ?_, ?_, hx.2⟩, he⟩
  · simpa only [longitudinalCoordinate, heq] using hband.1
  · simpa only [longitudinalCoordinate, heq] using hband.2

/-- Physical terminal control with the inverse patch constant gives the
source's transverse coordinate bound at the attained front. -/
theorem source_terminal_offset
    (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0) (k ε : ℝ) (z : ℂ)
    (hL : 0 < L)
    (hlower : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y))
    (hbase : ((k + 1 : ℝ) : ℂ) ∈ K) (hz : z ∈ P '' K)
    (hp : longitudinalCoordinate P K k z = 1)
    (hd : dist z (P ((k + 1 : ℝ) : ℂ)) < ε / (4 * (L : ℝ))) :
    (coordinateInverse P K z).re = k + 1 ∧
      |(coordinateInverse P K z).im| < ε / 4 := by
  constructor
  · dsimp [longitudinalCoordinate] at hp
    linarith
  · have hh := hlower _ (coordinateInverse_mem hz) _ hbase
    rw [coordinateInverse_right hz] at hh
    have him : |(coordinateInverse P K z).im| ≤
        dist (coordinateInverse P K z) ((k + 1 : ℝ) : ℂ) := by
      simpa only [dist_eq_norm, Complex.sub_im, Complex.ofReal_im, sub_zero]
        using Complex.abs_im_le_norm (coordinateInverse P K z - ((k + 1 : ℝ) : ℂ))
    have hLr : 0 < (L : ℝ) := hL
    have hden : 0 < 4 * (L : ℝ) := by positivity
    have hd' := (lt_div_iff₀ hden).mp hd
    have he : (L : ℝ) * dist z (P ((k + 1 : ℝ) : ℂ)) < ε / 4 := by
      linarith
    exact (him.trans hh).trans_lt he

end SLEExactGauge.RibbonCoordinates

end

end OAI
