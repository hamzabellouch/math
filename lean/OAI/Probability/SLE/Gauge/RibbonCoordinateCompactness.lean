import OAI.Probability.SLE.Gauge.RibbonCoordinateGeometry
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

namespace OAI

/-! Common physical domains and convergence of inverse ribbon coordinates
on a fixed compact coordinate patch. The uniform lower Lipschitz bound
controls the inverse without requiring derivative convergence. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal BoundedContinuousFunction

namespace SLEExactGauge.RibbonCoordinates

def coordinateInverse (P : ℂ → ℂ) (K : Set ℂ) : ℂ → ℂ := Function.invFunOn P K

theorem coordinateInverse_mem {P : ℂ → ℂ} {K : Set ℂ} {z : ℂ}
    (hz : z ∈ P '' K) : coordinateInverse P K z ∈ K :=
  Function.invFunOn_mem hz

theorem coordinateInverse_right {P : ℂ → ℂ} {K : Set ℂ} {z : ℂ}
    (hz : z ∈ P '' K) : P (coordinateInverse P K z) = z :=
  Function.invFunOn_eq hz

theorem coordinateInverse_left {P : ℂ → ℂ} {K : Set ℂ}
    (hi : InjOn P K) {z : ℂ} (hz : z ∈ K) :
    coordinateInverse P K (P z) = z :=
  hi.leftInvOn_invFunOn hz

/-- Physical coordinate regions agree with inverse-coordinate membership. -/
theorem coordinate_image_region_iff {P : ℂ → ℂ} {K A : Set ℂ}
    (hi : InjOn P K) (hA : A ⊆ K) {z : ℂ} :
    z ∈ P '' A ↔ z ∈ P '' K ∧ coordinateInverse P K z ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨mem_image_of_mem P (hA hx), by simpa only [coordinateInverse_left hi (hA hx)] using hx⟩
  · rintro ⟨hz, hAq⟩
    exact ⟨coordinateInverse P K z, hAq, coordinateInverse_right hz⟩

theorem coordinateInverse_lipschitz
    (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0)
    (hlower : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y)) :
    LipschitzOnWith L (coordinateInverse P K) (P '' K) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  have hh := hlower _ (coordinateInverse_mem hx) _ (coordinateInverse_mem hy)
  simpa only [coordinateInverse_right hx, coordinateInverse_right hy] using hh

theorem lower_lipschitz_uniform_limit
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y)) :
    ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y) := by
  intro x hx y hy
  exact ge_of_tendsto (tendsto_const_nhds.mul ((hconv.tendsto_at hx).dist (hconv.tendsto_at hy)))
    (Eventually.of_forall fun n => hlower n x hx y hy)

/-- Common image containment converts uniform forward convergence into
uniform inverse convergence on any retained physical set. -/
theorem coordinateInverse_uniform_on
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K S : Set ℂ) (L : ℝ≥0)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hSP : S ⊆ P '' K) (hcover : ∀ᶠ n in atTop, S ⊆ Pₙ n '' K) :
    TendstoUniformlyOn (fun n => coordinateInverse (Pₙ n) K) (coordinateInverse P K) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hη : 0 < ε / ((L : ℝ) + 1) := div_pos hε hL
  filter_upwards [hcover, Metric.tendstoUniformlyOn_iff.mp hconv _ hη] with n hn hclose
  intro z hz
  have hq : coordinateInverse P K z ∈ K := coordinateInverse_mem (hSP hz)
  have hqn : coordinateInverse (Pₙ n) K z ∈ K := coordinateInverse_mem (hn hz)
  have he := hlower n _ hqn _ hq
  rw [coordinateInverse_right (hn hz)] at he
  have hd := hclose _ hq
  rw [coordinateInverse_right (hSP hz)] at hd
  have he' : dist (coordinateInverse P K z) (coordinateInverse (Pₙ n) K z) ≤
      (L : ℝ) * dist z (Pₙ n (coordinateInverse P K z)) := by
    simpa only [dist_comm] using he
  calc
    _ ≤ (L : ℝ) * dist z (Pₙ n (coordinateInverse P K z)) := he'
    _ ≤ ((L : ℝ) + 1) * dist z (Pₙ n (coordinateInverse P K z)) :=
      mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) := mul_lt_mul_of_pos_left hd hL
    _ = ε := mul_div_cancel₀ ε hL.ne'

/-- The uniform inverse bound makes every coordinate chart injective. -/
theorem lower_lipschitz_injOn
    (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0)
    (hlower : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y)) :
    InjOn P K := by
  intro x hx y hy he
  have hh := hlower x hx y hy
  rw [he, dist_self, mul_zero] at hh
  exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)

/-- The limiting coordinate image has an open interior physical domain. -/
theorem isOpen_image_interior
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (K : Set ℂ)
    (hP : ContinuousOn P K) (hi : InjOn P K) :
    IsOpen (P '' interior K) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hsub : ball x r ⊆ K := hball.trans interior_subset
  have hopen := hpublished P x r hr (hP.mono hsub) (hi.mono hsub)
  exact mem_of_superset
    (hopen.mem_nhds (mem_image_of_mem P (mem_ball_self hr)))
    (image_mono hball)

/-- Compact physical subsets of the limiting interior image belong to
all sufficiently late moving interior images. -/
theorem eventual_compact_image_interior
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K S : Set ℂ) (L : ℝ≥0)
    (hL : 0 < L)
    (hPn : ∀ n, ContinuousOn (Pₙ n) K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hS : IsCompact S) (hSP : S ⊆ P '' interior K) :
    ∀ᶠ n in atTop, S ⊆ Pₙ n '' interior K := by
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hi := lower_lipschitz_injOn P K L hlim
  have hSK : S ⊆ P '' K := hSP.trans (image_mono interior_subset)
  let Q := coordinateInverse P K '' S
  have hQ : IsCompact Q := hS.image_of_continuousOn
    ((coordinateInverse_lipschitz P K L hlim).continuousOn.mono hSK)
  have hQK : Q ⊆ interior K := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, he⟩ := hSP hz
    have hqx : coordinateInverse P K z = x := hi
      (coordinateInverse_mem (hSK hz)) (interior_subset hx)
      ((coordinateInverse_right (hSK hz)).trans he.symm)
    simpa only [hqx] using hx
  obtain ⟨ρ, hρ, hthick⟩ := hQ.exists_cthickening_subset_open isOpen_interior hQK
  have hLr : 0 < (L : ℝ) := hL
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (ρ / L) (div_pos hρ hLr)] with n hn
  intro z hz
  let x := coordinateInverse P K z
  have hxQ : x ∈ Q := mem_image_of_mem _ hz
  have hxK : x ∈ K := interior_subset (hQK hxQ)
  have hball : closedBall x ρ ⊆ interior K := by
    intro y hy
    exact hthick (mem_cthickening_of_dist_le y x ρ Q hxQ hy)
  have hballK := hball.trans interior_subset
  have hiₙ := lower_lipschitz_injOn (Pₙ n) K L (hlower n)
  have hopen := hpublished (Pₙ n) x ρ hρ
    ((hPn n).mono (ball_subset_closedBall.trans hballK))
    (hiₙ.mono (ball_subset_closedBall.trans hballK))
  have hcontains := ball_subset_image_ball (Pₙ n) x hρ hLr
    ((hPn n).mono hballK) hopen
    (fun y hy => hlower n y (hballK hy) x hxK)
  apply (image_mono (ball_subset_closedBall.trans hball))
  apply hcontains
  have hh := hn x hxK
  rw [coordinateInverse_right (hSK hz)] at hh
  simpa only [mem_ball, dist_comm] using hh

/-- The inverse ribbon charts converge locally uniformly on the full
limiting interior image. Only compact subsets are eventually common. -/
theorem coordinateInverse_locally_uniform
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0)
    (hL : 0 < L) (hP : ContinuousOn P K)
    (hPn : ∀ n, ContinuousOn (Pₙ n) K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y)) :
    TendstoLocallyUniformlyOn (fun n => coordinateInverse (Pₙ n) K)
      (coordinateInverse P K) atTop (P '' interior K) := by
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hopen := isOpen_image_interior hpublished P K hP
    (lower_lipschitz_injOn P K L hlim)
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hopen).mpr
  intro S hSP hS
  exact coordinateInverse_uniform_on Pₙ P K S L hconv hlower
    (hSP.trans (image_mono interior_subset))
    ((eventual_compact_image_interior hpublished Pₙ P K S L hL hPn hconv hlower hS hSP).mono
      (fun _ h => h.trans (image_mono interior_subset)))

/-- A compact retained physical patch admits one common open neighborhood
contained in every sufficiently late coordinate image. -/
theorem common_physical_neighborhood
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K A : Set ℂ) (L : ℝ≥0)
    (hL : 0 < L) (hP : ContinuousOn P K)
    (hPn : ∀ n, ContinuousOn (Pₙ n) K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hA : IsCompact A) (hAP : A ⊆ P '' interior K) :
    ∃ U : Set ℂ, IsOpen U ∧ A ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ P '' interior K ∧
      (∀ᶠ n in atTop, closure U ⊆ Pₙ n '' interior K) ∧
      TendstoUniformlyOn (fun n => coordinateInverse (Pₙ n) K)
        (coordinateInverse P K) atTop (closure U) := by
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hopen := isOpen_image_interior hpublished P K hP
    (lower_lipschitz_injOn P K L hlim)
  obtain ⟨ρ, hρ, hthick⟩ := hA.exists_cthickening_subset_open hopen hAP
  let U := thickening ρ A
  have hclosure : closure U ⊆ cthickening ρ A := closure_thickening_subset_cthickening ρ A
  have hUc : IsCompact (closure U) := (hA.cthickening).of_isClosed_subset isClosed_closure hclosure
  have hUP : closure U ⊆ P '' interior K := hclosure.trans hthick
  have hlate := eventual_compact_image_interior hpublished Pₙ P K (closure U) L hL hPn
    hconv hlower hUc hUP
  exact ⟨U, isOpen_thickening, self_subset_thickening hρ A, hUc, hUP, hlate,
    coordinateInverse_uniform_on Pₙ P K (closure U) L hconv hlower
      (hUP.trans (image_mono interior_subset))
      (hlate.mono (fun _ h => h.trans (image_mono interior_subset)))⟩

/-- The source longitudinal coordinate is the real part of the inverse
ribbon chart, translated by the current front coordinate. -/
def longitudinalCoordinate (P : ℂ → ℂ) (K : Set ℂ) (k : ℝ) (z : ℂ) : ℝ :=
  (coordinateInverse P K z).re - k

theorem longitudinalCoordinate_locally_uniform
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0) (k : ℝ)
    (hL : 0 < L) (hP : ContinuousOn P K)
    (hPn : ∀ n, ContinuousOn (Pₙ n) K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y)) :
    TendstoLocallyUniformlyOn (fun n => longitudinalCoordinate (Pₙ n) K k)
      (longitudinalCoordinate P K k) atTop (P '' interior K) := by
  have hh := coordinateInverse_locally_uniform hpublished Pₙ P K L hL hP hPn hconv hlower
  have hu : UniformContinuous (fun z : ℂ => z.re - k) :=
    Complex.uniformContinuous_re.sub uniformContinuous_const
  exact hu.comp_tendstoLocallyUniformlyOn hh

theorem longitudinalCoordinate_continuousOn
    (P : ℂ → ℂ) (K : Set ℂ) (L : ℝ≥0) (k : ℝ)
    (hlower : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y)) :
    ContinuousOn (longitudinalCoordinate P K k) (P '' K) := by
  exact (Complex.continuous_re.comp_continuousOn
    (coordinateInverse_lipschitz P K L hlower).continuousOn).sub continuousOn_const

/-- A retained compact part of a ribbon has a common open physical chart
on which the actual longitudinal coordinates are eventually continuous
and converge locally uniformly. -/
theorem common_longitudinal_chart
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K A : Set ℂ) (L : ℝ≥0) (k : ℝ)
    (hL : 0 < L) (hP : ContinuousOn P K)
    (hPn : ∀ n, ContinuousOn (Pₙ n) K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hA : IsCompact A) (hAP : A ⊆ P '' interior K) :
    ∃ U : Set ℂ, IsOpen U ∧ A ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ P '' interior K ∧
      (∀ᶠ n in atTop, U ⊆ Pₙ n '' interior K) ∧
      ContinuousOn (longitudinalCoordinate P K k) U ∧
      (∀ᶠ n in atTop, ContinuousOn (longitudinalCoordinate (Pₙ n) K k) U) ∧
      TendstoLocallyUniformlyOn (fun n => longitudinalCoordinate (Pₙ n) K k)
        (longitudinalCoordinate P K k) atTop U := by
  obtain ⟨U, hU, hAU, hUc, hUP, hlate, _⟩ := common_physical_neighborhood
    hpublished Pₙ P K A L hL hP hPn hconv hlower hA hAP
  have hUImage : U ⊆ P '' interior K := subset_closure.trans hUP
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  refine ⟨U, hU, hAU, hUc, hUP, hlate.mono (fun _ h => subset_closure.trans h),
    (longitudinalCoordinate_continuousOn P K L k hlim).mono
      (hUImage.trans (image_mono interior_subset)), ?_, ?_⟩
  · filter_upwards [hlate] with n hn
    exact (longitudinalCoordinate_continuousOn (Pₙ n) K L k (hlower n)).mono
      (subset_closure.trans (hn.trans (image_mono interior_subset)))
  · exact (longitudinalCoordinate_locally_uniform hpublished Pₙ P K L k hL hP hPn
      hconv hlower).mono hUImage

/-- A compact set with limiting coordinates in an open coordinate region
has its moving coordinates in that same region for all sufficiently late
charts. This includes simultaneous longitudinal and transverse margins. -/
theorem eventual_compact_coordinate_region
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K S A : Set ℂ) (L : ℝ≥0)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hS : IsCompact S) (hSP : S ⊆ P '' K)
    (hcover : ∀ᶠ n in atTop, S ⊆ Pₙ n '' K)
    (hA : IsOpen A) (hSA : coordinateInverse P K '' S ⊆ A) :
    ∀ᶠ n in atTop, S ⊆ Pₙ n '' (K ∩ A) := by
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hcompact : IsCompact (coordinateInverse P K '' S) :=
    hS.image_of_continuousOn ((coordinateInverse_lipschitz P K L hlim).continuousOn.mono hSP)
  obtain ⟨ε, hε, heps⟩ := hcompact.exists_thickening_subset_open hA hSA
  have hu := coordinateInverse_uniform_on Pₙ P K S L hconv hlower hSP hcover
  filter_upwards [hcover, Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn hclose
  intro z hz
  refine ⟨coordinateInverse (Pₙ n) K z, ⟨coordinateInverse_mem (hn hz), ?_⟩,
    coordinateInverse_right (hn hz)⟩
  exact heps (mem_thickening_iff.mpr ⟨coordinateInverse P K z, mem_image_of_mem _ hz,
    by simpa only [dist_comm] using hclose z hz⟩)

/-- The admissible two-point patch bounds and a bounded marked point give
an actual uniformly convergent subsequence of the coordinate maps. Both
Lipschitz bounds pass to the limit, retaining an embedded limiting patch. -/
theorem exists_bilip_uniform_subsequence
    (Pₙ : ℕ → ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ K) (C L : ℝ≥0) (R : ℝ)
    (hupper : ∀ n, LipschitzOnWith C (Pₙ n) K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (htip : ∀ n, ‖Pₙ n x₀‖ ≤ R) :
    ∃ P : ℂ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => Pₙ (φ n)) P atTop K ∧
      LipschitzOnWith C P K ∧
      (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ L * dist (P x) (P y)) ∧
      InjOn P K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ℕ → K →ᵇ ℂ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨K.domRestrict (Pₙ n), (hupper n).continuousOn.domRestrict⟩
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall x₀
  have hbound n (x : K) : ‖f n x‖ ≤ R + C * M := by
    have hd := (hupper n).dist_le_mul x x.property x₀ hx₀
    have hh := norm_le_norm_add_const_of_dist_le hd
    exact hh.trans (add_le_add (htip n)
      (mul_le_mul_of_nonneg_left (hM x.property) C.coe_nonneg))
  have heq : Equicontinuous ((↑) : Set.range f → K → ℂ) := by
    apply (LipschitzWith.uniformEquicontinuous _ C ?_).equicontinuous
    rintro ⟨g, n, rfl⟩
    exact (hupper n).to_restrict
  have hcompact : IsCompact (closure (Set.range f)) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) (R + C * M))
      (isCompact_closedBall _ _) (Set.range f)
      (by rintro g x ⟨n, rfl⟩; simpa only [mem_closedBall, dist_zero_right] using hbound n x)
      heq
  obtain ⟨b, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hb : TendstoUniformly (fun n => f (φ n)) b atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  let P : ℂ → ℂ := fun z => if hz : z ∈ K then b ⟨z, hz⟩ else 0
  have hu : TendstoUniformlyOn (fun n => Pₙ (φ n)) P atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hb ε hε] with n hn
    intro z hz
    simpa [P, f, hz] using hn ⟨z, hz⟩
  have hPu : LipschitzOnWith C P K := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    exact le_of_tendsto ((hu.tendsto_at hx).dist (hu.tendsto_at hy))
      (Eventually.of_forall fun n => (hupper (φ n)).dist_le_mul x hx y hy)
  have hPl := lower_lipschitz_uniform_limit (fun n => Pₙ (φ n)) P K L hu
    (fun n => hlower (φ n))
  exact ⟨P, φ, hφ, hu, hPu, hPl, lower_lipschitz_injOn P K L hPl⟩

end SLEExactGauge.RibbonCoordinates

end

end OAI
