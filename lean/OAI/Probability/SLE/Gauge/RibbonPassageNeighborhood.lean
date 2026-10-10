import OAI.Probability.SLE.Gauge.RibbonCoordinateLimit

namespace OAI

/-! Common physical neighborhoods of compact passage routes. Strict
coordinate margins are retained on the closure before passing to moving
ribbon charts. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

/-- An embedded coordinate chart maps every open coordinate subset of its
controlled patch to an open physical subset. -/
theorem isOpen_image_coordinate_subset
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (K V : Set ℂ) (hP : ContinuousOn P K) (hi : InjOn P K)
    (hV : IsOpen V) (hVK : V ⊆ K) : IsOpen (P '' V) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x hx
  have hsub : ball x r ⊆ K := hball.trans hVK
  have hopen := hpublished P x r hr (hP.mono hsub) (hi.mono hsub)
  exact mem_of_superset
    (hopen.mem_nhds (mem_image_of_mem P (mem_ball_self hr)))
    (image_mono hball)

/-- A compact route strictly inside a coordinate region admits one open
physical neighborhood whose closure lies in the same region for every
sufficiently late ribbon chart. -/
theorem common_coordinate_region_neighborhood
    (hpublished : PublishedPlanarDiskOpenness)
    (Pₙ : ℕ → ℂ → ℂ) (P : ℂ → ℂ) (K A V : Set ℂ) (L : ℝ≥0)
    (hL : 0 < L) (hP : ContinuousOn P K)
    (hPn : ∀ n, ContinuousOn (Pₙ n) K)
    (hconv : TendstoUniformlyOn Pₙ P atTop K)
    (hlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ L * dist (Pₙ n x) (Pₙ n y))
    (hA : IsCompact A) (hV : IsOpen V)
    (hAV : A ⊆ P '' (interior K ∩ V)) :
    ∃ U : Set ℂ, IsOpen U ∧ A ⊆ U ∧ IsCompact (closure U) ∧
      closure U ⊆ P '' (interior K ∩ V) ∧
      (∀ᶠ n in atTop, closure U ⊆ Pₙ n '' (K ∩ V)) ∧
      (∀ᶠ n in atTop, closure U ⊆ Pₙ n '' interior K) ∧
      TendstoUniformlyOn (fun n => coordinateInverse (Pₙ n) K)
        (coordinateInverse P K) atTop (closure U) := by
  have hlim := lower_lipschitz_uniform_limit Pₙ P K L hconv hlower
  have hi := lower_lipschitz_injOn P K L hlim
  have hopen := isOpen_image_coordinate_subset hpublished P K (interior K ∩ V)
    hP hi (isOpen_interior.inter hV) (inter_subset_left.trans interior_subset)
  obtain ⟨ρ, hρ, hthick⟩ := hA.exists_cthickening_subset_open hopen hAV
  let U := thickening ρ A
  have hcl : closure U ⊆ cthickening ρ A := closure_thickening_subset_cthickening ρ A
  have hUc : IsCompact (closure U) := hA.cthickening.of_isClosed_subset isClosed_closure hcl
  have hUPV : closure U ⊆ P '' (interior K ∩ V) := hcl.trans hthick
  have hUP : closure U ⊆ P '' interior K := hUPV.trans (image_mono inter_subset_left)
  have hlate := eventual_compact_image_interior hpublished Pₙ P K (closure U) L hL hPn
    hconv hlower hUc hUP
  have hUV : coordinateInverse P K '' closure U ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, he⟩ := hUPV hz
    have heq : coordinateInverse P K z = x := by
      rw [← he]
      exact coordinateInverse_left hi (interior_subset hx.1)
    simpa only [heq] using hx.2
  have hcover : ∀ᶠ n in atTop, closure U ⊆ Pₙ n '' K :=
    hlate.mono (fun _ h => h.trans (image_mono interior_subset))
  have hregions := eventual_compact_coordinate_region Pₙ P K (closure U) V L hconv hlower
    hUc (hUP.trans (image_mono interior_subset)) hcover hV hUV
  exact ⟨U, isOpen_thickening, self_subset_thickening hρ A, hUc, hUPV, hregions, hlate,
    coordinateInverse_uniform_on Pₙ P K (closure U) L hconv hlower
      (hUP.trans (image_mono interior_subset)) hcover⟩

/-- Limiting coordinate guides have exact longitudinal progress and retain
the source transverse margin. -/
theorem limit_guide_coordinates
    (P : ℂ → ℂ) (K : Set ℂ) (hi : InjOn P K)
    (α : ℝ → ℂ) (x : ℝ)
    (hshape : EqOn α (fun t => P (guideCoordinate 0 x t)) (Icc 0 2))
    (hmem : ∀ t ∈ Icc (0 : ℝ) 2, guideCoordinate 0 x t ∈ K) :
    ∀ t ∈ Icc (0 : ℝ) 2,
      longitudinalCoordinate P K 0 (α t) = t ∧
        |(coordinateInverse P K (α t)).im| ≤ |x| := by
  intro t ht
  rw [hshape ht, coordinateInverse_left hi (hmem t ht)]
  constructor
  · simp only [longitudinalCoordinate, coordinateInverse_left hi (hmem t ht),
      guideCoordinate_re, zero_add, sub_zero]
  · exact guideCoordinate_im_bound ht.1

end SLEExactGauge.RibbonCoordinates

end

end OAI
