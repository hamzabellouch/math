import OAI.Analysis.KadisonKastler.L2MeasurableExtension
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # L² as the Hilbert sum of measurable strata

Restriction and extension by zero identify the L² space on a countable
measurable partition with the Hilbert sum of its individual L² spaces.
-/

namespace KadisonKastler

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X)

theorem l2Extension_inner (s : Set X) (hs : MeasurableSet s)
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) (g : Lp H 2 μ) :
    ⟪l2Extension μ s hs f, g⟫_ℂ = ⟪f, l2Restrict μ s hs g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, s.indicator (fun x => ⟪l2ExtensionFunction μ s f x, g x⟫_ℂ) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [l2Extend_apply_ae μ s hs f] with x hx
      change ⟪l2Extend μ s hs f x, g x⟫_ℂ = _
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [l2ExtensionFunction, hxs]
    _ = ∫ x in s, ⟪l2ExtensionFunction μ s f x, g x⟫_ℂ ∂μ :=
      integral_indicator hs
    _ = ∫ x : s, ⟪l2ExtensionFunction μ s f x.val, g x.val⟫_ℂ
        ∂Measure.comap ((↑) : s → X) μ := (integral_subtype_comap hs _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [l2Restrict_apply_ae μ s hs g] with x hx
      rw [l2ExtensionFunction_coe, hx]

theorem l2Restrict_extension_disjoint (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t)
    (f : Lp H 2 (Measure.comap ((↑) : t → X) μ)) :
    l2Restrict μ s hs (l2Extension μ t ht f) = 0 := by
  apply Lp.ext
  have he := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (l2Extend_apply_ae μ t ht f))
  filter_upwards [l2Restrict_apply_ae μ s hs (l2Extension μ t ht f), he,
    Lp.coeFn_zero (E := H) (p := 2) (Measure.comap ((↑) : s → X) μ)] with x hr he hz
  rw [hr, hz]
  change l2Extend μ t ht f x.val = 0
  rw [he]
  have hxt : x.val ∉ t := fun hx => Set.disjoint_left.mp hst x.property hx
  simp [l2ExtensionFunction, hxt]

variable {ι : Type*} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))

theorem l2Strata_orthogonal (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    OrthogonalFamily ℂ (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ))
      (fun i => l2Extension μ (s i) (hs i)) := by
  intro i j hij f g
  rw [l2Extension_inner, l2Restrict_extension_disjoint μ (s i) (s j)
    (hs i) (hs j) (hd hij), inner_zero_right]

omit [InnerProductSpace ℂ H] in
theorem l2_eq_zero_of_restrictions [Countable ι] (hcover : ⋃ i, s i = Set.univ)
    (g : Lp H 2 μ) (hg : ∀ i, l2Restrict μ (s i) (hs i) g = 0) : g = 0 := by
  have hzero (i : ι) : ∀ᵐ x ∂μ, x ∈ s i → g x = 0 := by
    apply (ae_restrict_iff' (hs i)).mp
    apply (ae_restrict_iff_subtype (hs i)).mpr
    filter_upwards [l2Restrict_apply_ae μ (s i) (hs i) g,
      Lp.coeFn_zero (E := H) (p := 2) (Measure.comap ((↑) : s i → X) μ)] with x hx hz
    rw [hg i] at hx
    exact hx.symm.trans hz
  apply Lp.ext
  filter_upwards [eventually_countable_forall.mpr hzero,
    Lp.coeFn_zero (E := H) (p := 2) μ] with x hx hz
  rw [hz]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
  exact hx i hi

theorem l2Strata_isHilbertSum [CompleteSpace H] [Countable ι]
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ i, s i = Set.univ) :
    IsHilbertSum ℂ (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ))
      (fun i => l2Extension μ (s i) (hs i)) := by
  apply IsHilbertSum.mk (l2Strata_orthogonal μ s hs hd)
  let M := (⨆ i, LinearMap.range (l2Extension (H := H) μ (s i) (hs i)).toLinearMap).closure
  suffices hM : M.toSubmodule = ⊤ by
    rw [show (⨆ i, LinearMap.range (l2Extension (H := H) μ (s i) (hs i)).toLinearMap).topologicalClosure =
      M.toSubmodule from rfl, hM]
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro g hg
  change g = 0
  apply l2_eq_zero_of_restrictions μ s hs hcover
  intro i
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← l2Extension_inner]
  apply hg
  exact Submodule.le_topologicalClosure _
    (Submodule.mem_iSup_of_mem i ⟨l2Restrict μ (s i) (hs i) g, rfl⟩)

/-- The actual Hilbert-space coordinates associated with a measurable partition. -/
def l2StrataCoordinates [CompleteSpace H] [Countable ι]
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ i, s i = Set.univ) :
    Lp H 2 μ ≃ₗᵢ[ℂ] lp (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ)) 2 :=
  (l2Strata_isHilbertSum μ s hs hd hcover).linearIsometryEquiv

end

end KadisonKastler

end OAI
