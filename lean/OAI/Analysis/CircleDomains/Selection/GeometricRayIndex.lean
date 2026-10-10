import OAI.Analysis.CircleDomains.Selection.FarRaySides
import Mathlib.Data.Int.ConditionallyCompleteOrder

namespace OAI

/-! The actual greatest-translate index. Compact strip bounds prove that
the defining set is nonempty and bounded above, uniformly over the arc law. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def rayJordan (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) : ℂ ≃ₜ ℂ :=
  Classical.choose ((translatedHalfPlaneRay γ hγ k).exists_jordan hsch)

theorem rayJordan_spec (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    (translatedHalfPlaneRay γ hγ k).IsJordan (rayJordan hsch γ hγ k) :=
  Classical.choose_spec ((translatedHalfPlaneRay γ hγ k).exists_jordan hsch)

def rayRightIndices (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) : Set ℤ :=
  {k | halfPlaneDisk z ∉ closure (jordanInterior (rayJordan hsch γ hγ k))}

def geometricRayIndex (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) : ℤ := sSup (rayRightIndices hsch γ hγ z)

theorem compact_ray_indices_bounded (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ B : ℤ, 0 < B ∧ ∀ (γ : K) (x y : ℝ), |x| ≤ X → 0 ≤ y → y ≤ Y →
      (-B ∈ rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) ∧
      B ∈ upperBounds (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  obtain ⟨N, hN, hfixed⟩ := translated_sides_eventually_fixed K hK hKS X Y hX hY
  obtain ⟨B, hB⟩ := exists_int_gt N
  have hBpos : 0 < B := by exact_mod_cast hN.trans hB
  refine ⟨B, hBpos, ?_⟩
  intro γ x y hx hy hyY
  have hneg : ((-B : ℤ) : ℝ) < -N := by rw [Int.cast_neg]; linarith
  constructor
  · exact (hfixed γ x y hx hy hyY (-B) (rayJordan hsch γ.val (hKS γ.property) (-B))
      (rayJordan_spec hsch γ.val (hKS γ.property) (-B))).2 hneg
  · intro k hk
    by_contra hnot
    have hBk : B < k := lt_of_not_ge hnot
    have hNk : N < (k : ℝ) := hB.trans (by exact_mod_cast hBk)
    exact hk ((hfixed γ x y hx hy hyY k (rayJordan hsch γ.val (hKS γ.property) k)
      (rayJordan_spec hsch γ.val (hKS γ.property) k)).1 hNk)

theorem rayRightIndices_nonempty_bddAbove (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    (rayRightIndices hsch γ hγ z).Nonempty ∧ BddAbove (rayRightIndices hsch γ hγ z) := by
  obtain ⟨B, _, hb⟩ := compact_ray_indices_bounded hsch {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) |z.re| z.im (abs_nonneg _) hz
  have h := hb ⟨γ, mem_singleton γ⟩ z.re z.im le_rfl hz le_rfl
  have he : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  simpa only [he] using And.intro (show (rayRightIndices hsch γ hγ
    ((z.re : ℂ) + (z.im : ℂ) * Complex.I)).Nonempty from ⟨-B, h.1⟩)
    (show BddAbove (rayRightIndices hsch γ hγ ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) from ⟨B, h.2⟩)

theorem geometricRayIndex_isGreatest (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    IsGreatest (rayRightIndices hsch γ hγ z) (geometricRayIndex hsch γ hγ z) := by
  obtain ⟨hne, hbdd⟩ := rayRightIndices_nonempty_bddAbove hsch γ hγ z hz
  exact ⟨Int.csSup_mem hne hbdd, fun _ hk => le_csSup hbdd hk⟩

theorem compact_geometricRayIndex_bound (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ M : ℝ, ∀ (γ : K) (x y : ℝ), |x| ≤ X → 0 ≤ y → y ≤ Y →
      |(geometricRayIndex hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I) : ℝ)| ≤ M := by
  obtain ⟨B, _, hB⟩ := compact_ray_indices_bounded hsch K hK hKS X Y hX hY
  refine ⟨(B : ℝ), ?_⟩
  intro γ x y hx hy hyY
  obtain ⟨hlow, hupp⟩ := hB γ x y hx hy hyY
  have hnon : (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)).Nonempty :=
    ⟨-B, hlow⟩
  have hbdd : BddAbove (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    ⟨B, hupp⟩
  have hsup := Int.csSup_mem hnon hbdd
  have hl := le_csSup hbdd hlow
  have hu := hupp hsup
  apply abs_le.mpr
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

end CircleDomainRigidity

end

end OAI
