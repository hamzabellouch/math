import FixedPointTheorems.brouwer
import Mathlib

namespace OAI

/-! Two transverse continuous crossings of a rectangle intersect, by
Brouwer's fixed-point theorem and the two-dimensional Poincaré–Miranda
argument. No simplicity or regularity of the crossing is needed. -/

noncomputable section
open Set
open scoped Topology

namespace SLEExactGauge.RectangleCrossing

def clampUnit (u : ℝ) : ℝ := max 0 (min 1 u)

theorem clampUnit_mem (u : ℝ) : clampUnit u ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clampUnit_continuous : Continuous clampUnit := by
  unfold clampUnit
  fun_prop

theorem clampUnit_fixed_forces_zero
    (u a : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (hlower : u = 0 → a ≤ 0) (hupper : u = 1 → 0 ≤ a)
    (he : clampUnit (u - a) = u) : a = 0 := by
  apply le_antisymm
  · by_contra hn
    have ha : 0 < a := lt_of_not_ge hn
    have hu0 : 0 < u := lt_of_le_of_ne hu.1 (by
      intro h
      exact (not_le_of_gt ha) (hlower h.symm))
    have hlt : clampUnit (u - a) < u :=
      max_lt hu0 ((min_le_right _ _).trans_lt (by linarith))
    exact (ne_of_lt hlt) he
  · by_contra hn
    have ha : a < 0 := lt_of_not_ge hn
    have hu1 : u < 1 := lt_of_le_of_ne hu.2 (by
      intro h
      exact (not_le_of_gt ha) (hupper h))
    have hlt : u < clampUnit (u - a) :=
      (lt_min hu1 (by linarith)).trans_le (le_max_right _ _)
    exact (ne_of_gt hlt) he

def unitSquare : Set (ℝ × ℝ) := Icc (0, 0) (1, 1)

/-- The rectangle intermediate-value theorem with signs on its four
faces. The map can have arbitrary behavior in the interior. -/
theorem poincare_miranda_square
    (F : ℝ × ℝ → ℝ × ℝ) (hF : ContinuousOn F unitSquare)
    (hleft : ∀ y ∈ Icc (0 : ℝ) 1, (F (0, y)).1 ≤ 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ (F (1, y)).1)
    (hbottom : ∀ x ∈ Icc (0 : ℝ) 1, (F (x, 0)).2 ≤ 0)
    (htop : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (F (x, 1)).2) :
    ∃ z ∈ unitSquare, F z = (0, 0) := by
  have hFc : Continuous (fun z : unitSquare => F z) := hF.domRestrict
  let f : C(unitSquare, unitSquare) :=
    ⟨fun z => ⟨(clampUnit (z.val.1 - (F z).1), clampUnit (z.val.2 - (F z).2)),
      ⟨⟨(clampUnit_mem _).1, (clampUnit_mem _).1⟩,
        ⟨(clampUnit_mem _).2, (clampUnit_mem _).2⟩⟩⟩,
      (clampUnit_continuous.comp (continuous_subtype_val.fst.sub hFc.fst)).prodMk
        (clampUnit_continuous.comp (continuous_subtype_val.snd.sub hFc.snd)) |>.subtype_mk _⟩
  obtain ⟨z, hz⟩ := brouwer_fixed_point unitSquare (convex_Icc _ _) isCompact_Icc
    ⟨(0, 0), by simp [unitSquare]⟩ f
  have hx : z.val.1 ∈ Icc (0 : ℝ) 1 := ⟨z.property.1.1, z.property.2.1⟩
  have hy : z.val.2 ∈ Icc (0 : ℝ) 1 := ⟨z.property.1.2, z.property.2.2⟩
  have hfx : (F z).1 = 0 := clampUnit_fixed_forces_zero _ _ hx
    (fun he => by rw [show z.val = (0, z.val.2) from Prod.ext he rfl]; exact hleft z.val.2 hy)
    (fun he => by rw [show z.val = (1, z.val.2) from Prod.ext he rfl]; exact hright z.val.2 hy)
    (congrArg (fun w : unitSquare => w.val.1) hz)
  have hfy : (F z).2 = 0 := clampUnit_fixed_forces_zero _ _ hy
    (fun he => by rw [show z.val = (z.val.1, 0) from Prod.ext rfl he]; exact hbottom z.val.1 hx)
    (fun he => by rw [show z.val = (z.val.1, 1) from Prod.ext rfl he]; exact htop z.val.1 hx)
    (congrArg (fun w : unitSquare => w.val.2) hz)
  exact ⟨z, z.property, Prod.ext hfx hfy⟩

/-- A longitudinal crossing and a transverse crossing of any nondegenerate
axis-aligned rectangle meet, even when either path has self-intersections. -/
theorem paths_intersect_rectangle
    (p q : ℝ → ℂ) (a b c d : ℝ) (_hab : a < b) (_hcd : c < d)
    (hp : ContinuousOn p (Icc 0 1)) (hq : ContinuousOn q (Icc 0 1))
    (hpr : ∀ t ∈ Icc (0 : ℝ) 1, (p t).re ∈ Icc a b ∧ (p t).im ∈ Icc c d)
    (hqr : ∀ t ∈ Icc (0 : ℝ) 1, (q t).re ∈ Icc a b ∧ (q t).im ∈ Icc c d)
    (hp0 : (p 0).re = a) (hp1 : (p 1).re = b)
    (hq0 : (q 0).im = c) (hq1 : (q 1).im = d) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, p s = q t := by
  let F : ℝ × ℝ → ℝ × ℝ := fun z =>
    ((p z.1).re - (q z.2).re, (q z.2).im - (p z.1).im)
  have hfst : MapsTo Prod.fst unitSquare (Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hz.1.1, hz.2.1⟩
  have hsnd : MapsTo Prod.snd unitSquare (Icc (0 : ℝ) 1) :=
    fun z hz => ⟨hz.1.2, hz.2.2⟩
  have hpc := hp.comp continuous_fst.continuousOn hfst
  have hqc := hq.comp continuous_snd.continuousOn hsnd
  have hFc : ContinuousOn F unitSquare :=
    (Complex.continuous_re.continuousOn.comp hpc (mapsTo_univ _ _)).sub
      (Complex.continuous_re.continuousOn.comp hqc (mapsTo_univ _ _)) |>.prodMk
        ((Complex.continuous_im.continuousOn.comp hqc (mapsTo_univ _ _)).sub
          (Complex.continuous_im.continuousOn.comp hpc (mapsTo_univ _ _)))
  obtain ⟨z, hz, he⟩ := poincare_miranda_square F hFc
    (fun t ht => by dsimp [F]; rw [hp0]; linarith [(hqr t ht).1.1])
    (fun t ht => by dsimp [F]; rw [hp1]; linarith [(hqr t ht).1.2])
    (fun s hs => by dsimp [F]; rw [hq0]; linarith [(hpr s hs).2.1])
    (fun s hs => by dsimp [F]; rw [hq1]; linarith [(hpr s hs).2.2])
  refine ⟨z.1, hfst hz, z.2, hsnd hz, Complex.ext ?_ ?_⟩
  · exact sub_eq_zero.mp (congrArg Prod.fst he)
  · exact (sub_eq_zero.mp (congrArg Prod.snd he)).symm

end SLEExactGauge.RectangleCrossing

end

end OAI
