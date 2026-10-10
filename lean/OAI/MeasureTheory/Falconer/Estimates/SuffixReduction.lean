import OAI.MeasureTheory.Falconer.Angular.SuffixDirection
import OAI.MeasureTheory.Falconer.Estimates.RetainedPairs

namespace OAI

/-! # The original-law suffix collision reduction

This is the analytic suffix step before substituting the profile test
threshold. The only test used is a projection collision test on each full
second cell, in the direction of an actual witness pair. The full retained
cell pairs are required to satisfy the child tests; no witness-dependent
restriction of the tested conditional law is made.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem tested_suffix_collision_bound
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) (n : ℕ) (G H : Set (Space d × Space d))
    (hG : MeasurableSet G) (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g w W : ℝ} (hg : 0 < g) (hw : 0 < w)
    (hws : w ≤ P.side/(2:ℝ)^n)
    (hsmall : 2*(d:ℝ)*(P.side/(2:ℝ)^n)^2/g ≤ w)
    (hwidth : w+4*(d:ℝ)*(P.side/(2:ℝ)^n)^2/g ≤ W)
    (hsep : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      g ≤ ‖(P.descendant c.1).center-(Q.descendant c.2).center‖)
    (F : ℝ≥0∞)
    (hproj : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      ∃ x ∈ (P.descendant c.1).carrier, ∃ y ∈ (Q.descendant c.2).carrier,
        x ≠ y ∧ ((ν.restrict (Q.descendant c.2).carrier).prod
          (ν.restrict (Q.descendant c.2).carrier))
          {z : Space d × Space d | |inner ℝ (‖x-y‖⁻¹ • (x-y)) (z.1-z.2)| ≤ W} ≤
            F*(ν (Q.descendant c.2).carrier)^2)
    (hchild : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      (P.descendant c.1).carrier ×ˢ (Q.descendant c.2).carrier ⊆ H)
    (C : ℝ) :
    ((testedCellDistance μ ν P Q G).prod (testedCellDistance μ ν P Q G))
      {z : ℝ × ℝ | |z.1-z.2| ≤ C*w} ≤
    (((PlanarFalconer.bandOffsets C).card : ℝ≥0∞) *
      ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * F) *
      ((testedCellDistance μ ν P Q H).prod (testedCellDistance μ ν P Q H))
        {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*(P.side/(2:ℝ)^n)} := by
  let S := retainedCellPairs μ ν P Q n G
  let P' := fun c : List (Fin d → Bool) × List (Fin d → Bool) => P.descendant c.1
  let Q' := fun c : List (Fin d → Bool) × List (Fin d → Bool) => Q.descendant c.2
  let e := fun c => ‖(P' c).center-(Q' c).center‖⁻¹ • ((P' c).center-(Q' c).center)
  have hlen (c) (hc : c ∈ S) : c.1.length = n ∧ c.2.length = n := by
    obtain ⟨hc,_⟩ := Finset.mem_filter.mp hc
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
    exact ⟨(mem_cubePaths d n c.1).mp (Finset.mem_filter.mp h₁).1,
      (mem_cubePaths d n c.2).mp (Finset.mem_filter.mp h₂).1⟩
  have hs₁ (c) (hc : c ∈ S) : (P' c).side = P.side/(2:ℝ)^n := by
    dsimp only [P']
    rw [P.descendant_side,(hlen c hc).1]
  have hs₂ (c) (hc : c ∈ S) : (Q' c).side = P.side/(2:ℝ)^n := by
    dsimp only [Q']
    rw [Q.descendant_side,(hlen c hc).2,hQ]
  have hspos (c) (hc : c ∈ S) : 0 < (P' c).side := by rw [hs₁ c hc]; positivity
  have hside (c) (hc : c ∈ S) : (Q' c).side = (P' c).side :=
    (hs₂ c hc).trans (hs₁ c hc).symm
  have hp (c) (hc : c ∈ S) :
      ((ν.restrict (Q' c).carrier).prod (ν.restrict (Q' c).carrier))
        {z : Space d × Space d | |inner ℝ (e c) (z.1-z.2)| ≤ w} ≤
          F*(ν (Q' c).carrier)^2 := by
    obtain ⟨x,hx,y,hy,hxy,hxyproj⟩ := hproj c hc
    apply le_trans _ hxyproj
    exact suffix_witness_projection_transfer ν (P' c) (Q' c) (hspos c hc) (hside c hc)
      hg (hsep c hc) hx hy hxy (by simpa only [hs₁ c hc] using hwidth)
  have hbin := finite_suffix_cell_comparison S μ ν P' Q' e
    (fun c => testedCellDistance μ ν (P' c) (Q' c) G)
    (show 0 ≤ P.side/(2:ℝ)^n by positivity) hw hws hs₁ hs₂
    (fun c _ => testedCellDistance_le μ ν (P' c) (Q' c) G)
    (fun c hc x hx y hy =>
      ((P' c).distance_linearization (Q' c) (hspos c hc) (hside c hc) hg (hsep c hc) hx hy).trans
        (by simpa only [hs₁ c hc] using hsmall)) F hp
  have hcoarse := full_retained_distance_le μ ν P Q n G H hchild
  have hfine := PlanarFalconer.real_bin_shifted_band_bound
    (testedCellDistance μ ν P Q G) (testedCellDistance μ ν P Q G) hw C 0
  simp only [sub_zero,← pow_two] at hfine
  change (PlanarFalconer.binL2Norm
    (∑ c ∈ retainedCellPairs μ ν P Q n G,
      testedCellDistance μ ν (P.descendant c.1) (Q.descendant c.2) G) w)^2 ≤ _ at hbin
  rw [← testedCellDistance_split μ ν P Q n G hG] at hbin
  apply (hfine.trans (mul_le_mul' le_rfl hbin)).trans
  have hh := mul_le_mul' (le_refl
    (((PlanarFalconer.bandOffsets C).card : ℝ≥0∞) *
      ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * F))
    (Measure.prod_mono hcoarse hcoarse
      {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*(P.side/(2:ℝ)^n)})
  simpa only [mul_assoc,S,P',Q'] using hh

end Falconer

end OAI
