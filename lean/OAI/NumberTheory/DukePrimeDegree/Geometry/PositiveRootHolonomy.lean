import OAI.NumberTheory.DukePrimeDegree.Geometry.PositiveRootPattern
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootHolonomy

namespace OAI

/-!
# Holonomy across a positive-root pattern

A flow neutral on one root and contracting every other allowed matrix
entry sends every element of the pattern to its selected root entry.
The proved neutral holonomy theorem then identifies the actual leaves.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootPattern_isolated_limit
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hdiag : ∀ r, (r, r) ∉ S) {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
      diagonalOneParameter ell hell (-t)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hab (g.val a b))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have he (t : ℝ) := conjugation_entry ell hell g t r s
  simp_rw [he]
  by_cases hrs : r = s
  · subst s
    have hd := hg r r (hdiag r)
    simp only [sub_self, zero_mul, Real.exp_zero, one_mul, hd]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) r r) atTop (𝓝 _)) using 1
    by_cases hra : r = a
    · subst r
      simp [Matrix.SpecialLinearGroup.transvection_coe, hab.symm]
    · simp [Matrix.SpecialLinearGroup.transvection_coe, Ne.symm hra]
  by_cases hrab : r = a ∧ s = b
  · obtain ⟨hra, hsb⟩ := hrab
    subst r
    subst s
    simp only [hneut, sub_self, zero_mul, Real.exp_zero, one_mul]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => g.val a b) atTop (𝓝 _)) using 1
    simp [Matrix.SpecialLinearGroup.transvection_coe, hab]
  have htarget : (Matrix.SpecialLinearGroup.transvection hab (g.val a b)).val r s = 0 := by
    simp_all [Matrix.SpecialLinearGroup.transvection_coe, eq_comm]
  rw [htarget]
  by_cases hS : (r, s) ∈ S
  · have hne : (r, s) ≠ (a, b) := by
      intro h
      cases h
      exact hrab ⟨rfl, rfl⟩
    have hneg := hdecay (r, s) hS hne
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (sub_pos.mpr hneg) tendsto_id)
    have hlim := ht.mul_const (g.val r s)
    have hsign (t : ℝ) : -((ell s - ell r) * t) = (ell r - ell s) * t := by ring
    simpa only [Function.comp_def, id_eq, hsign, zero_mul] using hlim
  · have hz : g.val r s = 0 := by
      simpa only [Matrix.one_apply, hrs, ite_false] using hg r s hS
    simp only [hz, mul_zero]
    exact tendsto_const_nhds

theorem positiveRootPattern_isolated_limit
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
      diagonalOneParameter ell hell (-t)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hab (g.val a b))) :=
  rootPattern_isolated_limit d S (fun r h => lt_irrefl r (hpos (r, r) h))
    hab ell hell hneut hdecay g hg

/-- One common null set controls all positive-pattern orbit pairs. This
is the leaf-constancy input for the root-product induction. -/
theorem exists_nullset_positiveRootPattern_holonomy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ y ∉ N, ∀ g : G (d + 1), PositiveRootPattern S g →
        rightAction x g = y → intrinsicRootLeaf hab μ y =
          basedRealMeasure (intrinsicRootLeaf hab μ x) (g.val a b) := by
  obtain ⟨N, hN, hN0, h⟩ := exists_nullset_neutral_root_holonomy d hab μ hA ell hell hneut
  refine ⟨N, hN, hN0, ?_⟩
  intro x hx y hy g hg hxy
  exact h x hx y hy g hxy _
    (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay g hg)

end DukePrimeDegree

end

end OAI
