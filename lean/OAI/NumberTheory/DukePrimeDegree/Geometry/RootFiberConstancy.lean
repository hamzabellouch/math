import OAI.NumberTheory.DukePrimeDegree.Geometry.ExtremalRootQuotient

namespace OAI

/-!
# Leaf constancy on the remaining-coordinate fibers

With the selected root last in the product coordinates, different
remaining coordinates are related by a conjugate of the remaining
group. Its normality and neutral holonomy therefore give equality of
the actual normalized root leaves on each such coordinate fiber.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem remaining_root_conjugate_mem
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (w : G (d + 1)) (hw : w ∈ positiveRootGeneratedGroup (S.erase (a, b))) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hab t)⁻¹ * w *
      Matrix.SpecialLinearGroup.transvection hab t ∈ positiveRootGeneratedGroup (S.erase (a, b)) := by
  let w' : positiveRootGeneratedGroup S :=
    ⟨w, positiveRootGeneratedGroup_mono (Finset.erase_subset (a, b) S) hw⟩
  let u : positiveRootGeneratedGroup S :=
    ⟨Matrix.SpecialLinearGroup.transvection hab t,
      transvection_mem_positiveRootGeneratedGroup S hab habS t⟩
  have hn := remaining_roots_normal d S hpos hcomp hab ell hell hneut hdecay
  exact hn.conj_mem' w' hw u

theorem exists_nullset_remaining_root_fiber_constancy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (t : ℝ)
        (w₁ w₂ : positiveRootGeneratedGroup (S.erase (a, b))),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection hab t) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection hab t) ∉ N →
        intrinsicRootLeaf hab μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection hab t)) =
          intrinsicRootLeaf hab μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection hab t)) := by
  obtain ⟨N, hN, hN0, hhol⟩ :=
    exists_nullset_positiveRootPattern_holonomy d S hpos hab ell hell hneut hdecay μ hA
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hab t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx a b hab
  obtain ⟨E, hbad, hE, hE0⟩ := exists_measurable_superset_of_null
    (ae_iff.mp ((ae_intrinsicRootLeaf_spec hab μ hfree).mono fun _ h => h.2))
  refine ⟨N ∪ E, hN.union hE, measure_union_null hN0 hE0, ?_⟩
  intro x t w₁ w₂ h₁ h₂
  let u := Matrix.SpecialLinearGroup.transvection hab t
  let g := u⁻¹ * (w₁.val⁻¹ * w₂.val) * u
  have hg : g ∈ positiveRootGeneratedGroup (S.erase (a, b)) :=
    remaining_root_conjugate_mem d S hpos hcomp hab habS ell hell hneut hdecay _
      ((positiveRootGeneratedGroup (S.erase (a, b))).mul_mem
        ((positiveRootGeneratedGroup (S.erase (a, b))).inv_mem w₁.prop) w₂.prop) t
  have hc := erase_neutral_root_closed S hcomp (a, b) ell hneut hdecay
  have hp := positiveRootGeneratedGroup_pattern (S.erase (a, b)) hc hg
  have hzero : g.val a b = 0 := by
    simpa only [Matrix.one_apply, hab, ite_false] using hp a b (by simp)
  have hrel : rightAction (rightAction x (w₁.val * u)) g = rightAction x (w₂.val * u) := by
    rw [rightAction_mul]
    congr 1
    dsimp [g]
    group
  have hunit : intrinsicRootLeaf hab μ (rightAction x (w₁.val * u)) (Metric.ball 0 1) = 1 := by
    by_contra h
    exact h₁ (Or.inr (hbad h))
  have h := hhol _ (fun h => h₁ (Or.inl h)) _ (fun h => h₂ (Or.inl h)) g
    (positiveRootPattern_mono (Finset.erase_subset (a, b) S) hp) hrel
  rw [hzero, basedRealMeasure_zero_of_unit _ hunit] at h
  exact h.symm

end DukePrimeDegree

end

end OAI
