import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFiberConstancy

namespace OAI

/-!
# Full holonomy in extremal-root product coordinates

The real quotient of a positive-root group records the displacement of
the selected intrinsic leaf even when both remaining and selected
coordinates change. This permits comparison at different good centers
in the disintegration step of EK2003, Proposition 8.3.
-/

noncomputable section
open Matrix MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_positiveRootGroup_holonomy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (g₁ g₂ : positiveRootGeneratedGroup S),
        rightAction x g₁.val ∉ N → rightAction x g₂.val ∉ N →
        intrinsicRootLeaf hab μ (rightAction x g₂.val) =
          basedRealMeasure (intrinsicRootLeaf hab μ (rightAction x g₁.val))
            (g₂.val.val a b - g₁.val.val a b) := by
  obtain ⟨N, hN, hN0, hhol⟩ :=
    exists_nullset_positiveRootPattern_holonomy d S hpos hab ell hell hneut hdecay μ hA
  refine ⟨N, hN, hN0, ?_⟩
  intro x g₁ g₂ h₁ h₂
  let F := neutralRootEntryHom d S hpos hcomp hab ell hell hneut hdecay
  have hi : (g₁⁻¹).val.val a b = -g₁.val.val a b := by
    have H := congrArg Multiplicative.toAdd (map_inv F g₁)
    exact H
  have he : (g₁.val⁻¹ * g₂.val).val a b = g₂.val.val a b - g₁.val.val a b := by
    have H := congrArg Multiplicative.toAdd (F.map_mul g₁⁻¹ g₂)
    change (g₁.val⁻¹ * g₂.val).val a b = (g₁⁻¹).val.val a b + g₂.val.val a b at H
    rw [hi] at H
    exact H.trans (by ring)
  have hrel : rightAction (rightAction x g₁.val) (g₁.val⁻¹ * g₂.val) =
      rightAction x g₂.val := by
    rw [rightAction_mul]
    congr 1
    group
  simpa only [he] using hhol _ h₁ _ h₂ (g₁.val⁻¹ * g₂.val)
    (positiveRootGeneratedGroup_pattern S hcomp ((g₁⁻¹ * g₂).prop)) hrel

theorem exists_nullset_rootFactor_holonomy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (w₁ w₂ : positiveRootGeneratedGroup (S.erase (a, b))) (t₁ t₂ : ℝ),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection hab t₁) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection hab t₂) ∉ N →
        intrinsicRootLeaf hab μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection hab t₂)) =
          basedRealMeasure (intrinsicRootLeaf hab μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection hab t₁))) (t₂ - t₁) := by
  obtain ⟨N, hN, hN0, hhol⟩ :=
    exists_nullset_positiveRootGroup_holonomy d S hpos hcomp hab ell hell hneut hdecay μ hA
  refine ⟨N, hN, hN0, ?_⟩
  intro x w₁ w₂ t₁ t₂ h₁ h₂
  let E := positiveRootRightFactorHomeomorph S hpos hcomp hab habS
    (erase_neutral_root_closed S hcomp (a, b) ell hneut hdecay)
  have he (w : positiveRootGeneratedGroup (S.erase (a, b))) (t : ℝ) :
      (E (w, t)).val.val a b = t :=
    congrArg Prod.snd (E.left_inv (w, t))
  have hE (w : positiveRootGeneratedGroup (S.erase (a, b))) (t : ℝ) :
      (E (w, t)).val = w.val * Matrix.SpecialLinearGroup.transvection hab t := rfl
  have H := hhol x (E (w₁, t₁)) (E (w₂, t₂)) h₁ h₂
  simp only [he] at H
  simpa only [hE] using H

end DukePrimeDegree

end

end OAI
