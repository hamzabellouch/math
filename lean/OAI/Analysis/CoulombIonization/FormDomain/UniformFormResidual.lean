import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.ApproximateLipschitz

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom

lemma approximate_uniform_positive_form {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive)
    (Q : V → Prop) (K : ℝ)
    (hne : ∀ η : ℝ, 0 < η → ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪F,B F⟫_ℂ).re ≤ η)
    {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪F,B F⟫_ℂ).re ≤ δ ∧
      ∀ G : V, ‖G‖^2 ≤ H → (⟪G,B F⟫_ℂ).re ≤ δ := by
  let A : ℝ := ‖B‖*H
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) hH
  let η : ℝ := min δ (δ^2/(A+1))
  have hη : 0 < η := lt_min hδ (div_pos (sq_pos_of_pos hδ) (by linarith))
  have hq : δ^2/(A+1)*(A+1) = δ^2 := div_mul_cancel₀ _ (by linarith : A+1 ≠ 0)
  have hηA : η*A ≤ δ^2 := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_right δ (δ^2/(A+1)))
      (by linarith : 0 ≤ A+1)
    change η*(A+1) ≤ _ at h1
    nlinarith
  obtain ⟨F,hF,hK,he⟩ := hne η hη
  refine ⟨F,hF,hK,he.trans (min_le_left _ _),fun G hG => ?_⟩
  have hr := positive_form_residual_bound B hB F G hη.le he
    (C := H) (K := 1) (hG.trans_eq (mul_one H).symm)
  simp only [mul_one] at hr
  change (⟪G,B F⟫_ℂ).re^2 ≤ η*A at hr
  nlinarith

attribute [local irreducible] graphComponent graphFormVector
  FermionLipschitzMultiplier.apply coulombFormOperator fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator

lemma sectorExcessOperator_diagonal_normalized {N : ℕ} (Z : ℝ) (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) :
    (⟪F,sectorExcessOperator Z N F⟫_ℂ).re = formEnergy Z (graphFormVector F)-energy Z N := by
  have he := sectorExcessOperator_diagonal Z F
  have hev : energy Z N*‖fermionGraphValue N F‖^2 = energy Z N :=
    (congrArg (fun t : ℝ => energy Z N*t) hn).trans (mul_one _)
  exact he.trans (congrArg (fun t : ℝ => formEnergy Z (graphFormVector F)-t) hev)

theorem quantum_uniform_form_residual {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      formEnergy Z (graphFormVector F) ≤ energy Z N+δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ := by
  apply Exists.imp (p := fun F : fermionGraph N =>
      ‖fermionGraphValue N F‖^2 = 1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ ∧
      ∀ G : fermionGraph N, ‖G‖^2 ≤ H →
        (⟪G,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ)
  · intro F h
    refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
    have hdiag := sectorExcessOperator_diagonal_normalized Z F h.1
    have he := h.2.2.1
    linarith only [he,hdiag]
  · exact approximate_uniform_positive_form
      (sectorExcessOperator Z N) (sectorExcessOperator_positive hZ N)
      (fun F : fermionGraph N => ‖fermionGraphValue N F‖^2 = 1)
      (4*(|energy Z N|+(N:ℝ)*Z^2+2))
      (fun _ hη => quantum_sector_excess_near_minimizer hZ N hη) hH hδ

end CoulombAtom

end

end OAI
