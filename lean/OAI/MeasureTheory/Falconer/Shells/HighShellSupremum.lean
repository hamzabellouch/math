import OAI.MeasureTheory.Falconer.Shells.HighShellParentEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

noncomputable def inverseShellEnergies (d : PositiveDistanceData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {h | ∃ j ∈ Finset.range (n+1),
    ∃ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList),
    ∃ ξ, h = (d.inversePhasedHF v Ψ b.2 ξ).toReal}

noncomputable def inverseShellSupremum (d : PositiveDistanceData) (n : ℕ)
    (v : ℝ) (Ψ : ℝ → ℝ) : ℝ := sSup (d.inverseShellEnergies n v Ψ)

theorem inverseShellEnergies_bddAbove (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hs : ∀ x, 4 < x → Ψ x = 0) : BddAbove (d.inverseShellEnergies n v Ψ) := by
  let μ := sourceAngularShellMeasure v Ψ
  let : IsFiniteMeasure μ := sourceAngularShellMeasure_finite v Ψ hW hΨW hs
  let E : ℝ := (2:ℝ)^(2*(v-d.a))
  let C := ∑ j ∈ Finset.range (n+1), (d.inversePhasedBound j)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨E*μ.real univ*C,?_⟩
  intro x hx
  rcases hx with rfl | ⟨j,hj,b,hb,ξ,rfl⟩
  · exact mul_nonneg (mul_nonneg (by dsimp [E]; positivity) measureReal_nonneg) hC
  · rw [(d.inversePhasedHF_finite_eq hQ j hb v Ψ hW hΨW hs ξ).2]
    have hd := d.inversePhasedForm_data hQ j hb
    have hm : Measurable (d.inversePhasedForm b.2 ξ) :=
      hd.1.comp (f := fun r : ℝ => (ξ,r)) (measurable_const.prodMk measurable_id)
    have hi := integrable_norm_square_bounded μ _ hm (d.inversePhasedBound_nonneg j)
      (Filter.Eventually.of_forall (fun r => hd.2 (ξ,r)))
    have hbnd := integral_mono hi (integrable_const ((d.inversePhasedBound j)^2))
      (fun r => pow_le_pow_left₀ (norm_nonneg _) (hd.2 (ξ,r)) 2)
    rw [integral_const,smul_eq_mul] at hbnd
    have hjC : (d.inversePhasedBound j)^2 ≤ C :=
      Finset.single_le_sum (fun i _ => sq_nonneg (d.inversePhasedBound i)) hj
    change E*(∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ _
    calc
      _ ≤ E*(μ.real univ*(d.inversePhasedBound j)^2) :=
        mul_le_mul_of_nonneg_left hbnd (by dsimp [E]; positivity)
      _ ≤ E*(μ.real univ*C) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjC measureReal_nonneg) (by dsimp [E]; positivity)
      _ = _ := by ring

theorem inverseShellSupremum_majorizes (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hs : ∀ x, 4 < x → Ψ x = 0) :
    0 ≤ d.inverseShellSupremum n v Ψ ∧
    ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ d.inverseShellSupremum n v Ψ := by
  have hb := d.inverseShellEnergies_bddAbove hQ n v Ψ hW hΨW hs
  refine ⟨le_csSup hb (Or.inl rfl),?_⟩
  intro j hj b hb' ξ
  exact le_csSup hb (Or.inr ⟨j,hj,b,hb',ξ,rfl⟩)

end PositiveDistanceData

end PlanarFalconer

end OAI
