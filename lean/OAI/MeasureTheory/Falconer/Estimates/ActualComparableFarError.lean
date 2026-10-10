import OAI.MeasureTheory.Falconer.Estimates.ActualFarSpatialError
import OAI.MeasureTheory.Falconer.Angular.AngularComparableCarrier
import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def angularComparableFarContribution (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (A B : CellPath) (a d : ℕ) (v Ma₁ Ma₂ : ℝ)
    (F : (Fin 4 → Plane) → ℂ) : ℂ :=
  (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
        if ¬ angularNear Q₁ Q₂ (a+d) row col then
          ∫ x in angularLengthComparable, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0

theorem uniform_actual_comparable_far_error {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (m l)) →
    ∀ (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ a ≤ N, ∀ A : Fin 2 → CellPath, (∀ l, (A l).length = a) →
    ∀ d : ℕ, ∀ v L₀ : ℝ, v ≤ N → v-(a+d:ℕ) = 2*L₀ →
    (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N lam sig (J l) (i l) (hsp l)
    let M := fun l => ((2:ℝ)^N)^(-m l a)
    ‖angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularOriginalSpatialKernel (β 0) (β 1) v Ψ) -
      angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularStationarySpatialKernel (β 0) (β 1) n v Ψ)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_actual_far_spatial_error (T := T+12*lam+2) hsig K hΨ hpos hs hW hw
  refine ⟨n,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA
    d v L₀ hvN hv hLL hL₀
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N lam sig (J l) (i l) (hsp l)
  let M := fun l => ((2:ℝ)^N)^(-m l a)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hc : (2:ℝ)^(2*(v-a)) ≤ ((2:ℝ)^N)^2 := by
    rw [← Real.rpow_natCast ((2:ℝ)^N) 2,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (0:ℝ) ≤ a := Nat.cast_nonneg a
    norm_num
    linarith
  have he := angular_four_sum_error_power (Q 0) (Q 1) (hQp 0) (hQp 1) (ρ 0) (ρ 1)
    (A 0) (A 1) d N lam (T+12*lam+2) ((2:ℝ)^(2*(v-a))) (M 0) (M 1)
    (by positivity) hc (by dsimp [M]; positivity) (by dsimp [M]; positivity)
    ((hd 0).normalized_cell_mass_le ha (hA 0)) ((hd 1).normalized_cell_mass_le ha (hA 1))
    (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)
    (fun row col => ∫ x in angularLengthComparable, angularOriginalSpatialKernel (β 0) (β 1) v Ψ x
      ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col)
    (fun row col => ∫ x in angularLengthComparable, angularStationarySpatialKernel (β 0) (β 1) n v Ψ x
      ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col) (by
      intro row hr col hcol hfar
      have hp := h₀ N hN S b k hcard hK L hLN hL Q hQp ρ m (fun _ => lam) J i hsp hm hb
        v (a+d:ℕ) L₀ hv hLL hL₀ (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col)
        angularLengthComparable measurable_angularLengthComparable
        (angular_comparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
          (sourceProductVertices_subset _ _ _ _ _ _ a d (hA 0) (hA 1) hr)
          (sourceProductVertices_subset _ _ _ _ _ _ a d (hA 0) (hA 1) hcol) hfar)
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _)))
  dsimp only [angularComparableFarContribution]
  rw [← smul_sub]
  convert he using 1
  congr 1
  ring

end PlanarFalconer

end OAI
