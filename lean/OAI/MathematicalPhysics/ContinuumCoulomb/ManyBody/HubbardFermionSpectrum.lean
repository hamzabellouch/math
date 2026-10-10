import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SuperexchangeSpectrum

namespace OAI

/-! The complete half-filled Fock variational problem has the concrete block form. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem euclidean_real_inner {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  rfl

theorem coordinateInclusion_real_inner {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (x : EuclideanSpace ℂ α) (y : EuclideanSpace ℂ β) :
    ⟪coordinateInclusion f x, y⟫_ℝ = ⟪x, coordinateRestriction f y⟫_ℝ := by
  rw [euclidean_real_inner, euclidean_real_inner]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right (coordinateInclusion f) x y).symm

theorem coordinateRestriction_inclusion {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (x : EuclideanSpace ℂ α) :
    coordinateRestriction f (coordinateInclusion f x) = x := by
  ext a
  rw [coordinateRestriction_apply, coordinateInclusion_apply_image f hf]

theorem lowFock_real_inner (m : ℕ) (p : ActualHubbardLowSpace m)
    (v : FockCoordinateSpace (2 * m + 1)) :
    ⟪lowFockInclusion m p, v⟫_ℝ = ⟪p, lowFockRestriction m v⟫_ℝ :=
  coordinateInclusion_real_inner _ p v

theorem highFock_real_inner (m : ℕ) (q : ActualHubbardHighSpace m)
    (v : FockCoordinateSpace (2 * m + 1)) :
    ⟪highFockInclusion m q, v⟫_ℝ = ⟪q, highFockRestriction m v⟫_ℝ :=
  coordinateInclusion_real_inner _ q v

theorem highFockRestriction_inclusion (m : ℕ) (q : ActualHubbardHighSpace m) :
    highFockRestriction m (highFockInclusion m q) = q :=
  coordinateRestriction_inclusion _ (highOccupationIndex_injective m) q

theorem lowFockInclusion_norm_map (m : ℕ) (p : ActualHubbardLowSpace m) :
    ‖lowFockInclusion m p‖ = ‖p‖ :=
  coordinateInclusion_norm_map _ (spinOccupationSet_injective m) p

theorem highFockInclusion_norm_map (m : ℕ) (q : ActualHubbardHighSpace m) :
    ‖highFockInclusion m q‖ = ‖q‖ :=
  coordinateInclusion_norm_map _ (highOccupationIndex_injective m) q

theorem highOccupationIndex_ne_spin (m : ℕ) (A : HalfFilledHighBasis m)
    (s : SourceSpinBasis (m + 1)) : highOccupationIndex m A ≠ spinOccupationSet m s := by
  intro h
  apply A.property
  intro i
  change occupationAt m (highOccupationIndex m A) i = 1
  rw [h, occupationAt_spinOccupationSet]

theorem lowFockRestriction_highInclusion (m : ℕ) (q : ActualHubbardHighSpace m) :
    lowFockRestriction m (highFockInclusion m q) = 0 := by
  ext s
  change coordinateRestriction (spinOccupationSet m) (highFockInclusion m q) s = 0
  rw [coordinateRestriction_apply]
  exact coordinateInclusion_apply_outside _ q _ (fun A => highOccupationIndex_ne_spin m A s)

theorem highFockRestriction_lowInclusion (m : ℕ) (p : ActualHubbardLowSpace m) :
    highFockRestriction m (lowFockInclusion m p) = 0 := by
  ext A
  change coordinateRestriction (highOccupationIndex m) (lowFockInclusion m p) A = 0
  rw [coordinateRestriction_apply]
  exact coordinateInclusion_apply_outside _ p _
    (fun s => Ne.symm (highOccupationIndex_ne_spin m A s))

theorem low_high_inner_zero (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    ⟪lowFockInclusion m p, highFockInclusion m q⟫_ℝ = 0 := by
  rw [lowFock_real_inner, lowFockRestriction_highInclusion, inner_zero_right]

theorem low_high_norm_sq (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    ‖lowFockInclusion m p + highFockInclusion m q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  rw [norm_add_sq_real, low_high_inner_zero, mul_zero, add_zero,
    lowFockInclusion_norm_map, highFockInclusion_norm_map]

theorem lowProjection_add_highProjection (m : ℕ) (x : Laughlin.Fock.Space (2 * m + 1))
    (hx : IsHalfFilled m x) : lowProjection m x + highProjection m x = x := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  simp only [map_add, Finsupp.add_apply, lowProjection, occupationDiagonal,
    highProjection, fockDiagonal_coordinate]
  by_cases hspin : ∀ i, occupationAt m A i = 1
  · simp [hspin]
  · by_cases hcard : A.card = m + 1
    · simp [hspin, hcard]
    · simp [hspin, hcard, hx A hcard]

def assembleFock (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    Laughlin.Fock.Space (2 * m + 1) :=
  (fockCoordinates (2 * m + 1)).symm (lowFockInclusion m p + highFockInclusion m q)

@[simp] theorem fockCoordinates_assemble (m : ℕ) (p : ActualHubbardLowSpace m)
    (q : ActualHubbardHighSpace m) :
    fockCoordinates (2 * m + 1) (assembleFock m p q) =
      lowFockInclusion m p + highFockInclusion m q :=
  (fockCoordinates (2 * m + 1)).apply_symm_apply _

theorem assembleFock_mass (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    fockMass (assembleFock m p q) = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  rw [← fockCoordinates_norm_sq, fockCoordinates_assemble, low_high_norm_sq]

theorem assembleFock_halfFilled (m : ℕ) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    IsHalfFilled m (assembleFock m p q) := by
  intro A hA
  have hl : ∀ s, spinOccupationSet m s ≠ A := by
    intro s hs
    exact hA (hs ▸ spinOccupationSet_card m s)
  have hh : ∀ B, highOccupationIndex m B ≠ A := by
    intro B hB
    exact hA (hB ▸ B.val.property)
  change fockCoordinates (2 * m + 1) (assembleFock m p q) A = 0
  rw [fockCoordinates_assemble]
  simp only [PiLp.add_apply]
  change coordinateInclusion (spinOccupationSet m) p A +
    coordinateInclusion (highOccupationIndex m) q A = 0
  rw [coordinateInclusion_apply_outside _ p A hl,
    coordinateInclusion_apply_outside _ q A hh, add_zero]

/-- Every vector in the full half-filled Fock sector has this low/high
decomposition, not just vectors generated by a trial-state ansatz. -/
theorem assembleFock_decomposition (m : ℕ) (x : Laughlin.Fock.Space (2 * m + 1))
    (hx : IsHalfFilled m x) :
    assembleFock m (lowFockRestriction m (fockCoordinates (2 * m + 1) x))
      (highFockRestriction m (fockCoordinates (2 * m + 1) x)) = x := by
  apply (fockCoordinates (2 * m + 1)).injective
  rw [fockCoordinates_assemble, lowFock_projector_coordinates, highFock_projector_coordinates,
    ← map_add, lowProjection_add_highProjection m x hx]

def chargePenaltyFock (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Module.End ℂ (Laughlin.Fock.Space (2 * m + 1)) :=
  occupationDiagonal m (fun o => (chargePenalty U V o : ℂ))

theorem chargePenaltyFock_spinEmbedding (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (u : SourceSpinVector (m + 1)) :
    chargePenaltyFock m U V (spinEmbedding m u) = 0 := by
  have hsingle (s : SourceSpinBasis (m + 1)) : chargePenaltyFock m U V (spinWedge m s) = 0 := by
    have h := occupationDiagonal_eigen m (fun o => (chargePenalty U V o : ℂ))
      (fun _ => 1) (spinWedge m s) (fun k => by simpa using siteNumber_spinWedge m s k)
    simpa [chargePenaltyFock, chargePenalty, occupationDeviation] using h
  change chargePenaltyFock m U V (∑ s, u s • spinWedge m s) = _
  simp only [map_sum, map_smul, hsingle, smul_zero, Finset.sum_const_zero]

def actualChargePenalty (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ActualHubbardHighSpace m →L[ℝ] ActualHubbardHighSpace m :=
  diagonalPenalty (fun A => chargePenalty U V (occupationAt m A.val.val))

theorem chargePenaltyFock_highInclusion (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (q : ActualHubbardHighSpace m) :
    fockOperator (chargePenaltyFock m U V) (highFockInclusion m q) =
      highFockInclusion m (actualChargePenalty m U V q) := by
  ext A
  rw [chargePenaltyFock, occupationDiagonal, fockOperator_diagonal_apply]
  change _ * coordinateInclusion (highOccupationIndex m) q A =
    coordinateInclusion (highOccupationIndex m) (actualChargePenalty m U V q) A
  by_cases hA : ∃ B, highOccupationIndex m B = A
  · obtain ⟨B, rfl⟩ := hA
    rw [coordinateInclusion_apply_image _ (highOccupationIndex_injective m),
      coordinateInclusion_apply_image _ (highOccupationIndex_injective m)]
    rfl
  · rw [coordinateInclusion_apply_outside _ _ A (by simpa using hA),
      coordinateInclusion_apply_outside _ _ A (by simpa using hA), mul_zero]

variable {Edge : Type*} [Fintype Edge]

theorem lowFockRestriction_hopping_low (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) (p : ActualHubbardLowSpace m) :
    lowFockRestriction m
      (fockOperator (graphHopping m left right (fun e => (t e : ℂ))) (lowFockInclusion m p)) = 0 := by
  have hinput : fockOperator (graphHopping m left right (fun e => (t e : ℂ)))
      (lowFockInclusion m p) = fockCoordinates (2 * m + 1)
        (graphHopping m left right (fun e => (t e : ℂ)) (spinEmbedding m (fun s => p s))) := by
    rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates]
  apply lowFockInclusion_injective m
  rw [hinput, lowFock_projector_coordinates,
    lowProjection_graphHopping_spinEmbedding_zero m left right _ hloop, map_zero, map_zero]

theorem fockHopping_real_symmetric (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (v w : FockCoordinateSpace (2 * m + 1)) :
    ⟪v, fockOperator (graphHopping m left right (fun e => (t e : ℂ))) w⟫_ℝ =
      ⟪fockOperator (graphHopping m left right (fun e => (t e : ℂ))) v, w⟫_ℝ := by
  rw [euclidean_real_inner, euclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right
    (fockOperator (graphHopping m left right (fun e => (t e : ℂ)))) v w
  rw [fockOperator_graphHopping_adjoint] at h
  exact congrArg Complex.re h

def hubbardFermionForm (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (x : Laughlin.Fock.Space (2 * m + 1)) : ℝ :=
  ⟪fockCoordinates (2 * m + 1) x,
    fockCoordinates (2 * m + 1)
      ((chargePenaltyFock m U V + graphHopping m left right (fun e => (t e : ℂ))) x)⟫_ℝ

theorem hubbardFermionForm_blocks (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) (p : ActualHubbardLowSpace m) (q : ActualHubbardHighSpace m) :
    hubbardFermionForm m U V left right t (assembleFock m p q) =
      Perturbation.blockEnergy (actualChargePenalty m U V)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) p q := by
  let H := fockOperator (graphHopping m left right (fun e => (t e : ℂ)))
  let P := fockOperator (chargePenaltyFock m U V)
  let lp := lowFockInclusion m p
  let hq := highFockInclusion m q
  have hPlow : P lp = 0 := by
    dsimp only [P, lp]
    rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates,
      chargePenaltyFock_spinEmbedding, map_zero]
  have hPhigh : P hq = highFockInclusion m (actualChargePenalty m U V q) :=
    chargePenaltyFock_highInclusion m U V q
  have hPenaltyCross : ⟪lp, P hq⟫_ℝ = 0 := by
    rw [hPhigh, low_high_inner_zero]
  have hPenaltyHigh : ⟪hq, P hq⟫_ℝ = ⟪q, actualChargePenalty m U V q⟫_ℝ := by
    rw [hPhigh, highFock_real_inner, highFockRestriction_inclusion]
  have hHopLow : ⟪lp, H lp⟫_ℝ = 0 := by
    rw [lowFock_real_inner, lowFockRestriction_hopping_low m left right t hloop,
      inner_zero_right]
  have hHopCross : ⟪hq, H lp⟫_ℝ = ⟪q, actualHubbardCoupling m left right t p⟫_ℝ := by
    rw [highFock_real_inner]
    rfl
  have hHopReverse : ⟪lp, H hq⟫_ℝ = ⟪q, actualHubbardCoupling m left right t p⟫_ℝ := by
    rw [fockHopping_real_symmetric, real_inner_comm, hHopCross]
  have hHopHigh : ⟪hq, H hq⟫_ℝ = ⟪q, actualHubbardHighHopping m left right t q⟫_ℝ := by
    rw [highFock_real_inner]
    rfl
  have hform : hubbardFermionForm m U V left right t (assembleFock m p q) =
      ⟪lp + hq, P (lp + hq) + H (lp + hq)⟫_ℝ := by
    unfold hubbardFermionForm
    rw [LinearMap.add_apply, map_add, ← fockOperator_coordinates, ← fockOperator_coordinates,
      fockCoordinates_assemble]
  rw [hform, map_add, map_add]
  simp only [inner_add_left, inner_add_right, hPlow, inner_zero_right,
    hPenaltyCross, hPenaltyHigh, hHopLow, hHopCross, hHopReverse, hHopHigh]
  unfold Perturbation.blockEnergy Perturbation.penaltyForm
  ring

/-- The actual fermionic spectral bottom on all nonzero half-filled
states, in the canonical occupation norm. -/
def hubbardFermionBottom (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ) : ℝ :=
  sInf {e | ∃ x : Laughlin.Fock.Space (2 * m + 1), IsHalfFilled m x ∧ 0 < fockMass x ∧
    e = hubbardFermionForm m U V left right t x / fockMass x}

theorem hubbardFermionBottom_eq_blockBottom (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) :
    hubbardFermionBottom m U V left right t =
      Perturbation.blockBottom (actualChargePenalty m U V)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) := by
  unfold hubbardFermionBottom Perturbation.blockBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, hmass, rfl⟩
    let p := lowFockRestriction m (fockCoordinates (2 * m + 1) x)
    let q := highFockRestriction m (fockCoordinates (2 * m + 1) x)
    have hdecomp : assembleFock m p q = x := assembleFock_decomposition m x hx
    have hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
      rw [← assembleFock_mass, hdecomp]
      exact hmass
    refine ⟨p, q, hnorm, ?_⟩
    rw [← hdecomp, hubbardFermionForm_blocks m U V left right t hloop, assembleFock_mass]
    rfl
  · rintro ⟨p, q, hnorm, rfl⟩
    refine ⟨assembleFock m p q, assembleFock_halfFilled m p q, ?_, ?_⟩
    · rw [assembleFock_mass]
      exact hnorm
    · rw [hubbardFermionForm_blocks m U V left right t hloop, assembleFock_mass]
      rfl

/-- The full fixed-particle fermion-to-Heisenberg energy comparison,
with actual CAR hopping, long-range charge penalty and all spin states. -/
theorem hubbardFermionBottom_Heisenberg (m : ℕ) (U R : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (hrow : ∀ i, ∑ j, |V i j| ≤ R) (hUR : R < U)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e)))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon < 1 / 2)
    (ht : 4 * ∑ e, |t e| ≤ epsilon * (U - R)) :
    |hubbardFermionBottom m U V left right t - graphSourceBottom m left right J| ≤
      2 * (U - R) * epsilon ^ 3 := by
  rw [hubbardFermionBottom_eq_blockBottom m U V left right t hloop]
  exact actual_hubbard_Heisenberg_bottom m U R V hsymm hdiag hrow hUR
    left right t J hloop hsimple hgap hcal hepsilon hsmall ht

end ContinuumCoulomb.HubbardGlobal

end

end OAI
