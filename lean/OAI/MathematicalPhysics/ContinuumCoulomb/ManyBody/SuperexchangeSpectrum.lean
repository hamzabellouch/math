import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSector

namespace OAI

/-! Exact spectral identification of the global Hubbard inverse term. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace
variable {Edge : Type*} [Fintype Edge]

def graphHeisenbergFock (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℂ) :
    Module.End ℂ (Space (2 * m + 1)) :=
  ∑ e, J e • (siteHeisenberg (siteMode m (left e) 0) (siteMode m (left e) 1)
    (siteMode m (right e) 0) (siteMode m (right e) 1) - 1)

def graphSourceAction (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℂ)
    (u : SourceSpinVector (m + 1)) : SourceSpinVector (m + 1) :=
  fun s => ∑ e, J e * (sourceHeisenbergAction (left e) (right e) u s - u s)

def graphSourceForm (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (u : SourceSpinVector (m + 1)) : ℝ :=
  ∑ e, J e * (sourceHeisenbergForm (left e) (right e) u - sourceSpinMass u)

theorem graphHeisenbergFock_spinEmbedding (m : ℕ)
    (left right : Edge → Fin (m + 1)) (J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (u : SourceSpinVector (m + 1)) :
    graphHeisenbergFock m left right J (spinEmbedding m u) =
      spinEmbedding m (graphSourceAction m left right J u) := by
  simp only [graphHeisenbergFock, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply,
    spinEmbedding_heisenberg m u _ _ (hloop _), ← map_sub, ← map_smul, ← map_sum]
  congr 1
  ext s
  simp [graphSourceAction]

/-- The checked basis compression extends to every entangled spin state. -/
theorem graphSuperexchange_spinEmbedding (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * ((U - V (left e) (right e) : ℝ) : ℂ))
    (u : SourceSpinVector (m + 1)) :
    -(lowProjection m (graphHopping m left right t
      (chargeInverse m U V (graphHopping m left right t (spinEmbedding m u))))) =
        spinEmbedding m (graphSourceAction m left right J u) := by
  let K : Module.End ℂ (Space (2 * m + 1)) :=
    -(lowProjection m * graphHopping m left right t * chargeInverse m U V *
      graphHopping m left right t)
  have hbasis (s : SourceSpinBasis (m + 1)) :
      K (spinWedge m s) = graphHeisenbergFock m left right J (spinWedge m s) := by
    simpa only [K, Module.End.mul_apply, LinearMap.neg_apply, graphHeisenbergFock,
      LinearMap.sum_apply, LinearMap.smul_apply] using
      graphSuperexchange_calibrated m U V hsymm hdiag left right t J
        hloop hsimple hgap hcal s
  have h : K (spinEmbedding m u) =
      graphHeisenbergFock m left right J (spinEmbedding m u) := by
    change K (∑ s, u s • spinWedge m s) =
      graphHeisenbergFock m left right J (∑ s, u s • spinWedge m s)
    simp only [map_sum, map_smul, hbasis]
  exact h.trans (graphHeisenbergFock_spinEmbedding m left right J hloop u)

theorem lowFockInclusion_spinEmbedding (m : ℕ) (p : ActualHubbardLowSpace m) :
    lowFockInclusion m p = fockCoordinates (2 * m + 1) (spinEmbedding m (fun s => p s)) := by
  ext A
  by_cases hA : ∃ s, spinOccupationSet m s = A
  · obtain ⟨s, rfl⟩ := hA
    rw [fockCoordinates_apply, spinEmbedding_coordinate]
    exact coordinateInclusion_apply_image _ (spinOccupationSet_injective m) p s
  · rw [fockCoordinates_apply,
      spinEmbedding_coordinate_outside m _ A (by simpa using hA)]
    exact coordinateInclusion_apply_outside _ p A (by simpa using hA)

theorem lowFockRestriction_inclusion (m : ℕ) (p : ActualHubbardLowSpace m) :
    lowFockRestriction m (lowFockInclusion m p) = p := by
  ext s
  change coordinateRestriction (spinOccupationSet m) (lowFockInclusion m p) s = p s
  rw [coordinateRestriction_apply]
  exact coordinateInclusion_apply_image _ (spinOccupationSet_injective m) p s

theorem lowFockInclusion_injective (m : ℕ) : Function.Injective (lowFockInclusion m) := by
  intro p q h
  simpa only [lowFockRestriction_inclusion] using congrArg (lowFockRestriction m) h

theorem fockOperator_diagonal_apply {Q : ℕ} (f : Finset (Fin (Q + 1)) → ℂ)
    (x : FockCoordinateSpace Q) (A : Finset (Fin (Q + 1))) :
    fockOperator (fockDiagonal f) x A = f A * x A := by
  obtain ⟨y, rfl⟩ := (fockCoordinates Q).surjective x
  rw [fockOperator_coordinates, fockCoordinates_apply, fockDiagonal_coordinate,
    fockCoordinates_apply]

def actualChargeInverse (m : ℕ) (U : ℝ) (V : Fin (m + 1) → Fin (m + 1) → ℝ) :
    ActualHubbardHighSpace m →L[ℝ] ActualHubbardHighSpace m :=
  diagonalPenalty (fun A => (chargePenalty U V (occupationAt m A.val.val))⁻¹)

theorem highFockInclusion_chargeInverse (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ) (q : ActualHubbardHighSpace m) :
    highFockInclusion m (actualChargeInverse m U V q) =
      fockOperator (chargeInverse m U V) (highFockInclusion m q) := by
  ext A
  rw [chargeInverse, occupationDiagonal, fockOperator_diagonal_apply]
  change coordinateInclusion (highOccupationIndex m) (actualChargeInverse m U V q) A =
    _ * coordinateInclusion (highOccupationIndex m) q A
  by_cases hA : ∃ B, highOccupationIndex m B = A
  · obtain ⟨B, rfl⟩ := hA
    rw [coordinateInclusion_apply_image _ (highOccupationIndex_injective m),
      coordinateInclusion_apply_image _ (highOccupationIndex_injective m)]
    rfl
  · rw [coordinateInclusion_apply_outside _ _ A (by simpa using hA),
      coordinateInclusion_apply_outside _ _ A (by simpa using hA), mul_zero]

/-- The inverse on the concrete high block is the same actual
occupation-diagonal inverse used in the global CAR compression. -/
theorem actualChargeInverse_coupling_inclusion (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e) (p : ActualHubbardLowSpace m) :
    highFockInclusion m (actualChargeInverse m U V (actualHubbardCoupling m left right t p)) =
      fockCoordinates (2 * m + 1)
        (chargeInverse m U V (graphHopping m left right (fun e => (t e : ℂ))
          (spinEmbedding m (fun s => p s)))) := by
  rw [highFockInclusion_chargeInverse]
  simp only [actualHubbardCoupling, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.comp_apply]
  rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates,
    highFock_projector_coordinates, highProjection_graphHopping_spinEmbedding m _ _ _ hloop,
    fockOperator_coordinates]

theorem graphSourceForm_expectation (m : ℕ)
    (left right : Edge → Fin (m + 1)) (J : Edge → ℝ)
    (u : SourceSpinVector (m + 1)) :
    graphSourceForm m left right J u =
      (∑ s, star (u s) * graphSourceAction m left right (fun e => (J e : ℂ)) u s).re := by
  have hpoint (e : Edge) (s : SourceSpinBasis (m + 1)) :
      (star (u s) * ((J e : ℂ) *
        (sourceHeisenbergAction (left e) (right e) u s - u s))).re =
      J e * ((star (u s) * sourceHeisenbergAction (left e) (right e) u s).re -
        Complex.normSq (u s)) := by
    simp [Complex.mul_re, Complex.normSq_apply]
    ring
  simp only [graphSourceForm, graphSourceAction, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  simp_rw [hpoint]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rfl

theorem lowFockRestriction_superexchange (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * ((U - V (left e) (right e) : ℝ) : ℂ))
    (u : SourceSpinVector (m + 1)) :
    lowFockRestriction m (fockCoordinates (2 * m + 1)
      (-(graphHopping m left right t
        (chargeInverse m U V (graphHopping m left right t (spinEmbedding m u)))))) =
      WithLp.toLp 2 (graphSourceAction m left right J u) := by
  apply lowFockInclusion_injective m
  rw [lowFock_projector_coordinates, map_neg,
    graphSuperexchange_spinEmbedding m U V hsymm hdiag left right t J
      hloop hsimple hgap hcal, lowFockInclusion_spinEmbedding]

/-- The effective quadratic form of the actual Hubbard blocks is
the entire graph Heisenberg form, with the exact scalar offset. -/
theorem actualHubbard_effectiveForm (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e)))
    (p : ActualHubbardLowSpace m) :
    Perturbation.effectiveForm
        (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (actualChargeInverse m U V) (actualHubbardCoupling m left right t) p =
      graphSourceForm m left right J (fun s => p s) := by
  let A := graphHopping m left right (fun e => (t e : ℂ))
  let x := spinEmbedding m (fun s => p s)
  let B := actualHubbardCoupling m left right t
  let T := actualChargeInverse m U V
  have hH : fockOperator A (lowFockInclusion m p) = fockCoordinates (2 * m + 1) (A x) := by
    rw [lowFockInclusion_spinEmbedding, fockOperator_coordinates]
  have hBp : B p = highFockRestriction m (fockCoordinates (2 * m + 1) (A x)) := by
    change highFockRestriction m (fockOperator A (lowFockInclusion m p)) = _
    rw [hH]
  have hinv : highFockInclusion m (T (B p)) =
      fockCoordinates (2 * m + 1) (chargeInverse m U V (A x)) :=
    actualChargeInverse_coupling_inclusion m U V left right t hloop p
  have hinner : ⟪B p, T (B p)⟫_ℂ =
      ⟪lowFockInclusion m p,
        fockCoordinates (2 * m + 1) (A (chargeInverse m U V (A x)))⟫_ℂ := by
    calc
      _ = ⟪fockCoordinates (2 * m + 1) (A x), highFockInclusion m (T (B p))⟫_ℂ := by
        rw [hBp]
        exact ContinuousLinearMap.adjoint_inner_left (highFockInclusion m) _ _
      _ = ⟪fockCoordinates (2 * m + 1) (A x),
          fockCoordinates (2 * m + 1) (chargeInverse m U V (A x))⟫_ℂ := by rw [hinv]
      _ = _ := by
        have h := ContinuousLinearMap.adjoint_inner_left (fockOperator A)
          (fockCoordinates (2 * m + 1) (chargeInverse m U V (A x))) (lowFockInclusion m p)
        rw [fockOperator_graphHopping_adjoint, hH, fockOperator_coordinates] at h
        exact h
  have hcalC (e : Edge) : (t e : ℂ) ^ 2 =
      (J e : ℂ) * ((U - V (left e) (right e) : ℝ) : ℂ) := by exact_mod_cast hcal e
  have hcompress := lowFockRestriction_superexchange m U V hsymm hdiag left right
    (fun e => (t e : ℂ)) (fun e => (J e : ℂ)) hloop hsimple hgap hcalC (fun s => p s)
  have heffective : -(⟪B p, T (B p)⟫_ℂ) =
      ⟪p, WithLp.toLp 2 (graphSourceAction m left right (fun e => (J e : ℂ)) (fun s => p s))⟫_ℂ := by
    rw [hinner]
    have h := ContinuousLinearMap.adjoint_inner_right (lowFockInclusion m) p
      (fockCoordinates (2 * m + 1) (-(A (chargeInverse m U V (A x)))))
    change ⟪p, lowFockRestriction m _⟫_ℂ = _ at h
    rw [hcompress, map_neg, inner_neg_right] at h
    exact h.symm
  calc
    _ = -⟪B p, T (B p)⟫_ℝ := by
      simp only [Perturbation.effectiveForm, Perturbation.inverseForm,
        zero_apply, inner_zero_right, zero_sub]
      rfl
    _ = (⟪p, WithLp.toLp 2
        (graphSourceAction m left right (fun e => (J e : ℂ)) (fun s => p s))⟫_ℂ).re := by
      have hreal : ⟪B p, T (B p)⟫_ℝ = (⟪B p, T (B p)⟫_ℂ).re := by
        simp only [PiLp.inner_apply, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro s _
        rfl
      rw [hreal]
      exact congrArg Complex.re heffective
    _ = _ := by
      rw [graphSourceForm_expectation]
      simp only [PiLp.inner_apply, RCLike.inner_apply']
      rfl

def graphSourceBottom (m : ℕ) (left right : Edge → Fin (m + 1)) (J : Edge → ℝ) : ℝ :=
  sInf {e | ∃ u : SourceSpinVector (m + 1),
    sourceSpinMass u = 1 ∧ e = graphSourceForm m left right J u}

theorem sourceSpinMass_euclidean (m : ℕ) (p : ActualHubbardLowSpace m) :
    sourceSpinMass (fun s => p s) = ‖p‖ ^ 2 := by
  simp only [sourceSpinMass, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

/-- Equality of the two actual variational bottoms; no minimizer or
assertion about the desired source energy is supplied as an assumption. -/
theorem actualHubbard_effectiveBottom (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℝ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * (U - V (left e) (right e))) :
    Perturbation.effectiveBottom
        (0 : ActualHubbardLowSpace m →L[ℝ] ActualHubbardLowSpace m)
        (actualChargeInverse m U V) (actualHubbardCoupling m left right t) =
      graphSourceBottom m left right J := by
  unfold Perturbation.effectiveBottom graphSourceBottom
  congr 1
  ext e
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun s => p s, ?_, ?_⟩
    · rw [sourceSpinMass_euclidean, hp]
      norm_num
    · exact actualHubbard_effectiveForm m U V hsymm hdiag left right t J
        hloop hsimple hgap hcal p
  · rintro ⟨u, hu, rfl⟩
    let p : ActualHubbardLowSpace m := WithLp.toLp 2 u
    have hp : ‖p‖ = 1 := by
      have hsq : ‖p‖ ^ 2 = 1 := (sourceSpinMass_euclidean m p).symm.trans hu
      nlinarith [norm_nonneg p]
    refine ⟨p, hp, ?_⟩
    exact (actualHubbard_effectiveForm m U V hsymm hdiag left right t J
      hloop hsimple hgap hcal p).symm

/-- Global second-order energy comparison with concrete Fock blocks
and the actual normalized graph-spin spectral bottom. -/
theorem actual_hubbard_Heisenberg_bottom (m : ℕ) (U R : ℝ)
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
    let weight : HalfFilledHighBasis m → ℝ :=
      fun A => chargePenalty U V (occupationAt m A.val.val)
    |Perturbation.blockBottom (diagonalPenalty weight)
        (actualHubbardHighHopping m left right t) (actualHubbardCoupling m left right t) -
      graphSourceBottom m left right J| ≤ 2 * (U - R) * epsilon ^ 3 := by
  have h := actual_hubbard_second_order m U R V hsymm hrow hUR left right t
    hepsilon hsmall ht
  rw [← actualHubbard_effectiveBottom m U V hsymm hdiag left right t J
    hloop hsimple hgap hcal]
  exact h

end ContinuumCoulomb.HubbardGlobal

end

end OAI
