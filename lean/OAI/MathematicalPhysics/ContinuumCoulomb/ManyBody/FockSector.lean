import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockBlocks

namespace OAI

/-! Fixed-particle support and the true low/high Fock projections. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators InnerProductSpace

variable {Q : ℕ}

theorem totalNumber_basis (A : Finset (Fin (Q + 1))) :
    totalNumber Q (fockBasis Q A) = (A.card : ℂ) • fockBasis Q A := by
  simp only [totalNumber, LinearMap.sum_apply, number_basis]
  have hpoint (i : Fin (Q + 1)) :
      (if i ∈ A then fockBasis Q A else 0) =
        (if i ∈ A then (1 : ℂ) else 0) • fockBasis Q A := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_smul]
  simp

theorem totalNumber_eq_diagonal (Q : ℕ) :
    totalNumber Q = fockDiagonal (fun A => (A.card : ℂ)) := by
  apply (fockBasis Q).ext
  intro A
  rw [totalNumber_basis, fockDiagonal_basis]

theorem totalNumber_eigen_coordinate_zero (N : ℕ) (x : Space Q)
    (hx : totalNumber Q x = (N : ℂ) • x) (A : Finset (Fin (Q + 1)))
    (hA : A.card ≠ N) : (fockBasis Q).repr x A = 0 := by
  have h := congrArg (fun y => (fockBasis Q).repr y A) hx
  rw [totalNumber_eq_diagonal, fockDiagonal_coordinate, map_smul,
    Finsupp.smul_apply, smul_eq_mul] at h
  have hne : (A.card : ℂ) ≠ (N : ℂ) := by exact_mod_cast hA
  have hz : ((A.card : ℂ) - N) * (fockBasis Q).repr x A = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

def IsHalfFilled (m : ℕ) (x : Space (2 * m + 1)) : Prop :=
  ∀ A, A.card ≠ m + 1 → (fockBasis (2 * m + 1)).repr x A = 0

theorem isHalfFilled_of_totalNumber (m : ℕ) (x : Space (2 * m + 1))
    (hx : totalNumber (2 * m + 1) x = ((m + 1 : ℕ) : ℂ) • x) : IsHalfFilled m x :=
  totalNumber_eigen_coordinate_zero (m + 1) x hx

theorem totalNumber_spinWedge (m : ℕ) (s : SourceSpinBasis (m + 1)) :
    totalNumber (2 * m + 1) (spinWedge m s) =
      ((m + 1 : ℕ) : ℂ) • spinWedge m s := by
  rw [spinWedge_eq_fockBasis, totalNumber_basis, spinOccupationSet_card]

theorem totalNumber_spinEmbedding (m : ℕ) (u : SourceSpinVector (m + 1)) :
    totalNumber (2 * m + 1) (spinEmbedding m u) =
      ((m + 1 : ℕ) : ℂ) • spinEmbedding m u := by
  change totalNumber (2 * m + 1) (∑ s, u s • spinWedge m s) =
    ((m + 1 : ℕ) : ℂ) • ∑ s, u s • spinWedge m s
  rw [map_sum]
  simp_rw [map_smul, totalNumber_spinWedge]
  simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem spinOccupationSet_range_iff (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∃ s, spinOccupationSet m s = A) ↔ ∀ i, occupationAt m A i = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    exact occupationAt_spinOccupationSet m s
  · intro hA
    exact ⟨occupationSpin m A, (onePerSite_eq_spinOccupationSet m A hA).symm⟩

theorem highOccupationIndex_range_iff (m : ℕ) (A : Finset (Fin ((2 * m + 1) + 1))) :
    (∃ B, highOccupationIndex m B = A) ↔
      A.card = m + 1 ∧ ¬ ∀ i, occupationAt m A i = 1 := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B.val.property, B.property⟩
  · rintro ⟨hcard, hdefect⟩
    exact ⟨⟨⟨A, hcard⟩, hdefect⟩, rfl⟩

theorem coordinateInclusion_restriction_apply {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (x : EuclideanSpace ℂ β) (b : β) :
    coordinateInclusion f (coordinateRestriction f x) b =
      if ∃ a, f a = b then x b else 0 := by
  classical
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [coordinateInclusion_apply_image f hf, coordinateRestriction_apply]
    simp
  · rw [ite_eq_right hb]
    exact coordinateInclusion_apply_outside f _ b (by simpa using hb)

theorem lowFock_projector_coordinates (m : ℕ) (x : Space (2 * m + 1)) :
    lowFockInclusion m (lowFockRestriction m (fockCoordinates (2 * m + 1) x)) =
      fockCoordinates (2 * m + 1) (lowProjection m x) := by
  ext A
  change coordinateInclusion _ (coordinateRestriction _ _) A = _
  rw [coordinateInclusion_restriction_apply _ (spinOccupationSet_injective m)]
  simp only [spinOccupationSet_range_iff, fockCoordinates_apply,
    lowProjection, occupationDiagonal, fockDiagonal_coordinate]
  split_ifs <;> simp

def highProjection (m : ℕ) : Module.End ℂ (Space (2 * m + 1)) :=
  fockDiagonal (fun A =>
    if A.card = m + 1 ∧ ¬ ∀ i, occupationAt m A i = 1 then 1 else 0)

theorem highFock_projector_coordinates (m : ℕ) (x : Space (2 * m + 1)) :
    highFockInclusion m (highFockRestriction m (fockCoordinates (2 * m + 1) x)) =
      fockCoordinates (2 * m + 1) (highProjection m x) := by
  ext A
  change coordinateInclusion _ (coordinateRestriction _ _) A = _
  rw [coordinateInclusion_restriction_apply _ (highOccupationIndex_injective m)]
  simp only [highOccupationIndex_range_iff, fockCoordinates_apply,
    highProjection, fockDiagonal_coordinate]
  split_ifs <;> simp

theorem highProjection_of_halfFilled_lowZero (m : ℕ) (x : Space (2 * m + 1))
    (hfill : IsHalfFilled m x) (hlow : lowProjection m x = 0) : highProjection m x = x := by
  apply (fockBasis (2 * m + 1)).repr.injective
  ext A
  rw [highProjection, fockDiagonal_coordinate]
  by_cases hcard : A.card = m + 1
  · by_cases hspin : ∀ i, occupationAt m A i = 1
    · have h := congrArg (fun y => (fockBasis (2 * m + 1)).repr y A) hlow
      simp [lowProjection, occupationDiagonal, fockDiagonal_coordinate, hspin] at h
      simp [hspin, h]
    · simp [hcard, hspin]
  · simp [hcard, hfill A hcard]

theorem lowProjection_transfer_spinWedge_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ : Fin 2) :
    lowProjection m (transfer (siteMode m i σ) (siteMode m j τ) (spinWedge m s)) = 0 := by
  apply lowProjection_eq_zero_of_numberEigen m i _ _
    (siteNumber_transfer_eigen m i i j σ τ _ _ (siteNumber_spinWedge m s i))
  norm_num [chargeShift, hij]

theorem lowProjection_siteHopping_spinWedge_zero (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    lowProjection m (siteHopping m i j (spinWedge m s)) = 0 := by
  simp only [siteHopping, twoSiteHopping, bondTransfer, LinearMap.add_apply, map_add,
    lowProjection_transfer_spinWedge_zero m s i j hij,
    lowProjection_transfer_spinWedge_zero m s j i (Ne.symm hij), add_zero]

variable {Edge : Type*} [Fintype Edge]

theorem totalNumber_commute_siteHopping (m : ℕ) (i j : Fin (m + 1)) :
    Commute (totalNumber (2 * m + 1)) (siteHopping m i j) := by
  exact ((totalNumber_commute_transfer _ _).add_right
    (totalNumber_commute_transfer _ _)).add_right
      ((totalNumber_commute_transfer _ _).add_right (totalNumber_commute_transfer _ _))

theorem totalNumber_commute_graphHopping (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    Commute (totalNumber (2 * m + 1)) (graphHopping m left right t) := by
  apply Commute.sum_right
  intro e _
  exact (totalNumber_commute_siteHopping m (left e) (right e)).smul_right (t e)

theorem graphHopping_preserves_halfFilling (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) (x : Space (2 * m + 1))
    (hx : totalNumber (2 * m + 1) x = ((m + 1 : ℕ) : ℂ) • x) :
    IsHalfFilled m (graphHopping m left right t x) := by
  apply isHalfFilled_of_totalNumber
  have h := LinearMap.congr_fun (totalNumber_commute_graphHopping m left right t).eq x
  change totalNumber (2 * m + 1) (graphHopping m left right t x) =
    graphHopping m left right t (totalNumber (2 * m + 1) x) at h
  rw [hx, map_smul] at h
  exact h

theorem lowProjection_graphHopping_spinEmbedding_zero (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (u : SourceSpinVector (m + 1)) :
    lowProjection m (graphHopping m left right t (spinEmbedding m u)) = 0 := by
  change lowProjection m (graphHopping m left right t (∑ s, u s • spinWedge m s)) = _
  simp only [graphHopping, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [lowProjection_siteHopping_spinWedge_zero m _ _ _ (hloop _),
    smul_zero, Finset.sum_const_zero]

/-- A true hop from an arbitrary spin state lies entirely in the actual
half-filled charge-defect space. -/
theorem highProjection_graphHopping_spinEmbedding (m : ℕ)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (u : SourceSpinVector (m + 1)) :
    highProjection m (graphHopping m left right t (spinEmbedding m u)) =
      graphHopping m left right t (spinEmbedding m u) :=
  highProjection_of_halfFilled_lowZero m _
    (graphHopping_preserves_halfFilling m left right t _ (totalNumber_spinEmbedding m u))
    (lowProjection_graphHopping_spinEmbedding_zero m left right t hloop u)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
