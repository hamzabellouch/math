import OAI.Analysis.KadisonKastler.InfiniteCornerInflation

namespace OAI

/-! # The canonical countable matrix corner

The coordinate injections and evaluations on the Hilbert direct sum give
actual matrix units.  Their initial corner is canonically isometric to
the original Hilbert space, and their diagonal projections sum strongly
to the identity.
-/

namespace KadisonKastler

noncomputable section

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def canonicalSingle (i : ℕ) : H →L[ℂ] CountableHilbertSum H :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i

def canonicalCoordinate (i : ℕ) : CountableHilbertSum H →L[ℂ] H :=
  lp.evalCLM ℂ (fun _ : ℕ => H) 2 i

@[simp] theorem canonicalSingle_apply (i : ℕ) (x : H) :
    canonicalSingle H i x = lp.single 2 i x := rfl

@[simp] theorem canonicalCoordinate_apply (i : ℕ) (x : CountableHilbertSum H) :
    canonicalCoordinate H i x = x i := rfl

def canonicalMatrixUnit (i j : ℕ) : CountableHilbertSum H →L[ℂ] CountableHilbertSum H :=
  (canonicalSingle H i).comp (canonicalCoordinate H j)

@[simp] theorem canonicalMatrixUnit_apply (i j : ℕ) (x : CountableHilbertSum H) :
    canonicalMatrixUnit H i j x = lp.single 2 i (x j) := rfl

theorem canonicalMatrixUnit_mul (i j k l : ℕ) :
    canonicalMatrixUnit H i j * canonicalMatrixUnit H k l =
      if j = k then canonicalMatrixUnit H i l else 0 := by
  ext x m
  by_cases h : j = k
  · subst k
    simp [mul_apply_eq_comp, canonicalMatrixUnit_apply, lp.single_apply]
  · simp [mul_apply_eq_comp, canonicalMatrixUnit_apply, lp.single_apply, h]

/-- The closed subspace supported at coordinate zero. -/
def canonicalInitialSpace : Submodule ℂ (CountableHilbertSum H) :=
  (canonicalSingle H 0).range

@[simp] theorem mem_canonicalInitialSpace (x : CountableHilbertSum H) :
    x ∈ canonicalInitialSpace H ↔ ∃ y : H, lp.single 2 0 y = x := Iff.rfl

/-- The initial coordinate has exactly the original Hilbert norm. -/
def canonicalInitialEquiv : H ≃ₗᵢ[ℂ] canonicalInitialSpace H where
  toFun x := ⟨lp.single 2 0 x, x, rfl⟩
  invFun x := x.val 0
  left_inv x := by simp [lp.single_apply]
  right_inv x := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change lp.single 2 0 (x.val 0) = x.val
    rw [← hy]
    simp [canonicalSingle, lp.single_apply]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (canonicalSingle H 0) x y
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (canonicalSingle H 0) c x
  norm_map' x := by
    change ‖(lp.single 2 0 x : CountableHilbertSum H)‖ = ‖x‖
    exact lp.norm_single (E := fun _ : ℕ => H) (p := 2) (by norm_num) 0 x

@[simp] theorem canonicalInitialEquiv_apply (x : H) :
    (canonicalInitialEquiv H x : CountableHilbertSum H) = lp.single 2 0 x := rfl

@[simp] theorem canonicalInitialEquiv_symm_apply (x : canonicalInitialSpace H) :
    (canonicalInitialEquiv H).symm x = x.val 0 := rfl

variable [CompleteSpace H]

instance canonicalInitialSpaceComplete : CompleteSpace (canonicalInitialSpace H) :=
  ((canonicalInitialEquiv H).symm.isometry.isUniformInducing.completeSpace_congr
    (canonicalInitialEquiv H).symm.surjective).mpr inferInstance

theorem canonicalSingle_adjoint (i : ℕ) :
    (canonicalSingle H i).adjoint = canonicalCoordinate H i := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact (lp.inner_single_right (𝕜 := ℂ) i y x).symm

theorem canonicalMatrixUnit_star (i j : ℕ) :
    star (canonicalMatrixUnit H i j) = canonicalMatrixUnit H j i := by
  have hc : (canonicalCoordinate H j).adjoint = canonicalSingle H j := by
    rw [← canonicalSingle_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [canonicalMatrixUnit, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, canonicalSingle_adjoint, hc]

theorem canonicalMatrixUnit_zero_zero :
    canonicalMatrixUnit H 0 0 = (canonicalInitialSpace H).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Eq.symm
  apply (canonicalInitialSpace H).eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨x 0, rfl⟩
  · intro w hw
    obtain ⟨y, rfl⟩ := hw
    change inner ℂ (x - lp.single 2 0 (x 0)) (lp.single 2 0 y) = 0
    rw [lp.inner_single_right]
    simp [lp.single_apply]

/-- The standard countable matrix units on the Hilbert direct sum. -/
def canonicalMatrixCorner : FullMatrixCorner (canonicalInitialSpace H) where
  entry := canonicalMatrixUnit H
  star_entry := canonicalMatrixUnit_star H
  mul_entry := canonicalMatrixUnit_mul H
  zero_zero := canonicalMatrixUnit_zero_zero H
  total x := lp.hasSum_single (by norm_num) x

@[simp] theorem canonicalMatrixCorner_entry (i j : ℕ) :
    (canonicalMatrixCorner H).entry i j = canonicalMatrixUnit H i j := rfl

@[simp] theorem canonicalMatrixCorner_column (i : ℕ) (x : H) :
    (canonicalMatrixCorner H).column i (canonicalInitialEquiv H x) =
      lp.single 2 i x := by
  change canonicalMatrixUnit H i 0 (lp.single 2 0 x) = _
  rw [canonicalMatrixUnit_apply]
  simp [lp.single_apply]

theorem canonicalMatrixCorner_matrixEntry (T : CountableHilbertSum H →L[ℂ]
    CountableHilbertSum H) (i j : ℕ) (x : H) :
    (canonicalInitialEquiv H).symm
      ((canonicalMatrixCorner H).matrixEntry T i j (canonicalInitialEquiv H x)) =
      (T (lp.single 2 j x)) i := by
  apply ext_inner_left ℂ
  intro y
  rw [← (canonicalInitialEquiv H).inner_map_map]
  rw [LinearIsometryEquiv.apply_symm_apply]
  change inner ℂ (canonicalInitialEquiv H y)
      (((canonicalMatrixCorner H).column i).toContinuousLinearMap.adjoint
        (T ((canonicalMatrixCorner H).column j (canonicalInitialEquiv H x)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ ((canonicalMatrixCorner H).column i (canonicalInitialEquiv H y))
    (T ((canonicalMatrixCorner H).column j (canonicalInitialEquiv H x))) = _
  rw [canonicalMatrixCorner_column, canonicalMatrixCorner_column, lp.inner_single_left]

end

end KadisonKastler

end OAI
