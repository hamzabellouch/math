import OAI.Analysis.PureInfiniteness.SpectralCharacters
import OAI.Analysis.PureInfiniteness.JointSpectralEstimates

namespace OAI

/-! Finite joint partitions with an explicit nonunital origin condition.
The reconstruction bound is the mesh size; no estimate depends on the
number of lattice cells. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

variable {D I : Type*} [CommCStarAlgebra D] [Fintype I] [DecidableEq I]

def jointGrid (N : ℤ) (_ : I) : Finset ℤ := Finset.Icc 0 (N + 1)

def jointGridReconstruction (a : I → D) (r : ℝ) (N : ℤ) (i : I) : D :=
  ∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
    ((r * (k i : ℝ) : ℝ) : ℂ) • productGridHatElement a r _ k

lemma scalarStarHom_reconstruction (φ : D →⋆ₐ[ℂ] ℂ) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (r : ℝ) (N : ℤ) (i : I) :
    φ (jointGridReconstruction a r N i) =
      ((r * ∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
        (k i : ℝ) * productGridHat _ k (fun j => (φ (a j)).re / r) : ℝ) : ℂ) := by
  unfold jointGridReconstruction
  simp only [map_sum, map_smul, scalarStarHom_productGridHat φ a ha]
  rw [Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_eq_mul, Complex.ofReal_mul, mul_assoc]

lemma norm_jointGridReconstruction_sub_le (a : I → D) (ha : ∀ i, IsSelfAdjoint (a i))
    (r : ℝ) (hr : 0 < r) (N : ℤ)
    (hN : ∀ χ i, 0 ≤ (spectralCharacter χ (a i)).re / r ∧
      (spectralCharacter χ (a i)).re / r ≤ (N : ℝ)) (i : I) :
    ‖a i - jointGridReconstruction a r N i‖ ≤ r := by
  apply norm_le_of_spectralCharacters _ _ hr.le
  intro χ
  let x (j : I) := (spectralCharacter χ (a j)).re / r
  have hp (j : I) : ∑ k ∈ jointGrid (I := I) N j, gridHat k (x j) = 1 :=
    sum_gridHat_eq_one 0 N (x j) (by simpa only [Int.cast_zero] using (hN χ j).1)
      (hN χ j).2
  have hm : ∑ k ∈ jointGrid (I := I) N i, (k : ℝ) * gridHat k (x i) = x i :=
    sum_gridHat_first_moment 0 N (x i)
      (by simpa only [Int.cast_zero] using (hN χ i).1) (hN χ i).2
  have hi (j : I) (k : ℤ) (hk : k ∈ jointGrid (I := I) N j) : 0 ≤ k :=
    (Finset.mem_Icc.mp hk).1
  have hb := joint_spectral_retained_moment (jointGrid (I := I) N) x i hp hm hi
  rw [map_sub, scalarStarHom_reconstruction _ a ha,
    scalarStarHom_eq_real _ (ha i)]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : (spectralCharacter χ (a i)).re -
      r * (∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
        (k i : ℝ) * productGridHat _ k x) =
      r * (x i - ∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
        (k i : ℝ) * productGridHat _ k x) := by
    dsimp only [x]
    field_simp
  rw [he, abs_mul, abs_of_pos hr]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hr.le

omit [DecidableEq I] in
lemma jointGridPlateau_in_kernel (φ : D →⋆ₐ[ℂ] ℂ) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (hzero : ∀ i, φ (a i) = 0)
    (r : ℝ) (N : ℤ) (k : SpectralGridCell (jointGrid (I := I) N))
    (hk : retainedSpectralCell _ k) :
    φ (productGridPlateauElement a r _ k) = 0 := by
  rw [scalarStarHom_productGridPlateau φ a ha]
  simp only [hzero, Complex.zero_re, zero_div]
  exact_mod_cast productGridPlateau_zero_at_origin _ k hk

omit [DecidableEq I] in
lemma jointGridHat_in_kernel (φ : D →⋆ₐ[ℂ] ℂ) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (hzero : ∀ i, φ (a i) = 0)
    (r : ℝ) (N : ℤ) (k : SpectralGridCell (jointGrid (I := I) N))
    (hk : retainedSpectralCell _ k) :
    φ (productGridHatElement a r _ k) = 0 := by
  have h := congrArg φ (productGridPlateauElement_mul_hat a r _ k)
  rw [map_mul, jointGridPlateau_in_kernel φ a ha hzero r N k hk, zero_mul] at h
  exact h.symm

section Positive
variable [PartialOrder D] [StarOrderedRing D]

omit [DecidableEq I] in
lemma jointGrid_bound_at_ceil (a : I → D) (ha : ∀ i, 0 ≤ a i)
    (r : ℝ) (hr : 0 < r) :
    ∀ χ i, 0 ≤ (spectralCharacter χ (a i)).re / r ∧
      (spectralCharacter χ (a i)).re / r ≤ (⌈(∑ i, ‖a i‖) / r⌉ : ℤ) := by
  intro χ i
  have hp : 0 ≤ (spectralCharacter χ (a i)).re :=
    (RCLike.nonneg_iff.mp (map_nonneg (spectralCharacter χ) (ha i))).1
  refine ⟨div_nonneg hp hr.le, ?_⟩
  calc
    _ ≤ ‖a i‖ / r := by
      apply div_le_div_of_nonneg_right _ hr.le
      exact (Complex.re_le_norm _).trans
        (NonUnitalStarAlgHom.norm_apply_le (spectralCharacter χ) (a i))
    _ ≤ (∑ j, ‖a j‖) / r := by
      apply div_le_div_of_nonneg_right _ hr.le
      exact Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)
    _ ≤ _ := Int.le_ceil _

omit [DecidableEq I] in
lemma exists_jointGrid_bound (a : I → D) (ha : ∀ i, 0 ≤ a i)
    (r : ℝ) (hr : 0 < r) :
    ∃ N : ℤ, ∀ χ i, 0 ≤ (spectralCharacter χ (a i)).re / r ∧
      (spectralCharacter χ (a i)).re / r ≤ (N : ℝ) :=
  ⟨_, jointGrid_bound_at_ceil a ha r hr⟩

omit [PartialOrder D] [StarOrderedRing D] in
lemma norm_sum_retained_hats_le (a : I → D) (ha : ∀ i, IsSelfAdjoint (a i))
    (r : ℝ) (N : ℤ)
    (hN : ∀ χ i, 0 ≤ (spectralCharacter χ (a i)).re / r ∧
      (spectralCharacter χ (a i)).re / r ≤ (N : ℝ)) :
    ‖∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
      productGridHatElement a r _ k‖ ≤ 1 := by
  apply norm_le_of_spectralCharacters _ _ zero_le_one
  intro χ
  rw [map_sum]
  simp_rw [scalarStarHom_productGridHat _ a ha]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  let x (i : I) := (spectralCharacter χ (a i)).re / r
  have hp (i : I) : ∑ k ∈ jointGrid (I := I) N i, gridHat k (x i) = 1 :=
    sum_gridHat_eq_one 0 N (x i) (by simpa only [Int.cast_zero] using (hN χ i).1)
      (hN χ i).2
  rw [abs_of_nonneg (Finset.sum_nonneg (fun k _ => productGridHat_nonneg _ k x))]
  calc
    _ ≤ ∑ k : SpectralGridCell (jointGrid (I := I) N), productGridHat _ k x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun k _ _ => productGridHat_nonneg _ k x)
    _ = 1 := sum_productGridHat _ x hp

end Positive
end WeakPureInfiniteness

end

end OAI
