import OAI.Analysis.PureInfiniteness.SpectralGrid

namespace OAI

/-! Finite spectral localization with a uniform overlap bound.
These are the one-coordinate building blocks of KR02 Remark 7.5. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gridHatElement (a : A) (r : ℝ) (k : ℤ) : A :=
  cfc (fun x : ℝ => gridHat k (x / r)) a

def gridPlateauElement (a : A) (r : ℝ) (k : ℤ) : A :=
  cfc (fun x : ℝ => gridPlateau k (x / r)) a

lemma gridHatElement_nonneg (a : A) (r : ℝ) (k : ℤ) :
    0 ≤ gridHatElement a r k :=
  cfc_nonneg (fun x _ => gridHat_nonneg k (x / r))

lemma gridPlateauElement_nonneg (a : A) (r : ℝ) (k : ℤ) :
    0 ≤ gridPlateauElement a r k :=
  cfc_nonneg (fun x _ => (gridPlateau_bounds k (x / r)).1)

omit [PartialOrder A] [StarOrderedRing A] in
lemma gridPlateauElement_mul_gridHatElement (a : A)
    (r : ℝ) (k : ℤ) :
    gridPlateauElement a r k * gridHatElement a r k = gridHatElement a r k := by
  dsimp only [gridPlateauElement, gridHatElement]
  have hf : Continuous (fun x : ℝ => gridPlateau k (x / r)) :=
    (continuous_gridPlateau k).comp (continuous_id.div_const r)
  have hg : Continuous (fun x : ℝ => gridHat k (x / r)) :=
    (continuous_gridHat k).comp (continuous_id.div_const r)
  rw [← cfc_mul (fun x : ℝ => gridPlateau k (x / r))
    (fun x : ℝ => gridHat k (x / r)) a hf.continuousOn hg.continuousOn]
  apply cfc_congr
  intro x _
  exact gridPlateau_mul_gridHat k (x / r)

omit [PartialOrder A] [StarOrderedRing A] in
lemma sum_gridHatElement_eq_one (a : A) (ha : IsSelfAdjoint a)
    (r : ℝ) (lo hi : ℤ)
    (hspec : ∀ x ∈ spectrum ℝ a, (lo : ℝ) ≤ x / r ∧ x / r ≤ (hi : ℝ)) :
    ∑ k ∈ Finset.Icc lo (hi + 1), gridHatElement a r k = 1 := by
  dsimp only [gridHatElement]
  rw [← cfc_sum (fun k x => gridHat k (x / r)) a _
    (fun k _ => ((continuous_gridHat k).comp (continuous_id.div_const r)).continuousOn)]
  calc
    _ = cfc (fun _ : ℝ => 1) a := by
      apply cfc_congr
      intro x hx
      simpa only [Finset.sum_apply] using
        sum_gridHat_eq_one lo hi (x / r) (hspec x hx).1 (hspec x hx).2
    _ = 1 := by rw [cfc_const 1 a ha]; simp

omit [PartialOrder A] [StarOrderedRing A] in
/-- The constant 5 depends only on one-dimensional overlap, not the number of
spectral cells. This keeps subsequent cp estimates uniform under refinement. -/
lemma norm_sum_gridPlateauElement_le (a : A) (r : ℝ) (s : Finset ℤ) :
    ‖∑ k ∈ s, gridPlateauElement a r k‖ ≤ 5 := by
  dsimp only [gridPlateauElement]
  rw [← cfc_sum (fun k x => gridPlateau k (x / r)) a _
    (fun k _ => ((continuous_gridPlateau k).comp (continuous_id.div_const r)).continuousOn)]
  apply norm_cfc_le (by norm_num)
  intro x _
  simp only [Finset.sum_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun k _ => (gridPlateau_bounds k (x / r)).1))]
  exact sum_gridPlateau_le_five s (x / r)

end WeakPureInfiniteness

end

end OAI
