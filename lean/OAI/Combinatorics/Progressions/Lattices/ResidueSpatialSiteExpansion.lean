import OAI.Combinatorics.Progressions.Geometry.SpatialSiteShift

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem residueSpatialWeight_site_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (H : ℝ) {r : ℝ} (hr : 0 < r) (a : Matrix (Unit ⊕ I) N (ZMod m))
    (v : (Unit ⊕ I) → ℤ) (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ 1) :
    ‖(residueSpatialWeight A B (fun _ => H) f a v : ℂ) -
      spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix a)) m f H 1 r v‖ ≤
        4 * (m : ℝ)^Fintype.card (Unit ⊕ I) * K * r := by
  have hpfull : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage A (Matrix.fromCols B (liftResidueMatrix a)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi : ((pivotFullImage A (Matrix.fromCols B (liftResidueMatrix a))).toAddSubgroup.index : ℝ) ≤
      (m : ℝ)^Fintype.card (Unit ⊕ I) := by
    exact_mod_cast residueLatticeImage_index_le _ m hpfull
  exact spatialSiteApprox_error _ _ m hpfull f hf hi zero_lt_one hr H v hv

theorem residueSpatialWeight_site_family {I J N X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype N] [DecidableEq N] [Fintype X]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (H : ℝ) {ε : ℝ} (hε : 0 < ε)
    (p : FiniteProbabilityWeights X) (F : X → Matrix (Unit ⊕ I) N (ZMod m))
    (t : Finset ((Unit ⊕ I) → ℤ)) (D : X → ((Unit ⊕ I) → ℤ) → ℝ)
    (φ : ((Unit ⊕ I) → ℤ) → ℂ) (hD : ∀ x v, 0 ≤ D x v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (ht : ∀ v ∈ t, ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ 1) :
    let r := spatialSiteRadius ((m : ℝ)^Fintype.card (Unit ⊕ I)) K ε
    ‖(∑ a, 𝔼 v ∈ t, (p.fiberMean F a (fun x => D x v) : ℂ) *
        (residueSpatialWeight A B (fun _ => H) f a v : ℂ) * φ v) -
      (∑ a, 𝔼 v ∈ t, (p.fiberMean F a (fun x => D x v) : ℂ) *
        spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix a)) m f H 1 r v * φ v)‖ ≤
      ε * p.mean (fun x => 𝔼 v ∈ t, D x v) := by
  have hG : 0 ≤ (m : ℝ)^Fintype.card (Unit ⊕ I) := by positivity
  have hr := spatialSiteRadius_pos hG K.coe_nonneg hε
  apply norm_fiber_site_replacement p F t D _ _ φ hD hφ
  intro a v hv
  exact (residueSpatialWeight_site_error A B m hp f hf H hr a v (ht v hv)).trans
    (spatialSiteRadius_error hG K.coe_nonneg hε.le)

end Erdos3

end

end OAI
