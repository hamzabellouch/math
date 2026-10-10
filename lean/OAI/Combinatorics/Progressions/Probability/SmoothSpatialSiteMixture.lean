import OAI.Combinatorics.Progressions.Lattices.ResidueSpatialSiteExpansion
import OAI.Combinatorics.Progressions.Lattices.SmoothSpatialResidueMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem smoothSpatial_site_mixture {I J N X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype N] [DecidableEq N] [Fintype X]
    {L B : ℕ} {H ρ ξ ε : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ))
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (p : FiniteProbabilityWeights X) (C : X → Matrix (Unit ⊕ I) N ℤ)
    (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ y, p.weight y ≠ 0 → ∀ i j, |(C y i j : ℝ)| * Q j ≤ ξ * H)
    (hρ : 0 < ρ) (hscale : ρ ≤ H / L) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ) (hε : 0 < ε)
    (t : Finset ((Unit ⊕ I) → ℤ)) (D : X → ((Unit ⊕ I) → ℤ) → ℝ)
    (φ : ((Unit ⊕ I) → ℤ) → ℂ) (hD : ∀ y v, 0 ≤ D y v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (ht : ∀ v ∈ t, ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ 1) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA H L hH (by exact_mod_cast hL)
    let r := spatialSiteRadius ((m : ℝ)^Fintype.card (Unit ⊕ I)) (smoothSpatialDensityLip s B) ε
    ‖p.complexMean (fun y => 𝔼 v ∈ t,
        ((D y v * ((∏ _i : Unit ⊕ I, H) *
          (smoothSpatialOutputLaw root (scalarCubeDifferenceMatrix x) (C y) H L Q hH
            (by exact_mod_cast hL) hQ v).toReal) : ℝ) : ℂ) * φ v) -
      ∑ a : Matrix (Unit ⊕ I) N (ZMod m), 𝔼 v ∈ t,
        (p.fiberMean (fun y => integerResidueMatrix (C y) m) a (fun y => D y v) : ℂ) *
          spatialSiteApprox A (Matrix.fromCols A' (liftResidueMatrix a)) m f H 1 r v * φ v‖ ≤
      (smoothSpatialError N s B L ρ ξ + ε) * p.mean (fun y => 𝔼 v ∈ t, D y v) := by
  have hfirst := smoothSpatial_residue_mixture s x root hB hL hH hx hroot m hp p C Q hQ
    hξ0 hξ1 hC hρ hscale hscaleQ hlarge t D φ (fun y _ v _ => hD y v) hφ
  have hf := (smoothSpatialKernelDensity_bounds s x root hB hL hH hx hroot).2
  have hsecond := residueSpatialWeight_site_family _ _ m hp _ hf H hε p
    (fun y => integerResidueMatrix (C y) m) t D φ hD hφ ht
  rw [Real.coe_toNNReal _ (smoothSpatialDensityLip_nonneg s B)] at hsecond
  simp only [Complex.ofReal_mul] at hfirst ⊢
  refine le_trans ?_ ((add_le_add hfirst hsecond).trans_eq (by ring))
  simp only [← dist_eq_norm]
  exact dist_triangle _ _ _

end Erdos3

end

end OAI
