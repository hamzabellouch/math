import OAI.Combinatorics.Progressions.Linear.SmoothSpatialKernelRegularity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem smoothSpatial_residue_mixture {I J N X : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype N] [DecidableEq N] [Fintype X]
    {L B : ℕ} {H ρ ξ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ))
    (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (p : FiniteProbabilityWeights X) (C : X → Matrix (Unit ⊕ I) N ℤ)
    (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ y, p.weight y ≠ 0 → ∀ i j, |(C y i j : ℝ)| * Q j ≤ ξ * H)
    (hρ : 0 < ρ) (hscale : ρ ≤ H / L) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ)
    (outputs : Finset ((Unit ⊕ I) → ℤ)) (D : X → ((Unit ⊕ I) → ℤ) → ℝ)
    (φ : ((Unit ⊕ I) → ℤ) → ℂ)
    (hD : ∀ y, p.weight y ≠ 0 → ∀ v ∈ outputs, 0 ≤ D y v)
    (hφ : ∀ v ∈ outputs, ‖φ v‖ ≤ 1) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA
      H L hH (by exact_mod_cast hL)
    ‖p.complexMean (fun y => 𝔼 v ∈ outputs,
        ((D y v * ((∏ _i : Unit ⊕ I, H) *
          (smoothSpatialOutputLaw root (scalarCubeDifferenceMatrix x) (C y) H L Q hH
            (by exact_mod_cast hL) hQ v).toReal) : ℝ) : ℂ) * φ v) -
      ∑ r : Matrix (Unit ⊕ I) N (ZMod m), 𝔼 v ∈ outputs,
        ((p.fiberMean (fun y => integerResidueMatrix (C y) m) r (fun y => D y v) *
          residueSpatialWeight A A' (fun _ => H) f r v : ℝ) : ℂ) * φ v‖ ≤
      smoothSpatialError N s B L ρ ξ * p.mean (fun y => 𝔼 v ∈ outputs, D y v) := by
  apply weightedResidueSpatial_mixture_comparison p outputs _ _ C _ _ m hperiod _ D φ hD hφ
  intro y hy v _
  exact smoothSpatial_original_error s x root hB hL hH hx hroot (C y) Q hQ hξ0 hξ1
    (hC y hy) hρ hscale hscaleQ hlarge v

end Erdos3

end

end OAI
