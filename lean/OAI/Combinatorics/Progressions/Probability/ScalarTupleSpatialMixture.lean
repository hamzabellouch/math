import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
import OAI.Combinatorics.Progressions.Lattices.SmoothSpatialResidueMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem goodScalarKernelTuple_spatial_mixture {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} {H ρ ξ : ℝ}
    (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hH : 0 < H)
    (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x) (hroot : ∀ j, |root j| ≤ (L : ℤ))
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hρ : 0 < ρ) (hscale : ρ ≤ H / L)
    (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA
      H L hH (by exact_mod_cast hL)
    ∃ (m : ℕ) (hm : 0 < m), m ≤ B ∧
      letI : NeZero m := ⟨hm.ne'⟩
      ∀ (T : N → ℕ) (c : N → ℤ)
        (axis : ∀ j, FiniteProbabilityWeights (IntegerScalarCubeBox I (T j)))
        (Q : N → ℝ) (hQ : ∀ j, 0 < Q j),
        (∀ j, ((|c j| : ℤ) + (T j : ℤ) : ℝ) * Q j ≤ ξ * H) →
        (∀ j, ρ ≤ Q j) →
        ∀ (outputs : Finset ((Unit ⊕ I) → ℤ))
          (D : (∀ j, IntegerScalarCubeBox I (T j)) → ((Unit ⊕ I) → ℤ) → ℝ)
          (φ : ((Unit ⊕ I) → ℤ) → ℂ),
          (∀ y, ∀ v ∈ outputs, 0 ≤ D y v) → (∀ v ∈ outputs, ‖φ v‖ ≤ 1) →
          let p := FiniteProbabilityWeights.pi axis
          let C := scalarTupleSpatialColumns T c
          ‖p.complexMean (fun y => 𝔼 v ∈ outputs,
              ((D y v * ((∏ _i : Unit ⊕ I, H) *
                (smoothSpatialOutputLaw root (scalarCubeDifferenceMatrix x) (C y) H L Q hH
                  (by exact_mod_cast hL) hQ v).toReal) : ℝ) : ℂ) * φ v) -
            ∑ r : Matrix (Unit ⊕ I) N (ZMod m), 𝔼 v ∈ outputs,
              ((p.fiberMean (fun y => integerResidueMatrix (C y) m) r (fun y => D y v) *
                residueSpatialWeight A A' (fun _ => H) f r v : ℝ) : ℂ) * φ v‖ ≤
            smoothSpatialError N s B L ρ ξ * p.mean (fun y => 𝔼 v ∈ outputs, D y v) := by
  obtain ⟨m, hm, hmB, hp⟩ := goodScalarKernelTuple_selected_period s x root hx
  refine ⟨m, hm, hmB, ?_⟩
  let : NeZero m := ⟨hm.ne'⟩
  intro T c axis Q hQ hwidth hscaleQ outputs D φ hD hφ
  exact smoothSpatial_residue_mixture s x root hB hL hH hx hroot m hp
    (FiniteProbabilityWeights.pi axis) (scalarTupleSpatialColumns T c) Q hQ hξ0 hξ1
    (fun y _ => scalarTupleSpatialColumns_scaled_bound T c Q (fun j => (hQ j).le) hwidth y)
    hρ hscale hscaleQ hlarge outputs D φ (fun y _ => hD y) hφ

end Erdos3

end

end OAI
