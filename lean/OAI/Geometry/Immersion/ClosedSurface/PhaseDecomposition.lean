import OAI.Geometry.Immersion.ClosedSurface.CompactPartition
import OAI.Geometry.Immersion.ClosedSurface.GridPhases

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates Set

lemma phase_square_partition_decomposition {ι : Type*} [Fintype ι]
    (P : ι → PhaseBasis) (χ : ι → ℝ) (hχ : ∑ a, (χ a)^2 = 1)
    (H : PhaseMean.Tensor) :
    ∑ a, ∑ i : Fin 3, ((χ a)^2 * (P a).Q i H) • covectorSquare ((P a).ξ i) = H := by
  calc
    _ = ∑ a, (χ a)^2 • H := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = (χ a)^2 • ∑ i : Fin 3, (P a).Q i H • covectorSquare ((P a).ξ i) := by
          rw [Finset.smul_sum]
          simp only [mul_smul]
        _ = (χ a)^2 • H := by rw [(P a).decomposition H]
    _ = (∑ a, (χ a)^2) • H := Finset.sum_smul.symm
    _ = H := by rw [hχ,one_smul]



lemma weighted_phase_coefficient_lower (P : PhaseBasis) (w : Fin 3 → ℝ)
    {W ε : ℝ} (hε : 0 < ε) (hW : 0 < W)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ W) (H : PhaseMean.Tensor) (i : Fin 3)
    (hQ : ε/2 ≤ P.Q i H) :
    (ε/2)/W^2 ≤ (P.weighted w (fun j => ne_of_gt (zero_lt_one.trans_le (hw j).1))).Q i H := by
  have hwi : 0 < w i := zero_lt_one.trans_le (hw i).1
  have hwsq : (w i)^2 ≤ W^2 := pow_le_pow_left₀ hwi.le (hw i).2 2
  change (ε/2)/W^2 ≤ (w i)^(-2 : ℤ) * P.Q i H
  rw [zpow_neg,zpow_ofNat]
  calc
    (ε/2)/W^2 ≤ (ε/2)/(w i)^2 :=
      (div_le_div_iff₀ (sq_pos_of_pos hW) (sq_pos_of_pos hwi)).mpr
        (mul_le_mul_of_nonneg_left hwsq (half_pos hε).le)
    _ ≤ P.Q i H/(w i)^2 := div_le_div_of_nonneg_right hQ (sq_nonneg _)
    _ = ((w i)^2)⁻¹ * P.Q i H := by rw [div_eq_mul_inv,mul_comm]





theorem compact_coordinate_polynomial_phase_data {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2)
    {K U : Set Base} (hKc : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hconv : Convex ℝ U) (R c A b L : ℝ)
    (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) (hL : 0 ≤ L) :
    ∃ z₀ D C W ε δ κ : ℝ, ∃ J : ℕ → ℝ,
      0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < D ∧ 1 ≤ C ∧ 0 < W ∧ 0 < ε ∧ 0 < δ ∧ 0 < κ ∧ (∀ j, 1 ≤ J j) ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ →
      ∀ F : RField 4, ContDiffOn ℝ ∞ F U → WeightedBound U z 3 A F →
        (∀ p ∈ U, ‖firstJetPair F p‖ ≤ R ∧
          c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2 ∧ b ≤ ‖realSecondTensor F p‖) →
      ∀ H : Base → PhaseMean.Tensor, (∀ p ∈ U, H p ∈ T) →
        (∀ x ∈ U, ∀ y ∈ U, ‖H y-H x‖ ≤ L*‖y-x‖) →
      ∃ (s : Finset PhaseGrid.Index) (P : {a // a ∈ s} → PhaseBasis)
        (w : {a // a ∈ s} × Fin 3 → ℝ),
        (s.card : ℝ) ≤ D/z^12 ∧ IsOpen (PhaseGrid.coverRegion s (z^6)) ∧
        K ⊆ PhaseGrid.coverRegion s (z^6) ∧ PhaseGrid.coverRegion s (z^6) ⊆ U ∧
        (∀ a i, ‖(P a).ξ i‖ ≤ C ∧ ‖(P a).Q i‖ ≤ C) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        (∀ a, ContDiffOn ℝ ∞ (PhaseGrid.normalizedCutoff s (z^6) a) (PhaseGrid.coverRegion s (z^6))) ∧
        (∀ a j x, x ∈ PhaseGrid.coverRegion s (z^6) →
          ‖iteratedFDeriv ℝ j (PhaseGrid.normalizedCutoff s (z^6) a) x‖ ≤ J j / z^(6*j)) ∧
        (∀ x ∈ PhaseGrid.coverRegion s (z^6), ∑ a ∈ s, (PhaseGrid.normalizedCutoff s (z^6) a x)^2 = 1) ∧
        (∀ a ∈ s, tsupport (PhaseGrid.normalizedCutoff s (z^6) a) ⊆ U) ∧
        (∀ a y G H', y ∈ tsupport (PhaseGrid.normalizedCutoff s (z^6) a.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 → ‖H'-H y‖ ≤ δ →
          c/2 ≤ NormalFrame.gramDet (firstJetPair G y).1 (firstJetPair G y).2 ∧
          b/2 ≤ ‖realSecondTensor G y‖ ∧ ∀ i, ε/2 ≤ (P a).Q i H' ∧
            (ε/4)*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y) (-((P a).ξ i).2,((P a).ξ i).1)‖ ∧
            Good (realSecondTensor G y) ((P a).ξ i)) ∧
        (∀ a d y G, a ≠ d → y ∈ tsupport (PhaseGrid.normalizedCutoff s (z^6) a.1.val) →
          y ∈ tsupport (PhaseGrid.normalizedCutoff s (z^6) d.1.val) →
          ‖firstJetPair F y-firstJetPair G y‖ ≤ z^4 →
          ‖secondJetTriple F y-secondJetTriple G y‖ ≤ z^4 →
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2).1)‖ ∧
          κ*‖realSecondTensor G y‖ ≤ ‖secondQuadratic (realSecondTensor G y)
            (-(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).2,(w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2).1)‖ ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2+w d • (P d.1).ξ d.2) ∧
          Good (realSecondTensor G y) (w a • (P a.1).ξ a.2-w d • (P d.1).ξ d.2)) := by
  obtain ⟨ε,C,δ,z₁,W,κ,hε,hC,hδ,hz₁,hz₁1,hW,hκ,hphases⟩ :=
    actual_polynomial_grid_phases hT hT0 hTd R c A b L hc hA hb hL
  obtain ⟨z₂,D,J,hz₂,hz₂1,hD,hJ,hpart⟩ :=
    PhaseGrid.compact_polynomial_square_partition hKc hU hKU
  refine ⟨min z₁ z₂,D,C,W,ε,δ,κ,J,lt_min hz₁ hz₂,
    (min_le_left _ _).trans hz₁1,hD,hC,hW,hε,hδ,hκ,hJ,?_⟩
  intro z hz hzsmall F hF hFb hmetric H hH hHLip
  obtain ⟨s,hcard,hopen,hinner,houter,hsub,hsmooth,hderiv,hsquares,hsupp⟩ :=
    hpart z hz (hzsmall.trans (min_le_right _ _))
  obtain ⟨P,w,hPB,hw,hpoint,hpair⟩ := hphases z hz (hzsmall.trans (min_le_left _ _))
    F U hU hconv hF hFb hmetric H hH hHLip s hsub
  refine ⟨s,P,w,hcard,hopen,hinner,houter,hPB,hw,hsmooth,hderiv,hsquares,hsupp,?_,?_⟩
  · intro a y G H' hy h1 h2 hH'
    exact hpoint a y G H' (PhaseGrid.normalizedCutoff_tsupport s (z^6) a.val hy) h1 h2 hH'
  · intro a d y G had hay hdy h1 h2
    exact hpair a d y G had (PhaseGrid.normalizedCutoff_tsupport s (z^6) a.1.val hay)
      (PhaseGrid.normalizedCutoff_tsupport s (z^6) d.1.val hdy) h1 h2

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
