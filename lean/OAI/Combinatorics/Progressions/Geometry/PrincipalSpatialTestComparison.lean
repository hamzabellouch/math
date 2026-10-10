import OAI.Combinatorics.Progressions.Probability.PrincipalTestMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalSpatial_mixed_test_comparison {D A α J N V : Type*}
    [Fintype D] [DecidableEq D] [Fintype A] [Fintype α] [DecidableEq α]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    {ℓ M : ℕ} {ρ ξ r ε : ℝ} (s : α ↪ J)
    (x : J → IntegerScalarCubeBox α ℓ) (root : J → ℤ)
    (hM : 0 < M) (hℓ : 0 < ℓ) (hx : GoodScalarKernelTuple s (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (ℓ : ℤ)) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hp : integerScalarLattice (Unit ⊕ α) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (c : A → N → ℤ) (index : A → N → PrincipalTupleIndex B h)
    (H : A → ℝ) (Q : A → N → ℝ) (hH : ∀ a, 0 < H a) (hQ : ∀ a n, 0 < Q a n)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ a n, ((|c a n| : ℤ)+(L (index a n) : ℤ) : ℝ)*Q a n ≤ ξ*H a)
    (hρ : 0 < ρ) (hscale : ∀ a, ρ ≤ H a/ℓ) (hscaleQ : ∀ a n, ρ ≤ Q a n)
    (hlarge : smoothSpatialMeshThreshold α J N ℓ ≤ ρ) (hr : 0 < r)
    (t : Finset V) (out : V → A → (Unit ⊕ α) → ℤ)
    (W : PrincipalIntegerTuples B h α L → V → ℝ)
    (T : (PrincipalTupleIndex B h → Option α → ZMod m) → (V → ℂ) → ℂ)
    (hT : ∀ rr z ψ, T rr (fun v => z * ψ v) = z * T rr ψ)
    (hW : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → ∀ v ∈ t, 0 ≤ W y v)
    (hmass : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → (∑ v ∈ t, W y v) ≤ 1)
    (hbox : ∀ v ∈ t, ∀ a i, |((spatialStar (out v a) i : ℤ) : ℝ)/H a| ≤ 1)
    (hcoeff : ∀ rr ψ, (∀ v ∈ t, ‖ψ v‖ ≤ 1) →
      ‖(principalResidueWeights B h L hL m hm rr hsize).complexMean
        (fun y => ∑ v ∈ t, (W y v : ℂ) * ψ v) - T rr ψ‖ ≤ ε)
    (φ : V → ℂ) (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1) :
    let P := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let F := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hP := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hM)) hx
    let f := fun a => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hP
      (H a) ℓ (hH a) (by exact_mod_cast hℓ)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let E := smoothSpatialError N s M ℓ ρ ξ
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    let site := fun rr v => ∏ a, spatialSiteApprox P
      (Matrix.fromCols F (liftResidueMatrix (principalSpatialResidueColumns m (c a) (index a) rr)))
      m (f a) (H a) 1 r (out v a)
    ‖source.complexMean (fun y => ∑ v ∈ t, (W y v : ℂ) *
        (((∏ a, ∏ _i : Unit ⊕ α, H a) *
          (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
            (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
            (by exact_mod_cast hℓ) hQ (out v)).toReal : ℝ) : ℂ) * φ v) -
      residues.complexMean (fun rr => T rr (fun v => site rr v * φ v))‖ ≤
      Fintype.card A * (E + 4 * G * smoothSpatialDensityLip s M * r) *
        (1 + G * smoothSpatialDensityCap s M + E)^Fintype.card A +
        (1 + (G * smoothSpatialDensityCap s M)^Fintype.card A) * ε := by
  dsimp only
  have hE := smoothSpatialError_nonneg N s M ℓ hρ.le hξ0
  have hC := smoothSpatialDensityCap_nonneg s M
  have hK := smoothSpatialDensityLip_nonneg s M
  let Csite := ((m : ℝ)^Fintype.card (Unit ⊕ α) * smoothSpatialDensityCap s M)^Fintype.card A
  have hCsite : 0 ≤ Csite := by dsimp [Csite]; positivity
  have hcap (rr) (v) (hv : v ∈ t) := residueSpatialSite_norm_le
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
    (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) m hp
    (fun a => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x)
      (goodScalarKernelTuple_spatial_det_ne_zero s x root (one_div_pos.mpr (by exact_mod_cast hM)) hx)
        (H a) ℓ (hH a) (by exact_mod_cast hℓ)) H zero_lt_one hr hC
    (fun a => (smoothSpatialKernelDensity_bounds s x root hM hℓ (hH a) hx hroot).1)
    (fun a => principalSpatialResidueColumns m (c a) (index a) rr) (out v) (hbox v hv)
  have he := principal_mixed_test_comparison B h L hL m hm hsize t W
    (fun y v => (((∏ a, ∏ _i : Unit ⊕ α, H a) *
      (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
        (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
        (by exact_mod_cast hℓ) hQ (out v)).toReal : ℝ) : ℂ))
    _ T hT (fun _ => 1 + Csite) (fun _ => ε) (fun _ => by positivity)
    (fun rr v hv => (hcap rr v hv).trans (le_add_of_nonneg_left zero_le_one))
    (δ := Fintype.card A * (smoothSpatialError N s M ℓ ρ ξ +
      4 * (m : ℝ)^Fintype.card (Unit ⊕ α) * smoothSpatialDensityLip s M * r) *
      (1 + (m : ℝ)^Fintype.card (Unit ⊕ α) * smoothSpatialDensityCap s M +
        smoothSpatialError N s M ℓ ρ ξ)^Fintype.card A)
    (by positivity) hW hmass
    (fun y _ v hv => principalVectorSpatial_site_error s x root hM hℓ hx hroot m hp c index H Q hH hQ
      hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hr y (out v) (hbox v hv)) hcoeff φ hφ
  simpa only [FiniteProbabilityWeights.mean_const] using he

end Erdos3

end

end OAI
