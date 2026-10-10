import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalSpatial_joint_test {D A α J N W : Type*}
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
    (hlarge : smoothSpatialMeshThreshold α J N ℓ ≤ ρ) (hr : 0 < r) (hε : 0 ≤ ε)
    (tv : Finset (A → (Unit ⊕ α) → ℤ)) (tw : Finset W)
    (coeff : PrincipalIntegerTuples B h α L → W → ℝ)
    (target : (PrincipalTupleIndex B h → Option α → ZMod m) → (W → ℂ) → ℂ)
    (hcoeff0 : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ w ∈ tw, 0 ≤ coeff y w)
    (hmass : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      (∑ w ∈ tw, coeff y w) ≤ 1)
    (hbox : ∀ v ∈ tv, ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ)/H a| ≤ 1)
    (hcoeff : ∀ rr ψ, (∀ w ∈ tw, ‖ψ w‖ ≤ 1) →
      ‖(principalResidueWeights B h L hL m hm rr hsize).complexMean
        (fun y => ∑ w ∈ tw, (coeff y w : ℂ) * ψ w) - target rr ψ‖ ≤ ε)
    (φ : (A → (Unit ⊕ α) → ℤ) → W → ℂ)
    (hφ : ∀ v ∈ tv, ∀ w ∈ tw, ‖φ v w‖ ≤ 1) :
    let P := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let F := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hP := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hM)) hx
    let f := fun a => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hP
      (H a) ℓ (hH a) (by exact_mod_cast hℓ)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let E := smoothSpatialError N s M ℓ ρ ξ
    let scale := ∏ a, ∏ _i : Unit ⊕ α, H a
    let error := Fintype.card A * (E + 4 * G * smoothSpatialDensityLip s M * r) *
      (1 + G * smoothSpatialDensityCap s M + E)^Fintype.card A
    let Δ := error / scale * tv.card
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    let site := fun rr v => ∏ a, spatialSiteApprox P
      (Matrix.fromCols F (liftResidueMatrix (principalSpatialResidueColumns m (c a) (index a) rr)))
      m (f a) (H a) 1 r (v a)
    ‖source.complexMean (fun y => ∑ v ∈ tv,
        ((smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
          (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
          (by exact_mod_cast hℓ) hQ v).toReal : ℂ) *
        (∑ w ∈ tw, (coeff y w : ℂ) * φ v w)) -
      residues.complexMean (fun rr => ∑ v ∈ tv, (site rr v / (scale : ℂ)) * target rr (φ v))‖ ≤
      Δ + (1 + Δ) * ε := by
  dsimp only
  let scale := ∏ a, ∏ _i : Unit ⊕ α, H a
  have hscale0 : 0 < scale := Finset.prod_pos (fun a _ => Finset.prod_pos (fun _ _ => hH a))
  have hscaleC : (scale : ℂ) ≠ 0 := by exact_mod_cast hscale0.ne'
  have hE := smoothSpatialError_nonneg N s M ℓ hρ.le hξ0
  have hC := smoothSpatialDensityCap_nonneg s M
  have hK := smoothSpatialDensityLip_nonneg s M
  apply principalRetained_test_comparison B h L hL m hm hsize tv tw
    (fun y => smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
      (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
      (by exact_mod_cast hℓ) hQ) _ coeff target (by positivity) hε hcoeff0 hmass
    _ hcoeff φ hφ
  intro y _ v hv
  have he := principalVectorSpatial_site_error s x root hM hℓ hx hroot m hp c index H Q hH hQ
    hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hr y v (hbox v hv)
  have he' := div_le_div_of_nonneg_right he hscale0.le
  have hid (z : ℝ) (b : ℂ) : (z : ℂ) - b / (scale : ℂ) =
      (((scale * z : ℝ) : ℂ) - b) / (scale : ℂ) := by
    push_cast
    field_simp
  rw [hid, norm_div, Complex.norm_real, Real.norm_of_nonneg hscale0.le]
  exact he'

end Erdos3

end

end OAI
