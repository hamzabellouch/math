import OAI.Geometry.NodalSets.Elliptic.SmoothTransportJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def smoothBeamVector (g : Fin 4 → Fin 4 → Coord → ℂ) (phi : Coord → ℂ)
    (i : Fin 4) : Coord → ℂ := fun x ↦ 2 * ∑ j, g i j x * coordPartial j phi x

def smoothBeamScalar (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (phi : Coord → ℂ) : Coord → ℂ := fun x ↦ smoothSecondOrder g b phi x + 6

lemma reval_beamVector (g : Fin 4 → Fin 4 → CPoly) (phi : CPoly) (i : Fin 4) :
    reval (beamVector g phi i) = smoothBeamVector (fun i j ↦ reval (g i j)) (reval phi) i := by
  ext x
  simp [beamVector, smoothBeamVector, reval, coordPartial_reval]

lemma reval_beamScalar (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (phi : CPoly) :
    reval (beamScalar g b phi) =
      smoothBeamScalar (fun i j ↦ reval (g i j)) (fun i ↦ reval (b i)) (reval phi) := by
  have he := reval_secondOrder g b phi
  ext x
  simpa [beamScalar, smoothBeamScalar, reval] using congrFun he x

lemma smoothBeamVector_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ} {phi : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hp : ContDiff ℝ ∞ phi) (i : Fin 4) :
    ContDiff ℝ ∞ (smoothBeamVector g phi i) :=
  contDiff_const.mul (ContDiff.sum (fun j _ ↦ (hg i j).mul (coordPartial_contDiff hp j)))

lemma smoothBeamScalar_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ}
    {b : Fin 4 → Coord → ℂ} {phi : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hp : ContDiff ℝ ∞ phi) : ContDiff ℝ ∞ (smoothBeamScalar g b phi) :=
  (smoothSecondOrder_contDiff hg hb hp).add contDiff_const

lemma flat_beamVector {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hjet : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0) (i : Fin 4) :
    FlatAt n (fun x ↦ smoothBeamVector g (reval phi) i x - reval (beamVector G phi i) x) 0 := by
  rw [reval_beamVector]
  have he : (fun x ↦ smoothBeamVector g (reval phi) i x -
      smoothBeamVector (fun i j ↦ reval (G i j)) (reval phi) i x) =
      fun x ↦ (∑ j, (g i j x - reval (G i j) x) * coordPartial j (reval phi) x) * 2 := by
    ext x
    simp only [smoothBeamVector, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  have hs : ContDiff ℝ ∞ (fun x ↦ ∑ j,
      (g i j x - reval (G i j) x) * coordPartial j (reval phi) x) :=
    ContDiff.sum (fun j _ ↦ ((hg i j).sub (reval_contDiff _)).mul
      (coordPartial_contDiff (reval_contDiff phi) j))
  apply FlatAt.mul hs contDiff_const
  exact FlatAt.sum Finset.univ
    (fun j _ ↦ ((hg i j).sub (reval_contDiff _)).mul (coordPartial_contDiff (reval_contDiff phi) j))
    (fun j _ ↦ (hjet i j).mul ((hg i j).sub (reval_contDiff _))
      (coordPartial_contDiff (reval_contDiff phi) j))

lemma flat_beamScalar {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ} {b : Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (B : Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0)
    (hbj : ∀ i, FlatAt n (fun x ↦ b i x - reval (B i) x) 0) :
    FlatAt n (fun x ↦ smoothBeamScalar g b (reval phi) x - reval (beamScalar G B phi) x) 0 := by
  rw [reval_beamScalar]
  simp only [smoothBeamScalar, add_sub_add_right_eq_sub]
  exact flat_secondOrder_coefficients hg (fun i j ↦ reval_contDiff _) hb
    (fun i ↦ reval_contDiff _) (reval_contDiff phi) hgj hbj

theorem smooth_beam_transport_flat {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    {b : Fin 4 → Coord → ℂ} (G : Fin 4 → Fin 4 → CPoly) (B : Fin 4 → CPoly)
    (phi prev a : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0)
    (hbj : ∀ i, FlatAt n (fun x ↦ b i x - reval (B i) x) 0)
    (hp : ∀ k, k ≤ n → homogeneousComponent k (polynomialTransport (beamVector G phi)
      (beamScalar G B phi) (-polynomialSecondOrder G B prev) a) = 0) :
    FlatAt n (smoothTransport (smoothBeamVector g (reval phi))
      (smoothBeamScalar g b (reval phi)) (fun x ↦ -smoothSecondOrder g b (reval prev) x)
      (reval a)) 0 := by
  apply smooth_transport_flat (beamVector G phi) (beamScalar G B phi)
    (-polynomialSecondOrder G B prev) a
    (smoothBeamVector_contDiff hg (reval_contDiff phi))
    (smoothBeamScalar_contDiff hg hb (reval_contDiff phi))
    (smoothSecondOrder_contDiff hg hb (reval_contDiff prev)).neg
    (flat_beamVector G phi hg hgj) (flat_beamScalar G B phi hg hb hgj hbj) _ hp
  have h := (flat_secondOrder_coefficients hg (fun i j ↦ reval_contDiff _) hb
    (fun i ↦ reval_contDiff _) (reval_contDiff prev) hgj hbj).neg
  have he : (fun x ↦ -smoothSecondOrder g b (reval prev) x -
      reval (-polynomialSecondOrder G B prev) x) =
      fun x ↦ -(smoothSecondOrder g b (reval prev) x -
        smoothSecondOrder (fun i j ↦ reval (G i j)) (fun i ↦ reval (B i)) (reval prev) x) := by
    rw [← reval_secondOrder]
    ext x
    simp [reval]
    ring
  rw [he]
  exact h

theorem smooth_wave_jets (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (G : Fin 4 → Fin 4 → CPoly) (B : Fin 4 → CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hmetric : ∀ i j, homogeneousComponent 0 (G i j) = if i = j then 1 else 0)
    (initial : Jet) (hi : ∀ k, (initial k).IsHomogeneous k)
    (hfirst : ∀ i, pderiv i (initial 1) = C (v i))
    (hcenter : (∑ i, v i * v i) + 4 = 0)
    (hsecond : eikonalCoefficient v (fun r i j ↦ homogeneousComponent r (G i j)) 0 initial = 0)
    (m J : ℕ)
    (hgj : ∀ i j, FlatAt m (fun x ↦ g i j x - reval (G i j) x) 0)
    (hbj : ∀ i, FlatAt m (fun x ↦ b i x - reval (B i) x) 0) :
    ∃ (phi : CPoly) (A : ℕ → CPoly),
      (∀ k, k ≤ 2 → homogeneousComponent k phi = initial k) ∧
      (∀ d, m + 2 * J + 3 < d → homogeneousComponent d phi = 0) ∧
      (∀ j, homogeneousComponent 0 (A j) = if j = 0 then 1 else 0) ∧
      (∀ j k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j) = 0) ∧
      FlatAt m (smoothEikonal g (reval phi)) 0 ∧
      FlatAt m (smoothTransport (smoothBeamVector g (reval phi))
        (smoothBeamScalar g b (reval phi)) (fun _ ↦ 0) (reval (A 0))) 0 ∧
      ∀ j, j < J → FlatAt m (smoothTransport (smoothBeamVector g (reval phi))
        (smoothBeamScalar g b (reval phi))
        (fun x ↦ -smoothSecondOrder g b (reval (A j)) x) (reval (A (j + 1)))) 0 := by
  obtain ⟨phi, A, hkeep, hdeg, he, hA0, hAd, ht0, htj⟩ :=
    polynomial_wave_jets v hv G B hmetric initial hi hfirst hcenter hsecond m J
  refine ⟨phi, A, hkeep, hdeg, hA0, hAd, ?_, ?_, ?_⟩
  · exact smooth_eikonal_flat G phi hg hgj (fun k hk ↦ he k (by omega))
  · have hp : ∀ k, k ≤ m → homogeneousComponent k (polynomialTransport (beamVector G phi)
        (beamScalar G B phi) (-polynomialSecondOrder G B 0) (A 0)) = 0 := by
      intro k hk
      simpa [polynomialSecondOrder] using ht0 k (by omega)
    have h := smooth_beam_transport_flat G B phi 0 (A 0) hg hb hgj hbj hp
    have hz : (fun x ↦ -smoothSecondOrder g b (reval 0) x) = fun _ ↦ 0 := by
      ext x
      simp [smoothSecondOrder, coordPartial_reval, reval]
    rw [hz] at h
    exact h
  · intro j hj
    exact smooth_beam_transport_flat G B phi (A j) (A (j + 1)) hg hb hgj hbj
      (fun k hk ↦ htj j hj k (by omega))

end
end Yau.Jets

end OAI
