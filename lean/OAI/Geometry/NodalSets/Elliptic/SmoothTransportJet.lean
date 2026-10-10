import OAI.Geometry.NodalSets.Elliptic.SmoothOperatorJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def smoothTransport (W : Fin 4 → Coord → ℂ) (c f a : Coord → ℂ) : Coord → ℂ :=
  fun x ↦ (∑ i, W i x * coordPartial i a x) + c x * a x - f x

lemma reval_transport (W : Fin 4 → CPoly) (c f a : CPoly) :
    reval (polynomialTransport W c f a) =
      smoothTransport (fun i ↦ reval (W i)) (reval c) (reval f) (reval a) := by
  funext x
  simp [reval, polynomialTransport, smoothTransport, coordPartial_reval]

lemma smoothTransport_contDiff {W : Fin 4 → Coord → ℂ} {c f a : Coord → ℂ}
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hc : ContDiff ℝ ∞ c)
    (hf : ContDiff ℝ ∞ f) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (smoothTransport W c f a) :=
  ((ContDiff.sum (fun i _ ↦ (hW i).mul (coordPartial_contDiff ha i))).add (hc.mul ha)).sub hf

lemma FlatAt.neg {n : ℕ} {f : Coord → ℂ} (h : FlatAt n f 0) :
    FlatAt n (fun x ↦ -f x) 0 := by
  intro k hk
  change iteratedFDeriv ℝ k (-f) 0 = 0
  rw [iteratedFDeriv_neg_apply, h k hk, neg_zero]

lemma FlatAt.sub {n : ℕ} {f g : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : FlatAt n f 0) (h' : FlatAt n g 0) : FlatAt n (fun x ↦ f x - g x) 0 := by
  simpa only [sub_eq_add_neg] using h.add hf hg.neg h'.neg

theorem flat_transport_coefficients {n : ℕ}
    {W W' : Fin 4 → Coord → ℂ} {c c' f f' a : Coord → ℂ}
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hW' : ∀ i, ContDiff ℝ ∞ (W' i))
    (hc : ContDiff ℝ ∞ c) (hc' : ContDiff ℝ ∞ c')
    (hf : ContDiff ℝ ∞ f) (hf' : ContDiff ℝ ∞ f') (ha : ContDiff ℝ ∞ a)
    (hjW : ∀ i, FlatAt n (fun x ↦ W i x - W' i x) 0)
    (hjc : FlatAt n (fun x ↦ c x - c' x) 0) (hjf : FlatAt n (fun x ↦ f x - f' x) 0) :
    FlatAt n (fun x ↦ smoothTransport W c f a x - smoothTransport W' c' f' a x) 0 := by
  have he : (fun x ↦ smoothTransport W c f a x - smoothTransport W' c' f' a x) =
      fun x ↦ (∑ i, (W i x - W' i x) * coordPartial i a x) +
        (c x - c' x) * a x - (f x - f' x) := by
    funext x
    simp only [smoothTransport, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  apply FlatAt.sub _ (hf.sub hf') _ hjf
  · exact (ContDiff.sum (fun i _ ↦ ((hW i).sub (hW' i)).mul
      (coordPartial_contDiff ha i))).add ((hc.sub hc').mul ha)
  · apply FlatAt.add _ ((hc.sub hc').mul ha) _ (hjc.mul (hc.sub hc') ha)
    · exact ContDiff.sum (fun i _ ↦ ((hW i).sub (hW' i)).mul (coordPartial_contDiff ha i))
    · exact FlatAt.sum Finset.univ
        (fun i _ ↦ ((hW i).sub (hW' i)).mul (coordPartial_contDiff ha i))
        (fun i _ ↦ (hjW i).mul ((hW i).sub (hW' i)) (coordPartial_contDiff ha i))

theorem smooth_transport_flat {n : ℕ} {W : Fin 4 → Coord → ℂ} {c f : Coord → ℂ}
    (WP : Fin 4 → CPoly) (cP fP a : CPoly)
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hjW : ∀ i, FlatAt n (fun x ↦ W i x - reval (WP i) x) 0)
    (hjc : FlatAt n (fun x ↦ c x - reval cP x) 0)
    (hjf : FlatAt n (fun x ↦ f x - reval fP x) 0)
    (hp : ∀ k, k ≤ n → homogeneousComponent k (polynomialTransport WP cP fP a) = 0) :
    FlatAt n (smoothTransport W c f (reval a)) 0 := by
  apply flat_of_sub (smoothTransport_contDiff hW hc hf (reval_contDiff a))
    (smoothTransport_contDiff (fun i ↦ reval_contDiff _) (reval_contDiff _)
      (reval_contDiff _) (reval_contDiff a))
  · exact flat_transport_coefficients hW (fun i ↦ reval_contDiff _) hc (reval_contDiff _)
      hf (reval_contDiff _) (reval_contDiff a) hjW hjc hjf
  · rw [← reval_transport]
    exact flatAt_reval hp

theorem real_polynomial_wave_jets (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (initial : Jet) (hi : ∀ k, (initial k).IsHomogeneous k)
    (hfirst : ∀ i, pderiv i (initial 1) = C (v i))
    (hcenter : (∑ i, v i * v i) + 4 = 0)
    (hsecond : eikonalCoefficient v (fun r i j ↦ homogeneousComponent r (g i j)) 0 initial = 0)
    (m J : ℕ) :
    ∃ (phi : CPoly) (A : ℕ → CPoly),
      (∀ k, k ≤ 2 → homogeneousComponent k phi = initial k) ∧
      (∀ j, homogeneousComponent 0 (A j) = if j = 0 then 1 else 0) ∧
      FlatAt m (smoothEikonal (fun i j ↦ reval (g i j)) (reval phi)) 0 ∧
      FlatAt m (smoothTransport (fun i ↦ reval (beamVector g phi i))
        (reval (beamScalar g b phi)) (reval 0) (reval (A 0))) 0 ∧
      ∀ j, j < J → FlatAt m (smoothTransport (fun i ↦ reval (beamVector g phi i))
        (reval (beamScalar g b phi))
        (fun x ↦ -smoothSecondOrder (fun i j ↦ reval (g i j)) (fun i ↦ reval (b i))
          (reval (A j)) x) (reval (A (j + 1)))) 0 := by
  obtain ⟨phi, A, hkeep, _, he, hA0, _, ht0, htj⟩ :=
    polynomial_wave_jets v hv g b hmetric initial hi hfirst hcenter hsecond m J
  refine ⟨phi, A, hkeep, hA0, ?_, ?_, ?_⟩
  · rw [← reval_eikonal]
    exact flatAt_reval (fun k hk ↦ he k (by omega))
  · rw [← reval_transport]
    exact flatAt_reval (fun k hk ↦ ht0 k (by omega))
  · intro j hj
    have heq : (fun x ↦ -smoothSecondOrder (fun i j ↦ reval (g i j))
        (fun i ↦ reval (b i)) (reval (A j)) x) = reval (-polynomialSecondOrder g b (A j)) := by
      rw [← reval_secondOrder]
      ext x
      simp [reval]
    rw [heq, ← reval_transport]
    exact flatAt_reval (fun k hk ↦ htj j hj k (by omega))

end
end Yau.Jets

end OAI
