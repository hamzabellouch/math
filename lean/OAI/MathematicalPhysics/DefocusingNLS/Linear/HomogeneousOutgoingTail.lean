import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingBounds

namespace OAI

/-! # A fixed outgoing combination on the entire far tail -/

open Set Filter Topology Asymptotics MeasureTheory
open scoped ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

private theorem outgoingTail_field_sub (νp νm eta : ℂ) (m : ℕ) (q : ℂ)
    (r : ℝ) (Z W : V₄) :
    spectralPhysicalCircularField νp νm eta m q r (Z - W) =
      spectralPhysicalCircularField νp νm eta m q r Z -
        spectralPhysicalCircularField νp νm eta m q r W := by
  have h := show spectralPhysicalCircularField νp νm eta m q r (1 • Z + (-1 : ℂ) • W) =
      (1 : ℂ) • spectralPhysicalCircularField νp νm eta m q r Z +
        (-1 : ℂ) • spectralPhysicalCircularField νp νm eta m q r W by
    simp only [spectralPhysicalCircularField_regular, spectralRegularField_add,
      spectralRegularField_smul, one_smul]
  simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using h

theorem homogeneousPhysicalOutgoingPlane_forward
    (νp νm eta : ℂ) (m : ℕ) (Q : ℝ → ℂ) (Z Zp Zm : ℝ → V₄)
    (R r : ℝ) (hR : 0 < R) (hr : R ≤ r)
    (hQ : ContinuousOn Q (Icc R r))
    (hZ : ∀ t ∈ Icc R r, HasDerivAt Z
      (spectralPhysicalCircularField νp νm eta m (Q t) t (Z t)) t)
    (hZp : ∀ t ∈ Icc R r, HasDerivAt Zp
      (spectralPhysicalCircularField νp νm eta m (Q t) t (Zp t)) t)
    (hZm : ∀ t ∈ Icc R r, HasDerivAt Zm
      (spectralPhysicalCircularField νp νm eta m (Q t) t (Zm t)) t)
    (c : ℂ × ℂ) (hc : Z R = c.1 • Zp R + c.2 • Zm R) :
    Z r = c.1 • Zp r + c.2 • Zm r := by
  let D := fun t => Z t - (c.1 • Zp t + c.2 • Zm t)
  have hd (t : ℝ) (ht : t ∈ Icc R r) : HasDerivAt D
      (spectralPhysicalCircularField νp νm eta m (Q t) t (D t)) t := by
    apply ((hZ t ht).sub (((hZp t ht).const_smul c.1).add
      ((hZm t ht).const_smul c.2))).congr_deriv
    dsimp only [D]
    rw [outgoingTail_field_sub]
    simp only [spectralPhysicalCircularField_regular, spectralRegularField_add,
      spectralRegularField_smul]
  obtain ⟨C, hC⟩ := spectralPhysicalCircularField_bounded_on νp νm eta m Q R r hR hQ
  have hz : D R = 0 := by simp only [D, hc, sub_self]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hz
    (fun t ht => hC t ⟨ht.1, ht.2.le⟩ (D t)) r ⟨hr, le_rfl⟩
  exact sub_eq_zero.mp hzero

theorem homogeneous_matched_canonicalColumn_derivative
    (n : ℕ) (z : ProfileMatchingBall) (eta lam : ℂ) (c : ℂ × ℂ)
    (Y : ℂ → ℝ → V₄)
    (hY : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) c Y)
    (r : ℝ) (hr : innerBoundaryRadius < r) :
    let ν := radialShootingNu (n + radialInnerShootingThreshold) z
    HasDerivAt (spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Y lam))
      (spectralPhysicalCircularField (ν - 2 * lam) (star ν - 2 * lam) eta
        (n + radialInnerShootingThreshold) (radialMatchedProfile n z r) r
        (spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Y lam) r)) r := by
  intro ν
  have hr0 : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hm := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hν : ν = -1 / ((n + radialInnerShootingThreshold : ℕ) : ℂ) +
      2 * Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ) := by
    dsimp only [ν]
    unfold radialShootingNu radialShootingQ
    ring
  have h := spectralPhysicalPair_hasDerivAt ν lam eta (n + radialInnerShootingThreshold)
    (by omega) (fun t => (radialExteriorCanonical ν (n + radialInnerShootingThreshold)
      (radialShootingM z) (Real.log innerBoundaryRadius) t).1) (Y lam) r hr0
    (by rw [hν]; exact spectralPhysicalFactor_scale _ hm _ r hr0)
    (hY.1 lam (Real.log r) (Real.log_nonneg (by linarith [innerBoundaryRadius_bounds.1])))
  simpa only [radialMatchedProfile, ite_eq_right hr.not_ge,
    radialShootingExteriorProfile, radialPhysicalExterior] using h

theorem spectralPhysicalJet_bigO (ν : ℂ) (Y : ℝ → ℂ × ℂ)
    (hY : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ t in atTop, ‖Y t‖ ≤ M) :
    (fun r => (spectralPhysicalJet ν Y r).1) =O[atTop] (fun r : ℝ => r ^ ν.re) ∧
    (fun r => (spectralPhysicalJet ν Y r).2) =O[atTop] (fun r : ℝ => r ^ (ν.re - 1)) := by
  obtain ⟨M, hM, hbound⟩ := hY
  have hb := Real.tendsto_log_atTop.eventually hbound
  constructor
  · apply IsBigO.of_bound M
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _), mul_comm] using
      (spectralPhysicalJet_bounds ν Y M r hr0 hr).1
  · apply IsBigO.of_bound ((‖ν‖ + 1) * M)
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _), mul_assoc,
      mul_comm, mul_left_comm] using (spectralPhysicalJet_bounds ν Y M r hr0 hr).2

theorem spectralPhysicalPair_bigO (νp νm : ℂ) (Y : ℝ → V₄) (Y₀ : V₄)
    (hY : Tendsto Y atTop (𝓝 Y₀)) :
    (fun r => (spectralPhysicalPair νp νm Y r).1.1) =O[atTop] (fun r : ℝ => r ^ νp.re) ∧
    (fun r => (spectralPhysicalPair νp νm Y r).1.2) =O[atTop] (fun r : ℝ => r ^ (νp.re - 1)) ∧
    (fun r => (spectralPhysicalPair νp νm Y r).2.1) =O[atTop] (fun r : ℝ => r ^ νm.re) ∧
    (fun r => (spectralPhysicalPair νp νm Y r).2.2) =O[atTop] (fun r : ℝ => r ^ (νm.re - 1)) := by
  have hb : ∀ᶠ t in atTop, ‖Y t‖ ≤ ‖Y₀‖ + 1 :=
    (hY.norm.eventually (gt_mem_nhds (show ‖Y₀‖ < ‖Y₀‖ + 1 by linarith))).mono
      (fun _ h => h.le)
  have hp := spectralPhysicalJet_bigO νp (fun t => (Y t).1)
    ⟨‖Y₀‖ + 1, by positivity, hb.mono (fun _ h => (norm_fst_le _).trans h)⟩
  have hm := spectralPhysicalJet_bigO νm (fun t => (Y t).2)
    ⟨‖Y₀‖ + 1, by positivity, hb.mono (fun _ h => (norm_snd_le _).trans h)⟩
  exact ⟨hp.1, hp.2, hm.1, hm.2⟩

theorem homogeneous_matched_pair_canonical_tail
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (eta : ℂ) (N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hhalf : -(1 / 32 : ℝ) ≤ lam.re)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) eta lam f g)
    (hbounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ r, ‖(f r, g r)‖ ≤ M)
    (hL2f : IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N f r‖ ^ 2) (Ioi 0))
    (hL2g : IntegrableOn (fun r => r ^ 11 * ‖iteratedDeriv N g r‖ ^ 2) (Ioi 0))
    (Yp Ym : ℂ → ℝ → V₄)
    (hYp : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (1, 0) Yp)
    (hYm : IsCanonicalHolomorphicColumn (radialShootingNu (n + radialInnerShootingThreshold) z)
      eta (radialShootingM z) (n + radialInnerShootingThreshold)
      (Real.log innerBoundaryRadius) (0, 1) Ym)
 :
    ∃ c : ℂ × ℂ, ∃ R₀ : ℝ, innerBoundaryRadius < R₀ ∧ ∀ r, R₀ ≤ r →
      harmonicRadialState f g r =
        c.1 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
          (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Yp lam) r +
        c.2 • spectralPhysicalPair (radialShootingNu (n + radialInnerShootingThreshold) z - 2 * lam)
          (star (radialShootingNu (n + radialInnerShootingThreshold) z) - 2 * lam) (Ym lam) r := by
  let R₀ := innerBoundaryRadius + 1
  have hi : innerBoundaryRadius < R₀ := by dsimp only [R₀]; linarith
  have hR₀ : 0 < R₀ := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hi
  obtain ⟨c, hc⟩ := homogeneous_matched_pair_canonical_span n z hX hz eta N hN lam hhalf
    f g hf hg he hbounded hL2f hL2g Yp Ym hYp hYm R₀ hi
  refine ⟨c, R₀, hi, ?_⟩
  intro r hr
  let ν := radialShootingNu (n + radialInnerShootingThreshold) z
  have hν : -2 * (radialShootingA n : ℂ) +
      2 * Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ) = ν :=
    (radialShootingNu_physical n z).symm
  have hνm : -2 * (radialShootingA n : ℂ) -
      2 * Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ) = star ν := by
    rw [← hν]
    simp only [star_add, star_mul, star_neg, star_ofNat, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  apply homogeneousPhysicalOutgoingPlane_forward (ν - 2 * lam) (star ν - 2 * lam) eta
    (n + radialInnerShootingThreshold) (radialMatchedProfile n z)
    (harmonicRadialState f g) _ _ R₀ r hR₀ hr
  · exact (radialMatchedProfile_contDiffOn n z hX hz).continuousOn.mono
      (fun _ ht => hR₀.trans_le ht.1)
  · intro t ht
    simpa only [hν, hνm] using harmonicRadialState_hasDerivAt (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold)
      (radialMatchedProfile n z) f g eta lam hf hg he t (hR₀.trans_le ht.1)
  · exact fun t ht => homogeneous_matched_canonicalColumn_derivative n z eta lam (1, 0)
      Yp hYp t (hi.trans_le ht.1)
  · exact fun t ht => homogeneous_matched_canonicalColumn_derivative n z eta lam (0, 1)
      Ym hYm t (hi.trans_le ht.1)
  · exact hc

end DefocusingNLS

end OAI
