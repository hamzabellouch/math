import OAI.Analysis.OInfinity.CommonCornerShrink

namespace OAI

/-! # Global comparison from the two concrete common-corner transfers

The transfer product has exact initial and final projections. Its norm
estimate keeps all three errors, and a shared spare isometry permits the
connected completion. The original canonical-generator transfer is separate.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Compose two transfers to the same corner with a unitary preserving it. -/
lemma commonCornerTransfer_products (P Q R c d : E) (u : unitary E)
    (hc : star c * c = P) (hcc : c * star c = R) (hcp : c * P = c)
    (hd : star d * d = Q) (hdd : d * star d = R) (hdq : d * Q = d)
    (hu : Commute (u : E) R) :
    let w := star d * (u : E) * c
    star w * w = P ∧ w * star w = Q ∧ w * P = w := by
  intro w
  have hRc : R * c = c := by rw [← hcc, mul_assoc, hc, hcp]
  have hRd : R * d = d := by rw [← hdd, mul_assoc, hd, hdq]
  have huR : (u : E) * R * star (u : E) = R := by
    rw [hu.eq, mul_assoc, u.property.2, mul_one]
  have hsuR : star (u : E) * R * (u : E) = R := by
    calc
      _ = star (u : E) * ((u : E) * R) := by rw [hu.eq]; noncomm_ring
      _ = R := by rw [← mul_assoc, u.property.1, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · change star (star d * (u : E) * c) * (star d * (u : E) * c) = P
    simp only [star_mul, star_star]
    calc
      _ = star c * (star (u : E) * (d * star d) * (u : E)) * c := by noncomm_ring
      _ = P := by rw [hdd, hsuR, mul_assoc, hRc, hc]
  · change (star d * (u : E) * c) * star (star d * (u : E) * c) = Q
    simp only [star_mul, star_star]
    calc
      _ = star d * ((u : E) * (c * star c) * star (u : E)) * d := by noncomm_ring
      _ = Q := by rw [hcc, huR, mul_assoc, hRd, hd]
  · change (star d * (u : E) * c) * P = _
    rw [mul_assoc, hcp]

private lemma negativeGlobal_sandwich_norm (c x : E) (hc : ‖c‖ ≤ 1) :
    ‖star c * x * c‖ ≤ ‖x‖ := by
  calc
    _ ≤ (‖star c‖ * ‖x‖) * ‖c‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖x‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (by simpa only [norm_star] using hc) (norm_nonneg _))
      hc (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- No error is lost when pulling the three comparison errors back through
contractive transfers. -/
lemma commonCornerTransfer_error (Q c d x y X Y : E) (u : unitary E)
    (hd : star d * d = Q) (hqy : Q * y = y) (hyq : y * Q = y)
    (hdn : ‖d‖ ≤ 1) (δ : ℝ)
    (hcx : ‖c * x * star c - X‖ < δ)
    (hdy : ‖d * y * star d - Y‖ < δ)
    (hu : ‖(u : E) * X * star (u : E) - Y‖ < δ) :
    let w := star d * (u : E) * c
    ‖w * x * star w - y‖ < 3 * δ := by
  intro w
  let a := (u : E) * (c * x * star c - X) * star (u : E)
  let b := (u : E) * X * star (u : E) - Y
  let e := Y - d * y * star d
  have ha : ‖a‖ < δ := by
    dsimp only [a]
    rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
    change ‖(c * x * star c - X) * (star u : unitary E)‖ < δ
    rw [CStarRing.norm_mul_coe_unitary]
    exact hcx
  have he : ‖e‖ < δ := by dsimp only [e]; rw [norm_sub_rev]; exact hdy
  have hid : w * x * star w - y = star d * (a + b + e) * d := by
    have hback : star d * (d * y * star d) * d = y := by
      calc
        _ = (star d * d) * y * (star d * d) := by noncomm_ring
        _ = y := by rw [hd, hqy, hyq]
    dsimp only [w, a, b, e]
    simp only [star_mul, star_star]
    calc
      _ = star d * ((u : E) * (c * x * star c) * star (u : E)) * d - y := by noncomm_ring
      _ = star d * ((u : E) * (c * x * star c) * star (u : E)) * d -
          star d * (d * y * star d) * d := by rw [hback]
      _ = _ := by noncomm_ring
  rw [hid]
  refine (negativeGlobal_sandwich_norm d (a + b + e) hdn).trans_lt ?_
  calc
    _ ≤ ‖a‖ + ‖b‖ + ‖e‖ := (norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl ‖e‖))
    _ < δ + δ + δ := add_lt_add (add_lt_add ha hu) he
    _ = _ := by ring

/-- Full ambient comparison of the stabilized rows. The two original
canonical rows themselves are not asserted to be conjugate here. -/
lemma exists_canonicalNegative_global_comparison [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ∀ i ≤ m, ‖(u : E) * canonicalNegativeRow s i * star (u : E) -
        canonicalNegativeRow t i‖ < ε := by
  let P := canonicalTailProjection s 1
  let Q := canonicalTailProjection t 1
  let R := P * Q
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hP : star P = P := canonicalTailProjection_star s 1
  have hQ : star Q = Q := canonicalTailProjection_star t 1
  have hPP : P * P = P := canonicalTailProjection_idempotent s hs 1
  have hQQ : Q * Q = Q := canonicalTailProjection_idempotent t ht 1
  have hPQ : Commute P Q := canonicalTailProjection_commutes s Q
    (fun i => ⟨(canonicalTailProjection_commutes t (s i)
      (fun j => ⟨(hc i j).1.symm, (hc i j).2.symm⟩) 1).symm,
      (canonicalTailProjection_commutes t (star (s i))
        (fun j => ⟨by simpa only [star_star] using (hc i j).2.star_star.symm,
          (hc i j).1.star_star.symm⟩) 1).symm⟩) 1
  obtain ⟨c, hcL, hcP, hcG, hcR, hec⟩ := exists_canonicalNegative_shrink s t hs ht hc m δ hδ
  have hct : bergRowsCommute t s := fun i j =>
    ⟨(hc j i).1.symm, by simpa only [star_star] using (hc j i).2.star_star.symm⟩
  obtain ⟨d, hdL, hdQ, hdG, hdR, hed⟩ := exists_canonicalNegative_shrink t s ht hs hct m δ hδ
  have hdR' : d * star d = R := hdR.trans hPQ.eq.symm
  obtain ⟨v, _hv, hvr, hvl, hev⟩ := exists_canonicalNegative_comparison s t hs ht hc m δ hδ
  have hvR : Commute (v : E) R := by
    have hh := hvr.trans hvl.symm
    rw [mul_sub, sub_mul, mul_one, one_mul] at hh
    exact sub_right_inj.mp hh
  let w := star d * (v : E) * c
  obtain ⟨hwP, hwQ, hwp⟩ := commonCornerTransfer_products P Q R c d v hcG hcR hcP
    hdG hdR' hdQ hvR
  have hdn : ‖d‖ ≤ 1 := by
    have hnorm := congrArg norm hdG
    rw [CStarRing.norm_star_mul_self] at hnorm
    have hqn : ‖Q‖ ≤ 1 := IsStarProjection.norm_le Q (isStarProjection_iff'.mpr ⟨hQQ, hQ⟩)
    nlinarith [norm_nonneg d]
  have hclose (i : ℕ) (hi : i ≤ m) :
      ‖w * canonicalNegativeRow s i * star w - canonicalNegativeRow t i‖ < ε := by
    have hsup := canonicalNegativeRow_support t ht i
    have hh := commonCornerTransfer_error Q c d (canonicalNegativeRow s i)
      (canonicalNegativeRow t i) (canonicalNegativeRow s i * Q)
      (canonicalNegativeRow t i * P) v hdG hsup.1 hsup.2 hdn δ
      (hec i hi) (hed i hi) (hev i hi)
    exact hh.trans_eq (by dsimp only [δ]; ring)
  let r := s 0 * t 0
  have hr : star r * r = 1 := by
    change star (s 0 * t 0) * (s 0 * t 0) = 1
    rw [star_mul]
    calc
      _ = star (t 0) * (star (s 0) * s 0) * t 0 := by noncomm_ring
      _ = 1 := by simp only [hs, ht, ite_true, mul_one]
  have hPr : P * r = 0 := by
    change P * (s 0 * t 0) = 0
    rw [← mul_assoc]
    have hh : P * s 0 = 0 := by
      simpa only [show (0 : ℕ) < 1 by omega, ite_true] using
        canonicalTailProjection_mul_generator s hs 1 0
    rw [hh, zero_mul]
  have hQr : Q * r = 0 := by
    have hsq : Commute (s 0) Q := (canonicalTailProjection_commutes t (s 0)
      (fun j => ⟨(hc 0 j).1.symm, (hc 0 j).2.symm⟩) 1).symm
    change Q * (s 0 * t 0) = 0
    rw [← mul_assoc, ← hsq.eq, mul_assoc]
    have hh : Q * t 0 = 0 := by
      simpa only [show (0 : ℕ) < 1 by omega, ite_true] using
        canonicalTailProjection_mul_generator t ht 1 0
    rw [hh, mul_zero]
  have hwww : w * star w * w = w := by rw [mul_assoc, hwP, hwp]
  obtain ⟨u, hu, _hue, hup⟩ := exists_explicit_connected_unitary_extension w r hwww hr
    (by rw [hwP]; exact hPr) (by rw [hwQ]; exact hQr)
  have huP : (u : E) * P = w := by
    have hwP' : star w * w = P := hwP
    rw [hwP'] at hup
    exact hup
  refine ⟨u, hu, fun i hi => ?_⟩
  have hsup := canonicalNegativeRow_support s hs i
  have he : (u : E) * canonicalNegativeRow s i * star (u : E) =
      w * canonicalNegativeRow s i * star w := by
    calc
      _ = ((u : E) * P) * canonicalNegativeRow s i * star ((u : E) * P) := by
        rw [star_mul, hP]
        symm
        calc
          _ = (u : E) * (P * canonicalNegativeRow s i * P) * star (u : E) := by noncomm_ring
          _ = _ := by rw [hsup.1, hsup.2]
      _ = _ := by rw [huP]
  rw [he]
  exact hclose i hi

end WeakPureInfiniteness

end

end OAI
