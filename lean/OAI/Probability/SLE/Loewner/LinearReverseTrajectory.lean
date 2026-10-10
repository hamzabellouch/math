import OAI.Probability.SLE.Loewner.SmoothRawTraceContinuity
import OAI.Probability.SLE.Loewner.PositiveReverseUniqueness

namespace OAI

/-! Linear drivers and their autonomous centered reverse trajectories.
These give concrete steering curves for the geometric support construction. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge.Target

def linearDriver (c : ℝ) : Driver :=
  ⟨⟨fun t => c*(t:ℝ), continuous_const.mul continuous_subtype_val⟩, by simp⟩

@[simp] lemma linearDriver_apply (c : ℝ) (t : ℝ≥0) :
    linearDriver c t=c*(t:ℝ) := rfl

lemma linearDriver_value (c t : ℝ) (ht : 0 ≤ t) :
    driverValue (linearDriver c) t=c*t := by
  simp only [driverValue,linearDriver_apply,Real.coe_toNNReal _ ht]

lemma linearDriver_derivative (c t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (driverValue (linearDriver c)) c (Ici 0) t := by
  have h := ((hasDerivAt_id t).const_mul c).hasDerivWithinAt (s := Ici 0)
  simpa only [mul_one] using h.congr
    (fun s hs => (linearDriver_value c s hs)) (linearDriver_value c t ht)

private lemma approximation_height_pos (n : ℕ) : 0 < 1/((n:ℝ)+1) := by positivity

def linearReverseBase (c : ℝ) (n : ℕ) : ℝ → ℂ :=
  (exists_reverse_trajectory (fun s => -c*s) (by fun_prop)
    (((1/((n:ℝ)+1):ℝ):ℂ)*I) (by simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero] using approximation_height_pos n)).choose

lemma linearReverseBase_spec (c : ℝ) (n : ℕ) :
    linearReverseBase c n 0=(((1/((n:ℝ)+1):ℝ):ℂ)*I) ∧
    (∀ t, 0 ≤ t → 1/((n:ℝ)+1) ≤ (linearReverseBase c n t).im) ∧
    ∀ t, 0 ≤ t → HasDerivWithinAt (linearReverseBase c n)
      (-2/(linearReverseBase c n t-((-c*t:ℝ):ℂ))) (Ici 0) t := by
  simpa only [linearReverseBase,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero] using
    (exists_reverse_trajectory (fun s => -c*s) (by fun_prop)
    (((1/((n:ℝ)+1):ℝ):ℂ)*I) (by simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero] using approximation_height_pos n)).choose_spec

def linearReverseApprox (c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  linearReverseBase c n t+((c*t:ℝ):ℂ)

lemma linearReverseApprox_derivative (c : ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (linearReverseApprox c n)
      ((c:ℂ)-2/linearReverseApprox c n t) (Ici 0) t := by
  have hd := (linearReverseBase_spec c n).2.2 t ht
  have hc := (((hasDerivAt_id t).const_mul c).ofReal_comp).hasDerivWithinAt (s := Ici 0)
  have h := hd.add hc
  change HasDerivWithinAt (linearReverseApprox c n)
    (-2/(linearReverseBase c n t-((-c*t:ℝ):ℂ))+((c*1:ℝ):ℂ)) (Ici 0) t at h
  exact h.congr_deriv (by
    simp only [linearReverseApprox,Complex.ofReal_neg,Complex.ofReal_mul,mul_one,
      neg_div]
    ring)

lemma linearReverseApprox_height (c : ℝ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < (linearReverseApprox c n t).im := by
  simpa only [linearReverseApprox,Complex.add_im,Complex.ofReal_im,add_zero] using
    (approximation_height_pos n).trans_le ((linearReverseBase_spec c n).2.1 t ht)

lemma linearReverseApprox_eq_inverse (c : ℝ) (n : ℕ) (T : ℝ≥0) :
    linearReverseApprox c n T = inverseFlow 1 (linearDriver c) T
      ((linearDriver c T:ℂ)+(((1/((n:ℝ)+1):ℝ):ℂ)*I)) := by
  let q := linearReverseBase c n
  let r (s : ℝ) := q s+((c*(T:ℝ):ℝ):ℂ)
  have hq := linearReverseBase_spec c n
  have hr (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt r
      (-2/(r s-(driverValue (linearDriver c) ((T:ℝ)-s):ℂ))) (Icc 0 (T:ℝ)) s := by
    have h := ((hq.2.2 s hs.1).add_const ((c*(T:ℝ):ℝ):ℂ)).mono (show Icc 0 (T:ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
    have he : r s-(driverValue (linearDriver c) ((T:ℝ)-s):ℂ)=q s-((-c*s:ℝ):ℂ) := by
      rw [linearDriver_value _ _ (sub_nonneg.mpr hs.2)]
      dsimp [r]
      push_cast
      ring
    simpa only [r,q,he] using h
  have hrp (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) : 0 < (r s).im := by
    simpa only [r,Complex.add_im,Complex.ofReal_im,add_zero] using
      (approximation_height_pos n).trans_le (hq.2.1 s hs.1)
  obtain ⟨v,hv0,hvp,hvd,hvend⟩ := exists_raw_reverse_trajectory (linearDriver c) T
    ((linearDriver c T:ℂ)+(((1/((n:ℝ)+1):ℝ):ℂ)*I))
    (by simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using approximation_height_pos n)
  have hvpos (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) : 0 < (v s).im := by
    apply (approximation_height_pos n).trans_le
    simpa only [Complex.add_im,Complex.ofReal_im,Complex.ofReal_re,Complex.mul_im,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hvp s hs.1
  have he := positive_reverse_unique T.coe_nonneg r v
    (fun s => driverValue (linearDriver c) ((T:ℝ)-s))
    (fun s hs => (hr s hs).continuousWithinAt)
    (fun s hs => (hvd s hs.1).continuousWithinAt.mono Icc_subset_Ici_self)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hr s (Ico_subset_Icc_self hs)))
    (fun s hs => (hvd s hs.1).mono (Ici_subset_Ici.mpr hs.1)) hrp hvpos
    (by simp only [r,q,hq.1,hv0,linearDriver_apply]; ring)
  exact (he T ⟨T.coe_nonneg,le_rfl⟩).trans hvend.symm

end SLEExactGauge.Target

end

end OAI
