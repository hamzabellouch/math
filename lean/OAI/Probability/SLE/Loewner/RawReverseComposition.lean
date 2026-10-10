import OAI.Probability.SLE.Loewner.SmoothRawInverse
import OAI.Probability.SLE.Loewner.ReverseLongContraction

namespace OAI

/-! A tail of a reverse trajectory is the raw inverse at the earlier
capacity time. This identity needs no geometric trace. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma reverse_height_mono_nonneg (q : ℝ → ℂ) (u : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt q (-2/(q t-(u t : ℂ))) (Ici 0) t)
    (hp : ∀ t, 0 ≤ t → 0 < (q t).im) :
    MonotoneOn (fun t => (q t).im) (Ici 0) := by
  intro s hs t ht hst
  exact reverse_height_monotone q u
    (fun v hv => (hd v hv.1).mono Icc_subset_Ici_self) (fun v hv => hp v hv.1)
    ⟨hs,hst⟩ ⟨ht,le_rfl⟩ hst

namespace Target

lemma raw_reverse_tail_inverse (b : Driver) (T S : ℝ≥0) (hST : S ≤ T)
    (q : ℝ → ℂ)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt q
      (-2/(q t-(driverValue b ((T : ℝ)-t) : ℂ))) (Ici 0) t)
    (hp : ∀ t, 0 ≤ t → 0 < (q t).im) :
    inverseFlow 1 b S (q ((T : ℝ)-S)) = q T := by
  let a : ℝ := (T : ℝ)-S
  have ha : 0 ≤ a := sub_nonneg.mpr hST
  have hmono := reverse_height_mono_nonneg q (fun t => driverValue b ((T : ℝ)-t)) hd hp
  let Q (s : ℝ) := q (a+s)
  let η : ℝ := (q a).im/2
  have hη : 0 < η := half_pos (hp a ha)
  have hheight (s : ℝ) (hs : 0 ≤ s) : η ≤ (Q s).im :=
    (half_le_self (hp a ha).le).trans
      (hmono ha (add_nonneg ha hs) (le_add_of_nonneg_right hs))
  have hQ (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt Q
      (reverseField η (driverValue b ((S : ℝ)-1*s)) (Q s)) (Ici 0) s := by
    have hi : HasDerivWithinAt (fun v : ℝ => a+v) 1 (Ici 0) s := by
      simpa using ((hasDerivAt_id s).const_add a).hasDerivWithinAt
    have hmaps : MapsTo (fun v : ℝ => a+v) (Ici 0) (Ici 0) :=
      fun v hv => add_nonneg ha hv
    have hh := (hd (a+s) (add_nonneg ha hs)).scomp s hi hmaps
    have he : (T : ℝ)-(a+s)=(S : ℝ)-1*s := by dsimp [a]; ring
    rw [reverseField,reverseCenter_eq (hheight s hs)]
    convert! hh using 1
    simp only [one_smul,he,Q,div_eq_mul_inv]
  have hh := inverseFlow_eq_reverse_trajectory 1 (by norm_num) b S (q a)
    η hη (half_le_self (hp a ha).le) Q (by simp [Q]) hQ
  convert hh using 1
  simp only [div_one,Q,a,sub_add_cancel]

end Target
end SLEExactGauge

end

end OAI
