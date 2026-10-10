import Mathlib

namespace OAI

/-! A forward Loewner real coordinate outside the driver range moves
outward. This elementary barrier also applies before a finite lifetime. -/
noncomputable section
open Set

namespace SLEExactGauge

lemma outward_real_barrier {a b c : ℝ} (X u D : ℝ → ℝ)
    (hX : ContinuousOn X (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt X (2*(X t-u t)/D t) (Ici t) t)
    (hD : ∀ t ∈ Ico a b, 0 < D t)
    (hu : ∀ t ∈ Ico a b, u t ≤ c) (hc : c < X a) :
    ∀ t ∈ Icc a b, X a ≤ X t := by
  have hh := image_le_of_deriv_right_lt_deriv_boundary hX.neg
    (fun t ht => (hd t ht).neg) (B := fun _ => -X a) (B' := fun _ => 0) le_rfl
    (fun t => hasDerivAt_const t (-X a)) (fun t ht he => ?_)
  · intro t ht
    have h := hh ht
    change -X t ≤ -X a at h
    linarith
  · change -X t = -X a at he
    have hval : X t=X a := by linarith
    have hp : 0 < X t-u t := by rw [hval]; linarith [hu t ht]
    exact neg_neg_of_pos (div_pos (mul_pos (by norm_num) hp) (hD t ht))

lemma inward_negative_real_barrier {a b c : ℝ} (X u D : ℝ → ℝ)
    (hX : ContinuousOn X (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt X (2*(X t-u t)/D t) (Ici t) t)
    (hD : ∀ t ∈ Ico a b, 0 < D t)
    (hu : ∀ t ∈ Ico a b, c ≤ u t) (hc : X a < c) :
    ∀ t ∈ Icc a b, X t ≤ X a := by
  have hd' (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (fun s => -X s) (2*((-X t)-(-u t))/D t) (Ici t) t := by
    convert! (hd t ht).neg using 1
    ring
  have hh := outward_real_barrier (fun t => -X t) (fun t => -u t) D hX.neg hd' hD
    (fun t ht => neg_le_neg (hu t ht)) (neg_lt_neg hc)
  intro t ht
  have h := hh t ht
  linarith

end SLEExactGauge

end

end OAI
