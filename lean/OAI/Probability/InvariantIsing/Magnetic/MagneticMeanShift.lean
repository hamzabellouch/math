import OAI.Probability.InvariantIsing.Magnetic.MagneticFamilyDerivative

namespace OAI

/-! A uniform mean-shift estimate from the Ising variance bound. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_mean_shift_deficit {M Q : ℝ → ℝ}
    (hd : ∀ z, HasDerivAt M (Q z) z)
    (hM : ∀ z, |M z| ≤ 1) (hQ : ∀ z, 0 ≤ Q z)
    (hb : ∀ z, Q z ≤ 1 - (M z) ^ 2) (x h : ℝ) :
    1 - M (x + h) ≤ Real.exp (2 * |h|) * (1 - M x) := by
  have hm : Monotone M := monotone_of_hasDerivAt_nonneg hd hQ
  have hp (z : ℝ) : 0 ≤ 1 - M z := by linarith [(abs_le.mp (hM z)).2]
  have hExp (z : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (2 * t))
      (2 * Real.exp (2 * z)) z := by
    simpa only [id_eq, one_mul, mul_one, mul_comm] using ((hasDerivAt_id z).const_mul 2).exp
  have he (z : ℝ) : HasDerivAt (fun t => Real.exp (2 * t) * (1 - M t))
      (Real.exp (2 * z) * (2 * (1 - M z) - Q z)) z := by
    convert (hExp z).mul ((hasDerivAt_const z 1).sub (hd z)) using 1
    simp only [Pi.sub_apply]
    ring
  have hw : Monotone (fun t => Real.exp (2 * t) * (1 - M t)) := by
    apply monotone_of_hasDerivAt_nonneg he
    intro z
    apply mul_nonneg (Real.exp_pos _).le
    have hsq : 0 ≤ (1 - M z) ^ 2 := sq_nonneg _
    nlinarith [hb z]
  by_cases hh : 0 ≤ h
  · have hmono := hm (show x ≤ x + h by linarith)
    have hexp : 1 ≤ Real.exp (2 * |h|) := Real.one_le_exp (by positivity)
    exact (sub_le_sub_left hmono 1).trans (le_mul_of_one_le_left (hp x) hexp)
  · have hh' : h ≤ 0 := (lt_of_not_ge hh).le
    have ht := hw (show x + h ≤ x by linarith)
    change Real.exp (2 * (x + h)) * (1 - M (x + h)) ≤ Real.exp (2 * x) * (1 - M x) at ht
    have heq : Real.exp (2 * (x + h)) = Real.exp (2 * x) * Real.exp (2 * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, mul_assoc] at ht
    have ht' := (mul_le_mul_iff_right₀ (Real.exp_pos (2 * x))).mp ht
    have hmul : Real.exp (2 * |h|) * Real.exp (2 * h) = 1 := by
      rw [abs_of_nonpos hh', ← Real.exp_add, show 2 * -h + 2 * h = 0 by ring, Real.exp_zero]
    have hh'' := mul_le_mul_of_nonneg_left ht' (Real.exp_pos (2 * |h|)).le
    simpa only [← mul_assoc, hmul, one_mul] using hh''

lemma magnetic_mean_shift_tendsto_one {ι : Type*} {l : Filter ι}
    {M Q : ι → ℝ → ℝ} {x : ι → ℝ}
    (hd : ∀ i z, HasDerivAt (M i) (Q i z) z)
    (hM : ∀ i z, |M i z| ≤ 1) (hQ : ∀ i z, 0 ≤ Q i z)
    (hb : ∀ i z, Q i z ≤ 1 - (M i z) ^ 2)
    (hx : Tendsto (fun i => M i (x i)) l (𝓝 1)) (h : ℝ) :
    Tendsto (fun i => M i (x i + h)) l (𝓝 1) := by
  have he : Tendsto (fun i => Real.exp (2 * |h|) * (1 - M i (x i))) l (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hx).const_mul (Real.exp (2 * |h|))
  have hzero : Tendsto (fun i => 1 - M i (x i + h)) l (𝓝 0) := by
    apply squeeze_zero (fun i => by linarith [(abs_le.mp (hM i (x i + h))).2])
      (fun i => magnetic_mean_shift_deficit (hd i) (hM i) (hQ i) (hb i) (x i) h)
    simpa only [sub_self, mul_zero] using he
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero

lemma magnetic_mean_shift_tendsto_neg_one {ι : Type*} {l : Filter ι}
    {M Q : ι → ℝ → ℝ} {x : ι → ℝ}
    (hd : ∀ i z, HasDerivAt (M i) (Q i z) z)
    (hM : ∀ i z, |M i z| ≤ 1) (hQ : ∀ i z, 0 ≤ Q i z)
    (hb : ∀ i z, Q i z ≤ 1 - (M i z) ^ 2)
    (hx : Tendsto (fun i => M i (x i)) l (𝓝 (-1))) (h : ℝ) :
    Tendsto (fun i => M i (x i + h)) l (𝓝 (-1)) := by
  have hd' (i : ι) (z : ℝ) : HasDerivAt (fun u => -M i (-u)) (Q i (-z)) z := by
    convert ((hd i (-z)).comp z (hasDerivAt_neg z)).neg using 1 <;>
      first | rfl | simp
  have hM' (i : ι) (z : ℝ) : |-M i (-z)| ≤ 1 := by simpa only [abs_neg] using hM i (-z)
  have hb' (i : ι) (z : ℝ) : Q i (-z) ≤ 1 - (-M i (-z)) ^ 2 := by
    simpa only [neg_sq] using hb i (-z)
  have hx' : Tendsto (fun i => -M i (- -x i)) l (𝓝 (1 : ℝ)) := by
    simpa only [neg_neg] using hx.neg
  have hh := magnetic_mean_shift_tendsto_one hd' hM' (fun i z => hQ i (-z)) hb' hx' (-h)
  simpa only [neg_add_rev, neg_neg, add_comm] using hh.neg


end InvariantIsing

end

end OAI
