import Mathlib

namespace OAI

/-! A derivative bound on positive times extends to the endpoint when
the function is continuous there. Used for squared reverse coordinates. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

lemma norm_sub_initial_le_of_deriv_on_Ioc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T C : ℝ} (hT : 0 ≤ T) (f f' : ℝ → E)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioc 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hb : ∀ t ∈ Ioc 0 T, ‖f' t‖ ≤ C) :
    ∀ t ∈ Icc 0 T, ‖f t-f 0‖ ≤ C*t := by
  intro t ht
  by_cases ht0 : t=0
  · subst t; simp
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  let x (n : ℕ) : ℝ := t/((n : ℝ)+1)
  have hx (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hxt (n : ℕ) : x n ≤ t := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hx0 : Tendsto x atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
    simpa only [x,mul_one_div,mul_zero] using h
  have hxin : Tendsto x atTop (𝓝[Icc 0 T] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hx0,Eventually.of_forall (fun n => ⟨(hx n).le,(hxt n).trans ht.2⟩)⟩
  have hfx := (hc 0 ⟨le_rfl,hT⟩).tendsto.comp hxin
  have hleft : Tendsto (fun n => ‖f t-f (x n)‖) atTop (𝓝 ‖f t-f 0‖) :=
    (hfx.const_sub (f t)).norm
  have hright : Tendsto (fun n => C*(t-x n)) atTop (𝓝 (C*t)) := by
    simpa only [sub_zero] using (hx0.const_sub t).const_mul C
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro n
  have hsub : Icc (x n) t ⊆ Icc 0 T := Icc_subset_Icc (hx n).le ht.2
  apply norm_image_sub_le_of_norm_deriv_right_le_segment (hc.mono hsub)
    (fun s hs => hd s ⟨(hx n).trans_le hs.1,hs.2.le.trans ht.2⟩)
    (fun s hs => hb s ⟨(hx n).trans_le hs.1,hs.2.le.trans ht.2⟩)
    t ⟨hxt n,le_rfl⟩

end SLEExactGauge

end

end OAI
