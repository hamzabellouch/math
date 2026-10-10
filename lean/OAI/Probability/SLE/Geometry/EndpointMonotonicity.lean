import OAI.Probability.SLE.Geometry.EndpointDerivativeBound

namespace OAI

/-! One-sided derivative comparisons remain valid at a continuous endpoint,
even when the derivative at that endpoint is singular. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

lemma le_initial_of_deriv_nonpos_on_Ioc {T : ℝ} (hT : 0 ≤ T)
    (f f' : ℝ → ℝ) (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioc 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hb : ∀ t ∈ Ioc 0 T, f' t ≤ 0) :
    ∀ t ∈ Icc 0 T, f t ≤ f 0 := by
  intro t ht
  by_cases ht0 : t=0
  · subst t; exact le_rfl
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
  apply ge_of_tendsto ((hc 0 ⟨le_rfl,hT⟩).tendsto.comp hxin)
  apply Eventually.of_forall
  intro n
  have hsub : Icc (x n) t ⊆ Icc 0 T := Icc_subset_Icc (hx n).le ht.2
  exact image_le_of_deriv_right_le_deriv_boundary (hc.mono hsub)
    (fun s hs => hd s ⟨(hx n).trans_le hs.1,hs.2.le.trans ht.2⟩)
    (B := fun _ => f (x n)) (B' := fun _ => 0) le_rfl continuousOn_const
    (fun s _ => hasDerivWithinAt_const s (Ici s) (f (x n)))
    (fun s hs => hb s ⟨(hx n).trans_le hs.1,hs.2.le.trans ht.2⟩) ⟨hxt n,le_rfl⟩

end SLEExactGauge

end

end OAI
