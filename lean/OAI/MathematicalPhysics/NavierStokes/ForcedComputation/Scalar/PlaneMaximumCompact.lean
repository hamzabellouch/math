import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMaximumPrinciple

namespace OAI

/-! The compactness step in the whole-plane maximum principle. Only the
positive superlevel set must remain in a compact spatial set; the scalar
itself may have noncompact diffusion tails. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped Topology ContDiff

theorem positive_cylinder_max {w : ℝ → Plane → ℝ} {T : ℝ}
    (hc : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ))
    {K : Set Plane} (hK : IsCompact K)
    (houtside : ∀ t ∈ Icc 0 T, ∀ x, 0 < w t x → x ∈ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) {x : Plane} (hx : 0 < w t x) :
    ∃ s ∈ Icc 0 T, ∃ y, 0 < w s y ∧ ∀ r ∈ Icc 0 T, ∀ z, w r z ≤ w s y := by
  have hne : (Icc (0 : ℝ) T ×ˢ K).Nonempty := ⟨(t, x), ht, houtside t ht x hx⟩
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod hK).exists_isMaxOn hne
    (hc.mono (fun _ hy => ⟨hy.1, mem_univ _⟩))
  have hpos : 0 < w p.1 p.2 := hx.trans_le
    (hmax (show (t, x) ∈ Icc (0 : ℝ) T ×ˢ K from ⟨ht, houtside t ht x hx⟩))
  refine ⟨p.1, hp.1, p.2, hpos, ?_⟩
  intro r hr z
  by_cases hz : 0 < w r z
  · exact hmax (show (r, z) ∈ Icc (0 : ℝ) T ×ˢ K from ⟨hr, houtside r hr z hz⟩)
  · exact (le_of_not_gt hz).trans hpos.le

theorem scalar_maximum_principle_compact_superlevel {w d : ℝ → Plane → ℝ}
    {a : ℝ → Plane → Plane} {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (hc : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ univ))
    (hcompact : ∀ ε : ℝ, 0 < ε → ∃ K : Set Plane, IsCompact K ∧
      ∀ t ∈ Icc 0 T, ∀ x, ε < w t x → x ∈ K)
    (hs : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (w t))
    (hd : ∀ t ∈ Ioc 0 T, ∀ x, HasDerivWithinAt (fun s => w s x) (d t x) (Icc 0 T) t)
    (he : ∀ t ∈ Ioc 0 T, ∀ x, d t x ≤ scalarGenerator ν (a t) (w t) x)
    (h₀ : ∀ x, w 0 x ≤ 0) : ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ 0 := by
  intro t ht x
  by_contra! hpos
  let ε := w t x / (4 * (T + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let v : ℝ → Plane → ℝ := fun s y => w s y - ε * (s + 1)
  have hvc : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ) :=
    hc.sub ((continuous_const.mul (continuous_fst.add continuous_const)).continuousOn)
  obtain ⟨K, hK, houtside⟩ := hcompact ε hε
  have hcv : ∀ s ∈ Icc 0 T, ∀ y, 0 < v s y → y ∈ K := by
    intro s hs y hy
    apply houtside s hs y
    dsimp [v] at hy
    nlinarith [mul_nonneg hε.le hs.1]
  have hvtx : 0 < v t x := by
    dsimp [v]
    have hm : ε * (4 * (T + 1)) = w t x := by
      dsimp [ε]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hε.le]
  obtain ⟨s, hsK, y, hvsy, hmax⟩ := positive_cylinder_max hvc hK hcv ht hvtx
  have hspos : 0 < s := by
    by_contra hn
    have hz : s = 0 := le_antisymm (le_of_not_gt hn) hsK.1
    subst s
    have h := h₀ y
    dsimp [v] at hvsy
    nlinarith
  have hst : s ∈ Ioc (0 : ℝ) T := ⟨hspos, hsK.2⟩
  have htime : 0 ≤ d s y - ε := by
    apply timeDerivative_nonneg_at_max hspos
      (fun r hr => hmax r ⟨hr.1, hr.2.trans hsK.2⟩ y)
    have hlin := (((hasDerivWithinAt_id s (Icc (0 : ℝ) T)).add_const 1).const_mul ε)
    simpa only [v, Pi.sub_def, id_eq, mul_one] using
      (((hd s hst y).sub hlin).mono (Icc_subset_Icc le_rfl hsK.2))
  have hspace : IsLocalMax (v s) y :=
    Filter.Eventually.of_forall (fun z => hmax s hsK z)
  have hgen := scalarGenerator_nonpos ((hs s hsK).sub contDiff_const) hspace hν (a s)
  rw [scalarGenerator_sub_const] at hgen
  have hle := (he s hst y).trans hgen
  linarith

end ForcedComputation.VelocityDetector

end

end OAI
