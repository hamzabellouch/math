import OAI.Probability.FreeIsing.Estimates.AbsoluteContinuity
import OAI.Probability.FreeIsing.Estimates.Osgood

namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Problem367

theorem contDiffOn_osgoodTransform {c K : ℝ} (hc : 0 < c) (hcK : c ≤ K) :
    ContDiffOn ℝ 1 (fun z : ℝ => Real.log (1 + Real.log (K / z))) (Icc c K) := by
  have hK : 0 < K := hc.trans_le hcK
  have hdiv : ContDiffOn ℝ 1 (fun z : ℝ => K / z) (Icc c K) :=
    contDiffOn_const.div contDiffOn_id (fun z hz => ne_of_gt (hc.trans_le hz.1))
  apply (contDiffOn_const.add (hdiv.log ?_)).log
  · intro z hz
    have hzpos : 0 < z := hc.trans_le hz.1
    have hlog : 0 ≤ Real.log (K / z) := Real.log_nonneg ((one_le_div hzpos).2 hz.2)
    linarith
  · intro z hz
    exact ne_of_gt (div_pos hK (hc.trans_le hz.1))

theorem absolutelyContinuousOnInterval_osgoodTransform
    {V : ℝ → ℝ} {a b K : ℝ}
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hpos : ∀ x ∈ uIcc a b, 0 < V x)
    (hupper : ∀ x ∈ uIcc a b, V x ≤ K) :
    AbsolutelyContinuousOnInterval
      (fun x => Real.log (1 + Real.log (K / V x))) a b := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_uIcc : IsCompact (uIcc a b)).exists_isMinOn
    (nonempty_uIcc : (uIcc a b).Nonempty) hV.continuousOn
  have hmap : MapsTo V (uIcc a b) (Icc (V x) K) := by
    intro y hy
    exact ⟨hmin hy, hupper y hy⟩
  change AbsolutelyContinuousOnInterval
    ((fun z : ℝ => Real.log (1 + Real.log (K / z))) ∘ V) a b
  exact absolutelyContinuousOnInterval_comp_contDiffOn_Icc hV
    (contDiffOn_osgoodTransform (hpos x hx) (hupper x hx)) hmap

theorem integral_le_integral_abs_superinterval
    {k : ℝ → ℝ} {a b u t : ℝ}
    (hau : a ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hk : IntervalIntegrable k volume a b) :
    (∫ x in u..t, k x) ≤ ∫ x in a..b, |k x| := by
  calc
    (∫ x in u..t, k x) ≤ |∫ x in u..t, k x| := le_abs_self _
    _ ≤ ∫ x in u..t, |k x| := intervalIntegral.abs_integral_le_integral_abs hut
    _ ≤ ∫ x in a..b, |k x| :=
      intervalIntegral.integral_mono_interval hau hut htb
        (Filter.Eventually.of_forall (fun x => abs_nonneg (k x))) hk.abs

theorem osgoodTransform_le_add_integral
    {V k : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hpos : ∀ x ∈ Icc a b, 0 < V x)
    (hupper : ∀ x ∈ Icc a b, V x ≤ K)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b),
      deriv V x ≤ k x * V x * (1 + Real.log (K / V x))) :
    osgoodTransform K (V a) ≤ osgoodTransform K (V b) + ∫ x in a..b, k x := by
  have hAC : AbsolutelyContinuousOnInterval (fun x => osgoodTransform K (V x)) a b := by
    apply absolutelyContinuousOnInterval_osgoodTransform hV
    · simpa only [uIcc_of_le hab] using hpos
    · simpa only [uIcc_of_le hab] using hupper
  apply ac_le_add_integral_of_neg_le_deriv hab hAC hk
  filter_upwards [hbound, ae_restrict_of_ae hV.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc] with x hx hxDiff hxmem
  have hxU : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hxmem
  have hd := (hasDerivAt_osgoodTransform (hpos x hxmem) (hupper x hxmem)).comp x
    (hxDiff hxU).hasDerivAt
  have hden : 0 < V x * (1 + Real.log (K / V x)) :=
    mul_pos (hpos x hxmem) (osgoodInner_pos (hpos x hxmem) (hupper x hxmem))
  have hquot : deriv V x / (V x * (1 + Real.log (K / V x))) ≤ k x := by
    apply (div_le_iff₀ hden).2
    simpa only [mul_assoc] using hx
  change -k x ≤ deriv (osgoodTransform K ∘ V) x
  rw [hd.deriv]
  convert! neg_le_neg hquot using 1
  ring

theorem osgoodTransform_le_add_integral_abs
    {V k : ℝ → ℝ} {a b u t K : ℝ}
    (hau : a ≤ u) (hut : u ≤ t) (htb : t ≤ b)
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hpos : ∀ x ∈ Icc u t, 0 < V x)
    (hupper : ∀ x ∈ Icc a b, V x ≤ K)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc a b), 0 < V x →
      deriv V x ≤ k x * V x * (1 + Real.log (K / V x))) :
    osgoodTransform K (V u) ≤ osgoodTransform K (V t) + ∫ x in a..b, |k x| := by
  have hab : a ≤ b := hau.trans (hut.trans htb)
  have hsub : Icc u t ⊆ Icc a b := Icc_subset_Icc hau htb
  have hsubU : uIcc u t ⊆ uIcc a b := by
    simpa only [uIcc_of_le hab, uIcc_of_le hut] using hsub
  have hlocal : ∀ᵐ x ∂volume.restrict (Icc u t),
      deriv V x ≤ k x * V x * (1 + Real.log (K / V x)) := by
    have hb := hbound.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hb, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    exact hx (hpos x hxmem)
  have hcompare := osgoodTransform_le_add_integral hut (hV.mono hsubU) hpos
    (fun x hx => hupper x (hsub hx)) (hk.mono_set hsubU) hlocal
  linarith [integral_le_integral_abs_superinterval hau hut htb hk]

end Problem367

end

end OAI
