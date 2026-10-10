import OAI.Probability.FreeIsing.Estimates.OsgoodIntegration

namespace OAI

noncomputable section

open Set Real MeasureTheory

namespace Problem367

theorem exists_last_level_crossing {V : ℝ → ℝ} {a t z : ℝ}
    (hat : a ≤ t) (hV : ContinuousOn V (Icc a t))
    (ha : V a < z) (ht : z < V t) :
    ∃ u ∈ Icc a t, V u = z ∧ ∀ s ∈ Icc u t, z ≤ V s := by
  let S : Set ℝ := Icc a t ∩ V ⁻¹' {z}
  have hSclosed : IsClosed S :=
    hV.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have hSne : S.Nonempty := by
    obtain ⟨u, hu, hVu⟩ := intermediate_value_Icc hat hV ⟨ha.le, ht.le⟩
    exact ⟨u, hu, hVu⟩
  obtain ⟨u, hu, hmax⟩ := hScompact.exists_isMaxOn hSne continuousOn_id
  have huat : u ∈ Icc a t := hu.1
  have hVu : V u = z := hu.2
  refine ⟨u, huat, hVu, ?_⟩
  intro s hs
  by_contra hsz
  have hsz' : V s < z := lt_of_not_ge hsz
  have hus : u < s := by
    apply lt_of_le_of_ne hs.1
    intro h
    subst s
    linarith
  have hst : s ≤ t := hs.2
  have hsub : Icc s t ⊆ Icc a t := by
    intro x hx
    exact ⟨huat.1.trans (hs.1.trans hx.1), hx.2⟩
  obtain ⟨v, hv, hVv⟩ :=
    intermediate_value_Icc hst (hV.mono hsub) ⟨hsz'.le, ht.le⟩
  have hvS : v ∈ S := ⟨hsub hv, hVv⟩
  have hvu : v ≤ u := hmax hvS
  linarith [hv.1]

theorem eq_zero_of_positive_interval_lower_bound {V : ℝ → ℝ} {a b : ℝ}
    (hV : ContinuousOn V (Icc a b)) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hbound : ∀ t ∈ Icc a b, 0 < V t →
      ∃ c > 0, ∀ u ∈ Icc a t,
        (∀ s ∈ Icc u t, 0 < V s) → c ≤ V u) :
    ∀ t ∈ Icc a b, V t = 0 := by
  intro t ht
  by_contra hzero
  have hpos : 0 < V t := lt_of_le_of_ne (hnonneg t ht) (Ne.symm hzero)
  obtain ⟨c, hc, hcbound⟩ := hbound t ht hpos
  let z : ℝ := min c (V t) / 2
  have hz : 0 < z := by dsimp [z]; positivity
  have hzc : z < c := by
    dsimp [z]
    linarith [min_le_left c (V t)]
  have hzt : z < V t := by
    dsimp [z]
    linarith [min_le_right c (V t)]
  have hsub : Icc a t ⊆ Icc a b := by
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  obtain ⟨u, hu, hVu, hafter⟩ :=
    exists_last_level_crossing ht.1 (hV.mono hsub) (by simpa [ha] using hz) hzt
  have hcu : c ≤ V u := hcbound u hu (fun s hs => hz.trans_le (hafter s hs))
  linarith

theorem lower_bound_of_log_log_le {K z B : ℝ} (hK : 0 < K) (hz : 0 < z)
    (hbound : Real.log (1 + Real.log (K / z)) ≤ B) :
    min K (K / Real.exp (Real.exp B - 1)) ≤ z := by
  by_cases hKz : K ≤ z
  · exact (min_le_left _ _).trans hKz
  have hzK : z < K := lt_of_not_ge hKz
  have hratio : 1 ≤ K / z := (le_div_iff₀ hz).2 (by simpa using hzK.le)
  have hinner : 0 < 1 + Real.log (K / z) := by
    have := Real.log_nonneg hratio
    linarith
  have hlog : Real.log (K / z) ≤ Real.exp B - 1 := by
    have := (Real.log_le_iff_le_exp hinner).1 hbound
    linarith
  have hratio_bound : K / z ≤ Real.exp (Real.exp B - 1) :=
    (Real.log_le_iff_le_exp (div_pos hK hz)).1 hlog
  have hlast : K / Real.exp (Real.exp B - 1) ≤ z := by
    apply (div_le_iff₀ (Real.exp_pos _)).2
    have := (div_le_iff₀ hz).1 hratio_bound
    nlinarith
  exact (min_le_right _ _).trans hlast

theorem eq_zero_of_log_log_comparison {V : ℝ → ℝ} {a b K C : ℝ}
    (hV : ContinuousOn V (Icc a b)) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t) (hK : 0 < K)
    (hcompare : ∀ t ∈ Icc a b, ∀ u ∈ Icc a t,
      (∀ s ∈ Icc u t, 0 < V s) →
      Real.log (1 + Real.log (K / V u)) ≤
        Real.log (1 + Real.log (K / V t)) + C) :
    ∀ t ∈ Icc a b, V t = 0 := by
  apply eq_zero_of_positive_interval_lower_bound hV ha hnonneg
  intro t ht hpos
  let B := Real.log (1 + Real.log (K / V t)) + C
  refine ⟨min K (K / Real.exp (Real.exp B - 1)), ?_, ?_⟩
  · exact lt_min hK (div_pos hK (Real.exp_pos _))
  · intro u hu hpositive
    apply lower_bound_of_log_log_le hK
      (hpositive u (left_mem_Icc.2 hu.2))
    exact hcompare t ht u hu hpositive

theorem eq_zero_of_ae_deriv_le_mul_self {V : ℝ → ℝ} {a b C : ℝ}
    (hV : AbsolutelyContinuousOnInterval V a b) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc a b → deriv V t ≤ C * V t) :
    ∀ t ∈ Icc a b, V t = 0 := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  let E : ℝ → ℝ := fun x => Real.exp (-C * x)
  let G : ℝ → ℝ := fun x => E x * V x
  have hEsmooth : ContDiff ℝ 1 E := by dsimp [E]; fun_prop
  have hEac : AbsolutelyContinuousOnInterval E a b :=
    hEsmooth.contDiffOn.absolutelyContinuousOnInterval
  have hGac : AbsolutelyContinuousOnInterval G a b := hEac.fun_mul hV
  have hGderiv : ∀ᵐ x : ℝ, x ∈ Icc a b → deriv G x ≤ 0 := by
    filter_upwards [hV.ae_differentiableAt, hderiv] with x hdiff hle hx
    have hVdiff : DifferentiableAt ℝ V x := hdiff (by simpa [uIcc_of_le hab] using hx)
    have hEdiff : HasDerivAt E (Real.exp (-C * x) * (-C)) x := by
      simpa [E, mul_comm] using ((hasDerivAt_id x).const_mul (-C)).exp
    have hGdiff := hEdiff.mul hVdiff.hasDerivAt
    change deriv (E * V) x ≤ 0
    rw [hGdiff.deriv]
    have hb := hle hx
    dsimp [E]
    nlinarith [Real.exp_pos (-C * x)]
  have hsub : uIcc a t ⊆ uIcc a b := by
    simp only [uIcc_of_le ht.1, uIcc_of_le hab]
    intro x hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  have hGat := hGac.mono hsub
  have hint : (∫ x in a..t, deriv G x) ≤ 0 := by
    calc
      _ ≤ ∫ x in a..t, (0 : ℝ) := by
        apply intervalIntegral.integral_mono_ae_restrict ht.1
          hGat.intervalIntegrable_deriv intervalIntegrable_const
        apply (ae_restrict_iff' measurableSet_Icc).2
        filter_upwards [hGderiv] with x hx hxat
        exact hx ⟨hxat.1, hxat.2.trans ht.2⟩
      _ = 0 := by simp
  rw [hGat.integral_deriv_eq_sub] at hint
  have hprod : Real.exp (-C * t) * V t ≤ 0 := by
    simpa [G, E, ha] using hint
  exact le_antisymm ((mul_le_mul_iff_right₀ (Real.exp_pos (-C * t))).1 (by simpa using hprod))
    (hnonneg t ht)

theorem eq_zero_of_ae_osgood {V k : ℝ → ℝ} {a b K : ℝ}
    (hV : AbsolutelyContinuousOnInterval V a b) (ha : V a = 0)
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ V t)
    (hupper : ∀ t ∈ Icc a b, V t ≤ K) (hK : 0 < K)
    (hk : IntervalIntegrable k volume a b)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc a b), 0 < V t →
      deriv V t ≤ k t * V t * (1 + Real.log (K / V t))) :
    ∀ t ∈ Icc a b, V t = 0 := by
  apply eq_zero_of_log_log_comparison
    (C := ∫ t in a..b, |k t|)
    (hV.continuousOn.mono Icc_subset_uIcc) ha hnonneg hK
  intro t ht u hu hpositive
  simpa only [osgoodTransform] using
    osgoodTransform_le_add_integral_abs hu.1 hu.2 ht.2 hV hpositive hupper hk hbound

end Problem367

end

end OAI
