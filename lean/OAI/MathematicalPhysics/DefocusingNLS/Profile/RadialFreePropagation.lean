import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShortBounds

namespace OAI

/-! Short-interval propagation and restart for arbitrary data in the free radial system. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_state_bound (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (X : ℝ → ℂ × ℂ) (hX : Continuous X) (x₀ : ℂ × ℂ)
    (he : ∀ r ∈ Icc l u, X r=x₀+∫ t in l..r, radialFreeField b t (X t)) :
    ∀ r ∈ Icc l u, ‖X r‖ ≤ 2*‖x₀‖ := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlu) hX.norm.continuousOn
  let M := ‖X m‖
  have hM : 0 ≤ M := norm_nonneg _
  have hi : ‖∫ t in l..m, radialFreeField b t (X t)‖ ≤ 7*M*(m-l) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
      have htI : t ∈ Icc l m := ⟨(uIoc_of_le hm.1 ▸ ht).1.le,(uIoc_of_le hm.1 ▸ ht).2⟩
      have htU : t ∈ Icc l u := ⟨htI.1,htI.2.trans hm.2⟩
      exact (radialFreeField_norm b t hb ⟨hl.trans htU.1,htU.2.trans hu⟩ (X t)).trans
        (mul_le_mul_of_nonneg_left (hmax htU) (by norm_num)))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hm.1),M] using hh
  have hineq : M ≤ ‖x₀‖+7*M*(m-l) := calc
    M = ‖x₀+∫ t in l..m, radialFreeField b t (X t)‖ := congrArg norm (he m hm)
    _ ≤ ‖x₀‖+‖∫ t in l..m, radialFreeField b t (X t)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl hi
  have hlen : m-l ≤ (1/1000 : ℝ) := by linarith [hm.2]
  have hprod := mul_le_mul_of_nonneg_left hlen (show 0 ≤ 7*M by positivity)
  have hbound : M ≤ 2*‖x₀‖ := by nlinarith [norm_nonneg x₀]
  intro r hr
  exact (hmax hr).trans hbound

theorem radial_free_state_restart (b l u m : ℝ) (hl : 0 < l) (hm : m ∈ Icc l u)
    (X : ℝ → ℂ × ℂ) (hX : Continuous X) (x₀ : ℂ × ℂ)
    (he : ∀ r ∈ Icc l u, X r=x₀+∫ t in l..r, radialFreeField b t (X t)) :
    ∀ r ∈ Icc m u, X r=X m+∫ t in m..r, radialFreeField b t (X t) := by
  have hi (a c : ℝ) (ha : a ∈ Icc l u) (hc : c ∈ Icc l u) (hac : a ≤ c) :
      IntervalIntegrable (fun t => radialFreeField b t (X t)) volume a c :=
    ContinuousOn.intervalIntegrable_of_Icc hac
      ((radialFreeField_continuousOn_curve b l u hl X hX).mono
        (fun t ht => ⟨ha.1.trans ht.1,ht.2.trans hc.2⟩))
  intro r hr
  have hrl : r ∈ Icc l u := ⟨hm.1.trans hr.1,hr.2⟩
  rw [he r hrl,he m hm,add_assoc,
    intervalIntegral.integral_add_adjacent_intervals (hi l m ⟨le_rfl,hm.1.trans hm.2⟩ hm hm.1)
      (hi m r hm hrl hr.1)]

theorem radial_free_components_state (b l u : ℝ) (hl : 0 < l)
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G) (f₀ g₀ : ℂ)
    (heF : ∀ r ∈ Icc l u, F r=f₀+∫ t in l..r, G t)
    (heG : ∀ r ∈ Icc l u, G r=g₀+∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t) :
    ∀ r ∈ Icc l u, (F r,G r)=(f₀,g₀)+∫ t in l..r,
      radialFreeField b t (F t,G t) := by
  intro r hr
  have hi : IntervalIntegrable (fun t => radialFreeField b t (F t,G t)) volume l r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((radialFreeField_continuousOn_curve b l u hl (fun t => (F t,G t))
        (hF.prodMk hG)).mono (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  apply Prod.ext
  · have hp := (ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm hi
    change (∫ t in l..r, G t)=(∫ t in l..r, radialFreeField b t (F t,G t)).1 at hp
    change F r=f₀+(∫ t in l..r, radialFreeField b t (F t,G t)).1
    rw [← hp]
    exact heF r hr
  · have hp := (ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm hi
    change (∫ t in l..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t)=
      (∫ t in l..r, radialFreeField b t (F t,G t)).2 at hp
    change G r=g₀+(∫ t in l..r, radialFreeField b t (F t,G t)).2
    rw [← hp]
    exact heG r hr

theorem radial_free_state_components (b l u : ℝ) (hl : 0 < l)
    (X : ℝ → ℂ × ℂ) (hX : Continuous X) (x₀ : ℂ × ℂ)
    (he : ∀ r ∈ Icc l u, X r=x₀+∫ t in l..r, radialFreeField b t (X t)) :
    (∀ r ∈ Icc l u, (X r).1=x₀.1+∫ t in l..r, (X t).2) ∧
    (∀ r ∈ Icc l u, (X r).2=x₀.2+∫ t in l..r,
      -radialFreeCoefficient t*(X t).2-(b : ℂ)*(X t).1) := by
  have hi (r : ℝ) (hr : r ∈ Icc l u) :
      IntervalIntegrable (fun t => radialFreeField b t (X t)) volume l r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((radialFreeField_continuousOn_curve b l u hl X hX).mono
        (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  constructor
  · intro r hr
    have hp := (ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm (hi r hr)
    have hx := congrArg Prod.fst (he r hr)
    change (∫ t in l..r, (X t).2)=(∫ t in l..r, radialFreeField b t (X t)).1 at hp
    change (X r).1=x₀.1+(∫ t in l..r, radialFreeField b t (X t)).1 at hx
    rwa [← hp] at hx
  · intro r hr
    have hp := (ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm (hi r hr)
    have hx := congrArg Prod.snd (he r hr)
    change (∫ t in l..r, -radialFreeCoefficient t*(X t).2-(b : ℂ)*(X t).1)=
      (∫ t in l..r, radialFreeField b t (X t)).2 at hp
    change (X r).2=x₀.2+(∫ t in l..r, radialFreeField b t (X t)).2 at hx
    rwa [← hp] at hx

theorem radial_free_state_sub (b l u : ℝ) (hl : 0 < l)
    (X Y : ℝ → ℂ × ℂ) (hX : Continuous X) (hY : Continuous Y) (x₀ y₀ : ℂ × ℂ)
    (heX : ∀ r ∈ Icc l u, X r=x₀+∫ t in l..r, radialFreeField b t (X t))
    (heY : ∀ r ∈ Icc l u, Y r=y₀+∫ t in l..r, radialFreeField b t (Y t)) :
    ∀ r ∈ Icc l u, X r-Y r=(x₀-y₀)+∫ t in l..r, radialFreeField b t (X t-Y t) := by
  have hi (Z : ℝ → ℂ × ℂ) (hZ : Continuous Z) (r : ℝ) (hr : r ∈ Icc l u) :
      IntervalIntegrable (fun t => radialFreeField b t (Z t)) volume l r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((radialFreeField_continuousOn_curve b l u hl Z hZ).mono
        (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  intro r hr
  simp_rw [radialFreeField_sub]
  rw [intervalIntegral.integral_sub (hi X hX r hr) (hi Y hY r hr),heX r hr,heY r hr]
  abel

end DefocusingNLS

end OAI
