import OAI.Probability.SLE.Loewner.ReverseConeContraction
import OAI.Probability.SLE.Loewner.ReverseLongContraction

namespace OAI

/-! A boundary-start reverse trajectory is the uniform limit of the
positive-height trajectories on each finite time interval. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

theorem exists_boundary_radial_distance_constant {T a L : ℝ}
    (ha : 0 < a) (haT : a ≤ T) (hL : 0 ≤ L) (hsmall : L^2*a ≤ 1)
    (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hqc : ContinuousOn q (Icc 0 T))
    (hq : ∀ t ∈ Ioc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Ioc 0 T, 0 < (q t).im)
    (hcone : ∀ t ∈ Icc 0 a, ((q t).re-u t)^2 ≤ t ∧ 3*t ≤ (q t).im^2)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u' t) (Icc 0 T) t)
    (hb : ∀ t ∈ Icc 0 T, |u' t| ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ → ℂ,
      (∀ t ∈ Icc 0 T, HasDerivWithinAt r
        (-2/(r t-(u t : ℂ))) (Ici 0) t) →
      (∀ t ∈ Icc 0 T, 0 < (r t).im) → (r 0).re=u 0 →
      dist (q T) (r T) ≤ dist (q 0) (r 0)*K := by
  have hT : 0 ≤ T := ha.le.trans haT
  have hpost : Icc a T ⊆ Icc 0 T := Icc_subset_Icc_left ha.le
  obtain ⟨s,hs,hsm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr haT)
    (Complex.continuous_im.comp_continuousOn (hqc.mono hpost))
  have hsp : s ∈ Ioc 0 T := ⟨ha.trans_le hs.1,hs.2⟩
  let η : ℝ := min (q s).im (Real.sqrt a)
  have hη : 0 < η := lt_min (hqp s hsp) (Real.sqrt_pos.mpr ha)
  let K : ℝ := Real.exp ((4*η⁻¹^2)*(T-a))
  refine ⟨K,(Real.exp_pos _).le,?_⟩
  intro r hr hrp hr0
  have hrd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt r
      (-2/(r t-(u t : ℂ))) (Icc 0 T) t := (hr t ht).mono Icc_subset_Ici_self
  have hrc : ContinuousOn r (Icc 0 T) := fun t ht => (hrd t ht).continuousWithinAt
  have hsub : Icc 0 a ⊆ Icc 0 T := Icc_subset_Icc_right haT
  have hrda (t : ℝ) (ht : t ∈ Icc 0 a) : HasDerivWithinAt r
      (-2/(r t-(u t : ℂ))) (Icc 0 a) t := (hrd t (hsub ht)).mono hsub
  have hua (t : ℝ) (ht : t ∈ Icc 0 a) : HasDerivWithinAt u
      (u' t) (Icc 0 a) t := (hu t (hsub ht)).mono hsub
  have hra := reverse_loewner_height_lower hL r u u' hrda hua
    (fun t ht => hb t (hsub ht)) (fun t ht => hrp t (hsub ht)) hr0 hsmall
  have hrx := (reverse_centered_coordinates hL r u u' hrda hua
    (fun t ht => hb t (hsub ht)) (fun t ht => hrp t (hsub ht)) hr0).1
  have hrcone (t : ℝ) (ht : t ∈ Ioc 0 a) : ((r t).re-u t)^2 ≤ t := by
    have ht' : t ∈ Icc 0 a := Ioc_subset_Icc_self ht
    have hxx := (sq_le_sq₀ (abs_nonneg ((r t).re-u t)) (mul_nonneg hL ht.1.le)).mpr (hrx t ht')
    rw [sq_abs] at hxx
    have hl := (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg L)).trans hsmall
    nlinarith [mul_le_mul_of_nonneg_right hl ht.1.le]
  have hshort := reverse_trajectories_contract_in_cones ha.le q r u
    (hqc.mono hsub) (hrc.mono hsub)
    (fun t ht => hq t ⟨ht.1,ht.2.trans haT⟩)
    (fun t ht => (hr t (hsub (Ioc_subset_Icc_self ht))).mono (Ici_subset_Ici.mpr ht.1.le))
    (fun t ht => hqp t ⟨ht.1,ht.2.trans haT⟩)
    (fun t ht => hrp t (hsub (Ioc_subset_Icc_self ht)))
    (fun t ht => (hcone t (Ioc_subset_Icc_self ht)).1) hrcone
    (fun t ht => by have hh := (hcone t (Ioc_subset_Icc_self ht)).2; linarith [ht.1])
    (fun t ht => by have hh := hra t (Ioc_subset_Icc_self ht); linarith [ht.1])
  have hQ (t : ℝ) (ht : t ∈ Icc a T) : η ≤ (q t).im :=
    (min_le_left _ _).trans (hsm ht)
  have hroot : Real.sqrt a ≤ (r a).im := by
    have hh := hra a ⟨ha.le,le_rfl⟩
    nlinarith [Real.sq_sqrt ha.le,Real.sqrt_nonneg a,hrp a ⟨ha.le,haT⟩]
  have hrmono := reverse_height_monotone r u hrd hrp
  have hR (t : ℝ) (ht : t ∈ Icc a T) : η ≤ (r t).im :=
    (min_le_right _ _).trans (hroot.trans (hrmono ⟨ha.le,haT⟩ (hpost ht) ht.1))
  have hdQ (t : ℝ) (ht : t ∈ Ico a T) : HasDerivWithinAt q
      (reverseField η (u t) (q t)) (Ici t) t := by
    rw [reverseField,reverseCenter_eq (hQ t (Ico_subset_Icc_self ht))]
    simpa only [div_eq_mul_inv] using hq t ⟨ha.trans_le ht.1,ht.2.le⟩
  have hdR (t : ℝ) (ht : t ∈ Ico a T) : HasDerivWithinAt r
      (reverseField η (u t) (r t)) (Ici t) t := by
    rw [reverseField,reverseCenter_eq (hR t (Ico_subset_Icc_self ht))]
    simpa only [div_eq_mul_inv] using
      (hr t (hpost (Ico_subset_Icc_self ht))).mono (Ici_subset_Ici.mpr (hpost (Ico_subset_Icc_self ht)).1)
  exact dist_le_of_trajectories_ODE (fun t => reverseField_lipschitz hη (u t))
    (hqc.mono hpost) hdQ (hrc.mono hpost) hdR
    (hshort a ⟨ha.le,le_rfl⟩) T ⟨haT,le_rfl⟩

end SLEExactGauge

end

end OAI
