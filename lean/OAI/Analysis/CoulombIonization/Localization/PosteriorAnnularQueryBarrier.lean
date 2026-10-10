import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ObservedPosteriorDensityBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PosteriorAnnularQuery_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff

open CoulombAtom CoulombObservation
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma posterior_query_difference_le_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    {a b C : ℝ} (y z : Space)
    (hbound : ∀ x, ‖masterKernel c₁ r₀ s g x y-masterKernel c₁ r₀ s g x z‖ ≤
      C*(if a ≤ ‖x‖ ∧ ‖x‖ ≤ b then 1 else 0))
    (d : OriginalDatum N K ell j) :
    ‖jointMasterPosterior μ ell j c₁ r₀ s g d y-
      jointMasterPosterior μ ell j c₁ r₀ s g d z‖ ≤
      C*∫ x, rawAnnularCount a b x ∂originalRawKernel μ ell j d := by
  let ν := originalRawKernel μ ell j d
  let f := fun (q : Space) (x : Configuration N) => ∑ i, masterKernel c₁ r₀ s g (x i) q
  have hfi (q) : Integrable (f q) ν := by
    have hm : Measurable (f q) := Finset.measurable_sum _ (fun i _ =>
      ((masterKernel_joint_continuous hc hr₀ hs hg).measurable.comp
        (f := fun x : Configuration N => (x i,q))
        ((measurable_pi_apply i).prodMk measurable_const)))
    obtain ⟨M,_hM,hM⟩ := masterConfigurationDensity_bound (N := N) hc hr₀ hs hrs hg hcg
    exact Integrable.of_bound hm.aestronglyMeasurable M (ae_of_all _ (fun x => hM x q))
  have hci : Integrable (rawAnnularCount a b) ν := by
    apply Integrable.of_bound (rawAnnularCount_measurable _ _).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (rawAnnularCount_nonneg _ _ x)]
      exact rawAnnularCount_le _ _ x)
  have hb (x : Configuration N) : ‖f y x-f z x‖ ≤ C*rawAnnularCount a b x := by
    dsimp only [f]
    rw [←Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hbound (x i))).trans_eq
      (by rw [rawAnnularCount,Finset.mul_sum]))
  unfold jointMasterPosterior
  change ‖(∫ x, f y x ∂ν)-(∫ x, f z x ∂ν)‖ ≤ C*∫ x, rawAnnularCount a b x ∂ν
  rw [←integral_sub (hfi y) (hfi z),←integral_const_mul]
  exact norm_integral_le_of_norm_le (hci.const_mul C) (ae_of_all _ hb)

 theorem exists_posterior_annular_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s →
      ∀ (d : OriginalDatum N K ell j) (y z : Space),
      r ≤ ‖y‖ → ‖y‖ ≤ 2*r → r ≤ ‖z‖ → ‖z‖ ≤ 2*r →
      ‖jointMasterPosterior μ ell j c₁ r₀ s g d y-
        jointMasterPosterior μ ell j c₁ r₀ s g d z‖ ≤
        C*r^(-4-4*masterExponent)*‖y-z‖*
          ∫ x, rawAnnularCount (r/2) (3*r) x ∂originalRawKernel μ ell j d := by
  obtain ⟨C,hC,hbound⟩ := exists_master_annular_query_constant hg hgs hc hcL
  refine ⟨C,hC,?_⟩
  intro N K μ hμ ell j r₀ s r hr₀ hs hs1 hrr hrs d y z hy hy2 hz hz2
  have hcg : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
      ((subset_tsupport g).trans (hgs.trans ball_subset_closedBall))
  exact posterior_query_difference_le_count μ ell j hc hr₀ hs (hrr.trans hrs) hg.continuous hcg
    y z (fun x => hbound hr₀ hs hs1 hrr hrs x y z hy hy2 hz hz2) d

end Work_PosteriorAnnularQuery_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff

open CoulombAtom CoulombObservation

lemma master_query_count_scale {r : ℝ} (hr : 0 < r) (D T t : ℝ) :
    D*r^(-4-4*masterExponent)*t*(T/r^3) = D*T*r^(-7-4*masterExponent)*t := by
  have he : T/r^3 = T*r^(-3:ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat]; rfl
  rw [he]
  calc
    _ = D*T*(r^(-4-4*masterExponent)*r^(-3:ℝ))*t := by ring
    _ = _ := by
      rw [←Real.rpow_add hr,show (-4-4*masterExponent)+(-3:ℝ) = -7-4*masterExponent by ring]

 theorem exists_observed_posterior_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ), (∀ k, 0 ≤ ell k) →
      ∀ (j : ℕ) (k : Fin K), j ≤ k.val → ∀ {r₀ s r T : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s →
      Real.sqrt 3*ell k ≤ r/4 →
      ∀ᵐ q ∂physicalObservationLaw μ K,
        observedAnnularCount ell k (r/4) (4*r) q ≤ T/r^3 →
        ∀ y z : Space, r ≤ ‖y‖ → ‖y‖ ≤ 2*r → r ≤ ‖z‖ → ‖z‖ ≤ 2*r →
          ‖jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j q) y-
            jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j q) z‖ ≤
            C*T*r^(-7-4*masterExponent)*‖y-z‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_posterior_annular_query_constant hg hgs hc hcL
  refine ⟨C,hC,?_⟩
  intro N K μ hμ ell hell j k hk r₀ s r T hr₀ hs hs1 hrr hrs hnoise
  have hr : 0 < r := hr₀.trans_le hrr
  filter_upwards [original_posterior_count_band_bound μ ell hell j k hk hr hnoise] with q hq
  intro hcount y z hy hy2 hz hz2
  exact (hbound μ ell j hr₀ hs hs1 hrr hrs _ y z hy hy2 hz hz2).trans
    ((mul_le_mul_of_nonneg_left (hq.trans hcount) (by positivity)).trans_eq
      (master_query_count_scale hr C T ‖y-z‖))

end CoulombBarrier

end

end OAI
