import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularEventNumericsBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UniformObservationNoise_barrier_scope

open Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombObservation

lemma uniform_observation_noise_eventually {ι : Type*} {l : Filter ι}
    {s : ι → ℝ} {a : ℝ} (ha : 0 < a) (hs0 : Tendsto s l (𝓝 0)) :
    ∀ᶠ i in l, ∀ u : ℝ, 0 < u → u ≤ s i →
      Real.sqrt 3*u^(101/100:ℝ) ≤ a*u := by
  let A : ι → Type := fun i => {u : ℝ // 0 < u ∧ u ≤ s i}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  let u : (Σ i, A i) → ℝ := fun q => q.2.1
  have ht : Tendsto π L l := tendsto_comap
  have hu : ∀ᶠ q in L, 0 < u q := Eventually.of_forall (fun q => q.2.2.1)
  have hu0 : Tendsto u L (𝓝 0) := squeeze_zero
    (fun q => q.2.2.1.le) (fun q => q.2.2.2) (hs0.comp ht)
  have hh := observation_annular_noise_eventually ha hu hu0
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro v hv hvs
  exact hi ⟨i,⟨v,hv,hvs⟩⟩ rfl

end CoulombAtom

end Work_UniformObservationNoise_barrier_scope

section Work_ObservedPosteriorCount_barrier_scope

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombBarrier CoulombObservation ProbabilityTheory

lemma raw_annular_count_le_observed {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (a b : ℝ) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    rawAnnularCount a b z.1 ≤
      observedAnnularCount ell k (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) z := by
  unfold observedAnnularCount rawAnnularCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · have ht := norm_sub_norm_le (physicalObservedConfiguration ell k z i) (z.1 i)
    have ht' := norm_sub_norm_le (z.1 i) (physicalObservedConfiguration ell k z i)
    rw [norm_sub_rev] at ht'
    exact False.elim (hj ⟨by linarith [hd i,hi.1],by linarith [hd i,hi.2]⟩)
  · norm_num
  · exact le_rfl

lemma observedAnnularCount_integrable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (k : Fin K) (a b : ℝ) :
    Integrable (observedAnnularCount ell k a b) (physicalObservationLaw μ K) := by
  have hm := (observedAnnularCount_information_measurable (N := N) ell k (j := 0) (Nat.zero_le _) a b).mono
    (observationInformation_le ell 0) le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable (N:ℝ)
  exact ae_of_all _ (fun z => by
    change ‖rawAnnularCount a b (physicalObservedConfiguration ell k z)‖ ≤ (N:ℝ)
    rw [Real.norm_of_nonneg (rawAnnularCount_nonneg _ _ _)]
    exact rawAnnularCount_le _ _ _)

lemma original_posterior_annular_count_le_observed {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) (j : ℕ) (k : Fin K)
    (hk : j ≤ k.val) (a b : ℝ) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      (∫ x, rawAnnularCount a b x ∂originalRawKernel μ ell j (originalDatum ell j z)) ≤
        observedAnnularCount ell k (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) z := by
  let P := physicalObservationLaw μ K
  let f := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => rawAnnularCount a b z.1
  let g := observedAnnularCount (N := N) ell k (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k)
  have hfi : Integrable f P := by
    apply Integrable.of_bound ((rawAnnularCount_measurable a b).comp measurable_fst).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun z => by
      change ‖rawAnnularCount a b z.1‖ ≤ (N:ℝ)
      rw [Real.norm_of_nonneg (rawAnnularCount_nonneg a b z.1)]
      exact rawAnnularCount_le a b z.1)
  have hgi : Integrable g P := observedAnnularCount_integrable μ ell k _ _
  have hfg : f ≤ᵐ[P] g := by
    filter_upwards [physicalObservationLaw_ae_displacement μ ell hell] with z hz
    exact raw_annular_count_le_observed ell k a b z (hz k)
  have hmono := condExp_mono (m := observationInformation ell j) hfi hgi hfg
  have hgmeas := observedAnnularCount_information_measurable (N := N) ell k hk
    (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k)
  rw [condExp_of_stronglyMeasurable (observationInformation_le ell j) hgmeas.stronglyMeasurable hgi] at hmono
  have he := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable (rawAnnularCount_measurable a b).stronglyMeasurable hfi
  simp only [originalDatum_comap] at he
  filter_upwards [hmono,he] with z hz hez
  exact hez ▸ hz

end CoulombAtom

end Work_ObservedPosteriorCount_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma posterior_density_le_raw_ball_count {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) {g : Space → ℝ}
    (hg : Continuous g) (y : Space) {R A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x, masterKernel c₁ r₀ s g x y ≤ A)
    (hsupport : Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆ ball y R)
    (d : OriginalDatum N K ell j) :
    jointMasterPosterior μ ell j c₁ r₀ s g d y ≤
      A * ∫ x, rawBallCount y R x ∂originalRawKernel μ ell j d := by
  let f : Configuration N → ℝ := fun x => ∑ i, masterKernel c₁ r₀ s g (x i) y
  have hm : Measurable f := Finset.measurable_sum _ (fun i _ =>
    ((masterKernel_joint_continuous hc hr hs hg).measurable.comp
      (f := fun x : Configuration N => (x i,y))
      ((measurable_pi_apply i).prodMk measurable_const)))
  have hn (x) : 0 ≤ f x := Finset.sum_nonneg fun i _ => masterKernel_nonneg _ _ _ _ _ _
  have hb (x) : f x ≤ A*rawBallCount y R x := by
    rw [rawBallCount,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · simpa only [mul_one] using hbound (x i)
    · have hz : masterKernel c₁ r₀ s g (x i) y = 0 := by
        by_contra hh
        have hmem := hsupport hh
        simp only [mem_ball,dist_eq_norm] at hmem
        exact h hmem
      simp only [hz,mul_zero,le_refl]
  have hfb (x) : ‖f x‖ ≤ A*N := by
    rw [Real.norm_of_nonneg (hn x)]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (rawBallCount_le y R x) hA)
  have hci : Integrable (rawBallCount y R) (originalRawKernel μ ell j d) := by
    apply Integrable.of_bound (rawBallCount_measurable y R).aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (rawBallCount_nonneg y R x)]; exact rawBallCount_le y R x)
  unfold jointMasterPosterior
  calc
    _ ≤ ∫ x, A*rawBallCount y R x ∂originalRawKernel μ ell j d :=
      integral_mono (Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hfb))
        (hci.const_mul _) hb
    _ = _ := integral_const_mul _ _

lemma integral_raw_ball_le_annular {N : ℕ} (ν : Measure (Configuration N))
    [IsFiniteMeasure ν] {r : ℝ} (hr : 0 ≤ r) {y : Space}
    (hy : r ≤ ‖y‖) (hy2 : ‖y‖ ≤ 2*r) :
    (∫ x, rawBallCount y (r/2) x ∂ν) ≤ ∫ x, rawAnnularCount (r/2) (3*r) x ∂ν := by
  have hi {f : Configuration N → ℝ} (hf : Measurable f)
      (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ N) : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable (N:ℝ)
    exact ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (hn x)]; exact hb x)
  exact integral_mono (hi (rawBallCount_measurable _ _) (rawBallCount_nonneg _ _) (rawBallCount_le _ _))
    (hi (rawAnnularCount_measurable _ _) (rawAnnularCount_nonneg _ _) (rawAnnularCount_le _ _))
    (rawBallCount_le_annular hr hy hy2 le_rfl)

 theorem exists_posterior_annular_density_constant {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s →
      ∀ (d : OriginalDatum N K ell j) (y : Space), r ≤ ‖y‖ → ‖y‖ ≤ 2*r →
      jointMasterPosterior μ ell j c₁ r₀ s g d y ≤
        D*r^(-3-3*masterExponent) *
          ∫ x, rawAnnularCount (r/2) (3*r) x ∂originalRawKernel μ ell j d := by
  obtain ⟨A,hAn,hA⟩ := masterKernel_amplitude hg hgs
  refine ⟨A*c₁⁻¹^3,by positivity,?_⟩
  intro N K μ hμ ell j r₀ s r hr₀ hs hs1 hrr hrs d y hy hy2
  have hr : 0 < r := hr₀.trans_le hrr
  let B := A*c₁⁻¹^3*r^(-3-3*masterExponent)
  have hBn : 0 ≤ B := by dsimp only [B]; positivity
  have hb (x) : masterKernel c₁ r₀ s g x y ≤ B :=
    (hA hc hcL hr₀ hs hs1 x y).trans (by
      simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left
        (masterWidth_inverse_cube_radius (r₀ := r₀) hc hr hrs hy) hAn)
  have ht := masterWidth_radius_upper hc.le hr₀ hs hs1 hrr hy hy2
  have hsmall : 2*masterWidth c₁ r₀ s y < r/2 := by
    have hc2 : c₁ < 1/8 := by norm_num at hcL ⊢; linarith
    nlinarith
  have hsupport : Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆ ball y (r/2) := by
    rw [masterKernel_eq_widthKernel hc hr₀ hs g]
    exact (widthKernel_support_local (masterWidth_small_lipschitz hc hcL hr₀ hs hs1)
      (masterWidth_pos hc hr₀ hs) (by norm_num) (masterProfile_support hgs) y).trans
      (closedBall_subset_ball hsmall)
  exact (posterior_density_le_raw_ball_count μ ell j hc hr₀ hs hg y hBn hb hsupport d).trans
    (mul_le_mul_of_nonneg_left (integral_raw_ball_le_annular _ hr.le hy hy2) hBn)

end CoulombBarrier

end

end OAI
