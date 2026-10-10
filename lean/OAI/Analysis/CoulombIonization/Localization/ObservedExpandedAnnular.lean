import Mathlib
import OAI.Analysis.CoulombIonization.Localization.MasterExpandedAnnularQuery

namespace OAI

noncomputable section

namespace CoulombBarrier
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology ContDiff
open CoulombAtom CoulombObservation

lemma original_posterior_expanded_count_band_bound {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) (j : ℕ) (k : Fin K)
    (hk : j ≤ k.val) {B r : ℝ} (hB : 1 ≤ B) (hr : 0 < r)
    (hnoise : Real.sqrt 3*ell k ≤ r/4) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      (∫ x, rawAnnularCount (r/2) (2*B*r) x ∂originalRawKernel μ ell j (originalDatum ell j z)) ≤
        observedAnnularCount ell k (r/4) (3*B*r) z := by
  filter_upwards [original_posterior_annular_count_le_observed μ ell hell j k hk (r/2) (2*B*r)] with z hz
  apply hz.trans
  exact rawAnnularCount_mono (by linarith) (by nlinarith) _

 theorem exists_observed_posterior_expanded_density_constant {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B) (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ), (∀ k, 0 ≤ ell k) →
      ∀ (j : ℕ) (k : Fin K), j ≤ k.val → ∀ {r₀ s r T : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ s → r₀ ≤ 2*r → r ≤ s →
      Real.sqrt 3*ell k ≤ r/4 →
      ∀ᵐ z ∂physicalObservationLaw μ K,
        observedAnnularCount ell k (r/4) (3*B*r) z ≤ T/r^3 →
        ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ B*r →
          jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y ≤
            D*T*r^(-6-3*masterExponent) := by
  obtain ⟨D,hD,hbound⟩ := exists_posterior_expanded_annular_density_constant hg hgs hB hc hcL
  refine ⟨D,hD,?_⟩
  intro N K μ hμ ell hell j k hk r₀ s r T hr₀ hs hs1 hr₀s hrr hrs hnoise
  have hr : 0 < r := by linarith
  filter_upwards [original_posterior_expanded_count_band_bound μ ell hell j k hk hB hr hnoise] with z hz
  intro hcount y hy hy2
  exact (hbound μ ell j hr₀ hs hs1 hrr hrs _ y hy hy2).trans
    ((mul_le_mul_of_nonneg_left (hz.trans hcount) (by positivity)).trans_eq
      (master_density_count_scale hr D T))

 theorem exists_observed_posterior_expanded_query_constant {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) {B c₁ : ℝ} (hB : 1 ≤ B)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ} (μ : Measure (Configuration N)),
      ∀ [IsFiniteMeasure μ] (ell : Fin K → ℝ), (∀ k, 0 ≤ ell k) →
      ∀ (j : ℕ) (k : Fin K), j ≤ k.val → ∀ {r₀ s r T : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ s → r₀ ≤ 2*r → r ≤ s →
      Real.sqrt 3*ell k ≤ r/4 →
      ∀ᵐ q ∂physicalObservationLaw μ K,
        observedAnnularCount ell k (r/4) (3*B*r) q ≤ T/r^3 →
        ∀ y z : Space, r ≤ ‖y‖ → ‖y‖ ≤ B*r → r ≤ ‖z‖ → ‖z‖ ≤ B*r →
          ‖jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j q) y-
            jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j q) z‖ ≤
            C*T*r^(-7-4*masterExponent)*‖y-z‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_posterior_expanded_annular_query_constant hg hgs hB hc hcL
  refine ⟨C,hC,?_⟩
  intro N K μ hμ ell hell j k hk r₀ s r T hr₀ hs hs1 hr₀s hrr hrs hnoise
  have hr : 0 < r := by linarith
  filter_upwards [original_posterior_expanded_count_band_bound μ ell hell j k hk hB hr hnoise] with q hq
  intro hcount y z hy hy2 hz hz2
  exact (hbound μ ell j hr₀ hs hs1 hr₀s hrr hrs _ y z hy hy2 hz hz2).trans
    ((mul_le_mul_of_nonneg_left (hq.trans hcount) (by positivity)).trans_eq
      (master_query_count_scale hr C T ‖y-z‖))

end CoulombBarrier

open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma rpow_half_scale {u : ℝ} (hu : 0 ≤ u) (e : ℝ) :
    (u/2)^e = (1/2:ℝ)^e*u^e := by
  rw [show u/2 = (1/2:ℝ)*u by ring, Real.mul_rpow (by norm_num) hu]

 theorem exists_actual_expanded_conditional_regularity_constants {B c₁ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ T D L : ℝ, 0 < T ∧ 0 ≤ D ∧ 0 ≤ L ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        let count := observedAnnularCount
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (3*B*u)
        Measurable[observationInformation
          (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] count ∧
        (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
          {z | T/u^3 < count z} < u^40 ∧
        ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i),
          count q ≤ T/u^3 →
            (∀ y : Space, u/2 ≤ ‖y‖ → ‖y‖ ≤ B*u →
              originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                D*u^(-6-3*masterExponent)) ∧
            (∀ y z : Space, u/2 ≤ ‖y‖ → ‖y‖ ≤ B*u → u/2 ≤ ‖z‖ → ‖z‖ ≤ B*u →
              ‖originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y-
                originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q z‖ ≤
                L*u^(-7-4*masterExponent)*‖y-z‖) := by
  obtain ⟨T,hT,hcount⟩ := exists_actual_uniform_annular_good_constant
    (by norm_num : (0:ℝ) < 1/8) (by linarith : (0:ℝ) < 3*B)
  obtain ⟨D,hD,hdensity⟩ := exists_observed_posterior_expanded_density_constant
    canonicalRealPacket_smooth.continuous canonicalRealPacket_support (by linarith : 1 ≤ 2*B) hc hcL
  obtain ⟨L,hL,hquery⟩ := exists_observed_posterior_expanded_query_constant
    canonicalRealPacket_smooth canonicalRealPacket_support (by linarith : 1 ≤ 2*B) hc hcL
  refine ⟨T,D*T*(1/2:ℝ)^(-6-3*masterExponent),L*T*(1/2:ℝ)^(-7-4*masterExponent),
    hT,by positivity,by positivity,?_⟩
  intro ι l r₀ s Z lam N K F δ hs0 hr₀ hstate
  have hn := uniform_observation_noise_eventually (by norm_num : (0:ℝ) < 1/8) hs0
  filter_upwards [hcount hs0 hr₀ hstate,hr₀,hn,
    hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hci hri hni hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  have hru : r₀ i ≤ u := le_mul_of_one_le_left hri.le (one_le_pow₀ (by norm_num))
  have hu : 0 < u := hri.trans_le hru
  have hs : 0 < s i := hu.trans_le hjs
  have hnoise : Real.sqrt 3*dyadicObservationWidth (r₀ i) j ≤ (u/2)/4 := by
    have hh := hni u hu hjs
    simpa only [dyadicObservationWidth,u,show (1.01:ℝ) = 101/100 by norm_num,
      one_div_mul_eq_div,div_div,show (2:ℝ)*4 = 8 by norm_num] using hh
  have hr₀s := hru.trans hjs
  have hrr : r₀ i ≤ 2*(u/2) := by linarith
  have hrs : u/2 ≤ s i := by linarith
  have henn : 0 ≤ u/2 := by positivity
  have hshape : (u/2)/4 = u/8 := by ring
  have hshape' : 3*(2*B)*(u/2) = 3*B*u := by ring
  have hshape'' : (2*B)*(u/2) = B*u := by ring
  refine ⟨observedAnnularCount_information_measurable _ j le_rfl _ _,?_,?_⟩
  · simpa only [one_div_mul_eq_div] using hci j hjs
  · filter_upwards [hdensity (graphRawLaw (F i)) _ (fun k => (dyadicObservationWidth_pos hri k).le)
      j j le_rfl hri hs hsi.le hr₀s hrr hrs hnoise,
      hquery (graphRawLaw (F i)) _ (fun k => (dyadicObservationWidth_pos hri k).le)
      j j le_rfl hri hs hsi.le hr₀s hrr hrs hnoise] with q hd hq
    intro hcut
    have hcut' : observedAnnularCount (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k)
        j ((u/2)/4) (3*(2*B)*(u/2)) q ≤ T/(u/2)^3 := by
      rw [hshape,hshape']
      exact hcut.trans (div_le_div_of_nonneg_left hT.le (by positivity)
        (pow_le_pow_left₀ henn (by linarith : u/2 ≤ u) 3))
    have hd' := hd hcut'
    have hq' := hq hcut'
    rw [hshape''] at hd' hq'
    constructor
    · intro y hyl hyh
      simpa only [rpow_half_scale hu.le,mul_assoc,u,originalQueryDensity] using hd' y hyl hyh
    · intro y z hyl hyh hzl hzh
      simpa only [rpow_half_scale hu.le,mul_assoc,u,originalQueryDensity] using hq' y z hyl hyh hzl hzh

end CoulombAtom

end

end OAI
