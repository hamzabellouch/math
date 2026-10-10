import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildInitialAE

namespace OAI

/-! # Fixed-interval stability of the countable cold system -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem cold_bounded_interval_stability {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {B D : ℝ}, 0 ≤ B → 0 ≤ D →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {c d : I → ℝ × JetPrototype.Phase → ℝ}
        {c₀ d₀ : I → JetPrototype.Phase → ℝ},
      Measurable F → Measurable G → (∀ i, Measurable (c i)) → (∀ i, Measurable (d i)) →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      (∀ i u, 0 ≤ c i u) → (∀ i u, 0 ≤ d i u) →
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u) →
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, d i u ≤ G u) →
      (∀ i, ColdMildAE q b L T F (c₀ i) (c i)) →
      (∀ i, ColdMildAE q b L T G (d₀ i) (d i)) →
      (∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ D) →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c₀ i p-d₀ i p|) ≤ B) →
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (t,p)-d i (t,p)|) ≤
        C*(B+T*(R*CutoffLipschitz.frequencyConstant q b)*D) := by
  classical
  let J := R*CutoffLipschitz.frequencyConstant q b
  let K := 2*R*HotApplication.realBound q+L+J
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    dsimp [K]
    positivity
  let δ := 1/(2*(K+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hδK : δ*K < 1/2 := by
    have hd : 0 < 2*(K+1) := by positivity
    dsimp [δ]
    rw [div_mul_eq_mul_div,div_lt_iff₀ hd]
    nlinarith
  obtain ⟨n,hn⟩ := exists_nat_ge (T/δ)
  have hreach : T ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  refine ⟨4^n,by positivity,?_⟩
  intro B D hB hD F G c d c₀ d₀ hFm hGm hcm hdm hF hG hcn hdn hcSum hdSum hce hde hFG hseed
  let Z := B+T*J*D
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hes (u) : Summable (fun i => |c i u-d i u|) :=
    ((summable_of_sum_le (fun i => hcn i u) (fun s => hcSum s u)).sub
      (summable_of_sum_le (fun i => hdn i u) (fun s => hdSum s u))).abs
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hcSum {i} u).trans (hF u).2
  have hdb (i) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    refine ⟨hdn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hdSum {i} u).trans (hG u).2
  have hzero : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (0,p)-d i (0,p)|) ≤ Z := by
    filter_upwards [ae_all_iff.mpr (fun i => (hce i).initial_ae hT),
      ae_all_iff.mpr (fun i => (hde i).initial_ae hT),hseed] with p hc hd hp
    simpa only [hc,hd] using hp.trans (show B ≤ Z from le_add_of_nonneg_right (by positivity))
  have hsteps : ∀ j : ℕ, ∀ t ∈ Icc 0 (min ((j:ℝ)*δ) T),
      ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (t,p)-d i (t,p)|) ≤ (4:ℝ)^j*Z := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have htzero : t ≤ 0 := by simpa only [Nat.cast_zero,zero_mul,min_eq_left hT] using ht.2
      have ht0 : t = 0 := le_antisymm htzero ht.1
      subst t
      simpa only [pow_zero,one_mul] using hzero
    | succ j ih =>
      intro t ht
      have htT : t ≤ T := ht.2.trans (min_le_right _ _)
      have htj : t ≤ ((j+1:ℕ):ℝ)*δ := ht.2.trans (min_le_left _ _)
      have hBj : 0 ≤ (4:ℝ)^j*Z := mul_nonneg (pow_nonneg (by norm_num) j) hZ
      by_cases hprefix : t ≤ min ((j:ℝ)*δ) T
      · exact (ih t ⟨ht.1,hprefix⟩).mono (fun p hp => hp.trans (by rw [pow_succ]; nlinarith))
      · let s : ℝ := (j:ℝ)*δ
        have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg j) hδ.le
        have hst : s < t := lt_of_not_ge (fun h => hprefix (le_min h htT))
        have hsT : s ≤ T := hst.le.trans htT
        have hinit := ih s ⟨hs,le_min le_rfl hsT⟩
        let U := t-s
        have hU : 0 ≤ U := sub_nonneg.mpr hst.le
        have hUδ : U ≤ δ := by
          dsimp [U,s]
          rw [Nat.cast_add,Nat.cast_one] at htj
          nlinarith
        have hUK : U*K < 1/2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUδ hK) hδK
        have hsU : s+U ≤ T := by dsimp [U]; linarith
        have hsmall : U*K < 1 := hUK.trans (by norm_num)
        have hwinFG : ∀ᵐ u ∂spacetimeVolume, |window s U F u-window s U G u| ≤ D := by
          apply (ae_prod_iff_ae_ae (measurableSet_le
            ((PositiveIntegral.measurable_window s U hFm).sub
              (PositiveIntegral.measurable_window s U hGm)).abs measurable_const)).mpr
          apply ae_of_all
          intro r
          change ∀ᵐ p ∂FlightMeasure.phaseVolume,
            |F (s+PositiveIntegral.time U r,p)-G (s+PositiveIntegral.time U r,p)| ≤ D
          have hr := PositiveIntegral.time_bounds hU r
          exact hFG (s+PositiveIntegral.time U r) ⟨by linarith [hr.1],by linarith [hr.2]⟩
        have hseedW (a : Finset I) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
            (∑ i ∈ a, |c i (s,p)-d i (s,p)|) ≤ (4:ℝ)^j*Z :=
          hinit.mono (fun p hp => ((hes (s,p)).sum_le_tsum a (fun i _ => abs_nonneg _)).trans hp)
        have hw := cold_family_difference_ae hq hb hL hU hR hBj hD hloss hsmall
          (PositiveIntegral.measurable_window s U hFm) (PositiveIntegral.measurable_window s U hGm)
          (fun i => PositiveIntegral.measurable_window s U (hcm i))
          (fun i => PositiveIntegral.measurable_window s U (hdm i))
          (fun u => hF _) (fun u => hG _) (fun i u => hcn i _) (fun i u => hdn i _)
          (fun a u => hcSum a _) (fun a u => hdSum a _) hwinFG hseedW
          (fun i => (hce i).window hq hb hL hT hR hloss hs hU hsU hFm (hcm i) hF (hcb i))
          (fun i => (hde i).window hq hb hL hT hR hloss hs hU hsU hGm (hdm i) hG (hdb i)) U
        have hUJD : U*J*D ≤ (4:ℝ)^j*Z := by
          have hUT : U ≤ T := by dsimp [U]; linarith
          have hzle : Z ≤ (4:ℝ)^j*Z := le_mul_of_one_le_left hZ (one_le_pow₀ (by norm_num))
          have hbound : U*J*D ≤ T*J*D := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hUT hJ) hD
          exact hbound.trans ((le_add_of_nonneg_left hB).trans hzle)
        have hfac : ((4:ℝ)^j*Z+U*J*D)/(1-U*K) ≤ (4:ℝ)^(j+1)*Z := by
          apply (div_le_iff₀ (by linarith : 0 < 1-U*K)).mpr
          rw [pow_succ]
          nlinarith
        filter_upwards [hw] with p hp
        change (∑' i, |c i (s+PositiveIntegral.time U U,p)-d i (s+PositiveIntegral.time U U,p)|) ≤ _ at hp
        rw [GaussianLocal.time_eq (show U ∈ Icc 0 U from ⟨hU,le_rfl⟩),
          show s+U=t by dsimp [U]; ring] at hp
        exact hp.trans hfac
  intro t ht
  exact hsteps n t ⟨ht.1,by simpa only [min_eq_right hreach] using ht.2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end OAI
