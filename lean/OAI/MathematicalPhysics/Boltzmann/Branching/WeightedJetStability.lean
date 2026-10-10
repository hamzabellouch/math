import OAI.MathematicalPhysics.Boltzmann.Approximation.MildInitialAE
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralWindow
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.ClampedMildAE
import OAI.MathematicalPhysics.Boltzmann.Branching.SliceUniformLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.SpaceTimeEssSup
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative

namespace OAI

section

/-! # Recovering a weighted weak limit from its unweighted density -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem identify_weighted_weak_limit {μ : Measure X} {f : ℕ → X → ℝ} {g G w : X → ℝ}
    (hg : WeakL1Converges μ f g)
    (hG : WeakL1Converges μ (fun n x => w x*f n x) G)
    (hw : Measurable w) (hw1 : ∀ x, 1 ≤ w x) :
    G =ᵐ[μ] (fun x => w x*g x) := by
  have hwpos (x) : 0 < w x := lt_of_lt_of_le zero_lt_one (hw1 x)
  have hinv : ∀ x, |(w x)⁻¹| ≤ 1 := by
    intro x
    rw [abs_of_pos (inv_pos.mpr (hwpos x))]
    exact inv_le_one_of_one_le₀ (hw1 x)
  have hback := hG.bounded_mul hw.inv 1 hinv
  change WeakL1Converges μ (fun n x => (w x)⁻¹*(w x*f n x))
    (fun x => (w x)⁻¹*G x) at hback
  have he : (fun n x => (w x)⁻¹*(w x*f n x)) = f := by
    funext n x
    rw [← mul_assoc,inv_mul_cancel₀ (hwpos x).ne',one_mul]
  rw [he] at hback
  have heq := hg.unique hback
  filter_upwards [heq] with x hx
  change g x = (w x)⁻¹*G x at hx
  rw [hx,← mul_assoc,mul_inv_cancel₀ (hwpos x).ne',one_mul]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Time windows for total and colored cutoff mild equations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem forcing_window (q b L s U : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) :
    forcing q b L (window s U F) u = window s U (forcing q b L F) u := rfl

theorem coldForcing_window (q b L s U : ℝ) (F c : ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) :
    coldForcing q b L (window s U F) (window s U c) u =
      window s U (coldForcing q b L F c) u := rfl

theorem MildAE.window {q b L T R s U : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hs : 0 ≤ s) (hU : 0 ≤ U) (hsU : s+U ≤ T)
    {F : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (he : MildAE q b L T f₀ F) :
    ∀ t, (fun p => window s U F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value U L JetBarrier.flight (fun p => F (s,p))
        (forcing q b L (window s U F)) (t,p)) := by
  have hbnd (u) : |forcing q b L F u| ≤ HotApplication.realBound q*R^2+L*R := by
    have h := HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (fun p => hF (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  exact PositiveIntegral.window_mild_ae hT hL hs hU hsU (measurable_forcing hFm q b L) hbnd he

theorem ColdMildAE.window {q b L T R s U : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hs : 0 ≤ s) (hU : 0 ≤ U) (hsU : s+U ≤ T)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc : ∀ u, 0 ≤ c u ∧ c u ≤ R)
    (he : ColdMildAE q b L T F c₀ c) :
    ∀ t, (fun p => window s U c (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value U L JetBarrier.flight (fun p => c (s,p))
        (coldForcing q b L (window s U F) (window s U c)) (t,p)) := by
  have hbnd (u) : |coldForcing q b L F c u| ≤ HotApplication.realBound q*R^2+L*R := by
    have h := HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hcm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ coldForcing q b L F c u ∧ coldForcing q b L F c u ≤ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  exact PositiveIntegral.window_mild_ae hT hL hs hU hsU (measurable_coldForcing hFm hcm q b L) hbnd he

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Quantitative local dependence for a.e. mild representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_difference_ae {q b L T R I : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ g₀ : JetPrototype.Phase → ℝ}
    (hseed : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ p-g₀ p| ≤ I)
    {F G : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) (t,p)))
    (hGeq : ∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p))) :
    ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤
      I/(1-T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)) := by
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  let D := SpaceTimeEssSup.size (fun u => F u-G u)
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]
    positivity
  have hD : 0 ≤ D := SpaceTimeEssSup.nonneg _
  have habs (u) : |F u-G u| ≤ 2*R :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg (hF u).1,abs_of_nonneg (hG u).1]; linarith [(hF u).2,(hG u).2])
  have hFD := SpaceTimeEssSup.ae_abs_le_size (hFm.sub hGm) habs
  have hdiff : ∀ᵐ u ∂spacetimeVolume, |forcing q b L F u-forcing q b L G u| ≤ K*D :=
    forcing_difference_ae hq hb hL hR hD hFm hGm hF hG hFD
  have hsrc (U : ℝ × JetPrototype.Phase → ℝ) (hUm : Measurable U)
      (hU : ∀ u, 0 ≤ U u ∧ U u ≤ R) (u) : |forcing q b L U u| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hUm)
      (fun p => hU (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ forcing q b L U u ∧ forcing q b L U u ≤ S at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hbnd (t : ℝ) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ I+T*(K*D) := by
    filter_upwards [hFeq t,hGeq t,
      PositiveIntegral.value_difference_initial_ae_all hT hL (mul_nonneg hK hD) hI hseed
        (measurable_forcing hFm q b L) (measurable_forcing hGm q b L)
        (hsrc F hFm hF) (hsrc G hGm hG) hdiff t] with p hf hg hp
    rwa [hf,hg]
  have hspace : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ I+T*(K*D) :=
    (ae_prod_iff_ae_ae (measurableSet_le (hFm.sub hGm).abs measurable_const)).mpr (ae_of_all _ hbnd)
  have hineq : D ≤ I+T*(K*D) :=
    SpaceTimeEssSup.size_le_ae (hFm.sub hGm) (by positivity) hspace
  have hden : 0 < 1-T*K := by dsimp [K]; linarith
  have hDQ : D ≤ I/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hineq])
  have hmul := mul_le_mul_of_nonneg_left hDQ (mul_nonneg hT hK)
  have hQ : I/(1-T*K)*(1-T*K) = I := div_mul_cancel₀ I hden.ne'
  have hfinal : I+T*(K*D) ≤ I/(1-T*K) := by nlinarith
  intro t
  exact (hbnd t).mono (fun p hp => hp.trans hfinal)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The hot remainder of a countable almost-everywhere mild cold family -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem family_hot_mildAE {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    {F₀ : JetPrototype.Phase → ℝ} {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hc₀n : ∀ i p, 0 ≤ c₀ i p)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : MildAE q b L T F₀ F) (hceq : ∀ i, ColdMildAE q b L T F (c₀ i) (c i)) :
    ∀ t ∈ Icc 0 T, (fun p => F (t,p)-∑' i, c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (fun x => F₀ x-∑' i, c₀ i x) (remainderForcing q b L F c) (t,p)) := by
  classical
  let G (i : I) := coldForcing q b L F (c i)
  let S := HotApplication.realBound q*R^2+L*R
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    have hs := hSum {i} u
    simpa only [Finset.sum_singleton] using hs.trans (hF u).2
  have hgm (i) : Measurable (G i) := measurable_coldForcing hFm (hcm i) q b L
  have hgb (i) (u) : 0 ≤ G i u ∧ G i u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hcm i)) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hcb i (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  have hgsum (s : Finset I) (u) : (∑ i ∈ s, G i u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i _ => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hFm)
      (fun i _ p => hcb i (p.1.1,(p.1.2,p.2))) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hSum s (p.1.1,(p.1.2,p.2))) _
  have hgs (u) : Summable (fun i => G i u) :=
    summable_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  have hgBound (u) : (∑' i, G i u) ≤ forcing q b L F u :=
    Real.tsum_le_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  have hga (u) : |∑' i, G i u| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hgb i u).1))]
    exact (hgBound u).trans (hfb u).2
  intro t ht
  have hcae : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ i, c i (t,p) =
      PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) (t,p) :=
    ae_all_iff.mpr (fun i => hceq i t ht)
  filter_upwards [hFeq t ht,hcae] with p hfp hcp
  have hs := PositiveIntegral.hasSum_value hT hL GaussianLocal.measurable_flight c₀
    (fun p => summable_of_sum_le (fun i => hc₀n i p) (fun s => hSum₀ s p)) G hgm hgb hgs
    (fun u => (hgBound u).trans (hfb u).2) (t,p)
  have he : (fun i => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) (t,p)) =
      (fun i => c i (t,p)) := funext (fun i => (hcp i).symm)
  rw [he] at hs
  rw [hfp,hs.tsum_eq]
  exact PositiveIntegral.value_sub hT hL (measurable_forcing hFm q b L) (Measurable.tsum hgm)
    (fun u => by rw [abs_of_nonneg (hfb u).1]; exact (hfb u).2) hga F₀ (fun p => ∑' i, c₀ i p) (t,p)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniqueness on each weighted local construction interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_unique {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    (f₀ : JetPrototype.Phase → ℝ) {f g : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L g) z) : f = g := by
  funext z
  have h := normalized_difference hq hb hL hT hR (le_refl 0) hloss hsmall
    (fun p => by simp only [sub_self,abs_zero,le_refl]) hfm hgm hf hg hfeq hgeq z
  rw [zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniform dependence on all prefixes of a fixed bounded interval -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem bounded_interval_stability_uniform {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (_hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : ℝ}, 0 ≤ U → U ≤ T → ∀ {A : ℝ}, 0 ≤ A →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ},
      Measurable F → Measurable G →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      MildAE q b L U F₀ F → MildAE q b L U G₀ G →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A) →
      ∀ t ∈ Icc 0 U, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ C*A := by
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
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
  refine ⟨2^n,by positivity,?_⟩
  intro U hU hUT A hA F G F₀ G₀ hFm hGm hF hG hFe hGe hseed
  have hreachU : U ≤ (n:ℝ)*δ := hUT.trans hreach
  have hzero : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (0,p)-G (0,p)| ≤ A := by
    filter_upwards [hFe.initial_ae hU,hGe.initial_ae hU,hseed] with p hf hg hp
    simpa only [hf,hg] using hp
  have hsteps : ∀ j : ℕ, ∀ t ∈ Icc 0 (min ((j:ℝ)*δ) U),
      ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ (2:ℝ)^j*A := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have htzero : t ≤ 0 := by simpa only [Nat.cast_zero,zero_mul,min_eq_left hU] using ht.2
      have ht0 : t = 0 := le_antisymm htzero ht.1
      subst t
      simpa only [pow_zero,one_mul] using hzero
    | succ j ih =>
      intro t ht
      have htT : t ≤ U := ht.2.trans (min_le_right _ _)
      have htj : t ≤ ((j+1:ℕ):ℝ)*δ := ht.2.trans (min_le_left _ _)
      have hAj : 0 ≤ (2:ℝ)^j*A := mul_nonneg (pow_nonneg (by norm_num) j) hA
      by_cases hprefix : t ≤ min ((j:ℝ)*δ) U
      · exact (ih t ⟨ht.1,hprefix⟩).mono (fun p hp => hp.trans (by
          rw [pow_succ]
          nlinarith))
      · let s : ℝ := (j:ℝ)*δ
        have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg j) hδ.le
        have hst : s < t := by
          have hnot : ¬ t ≤ (j:ℝ)*δ := fun h => hprefix (le_min h htT)
          exact lt_of_not_ge hnot
        have hsT : s ≤ U := hst.le.trans htT
        have hinit := ih s ⟨hs,le_min le_rfl hsT⟩
        let V := t-s
        have hV : 0 ≤ V := sub_nonneg.mpr hst.le
        have hUδ : V ≤ δ := by
          dsimp [V,s]
          rw [Nat.cast_add,Nat.cast_one] at htj
          nlinarith
        have hUK : V*K < 1/2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUδ hK) hδK
        have hsmall : V*K < 1 := hUK.trans (by norm_num)
        have hsU : s+V ≤ U := by dsimp [V]; linarith
        have hfwin := MildAE.window hq hb hL hU hR hloss hs hV hsU hFm hF hFe
        have hgwin := MildAE.window hq hb hL hU hR hloss hs hV hsU hGm hG hGe
        have he := normalized_difference_ae hq hb hL hV hR hAj hloss hsmall hinit
          (PositiveIntegral.measurable_window s V hFm) (PositiveIntegral.measurable_window s V hGm)
          (fun u => hF _) (fun u => hG _) hfwin hgwin V
        have hfac : ((2:ℝ)^j*A)/(1-V*K) ≤ (2:ℝ)^(j+1)*A := by
          apply (div_le_iff₀ (by linarith : 0 < 1-V*K)).mpr
          rw [pow_succ]
          nlinarith
        filter_upwards [he] with p hp
        have hUtime : PositiveIntegral.time V V = V := GaussianLocal.time_eq ⟨hV,le_rfl⟩
        change |F (s+PositiveIntegral.time V V,p)-G (s+PositiveIntegral.time V V,p)| ≤ _ at hp
        rw [hUtime,show s+V=t by dsimp [V]; ring] at hp
        exact hp.trans hfac
  intro t ht
  exact hsteps n t ⟨ht.1,by simpa only [min_eq_right hreachU] using ht.2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Closure of bounded positive mild solutions under uniform a.e. approximation -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

theorem exists_mild_limit {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℕ → ℝ × JetPrototype.Phase → ℝ}
    {f₀ : ℕ → JetPrototype.Phase → ℝ} {g₀ : JetPrototype.Phase → ℝ} {a : ℕ → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hF : ∀ n u, 0 ≤ F n u ∧ F n u ≤ R)
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hclose : ∀ n m t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F n (t,p)-F m (t,p)| ≤ a n+a m)
    (hseed : ∀ n, ∀ᵐ p ∂FlightMeasure.phaseVolume, |f₀ n p-g₀ p| ≤ a n)
    (hfix : ∀ n t, (fun p => F n (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (f₀ n) (forcing q b L (F n)) (t,p))) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧ (∀ u, 0 ≤ G u ∧ G u ≤ R) ∧
      (∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p))) ∧
      (∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F n (t,p)-G (t,p)| ≤ a n) ∧
      ∀ v : (ℝ × JetPrototype.Phase) → ℝ × JetPrototype.Phase,
        (∀ n u, F n (v u) = F n u) → ∀ u, G (v u) = G u := by
  obtain ⟨G,hGm,hG,hFG,hInv⟩ := exists_slice_uniform_limit hR hFm hF ha ha0 hclose
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K]
    positivity
  have hsrc (U : ℝ × JetPrototype.Phase → ℝ) (hUm : Measurable U)
      (hU : ∀ u, 0 ≤ U u ∧ U u ≤ R) (u) : |forcing q b L U u| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hUm) (fun p => hU (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ forcing q b L U u ∧ forcing q b L U u ≤ S at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hsource (n) : ∀ᵐ u ∂spacetimeVolume,
      |forcing q b L (F n) u-forcing q b L G u| ≤ K*a n :=
    forcing_difference_ae hq hb hL hR (ha n) (hFm n) hGm (hF n) hG
      ((ae_prod_iff_ae_ae (measurableSet_le ((hFm n).sub hGm).abs measurable_const)).mpr
        (ae_of_all _ (hFG n)))
  have hval (n t) := PositiveIntegral.value_difference_initial_ae_all hT hL
    (mul_nonneg hK (ha n)) (ha n) (hseed n)
    (measurable_forcing (hFm n) q b L) (measurable_forcing hGm q b L)
    (hsrc (F n) (hFm n) (hF n)) (hsrc G hGm hG) (hsource n) t
  refine ⟨G,hGm,hG,?_,hFG,hInv⟩
  intro t
  have hbnd (n) : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |G (t,p)-PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p)| ≤
        (2+T*K)*a n := by
    filter_upwards [hFG n t,hfix n t,hval n t] with p hp he hv
    calc
      _ ≤ |G (t,p)-F n (t,p)|+
          |F n (t,p)-PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L G) (t,p)| :=
        abs_sub_le _ _ _
      _ ≤ a n+(a n+T*(K*a n)) := by
        rw [abs_sub_comm] at hp
        rw [← he] at hv
        exact add_le_add hp hv
      _ = (2+T*K)*a n := by ring
  filter_upwards [ae_all_iff.mpr hbnd] with p hp
  have hz : Tendsto (fun n => (2+T*K)*a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ha0
  have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hz hp
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # A common positive local time for bounded weighted data -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocalControl

def damping (q b A : ℝ) : ℝ := 2*A*CutoffLipschitz.frequencyConstant q b

def sourceBound (q b A : ℝ) : ℝ := HotApplication.realBound q*(2*A)^2+damping q b A*(2*A)

def lipschitz (q b A : ℝ) : ℝ :=
  2*(2*A)*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+damping q b A

def lifespan (q b A : ℝ) : ℝ := min (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1))

theorem bounds {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) :
    0 ≤ damping q b A ∧ 0 ≤ sourceBound q b A ∧ 0 ≤ lipschitz q b A := by
  have hC := CutoffLipschitz.frequencyConstant_nonneg hb q
  have hG := (HotApplication.realBound_pos q).le
  have hL : 0 ≤ damping q b A := by unfold damping; positivity
  exact ⟨hL, by unfold sourceBound; positivity, by unfold lipschitz; positivity⟩

theorem lifespan_pos {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) : 0 < lifespan q b A := by
  obtain ⟨_,hS,hK⟩ := bounds (q := q) hb hA
  exact lt_min (div_pos hA (by positivity)) (div_pos (by norm_num) (by positivity))

theorem small {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) :
    lifespan q b A*lipschitz q b A < 1 := by
  obtain ⟨_,_,hK⟩ := bounds (q := q) hb hA
  have hT := lifespan_pos (q := q) hb hA
  have h := (le_div_iff₀ (by positivity : 0 < lipschitz q b A+1)).mp
    (min_le_right (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1)))
  change lifespan q b A*(lipschitz q b A+1) ≤ 1/2 at h
  nlinarith

theorem exists_solution {q b A : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ F : ℝ × JetPrototype.Phase → ℝ, Measurable F ∧
      (∀ z, 0 ≤ F z ∧ F z ≤ 2*A) ∧
      ∀ z, F z = PositiveIntegral.value (lifespan q b A) (damping q b A)
        JetBarrier.flight f₀ (WeightedLocal.forcing q b (damping q b A) F) z := by
  obtain ⟨hL,hS,_⟩ := bounds (q := q) hb hA
  have hT := lifespan_pos (q := q) hb hA
  have h := (le_div_iff₀ (by positivity : 0 < sourceBound q b A+1)).mp
    (min_le_left (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1)))
  change lifespan q b A*(sourceBound q b A+1) ≤ A at h
  have hball : A+lifespan q b A*sourceBound q b A ≤ 2*A := by nlinarith
  exact WeightedLocal.exists_normalized hq hb hL hT.le hA.le (by positivity) le_rfl hball
    (small hb hA) hf₀m hf₀

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Uniform dependence on a fixed bounded solution interval -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.PositiveIntegral (window)

namespace BoltzmannNonuniqueness.WeightedLocal

theorem bounded_interval_stability {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A : ℝ}, 0 ≤ A →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ},
      Measurable F → Measurable G →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      MildAE q b L T F₀ F → MildAE q b L T G₀ G →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A) →
      ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ C*A := by
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
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
  refine ⟨2^n,by positivity,?_⟩
  intro A hA F G F₀ G₀ hFm hGm hF hG hFe hGe hseed
  have hzero : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (0,p)-G (0,p)| ≤ A := by
    filter_upwards [hFe.initial_ae hT,hGe.initial_ae hT,hseed] with p hf hg hp
    simpa only [hf,hg] using hp
  have hsteps : ∀ j : ℕ, ∀ t ∈ Icc 0 (min ((j:ℝ)*δ) T),
      ∀ᵐ p ∂FlightMeasure.phaseVolume, |F (t,p)-G (t,p)| ≤ (2:ℝ)^j*A := by
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
      have hAj : 0 ≤ (2:ℝ)^j*A := mul_nonneg (pow_nonneg (by norm_num) j) hA
      by_cases hprefix : t ≤ min ((j:ℝ)*δ) T
      · exact (ih t ⟨ht.1,hprefix⟩).mono (fun p hp => hp.trans (by
          rw [pow_succ]
          nlinarith))
      · let s : ℝ := (j:ℝ)*δ
        have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg j) hδ.le
        have hst : s < t := by
          have hnot : ¬ t ≤ (j:ℝ)*δ := fun h => hprefix (le_min h htT)
          exact lt_of_not_ge hnot
        have hsT : s ≤ T := hst.le.trans htT
        have hinit := ih s ⟨hs,le_min le_rfl hsT⟩
        let U := t-s
        have hU : 0 ≤ U := sub_nonneg.mpr hst.le
        have hUδ : U ≤ δ := by
          dsimp [U,s]
          rw [Nat.cast_add,Nat.cast_one] at htj
          nlinarith
        have hUK : U*K < 1/2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hUδ hK) hδK
        have hsmall : U*K < 1 := hUK.trans (by norm_num)
        have hsU : s+U ≤ T := by dsimp [U]; linarith
        have hfwin := MildAE.window hq hb hL hT hR hloss hs hU hsU hFm hF hFe
        have hgwin := MildAE.window hq hb hL hT hR hloss hs hU hsU hGm hG hGe
        have he := normalized_difference_ae hq hb hL hU hR hAj hloss hsmall hinit
          (PositiveIntegral.measurable_window s U hFm) (PositiveIntegral.measurable_window s U hGm)
          (fun u => hF _) (fun u => hG _) hfwin hgwin U
        have hfac : ((2:ℝ)^j*A)/(1-U*K) ≤ (2:ℝ)^(j+1)*A := by
          apply (div_le_iff₀ (by linarith : 0 < 1-U*K)).mpr
          rw [pow_succ]
          nlinarith
        filter_upwards [he] with p hp
        have hUtime : PositiveIntegral.time U U = U := GaussianLocal.time_eq ⟨hU,le_rfl⟩
        change |F (s+PositiveIntegral.time U U,p)-G (s+PositiveIntegral.time U U,p)| ≤ _ at hp
        rw [hUtime,show s+U=t by dsimp [U]; ring] at hp
        exact hp.trans hfac
  intro t ht
  exact hsteps n t ⟨ht.1,by simpa only [min_eq_right hreach] using ht.2⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Restricting a mild solution to a shorter time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem MildAE.restrict_clamp {q b L T S : ℝ} (_hS : 0 ≤ S) (hST : S ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : MildAE q b L T f₀ F) : MildAE q b L S f₀ (clampTime S F) := by
  intro t ht
  filter_upwards [hF t ⟨ht.1,ht.2.trans hST⟩] with p hp
  change F (PositiveIntegral.time S t,p) = _
  rw [GaussianLocal.time_eq ht,hp]
  apply PositiveIntegral.value_eq_at_time ⟨ht.1,ht.2.trans hST⟩ ht.2
  intro r hr p
  rw [forcing_clampTime,GaussianLocal.time_eq ⟨hr.1,hr.2.trans ht.2⟩]

theorem clampTime_idempotent {T : ℝ} (hT : 0 ≤ T)
    (F : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    clampTime T F (PositiveIntegral.time T u.1,u.2) = clampTime T F u := by
  change F (PositiveIntegral.time T (PositiveIntegral.time T u.1),u.2) = _
  rw [PhaseEssSup.time_idempotent hT]
  rfl

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Periodic covariance follows from the constructed local uniqueness -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

theorem shift_neg_shift (y : Space) (p : JetPrototype.Phase) : shift (-y) (shift y p) = p := by
  simp [shift]

theorem shift_shift_neg (y : Space) (p : JetPrototype.Phase) : shift y (shift (-y) p) = p := by
  simp [shift]

theorem solution_covariance {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight f₀ (WeightedLocal.forcing q b L F) z)
    (y : Space) (hseed : ∀ p, f₀ (shift y p) = f₀ p) : pull y F = F := by
  have hseed' : (fun p => f₀ (shift y p)) = f₀ := funext hseed
  have hfix (z) := fixed_point_pull hFeq y z
  rw [hseed'] at hfix
  exact WeightedLocal.normalized_unique hq hb hL hT hR hloss hsmall f₀
    (measurable_pull hFm y) hFm (fun z => hF (z.1,shift y z.2)) hF hfix hFeq

end BoltzmannNonuniqueness.WeightedTranslation

end

end

section

/-! # Actual cold limits inherit the pointwise jet bound -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedJetComparison

theorem picard_le {q b L T R K α γ s d : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) z)
    (hseed : ∀ p, VelocityWeight.H q p.2 * c₀ p ≤ density η K α γ s d a p) :
    ∀ n t, t ∈ Ioc 0 T → ∀ p,
      physical q (coldPicard q b L T F c₀ n) (t,p) ≤ JetSupersolution.U η K α γ s d t a p := by
  have hp := coldPicard_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hFeq
  intro n
  induction n with
  | zero =>
    intro t ht p
    simpa only [physical, coldPicard, mul_zero] using JetSupersolution.nonneg hK hs hd η α γ t a p
  | succ n ih =>
    intro t ht p
    have hc (z) : 0 ≤ coldPicard q b L T F c₀ n z ∧ coldPicard q b L T F c₀ n z ≤ R :=
      ⟨((hp n).2 z).1, ((hp n).2 z).2.trans (hF z).2⟩
    have hh := step_le hq hb hL hT hR hloss hK hα hγ hs hd hTmax hε η a
      hFm (hp n).1 hF hc hseed ih ht (JetBarrier.flight (-t) p)
    simpa only [coldPicard, JetSupersolution.along, JetFreeTransport.flight_neg] using hh

theorem limit_le {q b L T R K α γ s d : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) z)
    (hseed : ∀ p, VelocityWeight.H q p.2 * c₀ p ≤ density η K α γ s d a p)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (coldLimit q b L T F c₀) (t,p) ≤ JetSupersolution.U η K α γ s d t a p := by
  have hlim := (coldLimit_solution hq hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hFeq).2.2.2 (t,p)
  apply le_of_tendsto (hlim.const_mul (VelocityWeight.H q p.2))
  exact Eventually.of_forall (fun n =>
    picard_le hq hb hL hT hR hloss hK hα hγ hs hd hTmax hε η a hFm hc₀m hF hc₀ hF₀ hFeq hseed n t ht p)

end BoltzmannNonuniqueness.WeightedJetComparison

end

end

section

/-! # Geometric cold control for each actual periodic copy -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedJetComparison

theorem shifted_limit_le {q b L T R K α γ s d : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (hTmax : T ≤ 1) (hε : JetSupersolution.epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) (y : Space)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) z)
    (hseed : ∀ p, VelocityWeight.H q p.2*c₀ p ≤ density η K α γ s d a (shift y p))
    {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    physical q (coldLimit q b L T F c₀) (t,p) ≤
      JetSupersolution.U η K α γ s d t a (shift y p) := by
  have hs' (u) : VelocityWeight.H q u.2*c₀ (shift (-y) u) ≤ density η K α γ s d a u := by
    have h := hseed (shift (-y) u)
    change VelocityWeight.H q u.2*c₀ (shift (-y) u) ≤
      density η K α γ s d a (shift y (shift (-y) u)) at h
    rwa [shift_shift_neg] at h
  have h := limit_le hq hb hL hT hR hloss hK hα hγ hs hd hTmax hε η a
    (measurable_pull hFm (-y)) (hc₀m.comp (measurable_shift (-y)))
    (fun z => hF (z.1,shift (-y) z.2)) (fun u => hc₀ (shift (-y) u))
    (fun u => hF₀ (shift (-y) u)) (fixed_point_pull hFeq (-y)) hs' ht (shift y p)
  change VelocityWeight.H q p.2 *
    coldLimit q b L T (pull (-y) F) (fun u => c₀ (shift (-y) u)) (t,shift y p) ≤ _ at h
  rw [coldLimit_pull] at h
  change VelocityWeight.H q p.2 * coldLimit q b L T F c₀ (t,shift (-y) (shift y p)) ≤ _ at h
  rwa [shift_neg_shift] at h

end BoltzmannNonuniqueness.WeightedJetComparison

end

end

end OAI
