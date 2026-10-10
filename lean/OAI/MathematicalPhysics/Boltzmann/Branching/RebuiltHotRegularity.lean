import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdTime
import OAI.MathematicalPhysics.Boltzmann.Branching.FamilyHotBounds
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPhysicalSource
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.RebuiltHotInitial
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdFamilyGlobalStabilityAE
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative

namespace OAI

section

/-! # Dependence of the reconstructed hot remainder on its total seed -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem rebuilt_hot_difference_ae {I : Type*} [Countable I] {q b L T R A : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hcF₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hcG₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ G₀ p)
    (hseed : ∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p)))
    (hGeq : ∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight G₀ (forcing q b L G) (t,p)))
    (hFc : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (hGc : ∀ u, G (PositiveIntegral.time T u.1,u.2) = G u) :
    let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
    let J := R*CutoffLipschitz.frequencyConstant q b
    let C := 2*R*HotApplication.realBound q+L+J
    ∀ t, |PhaseEssSup.size (fun p => F (t,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (t,p))-
      PhaseEssSup.size (fun p => G (t,p)-∑' i, rebuiltColdFamily q b L T G c₀ i (t,p))| ≤
      A/(1-T*K)+(T*J*(A/(1-T*K)))/(1-T*C) := by
  dsimp only
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let J := R*CutoffLipschitz.frequencyConstant q b
  let C := 2*R*HotApplication.realBound q+L+J
  let D := A/(1-T*K)
  let c := rebuiltColdFamily q b L T F c₀
  let d := rebuiltColdFamily q b L T G c₀
  have hden : 0 < 1-T*K := by dsimp [K]; linarith
  have hD : 0 ≤ D := div_nonneg hA hden.le
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  have hCK : C ≤ K := by dsimp [C,K]; nlinarith
  have hsmallC : T*C < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hCK hT) hsmall
  have hE : 0 ≤ T*J*D/(1-T*C) := div_nonneg (by positivity) (by linarith)
  obtain ⟨hcm,hcb,hcs,_,hce⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hFm hc₀m hF hc₀ hcF₀ hFeq
  obtain ⟨hdm,hdb,hds,_,hde⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hGm hc₀m hG hc₀ hcG₀ hGeq
  have hcn (i) (u) : 0 ≤ c i u := (hcb i u).1
  have hdn (i) (u) : 0 ≤ d i u := (hdb i u).1
  have hFG := normalized_difference_ae hq hb hL hT hR hA hloss hsmall hseed hFm hGm hF hG hFeq hGeq
  have hFGspace : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D :=
    (ae_prod_iff_ae_ae (measurableSet_le (hFm.sub hGm).abs measurable_const)).mpr (ae_of_all _ hFG)
  have hceall (i) := mild_all_of_time_clamp hT L
    (rebuiltColdFamily_time_clamp hT q b L hFc c₀ i) (hce i)
  have hdeall (i) := mild_all_of_time_clamp hT L
    (rebuiltColdFamily_time_clamp hT q b L hGc c₀ i) (hde i)
  have hseedC (s : Finset I) : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, |c₀ i p-c₀ i p|) ≤ 0 := by
    exact ae_of_all _ (fun p => by simp only [sub_self,abs_zero,Finset.sum_const_zero,le_refl])
  have hcd := cold_family_difference_ae hq hb hL hT hR (le_refl 0) hD hloss hsmallC
    hFm hGm hcm hdm hF hG hcn hdn hcs hds hFGspace hseedC hceall hdeall
  intro t
  have hn := PhaseEssSup.hot_difference_ae hD hE
    (hFm.comp (measurable_const.prodMk measurable_id)) (hGm.comp (measurable_const.prodMk measurable_id))
    (fun i => (hcm i).comp (measurable_const.prodMk measurable_id))
    (fun i => (hdm i).comp (measurable_const.prodMk measurable_id))
    (fun p => hF (t,p)) (fun p => hG (t,p)) (fun i p => hcn i (t,p)) (fun i p => hdn i (t,p))
    (fun s p => hcs s (t,p)) (fun s p => hds s (t,p)) (hFG t)
    (by simpa only [zero_add,Function.comp_apply,id_eq,J,C] using hcd t)
  exact hn

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniform seed dependence for the reconstructed hot norm on a fixed interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem exists_rebuilt_hot_stability_constant {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A : ℝ}, 0 ≤ A →
      ∀ {F G : ℝ × JetPrototype.Phase → ℝ} {F₀ G₀ : JetPrototype.Phase → ℝ}
        {c₀ : I → JetPrototype.Phase → ℝ},
      Measurable F → Measurable G → (∀ i, Measurable (c₀ i)) →
      (∀ u, 0 ≤ F u ∧ F u ≤ R) → (∀ u, 0 ≤ G u ∧ G u ≤ R) →
      (∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R) →
      (∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p) →
      (∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ G₀ p) →
      (∀ᵐ p ∂FlightMeasure.phaseVolume, |F₀ p-G₀ p| ≤ A) →
      (∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) →
      (∀ t, (fun p => G (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value T L JetBarrier.flight G₀ (forcing q b L G) (t,p))) →
      ∀ t ∈ Icc 0 T,
        |PhaseEssSup.size (fun p => F (t,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (t,p))-
          PhaseEssSup.size (fun p => G (t,p)-∑' i, rebuiltColdFamily q b L T G c₀ i (t,p))| ≤ C*A := by
  obtain ⟨C,hC,hTotal⟩ := bounded_interval_stability hq hb hL hT hR hloss
  obtain ⟨E,hE,hCold⟩ := cold_bounded_interval_stability (I := I) hq hb hL hT hR hloss
  let J := R*CutoffLipschitz.frequencyConstant q b
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  refine ⟨C+E*T*J*C,by positivity,?_⟩
  intro A hA F G F₀ G₀ c₀ hFm hGm hc₀m hF hG hc₀ hcF₀ hcG₀ hseed hFeq hGeq
  obtain ⟨hcm,hcb,hcs,_,hce⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hFm hc₀m hF hc₀ hcF₀ hFeq
  obtain ⟨hdm,hdb,hds,_,hde⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hGm hc₀m hG hc₀ hcG₀ hGeq
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F c₀ i u := (hcb i u).1
  have hdn (i) (u) : 0 ≤ rebuiltColdFamily q b L T G c₀ i u := (hdb i u).1
  have hFG := hTotal hA hFm hGm hF hG (fun t _ => hFeq t) (fun t _ => hGeq t) hseed
  have hseedC : ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c₀ i p-c₀ i p|) ≤ (0:ℝ) := by
    exact ae_of_all _ (fun p => by simp only [sub_self,abs_zero,tsum_zero,le_refl])
  have hcd := hCold (le_refl 0) (mul_nonneg hC.le hA) hFm hGm hcm hdm hF hG
    hcn hdn hcs hds hce hde hFG hseedC
  intro t ht
  have hn := PhaseEssSup.hot_difference_ae (mul_nonneg hC.le hA)
    (show 0 ≤ E*(T*J*(C*A)) by positivity)
    (hFm.comp (measurable_const.prodMk measurable_id)) (hGm.comp (measurable_const.prodMk measurable_id))
    (fun i => (hcm i).comp (measurable_const.prodMk measurable_id))
    (fun i => (hdm i).comp (measurable_const.prodMk measurable_id))
    (fun p => hF (t,p)) (fun p => hG (t,p)) (fun i p => hcn i (t,p)) (fun i p => hdn i (t,p))
    (fun s p => hcs s (t,p)) (fun s p => hds s (t,p)) (hFG t ht)
    (by simpa only [zero_add,Function.comp_apply,id_eq,J] using hcd t ht)
  calc
    _ ≤ C*A+E*(T*J*(C*A)) := hn
    _ = (C+E*T*J*C)*A := by ring

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Time regularity of the reconstructed hot remainder -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem rebuilt_hot_continuous {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF₀m : Measurable F₀) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hF₀ : ∀ p, F₀ p ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ContinuousOn (fun t => PhaseEssSup.size (fun p =>
      F (t,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (t,p))) (Icc 0 T) := by
  obtain ⟨hcm,hcb,hSum,_,hceq⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hFm hc₀m hF hc₀ hSum₀ hFeq
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F c₀ i u := (hcb i u).1
  have hhb := family_hot_bounds hq hb hR hloss hFm hcm hF hcn hSum
  have hhm := family_hot_mildAE hq hb hL hT hR hloss hFm hcm hF hcn hSum
    (fun i p => (hc₀ i p).1) hSum₀ (fun t _ => hFeq t) hceq
  have hinit (p) : 0 ≤ F₀ p-∑' i, c₀ i p ∧ F₀ p-∑' i, c₀ i p ≤ R := by
    have hn : 0 ≤ ∑' i, c₀ i p := tsum_nonneg (fun i => (hc₀ i p).1)
    have hs : (∑' i, c₀ i p) ≤ F₀ p := Real.tsum_le_of_sum_le
      (fun i => (hc₀ i p).1) (fun s => hSum₀ s p)
    exact ⟨sub_nonneg.mpr hs,(sub_le_self _ hn).trans (hF₀ p)⟩
  exact PhaseEssSup.continuousOn_size_of_mildAE
    (f₀ := fun p => F₀ p-∑' i, c₀ i p)
    (g := remainderForcing q b L F (rebuiltColdFamily q b L T F c₀))
    (f := fun u => F u-∑' i, rebuiltColdFamily q b L T F c₀ i u) hT hL hR
    (show 0 ≤ HotApplication.realBound q*R^2+L*R by have := (HotApplication.realBound_pos q).le; positivity)
    (hF₀m.sub (Measurable.tsum hc₀m)) hhb.2.2.1 hinit hhb.2.2.2 hhm

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
