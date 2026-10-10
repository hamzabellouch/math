import OAI.MathematicalPhysics.Boltzmann.Approximation.ColoredSourceDifferenceAE
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdFiniteLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.HotCanonicalFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.SpaceTimeEssSup
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreMomentBound
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

section

/-! # The polynomial optical depth used in the cold-core survival estimate -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def coldOpticalDepth (B A δ D : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  B*t+A*(t^2/2+δ*t)+D*t^(m+1)/(m+1)

theorem coldOpticalDepth_zero (B A δ D : ℝ) (m : ℕ) :
    coldOpticalDepth B A δ D m 0 = 0 := by
  simp [coldOpticalDepth]

theorem coldOpticalDepth_derivative (B A δ D : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (coldOpticalDepth B A δ D m) (B+A*(t+δ)+D*t^m) t := by
  have hB : HasDerivAt (fun t : ℝ => B*t) B t := by
    simpa using (hasDerivAt_id t).const_mul B
  have hA : HasDerivAt (fun t : ℝ => A*(t^2/2+δ*t)) (A*(t+δ)) t := by
    convert (((hasDerivAt_id t).pow 2).div_const 2 |>.add
      ((hasDerivAt_id t).const_mul δ)).const_mul A using 1
    · funext r
      simp only [Pi.add_apply,Pi.pow_apply,id_eq]
    · simp only [id_eq]
      ring
  have hD : HasDerivAt (fun t : ℝ => D*t^(m+1)/(m+1)) (D*t^m) t := by
    convert (((hasDerivAt_id t).pow (m+1)).const_mul D).div_const (m+1:ℝ) using 1
    · funext r
      simp only [Pi.pow_apply,id_eq]
    · simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,id_eq]
      field_simp
  exact (hB.add hA).add hD

theorem coldOpticalDepth_nonneg {B A δ D t : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ coldOpticalDepth B A δ D m t := by
  unfold coldOpticalDepth
  positivity

namespace WeightedLocal

theorem cold_survival_polynomial {q b L T R t B A δ D : ℝ} (m : ℕ)
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (hceq : ∀ s ∈ Icc 0 T, ∀ p, c (s,p) =
      PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c) (s,p))
    (ht : t ∈ Icc 0 T) (p : JetPrototype.Phase)
    (hν : ∀ᵐ r, r ∈ Icc 0 t → CollisionCutoff.frequency b
      (fun v => physical q F (r,((JetBarrier.flight r p).1,v))) p.2 ≤
        B+A*(r+δ)+D*r^m) :
    Real.exp (-coldOpticalDepth B A δ D m t)*c₀ p ≤ c (t,JetBarrier.flight t p) := by
  have he : ContDiff ℝ 1 (coldOpticalDepth B A δ D m) := by
    unfold coldOpticalDepth
    fun_prop
  have h := cold_survival hq hb hR hloss hFm hcm hF hc hceq ht p he
    (coldOpticalDepth_derivative B A δ D m) hν
  simpa only [coldOpticalDepth_zero,zero_sub] using h

end WeightedLocal
end BoltzmannNonuniqueness

end

end

section

/-! # Pointwise dominated representatives of an almost-everywhere cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

def normalizedFamily (F : ℝ × JetPrototype.Phase → ℝ)
    (c : I → ℝ × JetPrototype.Phase → ℝ) (i : I) (u : ℝ × JetPrototype.Phase) : ℝ := by
  classical
  exact if ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u then c i u else 0

theorem measurable_normalizedFamily {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hcm : ∀ i, Measurable (c i)) (i : I) :
    Measurable (normalizedFamily F c i) := by
  classical
  have he : {u : ℝ × JetPrototype.Phase | ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u} =
      ⋂ s : Finset I, {u | (∑ j ∈ s, c j u) ≤ F u} := by ext u; simp
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u} := by
    rw [he]
    exact MeasurableSet.iInter (fun s => measurableSet_le
      (Finset.measurable_sum s (fun j _ => hcm j)) hFm)
  exact (hcm i).ite hm measurable_const

omit [Countable I] in
theorem normalizedFamily_bounds {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hcn : ∀ i u, 0 ≤ c i u) (i : I) (u) :
    0 ≤ normalizedFamily F c i u ∧ normalizedFamily F c i u ≤ c i u := by
  classical
  unfold normalizedFamily
  split_ifs
  · exact ⟨hcn i u,le_rfl⟩
  · exact ⟨le_rfl,hcn i u⟩

omit [Countable I] in
theorem normalizedFamily_sum_le {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) (c : I → ℝ × JetPrototype.Phase → ℝ) (s : Finset I) (u) :
    (∑ i ∈ s, normalizedFamily F c i u) ≤ F u := by
  classical
  by_cases hu : ∀ r : Finset I, (∑ j ∈ r, c j u) ≤ F u
  · simpa only [normalizedFamily,ite_eq_left hu] using hu s
  · simpa only [normalizedFamily,ite_eq_right hu,Finset.sum_const_zero] using hF u

theorem normalizedFamily_ae_at_time {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hfinite : ∀ s : Finset I, ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, c i (t,p)) ≤ F (t,p))
    (i : I) (t : ℝ) : (fun p => normalizedFamily F c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => c i (t,p)) := by
  classical
  have hg : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ s : Finset I, (∑ j ∈ s, c j (t,p)) ≤ F (t,p) :=
    ae_all_iff.mpr (fun s => hfinite s t)
  filter_upwards [hg] with p hp
  exact ite_eq_left hp

omit [Countable I] in
theorem normalizedFamily_summable {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u) (hcn : ∀ i u, 0 ≤ c i u) (u) :
    Summable (fun i => normalizedFamily F c i u) ∧ (∑' i, normalizedFamily F c i u) ≤ F u := by
  have hn (i) : 0 ≤ normalizedFamily F c i u := (normalizedFamily_bounds hcn i u).1
  have hs (s : Finset I) := normalizedFamily_sum_le hF c s u
  exact ⟨summable_of_sum_le hn hs,Real.tsum_le_of_sum_le hn hs⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Covariance of sums and sources under relabeling of a cold family -/

noncomputable section

open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

omit [Countable I] in
theorem family_sum_pull (y : JetPrototype.Space) (e : I ≃ I)
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hc : ∀ i, pull y (c i) = c (e i))
    (u : ℝ × JetPrototype.Phase) :
    (∑' i, c i (u.1,shift y u.2)) = ∑' i, c i u := by
  have he (i) : c i (u.1,shift y u.2) = c (e i) u := congrFun (hc i) u
  simp_rw [he]
  exact e.tsum_eq (fun i => c i u)

omit [Countable I] in
theorem familyReplacement_pull (y : JetPrototype.Space) (e : I ≃ I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hF : pull y F = F) (hc : ∀ i, pull y (c i) = c (e i)) :
    pull y (HotCanonical.familyReplacement F c) = HotCanonical.familyReplacement F c := by
  funext u
  simp only [pull,HotCanonical.familyReplacement,HotCanonical.replacement,PhaseEssSup.canonical]
  rw [family_sum_pull y e hc u,show F (u.1,shift y u.2) = F u from congrFun hF u]

omit [Countable I] in
theorem remainderForcing_pull (q b L : ℝ) (y : JetPrototype.Space) (e : I ≃ I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hF : pull y F = F) (hc : ∀ i, pull y (c i) = c (e i)) :
    pull y (remainderForcing q b L F c) = remainderForcing q b L F c := by
  have hf : pull y (forcing q b L F) = forcing q b L F := by rw [← forcing_pull,hF]
  funext u
  change forcing q b L F (u.1,shift y u.2)-_ = forcing q b L F u-_
  rw [show forcing q b L F (u.1,shift y u.2) = forcing q b L F u from congrFun hf u]
  congr 1
  have he (i) : coldForcing q b L F (c i) (u.1,shift y u.2) = coldForcing q b L F (c (e i)) u := by
    have h := coldForcing_pull q b L y F (c i)
    rw [hF,hc i] at h
    exact (congrFun h u).symm
  simp_rw [he]
  exact e.tsum_eq (fun i => coldForcing q b L F (c i) u)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Local stability of a countable cold family in the sum norm -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem cold_family_difference_ae {I : Type*} [Countable I] {q b L T R B D : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*HotApplication.realBound q+L+R*CutoffLipschitz.frequencyConstant q b) < 1)
    {F G : ℝ × JetPrototype.Phase → ℝ} {c d : I → ℝ × JetPrototype.Phase → ℝ}
    {c₀ d₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i, Measurable (c i)) (hdm : ∀ i, Measurable (d i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hcn : ∀ i u, 0 ≤ c i u) (hdn : ∀ i u, 0 ≤ d i u)
    (hcSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hdSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, d i u ≤ G u)
    (hFG : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D)
    (hseed : ∀ s : Finset I, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, |c₀ i p-d₀ i p|) ≤ B)
    (hceq : ∀ i t, (fun p => c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (coldForcing q b L F (c i)) (t,p)))
    (hdeq : ∀ i t, (fun p => d i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (d₀ i) (coldForcing q b L G (d i)) (t,p))) :
    ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑' i, |c i (t,p)-d i (t,p)|) ≤
      (B+T*(R*CutoffLipschitz.frequencyConstant q b)*D)/
        (1-T*(2*R*HotApplication.realBound q+L+R*CutoffLipschitz.frequencyConstant q b)) := by
  classical
  let J := R*CutoffLipschitz.frequencyConstant q b
  let K := 2*R*HotApplication.realBound q+L+J
  let S := HotApplication.realBound q*R^2+L*R
  let e (u : ℝ × JetPrototype.Phase) := ∑' i, |c i u-d i u|
  let E := SpaceTimeEssSup.size e
  have hJ : 0 ≤ J := mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    dsimp [K]
    positivity
  have hE : 0 ≤ E := SpaceTimeEssSup.nonneg _
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hcSum {i} u).trans (hF u).2
  have hdb (i) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    refine ⟨hdn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hdSum {i} u).trans (hG u).2
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hcSum s u)
  have hds (u) : Summable (fun i => d i u) := summable_of_sum_le (fun i => hdn i u) (fun s => hdSum s u)
  have hes (u) : Summable (fun i => |c i u-d i u|) := (hcs u |>.sub (hds u)).abs
  have hem : Measurable e := Measurable.tsum (fun i => (hcm i |>.sub (hdm i)).abs)
  have hen (u) : 0 ≤ e u := tsum_nonneg (fun i => abs_nonneg _)
  have heb (u) : |e u| ≤ 2*R := by
    rw [abs_of_nonneg (hen u)]
    have hcF : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hcSum s u)
    have hdG : (∑' i, d i u) ≤ G u := Real.tsum_le_of_sum_le (fun i => hdn i u) (fun s => hdSum s u)
    have hecd : e u ≤ (∑' i, c i u)+(∑' i, d i u) := by
      rw [← (hcs u).tsum_add (hds u)]
      exact (hes u).tsum_le_tsum (fun i => by
        rw [abs_sub_le_iff]
        constructor <;> linarith [hcn i u,hdn i u]) ((hcs u).add (hds u))
    linarith [(hF u).2,(hG u).2]
  have heAE : ∀ᵐ u ∂spacetimeVolume, e u ≤ E := by
    filter_upwards [SpaceTimeEssSup.ae_abs_le_size hem heb] with u hu
    exact (le_abs_self _).trans hu
  have hsource (s : Finset I) : ∀ᵐ u ∂spacetimeVolume,
      (∑ i ∈ s, |coldForcing q b L F (c i) u-coldForcing q b L G (d i) u|) ≤ K*E+J*D := by
    have hefin : ∀ᵐ u ∂spacetimeVolume, (∑ i ∈ s, |c i u-d i u|) ≤ E :=
      heAE.mono (fun u hu => ((hes u).sum_le_tsum s (fun i _ => abs_nonneg _)).trans hu)
    have h := finite_coldForcing_difference_ae s hq hb hL hR hD hE hFm hGm hcm hdm hF hG hcb hdb
      hFG hefin (fun u => (hdSum s u).trans (hG u).2)
    filter_upwards [h] with u hu
    calc
      _ ≤ 2*R*E*HotApplication.realBound q+
          (L+R*CutoffLipschitz.frequencyConstant q b)*E+
          D*CutoffLipschitz.frequencyConstant q b*R := hu
      _ = K*E+J*D := by dsimp [K,J]; ring
  have hsrc (U : ℝ × JetPrototype.Phase → ℝ) (a : I → ℝ × JetPrototype.Phase → ℝ)
      (hUm : Measurable U) (ham : ∀ i, Measurable (a i))
      (hU : ∀ u, 0 ≤ U u ∧ U u ≤ R) (ha : ∀ i u, 0 ≤ a i u ∧ a i u ≤ R)
      (i : I) (u) : |coldForcing q b L U (a i) u| ≤ S := by
    have h := HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hUm) (GaussianLocal.measurable_state (ham i))
      (fun p => hU (p.1.1,(p.1.2,p.2))) (fun p => ha i (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
    change 0 ≤ coldForcing q b L U (a i) u ∧ coldForcing q b L U (a i) u ≤ S at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hbound (t : ℝ) : ∀ᵐ p ∂FlightMeasure.phaseVolume, e (t,p) ≤ B+T*(K*E+J*D) := by
    have hcAll := ae_all_iff.mpr (fun i => hceq i t)
    have hdAll := ae_all_iff.mpr (fun i => hdeq i t)
    have hf (s : Finset I) := PositiveIntegral.finite_difference_ae hT hL
      (show 0 ≤ K*E+J*D by positivity) hB s c₀ d₀
      (fun i => coldForcing q b L F (c i)) (fun i => coldForcing q b L G (d i))
      (fun i _ => measurable_coldForcing hFm (hcm i) q b L)
      (fun i _ => measurable_coldForcing hGm (hdm i) q b L)
      (fun i _ => hsrc F c hFm hcm hF hcb i) (fun i _ => hsrc G d hGm hdm hG hdb i)
      (hseed s) (hsource s) t
    filter_upwards [hcAll,hdAll,ae_all_iff.mpr hf] with p hcp hdp hp
    apply Real.tsum_le_of_sum_le (fun i => abs_nonneg _)
    intro s
    simpa only [← hcp,← hdp] using hp s
  have hspace : ∀ᵐ u ∂spacetimeVolume, e u ≤ B+T*(K*E+J*D) :=
    (ae_prod_iff_ae_ae (measurableSet_le hem measurable_const)).mpr (ae_of_all _ hbound)
  have hineq : E ≤ B+T*(K*E+J*D) := SpaceTimeEssSup.size_le_ae hem (by positivity)
    (hspace.mono (fun u hu => by rwa [abs_of_nonneg (hen u)]))
  have hden : 0 < 1-T*K := by dsimp [K,J]; linarith
  have hEQ : E ≤ (B+T*J*D)/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hineq])
  have hmul := mul_le_mul_of_nonneg_left hEQ (mul_nonneg hT hK)
  have hQ : (B+T*J*D)/(1-T*K)*(1-T*K) = B+T*J*D := div_mul_cancel₀ _ hden.ne'
  have hfinal : B+T*(K*E+J*D) ≤ (B+T*J*D)/(1-T*K) := by nlinarith
  intro t
  exact (hbound t).mono (fun p hp => hp.trans hfinal)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Total-variation control from the cold-core survival sandwich -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem abs_sub_le_of_survival {c f r E : ℝ} (hf : 0 ≤ f) (hr : 0 ≤ r)
    (hE : 0 ≤ E) (hlower : Real.exp (-E)*f ≤ c) (hupper : c ≤ f+r) :
    |c-f| ≤ E*f+r := by
  have he : 1-E ≤ Real.exp (-E) := by linarith only [Real.add_one_le_exp (-E)]
  have hmul := mul_le_mul_of_nonneg_right he hf
  apply abs_le.mpr
  constructor <;> nlinarith only [hlower,hupper,hmul,mul_nonneg hE hf,hr]

theorem integral_abs_sub_le_of_survival {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {c f r : X → ℝ} {E : ℝ}
    (hc : AEStronglyMeasurable c μ) (hf : Integrable f μ) (hr : Integrable r μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) (hrn : ∀ᵐ x ∂μ, 0 ≤ r x) (hE : 0 ≤ E)
    (hlower : ∀ᵐ x ∂μ, Real.exp (-E)*f x ≤ c x)
    (hupper : ∀ᵐ x ∂μ, c x ≤ f x+r x) :
    Integrable (fun x => |c x-f x|) μ ∧
      (∫ x, |c x-f x| ∂μ) ≤ E*(∫ x, f x ∂μ)+(∫ x, r x ∂μ) := by
  have hb : ∀ᵐ x ∂μ, |c x-f x| ≤ E*f x+r x := by
    filter_upwards [hfn,hrn,hlower,hupper] with x hf hr hl hu
    exact abs_sub_le_of_survival hf hr hE hl hu
  have hmaj : Integrable (fun x => E*f x+r x) μ := (hf.const_mul E).add hr
  have hi : Integrable (fun x => |c x-f x|) μ := by
    apply hmaj.mono' (hc.sub hf.aestronglyMeasurable).norm
    simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply] using hb
  refine ⟨hi,?_⟩
  have h := integral_mono_ae hi hmaj hb
  rwa [integral_add (hf.const_mul E) hr,integral_const_mul] at h

theorem scaled_survival_error_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {c f r : ℕ → X → ℝ} {scale E : ℕ → ℝ} {C : ℝ}
    (hscale : ∀ n, 0 ≤ scale n) (hE : ∀ n, 0 ≤ E n)
    (hc : ∀ n, AEStronglyMeasurable (c n) μ)
    (hf : ∀ n, Integrable (f n) μ) (hr : ∀ n, Integrable (r n) μ)
    (hfn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (hrn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ r n x)
    (hlower : ∀ n, ∀ᵐ x ∂μ, Real.exp (-E n)*f n x ≤ c n x)
    (hupper : ∀ n, ∀ᵐ x ∂μ, c n x ≤ f n x+r n x)
    (hmass : ∀ n, scale n*(∫ x, f n x ∂μ) ≤ C)
    (hElim : Tendsto E atTop (𝓝 0))
    (hrlim : Tendsto (fun n => scale n*(∫ x, r n x ∂μ)) atTop (𝓝 0)) :
    Tendsto (fun n => scale n*(∫ x, |c n x-f n x| ∂μ)) atTop (𝓝 0) := by
  have hbound (n : ℕ) : scale n*(∫ x, |c n x-f n x| ∂μ) ≤
      E n*C+scale n*(∫ x, r n x ∂μ) := by
    have h := (integral_abs_sub_le_of_survival (hc n) (hf n) (hr n)
      (hfn n) (hrn n) (hE n) (hlower n) (hupper n)).2
    have hs := mul_le_mul_of_nonneg_left h (hscale n)
    have hm := mul_le_mul_of_nonneg_left (hmass n) (hE n)
    nlinarith only [hs,hm]
  have hlim : Tendsto (fun n => E n*C+scale n*(∫ x, r n x ∂μ)) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_add] using (hElim.mul_const C).add hrlim
  exact squeeze_zero (fun n => mul_nonneg (hscale n) (integral_nonneg (fun _ => abs_nonneg _)))
    hbound hlim

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform optical-depth errors on bounded dilation windows -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

/-- `S` bounds the rescaled jet size, and `U` bounds rescaled time. -/
def coldDilationError (C A D S U : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  C*S^9*U*r^10+A*(U^2/2+U)*r^2+D*U^(m+1)*r^(m+1)/(m+1)

theorem coldOpticalDepth_le_dilationError {C A D S U r s t δ : ℝ} (m : ℕ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsr : s ≤ S*r) (htr : t ≤ U*r) (hδr : δ ≤ r) :
    coldOpticalDepth (C*s^9) A δ D m t ≤ coldDilationError C A D S U m r := by
  have hfirst : C*s^9*t ≤ C*(S*r)^9*(U*r) := by gcongr
  have hsecond : A*(t^2/2+δ*t) ≤ A*((U*r)^2/2+r*(U*r)) := by gcongr
  have hthird : D*t^(m+1)/(m+1) ≤ D*(U*r)^(m+1)/(m+1) := by gcongr
  calc
    _ ≤ C*(S*r)^9*(U*r)+A*((U*r)^2/2+r*(U*r))+D*(U*r)^(m+1)/(m+1) :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by unfold coldDilationError; rw [mul_pow]; ring

theorem coldDilationError_nonneg {C A D S U r : ℝ} (m : ℕ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hS : 0 ≤ S) (hU : 0 ≤ U)
    (hr : 0 ≤ r) : 0 ≤ coldDilationError C A D S U m r := by
  unfold coldDilationError
  positivity

theorem coldDilationError_tendsto_zero (C A D S U : ℝ) (m : ℕ) :
    Tendsto (coldDilationError C A D S U m) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (coldDilationError C A D S U m) := by
    unfold coldDilationError
    fun_prop
  simpa [coldDilationError] using hc.continuousAt.tendsto (x := (0:ℝ))

theorem coldOpticalDepth_tendsto_zero {C A D S U : ℝ} {m : ℕ}
    {r s t δ : ℕ → ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hS : 0 ≤ S) (hr : ∀ n, 0 ≤ r n) (hs : ∀ n, 0 ≤ s n)
    (ht : ∀ n, 0 ≤ t n) (hδ : ∀ n, 0 ≤ δ n)
    (hsr : ∀ n, s n ≤ S*r n) (htr : ∀ n, t n ≤ U*r n) (hδr : ∀ n, δ n ≤ r n)
    (hrlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => coldOpticalDepth (C*s n^9) A (δ n) D m (t n)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => coldOpticalDepth_nonneg (mul_nonneg hC (pow_nonneg (hs n) _))
      hA (hδ n) hD (ht n) m)
    (fun n => coldOpticalDepth_le_dilationError m hC hA hD hS
      (hr n) (hs n) (ht n) (hsr n) (htr n) (hδr n))
  exact (coldDilationError_tendsto_zero C A D S U m).comp hrlim

end BoltzmannNonuniqueness

end

end

section

/-! # The local cold error vanishes after the physical dilation -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem scaled_local_error_le {I E ε V C K r s a : ℝ}
    (hE : 0 ≤ E) (hε : 0 ≤ ε) (hV : 0 ≤ V) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : 0 < r) (hs : 0 < s) (ha : 0 < a) (has : a*r ≤ s)
    (hI : I ≤ (E+ε)*(r^3*V)*(C*(K/s))) :
    I/r^2 ≤ (E+ε)*(V*C*K/a) := by
  have hratio : r/s ≤ 1/a := (div_le_div_iff₀ hs ha).mpr (by nlinarith only [has])
  calc
    I/r^2 ≤ ((E+ε)*(r^3*V)*(C*(K/s)))/r^2 :=
      div_le_div_of_nonneg_right hI (sq_nonneg r)
    _ = (E+ε)*V*C*K*(r/s) := by field_simp
    _ ≤ (E+ε)*V*C*K*(1/a) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem scaled_local_error_tendsto_zero {I E ε r s : ℕ → ℝ} {V C K a : ℝ}
    (hE : ∀ n, 0 ≤ E n) (hε : ∀ n, 0 ≤ ε n)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : ∀ n, 0 < r n) (hs : ∀ n, 0 < s n) (ha : 0 < a)
    (has : ∀ n, a*r n ≤ s n) (hIn : ∀ n, 0 ≤ I n)
    (hI : ∀ n, I n ≤ (E n+ε n)*((r n)^3*V)*(C*(K/s n)))
    (hElim : Tendsto E atTop (𝓝 0)) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => I n/(r n)^2) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg (hIn n) (sq_nonneg _))
    (fun n => scaled_local_error_le (hE n) (hε n) hV hC hK (hr n) (hs n) ha (has n) (hI n))
  simpa only [zero_add,zero_mul] using (hElim.add hεlim).mul_const (V*C*K/a)

theorem jet_epsilon_tendsto_zero {r s : ℕ → ℝ} {S : ℝ}
    (hs : ∀ n, 0 < s n) (hsr : ∀ n, s n ≤ S*r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (K d₀ : ℝ) :
    Tendsto (fun n => JetSupersolution.epsilon K (s n) (d₀*(s n)^10)) atTop (𝓝 0) := by
  have hslim : Tendsto s atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hs n).le) hsr
    simpa only [mul_zero] using hrlim.const_mul S
  simp_rw [JetEscapedEnvelope.epsilon_eq (hs _)]
  simpa only [zero_pow (by norm_num : (9:ℕ) ≠ 0),mul_zero] using
    (hslim.pow 9).const_mul (JetComparisonCoefficient.coefficient K*d₀)

end BoltzmannNonuniqueness

end

end

section

/-! # The three-dimensional Jacobian in the cold dilation -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness.ColdDilationMeasure

theorem space_finrank : Module.finrank ℝ JetPrototype.Space = 3 := by
  simp [JetPrototype.Space,VelocityWeight.Transverse,Module.finrank_prod]

theorem setIntegral_space_smul (f : JetPrototype.Space → ℝ) (Ω : Set JetPrototype.Space)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in Ω, f (r • x) ∂JetPrototype.spaceVolume) =
      (r^3)⁻¹*(∫ x in r • Ω, f x ∂JetPrototype.spaceVolume) := by
  simpa only [space_finrank,smul_eq_mul] using
    Measure.setIntegral_comp_smul_of_pos JetPrototype.spaceVolume f Ω hr

theorem dilated_error_integral (f : JetPrototype.Phase → ℝ) (Ω : Set JetPrototype.Space)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in Ω, ∫ v : Velocity, |r*f (r • x,v)| ∂volume ∂JetPrototype.spaceVolume) =
      (∫ x in r • Ω, ∫ v : Velocity, |f (x,v)| ∂volume ∂JetPrototype.spaceVolume)/r^2 := by
  simp_rw [abs_mul,abs_of_pos hr,integral_const_mul]
  rw [setIntegral_space_smul (fun x => ∫ v : Velocity, |f (x,v)|) Ω hr]
  field_simp

theorem spaceVolume_real_smul (Ω : Set JetPrototype.Space) {r : ℝ} (hr : 0 < r) :
    JetPrototype.spaceVolume.real (r • Ω) = r^3*JetPrototype.spaceVolume.real Ω := by
  have h := setIntegral_space_smul (fun _ => (1:ℝ)) Ω hr
  simp only [setIntegral_const,smul_eq_mul,mul_one] at h
  have hr3 : r^3 ≠ 0 := pow_ne_zero _ hr.ne'
  exact (inv_mul_eq_iff_eq_mul₀ hr3).mp h.symm

end BoltzmannNonuniqueness.ColdDilationMeasure

end

end

section

/-! # Small dilated jets satisfy the geometric survival conditions automatically -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness

theorem eventually_cold_survival_geometry {s : ℕ → ℝ} {η d₀ T : ℝ}
    (hη : 0 < η) (hslim : Tendsto s atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      T*(d₀*(s n)^10) ≤ enlargementWidth η (s n) ∧ d₀*(s n)^10 ≤ 1/64 := by
  have h8 : Tendsto (fun n => T*d₀*(s n)^8) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (8:ℕ) ≠ 0),mul_zero] using (hslim.pow 8).const_mul (T*d₀)
  have h10 : Tendsto (fun n => d₀*(s n)^10) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (10:ℕ) ≠ 0),mul_zero] using (hslim.pow 10).const_mul d₀
  have hw : ∀ᶠ n in atTop, T*d₀*(s n)^8 < gapCoefficient η/4 :=
    h8.eventually (gt_mem_nhds (div_pos (gapCoefficient_pos hη) (by norm_num)))
  have hd : ∀ᶠ n in atTop, d₀*(s n)^10 < 1/64 :=
    h10.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hw,hd] with n hn hdn
  refine ⟨?_,hdn.le⟩
  have h := mul_le_mul_of_nonneg_right hn.le (sq_nonneg (s n))
  calc
    T*(d₀*(s n)^10) = T*d₀*(s n)^8*(s n)^2 := by ring
    _ ≤ enlargementWidth η (s n) := h

end BoltzmannNonuniqueness

end

end

section

/-! # Product-space integrability and measure change for the spatial dilation -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness.ColdDilationMeasure

def spaceEquiv (r : ℝ) (hr : r ≠ 0) : JetPrototype.Space ≃ᵐ JetPrototype.Space :=
  (Homeomorph.smul (Units.mk0 r hr)).toMeasurableEquiv

def phaseEquiv (r : ℝ) (hr : r ≠ 0) : JetPrototype.Phase ≃ᵐ JetPrototype.Phase :=
  (spaceEquiv r hr).prodCongr (MeasurableEquiv.refl Velocity)

theorem map_space_restrict {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space) :
    Measure.map (fun x : JetPrototype.Space => r • x) (JetPrototype.spaceVolume.restrict Ω) =
      ENNReal.ofReal ((r^3)⁻¹) • JetPrototype.spaceVolume.restrict (r • Ω) := by
  let e := spaceEquiv r hr.ne'
  have hp : e ⁻¹' (r • Ω) = Ω := by
    ext x
    exact smul_mem_smul_set_iff₀ hr.ne' Ω x
  have h := e.restrict_map JetPrototype.spaceVolume (r • Ω)
  rw [hp] at h
  change (Measure.map (fun x : JetPrototype.Space => r • x) JetPrototype.spaceVolume).restrict (r • Ω) =
    Measure.map (fun x : JetPrototype.Space => r • x) (JetPrototype.spaceVolume.restrict Ω) at h
  rw [Measure.map_addHaar_smul JetPrototype.spaceVolume hr.ne',space_finrank,
    abs_of_pos (inv_pos.mpr (pow_pos hr 3)),Measure.restrict_smul] at h
  exact h.symm

theorem map_phase_restrict {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space) :
    Measure.map (fun p : JetPrototype.Phase => (r • p.1,p.2))
      ((JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity)) =
      ENNReal.ofReal ((r^3)⁻¹) •
        ((JetPrototype.spaceVolume.restrict (r • Ω)).prod (volume : Measure Velocity)) := by
  change Measure.map (Prod.map (fun x : JetPrototype.Space => r • x) id) _ = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    map_space_restrict hr Ω,Measure.map_id,Measure.prod_smul_left]

theorem integrable_dilate {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space)
    {f : JetPrototype.Phase → ℝ}
    (hf : Integrable f ((JetPrototype.spaceVolume.restrict (r • Ω)).prod volume)) :
    Integrable (fun p : JetPrototype.Phase => f (r • p.1,p.2))
      ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  have hc0 : ENNReal.ofReal ((r^3)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr 3))).ne'
  have hm : Integrable f (Measure.map (phaseEquiv r hr.ne')
      ((JetPrototype.spaceVolume.restrict Ω).prod volume)) := by
    change Integrable f (Measure.map (fun p : JetPrototype.Phase => (r • p.1,p.2)) _)
    rw [map_phase_restrict hr Ω]
    exact (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).mpr hf
  exact (integrable_map_equiv (phaseEquiv r hr.ne') f).mp hm

theorem integrable_dilated_error {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space)
    {f : JetPrototype.Phase → ℝ}
    (hf : Integrable (fun p => |f p|) ((JetPrototype.spaceVolume.restrict (r • Ω)).prod volume)) :
    Integrable (fun p : JetPrototype.Phase => |r*f (r • p.1,p.2)|)
      ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  simpa only [abs_mul,abs_of_pos hr] using (integrable_dilate hr Ω hf).const_mul r

theorem product_dilated_error_integral {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space)
    {f : JetPrototype.Phase → ℝ}
    (hf : Integrable (fun p => |f p|) ((JetPrototype.spaceVolume.restrict (r • Ω)).prod volume)) :
    (∫ p : JetPrototype.Phase, |r*f (r • p.1,p.2)|
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) =
    (∫ p : JetPrototype.Phase, |f p|
      ∂(JetPrototype.spaceVolume.restrict (r • Ω)).prod volume)/r^2 := by
  rw [integral_prod _ (integrable_dilated_error hr Ω hf),dilated_error_integral f Ω hr,
    ← integral_prod _ hf]

end BoltzmannNonuniqueness.ColdDilationMeasure

end

end

section

/-! # Cold mild equations are independent of spatial representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem ColdMildAE.representative {q b L T : ℝ} {c₀ : JetPrototype.Phase → ℝ}
    {F c d : ℝ × JetPrototype.Phase → ℝ} (hc : ColdMildAE q b L T F c₀ c)
    (hcm : Measurable c) (hdm : Measurable d)
    (hcd : ∀ t, (fun p => c (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => d (t,p))) :
    ColdMildAE q b L T F c₀ d := by
  have hsource := coldForcing_congr_cold (slice_congr_spacetime hcm hdm hcd) q b L F
  intro t ht
  exact (hcd t).symm.trans ((hc t ht).trans
    (FlightMeasure.value_congr_at_time (ae_of_all _ (fun _ => rfl)) hsource T L t))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
