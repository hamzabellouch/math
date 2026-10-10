import OAI.MathematicalPhysics.Boltzmann.Branching.ClampedMildAE
import OAI.MathematicalPhysics.Boltzmann.Branching.FlightMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetStability
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Jets.PeriodicJetFamilies

namespace OAI

section

/-! # A uniform positive local interval from an essentially bounded time slice -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

def clippedSlice (A : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) (s : ℝ)
    (p : JetPrototype.Phase) : ℝ := min (F (s,p)) A

theorem exists_extension {q b A s : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hFn : ∀ p, 0 ≤ F (s,p))
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (s,p) ≤ A)
    (hper : ∀ n, pull (JetCopyDatum.displacement n) F = F) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧
      (∀ u, 0 ≤ G u ∧ G u ≤ 2*A) ∧
      (∀ u, G u = PositiveIntegral.value (lifespan q b A) (damping q b A)
        JetBarrier.flight (clippedSlice A F s) (WeightedLocal.forcing q b (damping q b A) G) u) ∧
      ((fun p => G (0,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p))) ∧
      ∀ n, pull (JetCopyDatum.displacement n) G = G := by
  have hsm : Measurable (clippedSlice A F s) :=
    (hFm.comp (measurable_const.prodMk measurable_id)).min measurable_const
  have hsb (p) : 0 ≤ clippedSlice A F s p ∧ clippedSlice A F s p ≤ A :=
    ⟨le_min (hFn p) hA.le,min_le_right _ _⟩
  obtain ⟨G,hGm,hG,hGeq⟩ := exists_solution hq hb hA hsm hsb
  have hT : 0 ≤ lifespan q b A := (lifespan_pos hb hA).le
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  refine ⟨G,hGm,hG,hGeq,?_,?_⟩
  · filter_upwards [hFA] with p hp
    rw [hGeq (0,p)]
    have ht : PositiveIntegral.time (lifespan q b A) 0 = 0 := GaussianLocal.time_eq ⟨le_rfl,hT⟩
    simp [PositiveIntegral.value,ht,JetBarrier.flight,clippedSlice,min_eq_left hp]
  · intro n
    apply solution_covariance hq hb hL hT (by positivity)
      (show (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A from le_rfl)
      (small hb hA) hGm hG hGeq
    intro p
    have hp := congrFun (hper n) (s,p)
    change F (s,shift (JetCopyDatum.displacement n) p) = F (s,p) at hp
    unfold clippedSlice
    rw [hp]

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Extending a bounded positive periodic solution from a bounded time slice -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem exists_continuation_step {q b A s : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hA : 0 < A) (hs : 0 ≤ s) {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ 2*A)
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (s,p) ≤ A)
    (hfix : MildAE q b (damping q b A) s f₀ F)
    (hper : ∀ n, pull (JetCopyDatum.displacement n) F = F) :
    ∃ H : ℝ × JetPrototype.Phase → ℝ, Measurable H ∧
      (∀ u, 0 ≤ H u ∧ H u ≤ 2*A) ∧
      (∀ t, (fun p => H (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value (s+lifespan q b A) (damping q b A)
          JetBarrier.flight f₀ (forcing q b (damping q b A) H) (t,p))) ∧
      (∀ n, pull (JetCopyDatum.displacement n) H = H) ∧
      ∀ t ∈ Icc 0 s, ∀ p, H (t,p) = F (t,p) := by
  obtain ⟨G,hGm,hG,hGeq,_,hGper⟩ := exists_extension hq hb hA hFm
    (fun p => (hF (s,p)).1) hFA hper
  let P := paste s F G
  have hPm : Measurable P := measurable_paste hFm hGm
  have hPb (u) : 0 ≤ P u ∧ P u ≤ 2*A := paste_bounds hF hG u
  have hδ : 0 ≤ lifespan q b A := (lifespan_pos hb hA).le
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hsrc (u) : |forcing q b (damping q b A) P u| ≤ sourceBound q b A := by
    have h := HotRepresentative.source_bounds hq hb (by positivity : 0 ≤ 2*A)
      (show (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A from le_rfl)
      (GaussianLocal.measurable_state hPm) (fun v => hPb (v.1.1,(v.1.2,v.2)))
      ((u.1,u.2.1),u.2.2)
    exact (abs_of_nonneg h.1).trans_le h.2
  have hclip : clippedSlice A F s =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p)) := by
    filter_upwards [hFA] with p hp
    exact min_eq_left hp
  have hPeq : MildAE q b (damping q b A) (s+lifespan q b A) f₀ P :=
    paste_mildAE hs hδ hL hFm hGm hsrc hfix (mildAE_of_pointwise hGeq) hclip
  have hPper (n) : pull (JetCopyDatum.displacement n) P = P := by
    dsimp only [P]
    rw [paste_pull,hper n,hGper n]
  let H := clampTime (s+lifespan q b A) P
  have htot := add_nonneg hs hδ
  refine ⟨H,measurable_clampTime hPm _,fun u => hPb _,mildAE_all_times htot hPeq,?_,?_⟩
  · intro n
    funext u
    exact congrFun (hPper n) (PositiveIntegral.time (s+lifespan q b A) u.1,u.2)
  · intro t ht p
    change P (PositiveIntegral.time (s+lifespan q b A) t,p) = F (t,p)
    rw [GaussianLocal.time_eq ⟨ht.1,by linarith [ht.2]⟩]
    exact ite_eq_left ht.2

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # The normalized hot source retains the uniform geometric estimate -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem jet_gain_difference (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q R D : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D)
    (η : ℝ) (a : Bool) (x : Space) {F c : X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hc : ∀ p, 0 ≤ c p) (hcF : ∀ p, c p ≤ F p) (hF : ∀ p, F p ≤ R)
    (y : X)
    (hcU : ∀ w, H q w * c (y,w) ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,w))
    (hrem : ∀ w, F (y,w) - c (y,w) ≤ D) (b : ℝ) :
    ∀ᵐ v : Velocity, gain q b F (y,v) - gain q b c (y,v) ≤
      2*D*JetMainGain.coefficient K α γ q / (s+t) + D^2*HotApplication.realBound q := by
  have hbound := JetHotGain.remainder_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max
    ht htmax hq₁ hq₂ hD η a x
    ((measurable_density hFm q).comp (measurable_const.prodMk measurable_id))
    ((measurable_density hcm q).comp (measurable_const.prodMk measurable_id))
    (fun w => mul_nonneg (H_nonneg q w) (hc (y,w)))
    (fun w => mul_le_mul_of_nonneg_left (hcF (y,w)) (H_nonneg q w))
    (fun w => (mul_le_mul_of_nonneg_left (hF (y,w)) (H_nonneg q w)).trans_eq (mul_comm _ _))
    hcU (fun w => by
      change H q w * F (y,w) - H q w * c (y,w) ≤ D * H q w
      rw [← mul_sub]
      exact (mul_le_mul_of_nonneg_left (hrem w) (H_nonneg q w)).trans_eq (mul_comm _ _)) b
  filter_upwards [ae_good hcarleman hq₁ hq₂, hbound] with v hv hg
  simp only [gain, ite_eq_left hv]
  rw [← sub_div]
  exact (div_le_iff₀ (H_pos q v)).mpr hg

theorem jet_hot_source_le (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q R D : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D)
    (η : ℝ) (a : Bool) (x : Space) {F : X × Velocity → ℝ} {c : I → X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ u : Finset I, ∀ p, ∑ i ∈ u, c i p ≤ F p)
    (i : I) (y : X)
    (hcU : ∀ w, H q w * c i (y,w) ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,w))
    (hrem : ∀ w, F (y,w) - c i (y,w) ≤ D) (b L : ℝ) :
    ∀ᵐ v : Velocity,
      source q b L F (y,v) - (∑' j, coldSource q b L F (c j) (y,v)) -
          L * (F (y,v) - ∑' j, c j (y,v)) ≤
        2*D*JetMainGain.coefficient K α γ q / (s+t) + D^2*HotApplication.realBound q := by
  classical
  have hciF (p) : c i p ≤ F p := by simpa only [Finset.sum_singleton] using hSum {i} p
  filter_upwards [jet_gain_difference hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax
    hq₁ hq₂ hD η a x hFm (hcm i) (fun p => (hc i p).1) hciF (fun p => (hF p).2) y hcU hrem b]
      with v hv
  exact (hot_source_le_single L hcm hFm hc hF hSum i (y,v)).trans hv

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
