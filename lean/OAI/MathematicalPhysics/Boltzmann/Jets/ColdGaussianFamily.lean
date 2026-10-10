import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace OAI

section

/-! # The scalar integral Gronwall step in cold-color comparison -/

noncomputable section

open MeasureTheory Set Filter

namespace BoltzmannNonuniqueness.ColdGronwall

def primitive (z : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in 0..t, z r

/-- A nonnegative integrable error bounded by a constant times its past integral vanishes. -/
theorem eq_zero_of_integral_bound {z : ℝ → ℝ} {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hi : IntervalIntegrable z volume 0 T) (hz : ∀ t ∈ Icc 0 T, 0 ≤ z t)
    (hb : ∀ t ∈ Icc 0 T, z t ≤ C * primitive z t) : ∀ t ∈ Icc 0 T, z t = 0 := by
  let W : ℝ → ℝ := fun t => Real.exp (-C * t) * primitive z t
  have hZ : AbsolutelyContinuousOnInterval (primitive z) 0 T :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-C * t)) := by fun_prop
  have hW : AbsolutelyContinuousOnInterval W 0 T := he.contDiffOn.absolutelyContinuousOnInterval.mul hZ
  have hder : ∀ᵐ t, t ∈ Icc 0 T → deriv W t ≤ 0 := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hzt := ht (by simpa only [uIcc_of_le hT] using hmem) 0 (by simp)
    have het := ((hasDerivAt_id t).const_mul (-C)).exp
    have hw := het.mul hzt
    change HasDerivAt W _ t at hw
    rw [hw.deriv]
    have hbt := hb t hmem
    have hp := mul_le_mul_of_nonneg_left hbt (Real.exp_pos (-C * t)).le
    dsimp only [primitive, id] at hp ⊢
    nlinarith only [hp]
  intro t ht
  have hWt : AbsolutelyContinuousOnInterval W 0 t := by
    apply hW.mono
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    intro r hr
    exact ⟨hr.1, hr.2.trans ht.2⟩
  have hint : 0 ≤ ∫ r in 0..t, -deriv W r := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc] with r hr hrt
    exact neg_nonneg.mpr (hr ⟨hrt.1, hrt.2.trans ht.2⟩)
  rw [intervalIntegral.integral_neg, hWt.integral_deriv_eq_sub] at hint
  have hW0 : W 0 = 0 := by simp [W, primitive]
  rw [hW0] at hint
  have hZt : primitive z t ≤ 0 := by
    dsimp only [W] at hint
    nlinarith [Real.exp_pos (-C * t)]
  exact le_antisymm ((hb t ht).trans (mul_nonpos_of_nonneg_of_nonpos hC hZt)) (hz t ht)

end BoltzmannNonuniqueness.ColdGronwall

end

end

section

/-! # Positive cold-color iteration beneath an actual total solution -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GaussianLocal

def coldForcing (β b L : ℝ) (F c : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) : ℝ :=
  GaussianCutoff.coldSource β b L (state F) (state c) ((z.1, z.2.1), z.2.2)

def coldPicard (β b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) : ℕ → ℝ × JetPrototype.Phase → ℝ
  | 0 => fun _ => 0
  | n+1 => PositiveIntegral.value T L JetBarrier.flight c₀
      (coldForcing β b L F (coldPicard β b L T F c₀ n))

theorem measurable_coldForcing {F c : ℝ × JetPrototype.Phase → ℝ}
    (hF : Measurable F) (hc : Measurable c) (β b L : ℝ) : Measurable (coldForcing β b L F c) :=
  (GaussianCutoff.measurable_coldSource (measurable_state hF) (measurable_state hc) β b L).comp (by fun_prop)

theorem coldPicard_properties {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (n : ℕ) : Measurable (coldPicard β b L T F c₀ n) ∧
      ∀ z, 0 ≤ coldPicard β b L T F c₀ n z ∧ coldPicard β b L T F c₀ n z ≤ F z := by
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  obtain ⟨hG, hC⟩ := GaussianCutoff.constants_nonneg hb β
  have hS : 0 ≤ S := add_nonneg (mul_nonneg hG (sq_nonneg _)) (mul_nonneg hL hR)
  induction n with
  | zero => exact ⟨measurable_const, fun z => ⟨le_rfl, (hF z).1⟩⟩
  | succ n ih =>
    have hc (z) : 0 ≤ coldPicard β b L T F c₀ n z ∧ coldPicard β b L T F c₀ n z ≤ R :=
      ⟨(ih.2 z).1, (ih.2 z).2.trans (hF z).2⟩
    have hcm := measurable_coldForcing hFm ih.1 β b L
    have hcs (z) : 0 ≤ coldForcing β b L F (coldPicard β b L T F c₀ n) z ∧
        coldForcing β b L F (coldPicard β b L T F c₀ n) z ≤ S :=
      GaussianCutoff.coldSource_bounds hβ hb hR hloss
        (fun p => hF (p.1.1, (p.1.2, p.2))) (fun p => hc (p.1.1, (p.1.2, p.2))) _
    have hfs (z) : 0 ≤ forcing β b L F z ∧ forcing β b L F z ≤ S :=
      GaussianCutoff.source_bounds hβ hb hR hloss (fun p => hF (p.1.1, (p.1.2, p.2))) _
    refine ⟨PositiveIntegral.measurable_value hT measurable_flight hc₀m hcm, fun z => ⟨?_, ?_⟩⟩
    · exact (PositiveIntegral.value_bounds hT hL hR hS JetBarrier.flight
        (fun p => ⟨(hc₀ p).1, (hc₀ p).2.trans (hF₀ p)⟩) hcs z).1
    · rw [hFeq z]
      apply PositiveIntegral.value_mono hT hL measurable_flight (fun p => (hc₀ p).2)
        hcm (measurable_forcing hFm β b L)
        (fun z => by rw [abs_of_nonneg (hcs z).1]; exact (hcs z).2)
        (fun z => by rw [abs_of_nonneg (hfs z).1]; exact (hfs z).2)
      intro q
      exact GaussianCutoff.coldSource_mono hβ hb hR hloss (measurable_state ih.1)
        (measurable_state hFm) (fun p => hF (p.1.1, (p.1.2, p.2)))
        (fun p => (ih.2 (p.1.1, (p.1.2, p.2))).1)
        (fun p => (ih.2 (p.1.1, (p.1.2, p.2))).2)
        (fun p => (hF (p.1.1, (p.1.2, p.2))).2) _

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Polynomial smallness of a cold Gaussian away from the velocity axis -/
noncomputable section
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetBarrier

theorem off_axis_bound {K s d t ε : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1) (hε : 0 < ε)
    (η α γ : ℝ) (a : Bool) (x : Space) (v : Velocity)
    (hv : ε ≤ ‖transverse v‖) :
    barrier η K α γ s d t a (x,v) ≤
      (Real.exp 4*JetThermalKernel.bound)*(K/s)*(d^3)⁻¹*Real.exp (-(ε^2/d^2)) := by
  have hn : ε^2 ≤ ‖v-centerVelocity α γ s t a x‖^2 := by
    have he := norm_sq_split (v-centerVelocity α γ s t a x)
    rw [PlaneChart.transverse_sub,centerVelocity,PlaneChart.transverse_join,sub_zero] at he
    change ε^2 ≤ ‖v-PlaneChart.join 0 (AxialFlow.velocity (sign a) α γ s t x.2)‖^2
    nlinarith only [he,hv,hε,norm_nonneg (transverse v),sq_nonneg (axial (v-centerVelocity α γ s t a x))]
  have hD : 0 ≤ distanceSquared η α γ s t a x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdist : 0 ≤ (1/8:ℝ)*distanceSquared η α γ s t a x/(d^2*t) := by positivity
  have hvd : ε^2/d^2 ≤ (2-t)*‖v-centerVelocity α γ s t a x‖^2/d^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg d)
    nlinarith only [hn,htmax,sq_nonneg ‖v-centerVelocity α γ s t a x‖]
  have he : exponent η α γ s d t a (x,v) ≤ 1-ε^2/d^2 := by
    dsimp only [exponent]
    linarith only [htmax,hvd,hdist]
  have hcoef : 0 ≤ (Real.exp 3*JetThermalKernel.bound)*(K/s)*(d^3)⁻¹ := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ (Real.exp 3*JetThermalKernel.bound)*(K/s)*(d^3)⁻¹*Real.exp (1-ε^2/d^2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hcoef
    _ = _ := by
      rw [sub_eq_add_neg,Real.exp_add]
      have he4 : Real.exp (3:ℝ)*Real.exp 1 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
      calc
        _ = (Real.exp 3*Real.exp 1)*JetThermalKernel.bound*(K/s)*(d^3)⁻¹*Real.exp (-(ε^2/d^2)) := by ring
        _ = _ := by rw [he4]

end BoltzmannNonuniqueness.JetBarrier
namespace BoltzmannNonuniqueness.JetSupersolution

def transverseDecayConstant (K d₀ ε : ℝ) : ℝ :=
  4*Real.exp 4*JetThermalKernel.bound*K*d₀/ε^4

theorem transverseDecayConstant_nonneg {K d₀ ε : ℝ} (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) :
    0 ≤ transverseDecayConstant K d₀ ε := by
  unfold transverseDecayConstant
  have := JetThermalKernel.bound_pos
  positivity

theorem off_axis_small_scale {K s d₀ t ε α γ : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (hd₀ : 0 < d₀) (ht : 0 < t) (htmax : t ≤ 1) (hε : 0 < ε)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hsmall : epsilon K s (d₀*s^10) ≤ 1)
    (η : ℝ) (a : Bool) (x : Space) (v : Velocity) (hv : ε ≤ ‖transverse v‖) :
    U η K α γ s (d₀*s^10) t a (x,v) ≤ transverseDecayConstant K d₀ ε*s^9 := by
  have hd : 0 < d₀*s^10 := by positivity
  have hb := JetBarrier.off_axis_bound hK hs hd ht htmax hε η α γ a x v hv
  have he := JetEscapePower.exp_neg_le (show 0 < ε^2/(d₀*s^10)^2 by positivity) 2
  have hc : 0 ≤ (Real.exp 4*JetThermalKernel.bound)*(K/s)*((d₀*s^10)^3)⁻¹ := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ 2*JetBarrier.barrier η K α γ s (d₀*s^10) t a (x,v) :=
      le_twice_barrier hK hs hd hα hγ ht htmax hsmall η a (x,v)
    _ ≤ 2*((Real.exp 4*JetThermalKernel.bound)*(K/s)*((d₀*s^10)^3)⁻¹*
        Real.exp (-(ε^2/(d₀*s^10)^2))) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2*((Real.exp 4*JetThermalKernel.bound)*(K/s)*((d₀*s^10)^3)⁻¹*
        ((2:ℕ).factorial/(ε^2/(d₀*s^10)^2)^2)) := by gcongr
    _ = _ := by
      norm_num only [Nat.factorial_two,Nat.cast_ofNat]
      unfold transverseDecayConstant
      field_simp
      ring

end BoltzmannNonuniqueness.JetSupersolution

end

end

section

/-! # Convergence of the positive cold iteration with common total loss -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GaussianLocal

def coldLimit (β b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  ⨆ n, coldPicard β b L T F c₀ n z

theorem coldLimit_solution {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z) :
    Measurable (coldLimit β b L T F c₀) ∧
      (∀ z, 0 ≤ coldLimit β b L T F c₀ z ∧ coldLimit β b L T F c₀ z ≤ F z) ∧
      (∀ z, coldLimit β b L T F c₀ z = PositiveIntegral.value T L JetBarrier.flight c₀
        (coldForcing β b L F (coldLimit β b L T F c₀)) z) ∧
      ∀ z, Tendsto (fun n => coldPicard β b L T F c₀ n z) atTop (𝓝 (coldLimit β b L T F c₀ z)) := by
  let u := coldPicard β b L T F c₀
  have hu := coldPicard_properties hβ hb hL hT hR hloss hFm hc₀m hF hc₀ hF₀ hFeq
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  have hsource (n) (z) : 0 ≤ coldForcing β b L F (u n) z ∧
      coldForcing β b L F (u n) z ≤ S :=
    GaussianCutoff.coldSource_bounds (F := state F) (c := state (u n)) hβ hb hR hloss
      (fun p => hF (p.1.1, (p.1.2, p.2)))
      (fun p => ⟨((hu n).2 (p.1.1, (p.1.2, p.2))).1,
        (((hu n).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2⟩) ((z.1, z.2.1), z.2.2)
  have hstep : ∀ n z, u n z ≤ u (n+1) z := by
    intro n
    induction n with
    | zero => intro z; exact ((hu 1).2 z).1
    | succ n ih =>
      intro z
      apply PositiveIntegral.value_mono hT hL measurable_flight (fun _ => le_rfl)
        (measurable_coldForcing hFm (hu n).1 β b L)
        (measurable_coldForcing hFm (hu (n+1)).1 β b L)
        (fun z => by rw [abs_of_nonneg (hsource n z).1]; exact (hsource n z).2)
        (fun z => by rw [abs_of_nonneg (hsource (n+1) z).1]; exact (hsource (n+1) z).2)
      intro q
      exact GaussianCutoff.coldSource_mono hβ hb hR hloss
        (measurable_state (hu n).1) (measurable_state (hu (n+1)).1)
        (fun p => hF (p.1.1, (p.1.2, p.2)))
        (fun p => ((hu n).2 (p.1.1, (p.1.2, p.2))).1)
        (fun p => ih (p.1.1, (p.1.2, p.2)))
        (fun p => (((hu (n+1)).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2) _
  have hmono (z) : Monotone (fun n => u n z) := monotone_nat_of_le_succ (fun n => hstep n z)
  have hbdd (z) : BddAbove (Set.range (fun n => u n z)) :=
    ⟨F z, by rintro _ ⟨n, rfl⟩; exact ((hu n).2 z).2⟩
  let c := coldLimit β b L T F c₀
  have hlim (z) : Tendsto (fun n => u n z) atTop (𝓝 (c z)) := tendsto_atTop_ciSup (hmono z) (hbdd z)
  have hcm : Measurable c := measurable_of_tendsto_metrizable (fun n => (hu n).1) (tendsto_pi_nhds.mpr hlim)
  have hcb (z) : 0 ≤ c z ∧ c z ≤ F z :=
    ⟨(le_ciSup (hbdd z) 0 : u 0 z ≤ c z), ciSup_le (fun n => ((hu n).2 z).2)⟩
  refine ⟨hcm, hcb, ?_, hlim⟩
  intro z
  have hsourcelim (q) : Tendsto (fun n => coldForcing β b L F (u n) q) atTop
      (𝓝 (coldForcing β b L F c q)) := by
    exact GaussianCutoff.coldSource_tendsto hβ hb hR L (state F)
      (fun n => measurable_state (hu n).1)
      (fun n p => by
        change |coldPicard β b L T F c₀ n (p.1.1, (p.1.2, p.2))| ≤ R
        rw [abs_of_nonneg ((hu n).2 (p.1.1, (p.1.2, p.2))).1]
        exact (((hu n).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2)
      (fun p => hlim (p.1.1, (p.1.2, p.2))) _
  have hv := PositiveIntegral.value_tendsto hT hL measurable_flight c₀
    (fun n => measurable_coldForcing hFm (hu n).1 β b L)
    (fun n q => by rw [abs_of_nonneg (hsource n q).1]; exact (hsource n q).2)
    hsourcelim z
  have hs := (hlim z).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hs hv

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Summable cold families and the nonnegative hot remainder -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.GaussianLocal

variable {I : Type*}

theorem finite_sum_picard_le {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ} (s : Finset I)
    (hFm : Measurable F) (hc₀m : ∀ i ∈ s, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i ∈ s, ∀ p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (n : ℕ) (z : ℝ × JetPrototype.Phase) :
    ∑ i ∈ s, coldPicard β b L T F (c₀ i) n z ≤ F z := by
  have hu (i) (hi : i ∈ s) := coldPicard_properties hβ hb hL hT hR hloss
    hFm (hc₀m i hi) hF (hc₀ i hi) hF₀ hFeq
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  have hfs (q) : 0 ≤ forcing β b L F q ∧ forcing β b L F q ≤ S :=
    GaussianCutoff.source_bounds (f := state F) hβ hb hR hloss
      (fun p => hF (p.1.1, (p.1.2, p.2))) ((q.1, q.2.1), q.2.2)
  induction n generalizing z with
  | zero => simpa only [coldPicard, Finset.sum_const_zero] using (hF z).1
  | succ n ih =>
    let g (i : I) := coldForcing β b L F (coldPicard β b L T F (c₀ i) n)
    have hgm (i) (hi : i ∈ s) : Measurable (g i) :=
      measurable_coldForcing hFm (hu i hi n).1 β b L
    have hgs (i) (hi : i ∈ s) (q) : 0 ≤ g i q ∧ g i q ≤ S :=
      GaussianCutoff.coldSource_bounds (F := state F)
        (c := state (coldPicard β b L T F (c₀ i) n)) hβ hb hR hloss
        (fun p => hF (p.1.1, (p.1.2, p.2)))
        (fun p => ⟨((hu i hi n).2 (p.1.1, (p.1.2, p.2))).1,
          (((hu i hi n).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2⟩)
        ((q.1, q.2.1), q.2.2)
    have hsum (q) : ∑ i ∈ s, g i q ≤ forcing β b L F q :=
      GaussianCutoff.finite_sum_coldSource_le hβ hb hR hloss s
        (fun i hi => measurable_state (hu i hi n).1) (measurable_state hFm)
        (fun i hi p => ⟨((hu i hi n).2 (p.1.1, (p.1.2, p.2))).1,
          (((hu i hi n).2 (p.1.1, (p.1.2, p.2))).2).trans (hF _).2⟩)
        (fun p => hF (p.1.1, (p.1.2, p.2)))
        (fun p => ih (p.1.1, (p.1.2, p.2))) ((q.1, q.2.1), q.2.2)
    change (∑ i ∈ s, PositiveIntegral.value T L JetBarrier.flight (c₀ i) (g i) z) ≤ F z
    rw [PositiveIntegral.value_finsetSum hT hL measurable_flight s c₀ g hgm
      (fun i hi q => by rw [abs_of_nonneg (hgs i hi q).1]; exact (hgs i hi q).2), hFeq z]
    have hsabs (q) : |∑ i ∈ s, g i q| ≤ S := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i hi => (hgs i hi q).1))]
      exact (hsum q).trans (hfs q).2
    have hfabs (q) : |forcing β b L F q| ≤ S := by
      rw [abs_of_nonneg (hfs q).1]
      exact (hfs q).2
    exact PositiveIntegral.value_mono hT hL measurable_flight hSum₀
      (Finset.measurable_sum s hgm) (measurable_forcing hFm β b L)
      hsabs hfabs hsum z

theorem finite_sum_coldLimit_le {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ} (s : Finset I)
    (hFm : Measurable F) (hc₀m : ∀ i ∈ s, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i ∈ s, ∀ p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (z : ℝ × JetPrototype.Phase) : ∑ i ∈ s, coldLimit β b L T F (c₀ i) z ≤ F z := by
  have ht := tendsto_finsetSum s (fun i hi =>
    (coldLimit_solution hβ hb hL hT hR hloss hFm (hc₀m i hi) hF (hc₀ i hi) hF₀ hFeq).2.2.2 z)
  exact le_of_tendsto ht (.of_forall (fun n =>
    finite_sum_picard_le hβ hb hL hT hR hloss s hFm hc₀m hF hc₀ hF₀ hSum₀ hFeq n z))

theorem cold_family_summable {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ F₀ p)
    (hF₀ : ∀ p, F₀ p ≤ R) (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight F₀ (forcing β b L F) z)
    (z : ℝ × JetPrototype.Phase) :
    Summable (fun i => coldLimit β b L T F (c₀ i) z) ∧
      (∑' i, coldLimit β b L T F (c₀ i) z) ≤ F z := by
  have hn (i) : 0 ≤ coldLimit β b L T F (c₀ i) z :=
    ((coldLimit_solution hβ hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hF₀ hFeq).2.1 z).1
  have hs (s : Finset I) : (∑ i ∈ s, coldLimit β b L T F (c₀ i) z) ≤ F z :=
    finite_sum_coldLimit_le hβ hb hL hT hR hloss s hFm (fun i _ => hc₀m i) hF
      (fun i _ => hc₀ i) hF₀ (hSum₀ s) hFeq z
  exact ⟨summable_of_sum_le hn hs, Real.tsum_le_of_sum_le hn hs⟩

end BoltzmannNonuniqueness.GaussianLocal

end

end

end OAI
