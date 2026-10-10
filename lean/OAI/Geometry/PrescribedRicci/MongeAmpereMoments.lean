import Mathlib
import OAI.Geometry.PrescribedRicci.MongeAmperePowerEnergy
import OAI.Geometry.PrescribedRicci.MoserIteration
import OAI.Geometry.PrescribedRicci.KahlerSobolev
import OAI.Geometry.PrescribedRicci.KahlerVolumeMeasure

namespace OAI

/-! Monge Ampere Moments. -/

section

 
noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical NNReal ENNReal
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {A : ComplexAtlas d X}

def powerIntegral (g : KaehlerMetric A) (φ : SmoothRealFunction A) (p : ℝ) : ℝ :=
  g.integral (fun x => (1+φ.value x^2)^(p/2))
def powerMoment (g : KaehlerMetric A) (φ : SmoothRealFunction A) (p : ℝ) : ℝ :=
  (g.powerIntegral φ p)^(1/p)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma powerIntegrand_continuous (φ : SmoothRealFunction A) (p : ℝ) :
    Continuous (fun x => (1+φ.value x^2)^(p/2)) :=
  (continuous_const.add (φ.continuous.pow 2)).rpow_const (fun x => Or.inl (show 1+φ.value x^2 ≠ 0 from ne_of_gt (by positivity)))
omit [MeasurableSpace X] [BorelSpace X] in
lemma powerIntegral_nonneg (g : KaehlerMetric A) (φ : SmoothRealFunction A) (p : ℝ) :
    0 ≤ g.powerIntegral φ p := g.integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
omit [MeasurableSpace X] [BorelSpace X] in
lemma powerMoment_nonneg (g : KaehlerMetric A) (φ : SmoothRealFunction A) (p : ℝ) :
    0 ≤ g.powerMoment φ p := Real.rpow_nonneg (g.powerIntegral_nonneg φ p) _

lemma moserPower_lpNorm_sq (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    {q : ℝ≥0} (hq : 0 < q) (p : ℝ) :
    (lpNorm (φ.compose (moserPower p) (moserPower_smooth p)).value q g.volumeMeasure)^2 =
      (g.powerIntegral φ (p*(q:ℝ)/2))^(2/(q:ℝ)) := by
  rw [lpNorm_nnreal_eq_integral_norm_rpow (ne_of_gt hq)
    (φ.compose (moserPower p) (moserPower_smooth p)).continuous.aestronglyMeasurable]
  have he : (fun x => ‖(φ.compose (moserPower p) (moserPower_smooth p)).value x‖^(q:ℝ)) =
      (fun x => (1+φ.value x^2)^((p*(q:ℝ)/2)/2)) := by
    funext x
    rw [show (φ.compose (moserPower p) (moserPower_smooth p)).value x = moserPower p (φ.value x) from rfl,
      moserPower_rpow]
    congr 1; ring
  rw [he, g.integral_volumeMeasure (powerIntegrand_continuous φ _)]
  change ((g.powerIntegral φ (p*(q:ℝ)/2))^((q:ℝ)⁻¹))^2 = _
  rw [← Real.rpow_two, ← Real.rpow_mul (g.powerIntegral_nonneg φ _)]
  congr 1; ring

 
theorem mongeAmpere_moment_step (g : KaehlerMetric A) (hd : 2 ≤ d)
    (D : ℝ) (hD : 0 ≤ D) : ∃ ν C : ℝ, 1 < ν ∧ 0 < C ∧
    ∀ φ : SmoothRealFunction A, g.PositivePotential φ →
      (∀ x, |1-(g.potentialDensity φ).value x| ≤ D) →
      ∀ p : ℝ, 2 ≤ p → g.powerMoment φ (p*ν) ≤
        (C*p^2)^(1/p) * g.powerMoment φ p := by
  obtain ⟨q,hq,S,hS,hsob⟩ := g.sobolev hd
  have hqR : (2:ℝ) < q := by exact_mod_cast hq
  let ν : ℝ := (q:ℝ)/2
  let K : ℝ := D/(1/2:ℝ)^d
  let C : ℝ := S*(K+1)
  have hK : 0 ≤ K := div_nonneg hD (by positivity)
  have hC : 0 < C := mul_pos hS (by linarith)
  refine ⟨ν,C,by dsimp [ν]; linarith,hC,?_⟩
  intro φ hp hρ p hpow
  let ψ := φ.compose (moserPower p) (moserPower_smooth p)
  have hs := hsob ψ
  have he := g.mongeAmpere_power_energy (by omega : 0 < d) D hD φ hp hρ p hpow
  have heI : g.integral (fun x => (moserPower p (φ.value x))^2) = g.powerIntegral φ p := by
    simp only [moserPower_sq, powerIntegral]
  have hsI : g.integral (fun x => ψ.value x^2) = g.powerIntegral φ p := heI
  rw [heI] at he
  rw [hsI, g.moserPower_lpNorm_sq φ (lt_trans (by norm_num) hq) p] at hs
  have hp0 : 0 < p := by linarith
  have hc : S*((p^2/4)*K+1) ≤ C*p^2 := by
    dsimp only [C]
    have hp2 : 1 ≤ p^2 := by nlinarith
    have hh : (p^2/4)*K+1 ≤ (K+1)*p^2 := by nlinarith [mul_nonneg hK (sq_nonneg p)]
    nlinarith [mul_le_mul_of_nonneg_left hh hS.le]
  have hh : (g.powerIntegral φ (p*ν))^(1/ν) ≤ C*p^2*g.powerIntegral φ p := by
    have hνeq : 1/ν = 2/(q:ℝ) := by dsimp [ν]; ring
    have hpe : p*ν = p*(q:ℝ)/2 := by dsimp [ν]; ring
    rw [hνeq,hpe]
    calc
      _ ≤ S*(g.integral (g.energy ψ ψ).value + g.powerIntegral φ p) := hs
      _ ≤ S*((p^2/4)*K*g.powerIntegral φ p + g.powerIntegral φ p) := mul_le_mul_of_nonneg_left (by dsimp only [ψ,K]; linarith only [he]) hS.le
      _ = S*((p^2/4)*K+1)*g.powerIntegral φ p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (g.powerIntegral_nonneg φ p)
  have hν0 : 0 < ν := by dsimp [ν]; positivity
  have hh' := Real.rpow_le_rpow (Real.rpow_nonneg (g.powerIntegral_nonneg φ (p*ν)) _) hh (le_of_lt (one_div_pos.mpr hp0))
  rw [← Real.rpow_mul (g.powerIntegral_nonneg φ (p*ν)),
    Real.mul_rpow (mul_nonneg hC.le (sq_nonneg p)) (g.powerIntegral_nonneg φ p)] at hh'
  convert hh' using 1 <;> dsimp only [powerMoment]
  congr 1
  field_simp

 
theorem mongeAmpere_moment_bounds (g : KaehlerMetric A) (hd : 2 ≤ d)
    (D : ℝ) (hD : 0 ≤ D) : ∃ ν B : ℝ, 1 < ν ∧ 0 ≤ B ∧
    ∀ φ : SmoothRealFunction A, g.PositivePotential φ →
      (∀ x, |1-(g.potentialDensity φ).value x| ≤ D) →
      ∀ n : ℕ, g.powerMoment φ (2*ν^n) ≤ B * g.powerMoment φ 2 := by
  obtain ⟨ν,C,hν,hC,hstep⟩ := g.mongeAmpere_moment_step hd D hD
  let a (n : ℕ) := (C*(2*ν^n)^2)^(1/(2*ν^n))
  let u (n : ℕ) := ∏ j ∈ Finset.range n, a j
  have hu : ∀ n, 0 ≤ u n := fun n => Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)
  have hs (n : ℕ) : u (n+1) ≤ (C*(2*ν^n)^2)^(1/(2*ν^n))*u n := by simp only [u, Finset.prod_range_succ, a]; rw [mul_comm]
  obtain ⟨B,hB,hbound⟩ := moser_sequence_bound ν C 2 hν hC u hu hs (by norm_num)
  refine ⟨ν,B,hν,hB,fun φ hp hρ n => ?_⟩
  have hi (n : ℕ) : g.powerMoment φ (2*ν^n) ≤ u n * g.powerMoment φ 2 := by
    induction n with
    | zero => simp [u]
    | succ n ih =>
      have hn : 2 ≤ 2*ν^n := by nlinarith [one_le_pow₀ (n:=n) hν.le]
      have he : 2*ν^(n+1) = (2*ν^n)*ν := by rw [pow_succ]; ring
      rw [he]
      calc
        _ ≤ a n * g.powerMoment φ (2*ν^n) := hstep φ hp hρ (2*ν^n) hn
        _ ≤ a n * (u n * g.powerMoment φ 2) := mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg (by positivity) _)
        _ = _ := by dsimp only [u]; rw [Finset.prod_range_succ]; ring
  apply (hi n).trans
  apply mul_le_mul_of_nonneg_right _ (g.powerMoment_nonneg φ 2)
  simpa only [u, Finset.range_zero, Finset.prod_empty, mul_one] using hbound n

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
