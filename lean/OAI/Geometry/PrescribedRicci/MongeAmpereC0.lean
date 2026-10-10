import Mathlib
import OAI.Geometry.PrescribedRicci.MomentBoundPointwise
import OAI.Geometry.PrescribedRicci.MongeAmpereMoments
import OAI.Geometry.PrescribedRicci.MongeAmpereL2
import OAI.Geometry.PrescribedRicci.KahlerIntegralPos
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Monge Ampere C0. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

 

theorem mongeAmpere_C0_bound (g : KaehlerMetric A) (hd : 2 ≤ d)
    (D : ℝ) (hD : 0 ≤ D) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : SmoothRealFunction A, g.PositivePotential φ → g.integral φ.value = 0 →
      (∀ x, |1-(g.potentialDensity φ).value x| ≤ D) → ∀ x, |φ.value x| ≤ C := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨L,hL,hL2⟩ := g.mongeAmpere_L2_bound (by omega : 0 < d) D hD
  obtain ⟨ν,B,hν,hB,hM⟩ := g.mongeAmpere_moment_bounds hd D hD
  let V := g.integral (fun _ => (1:ℝ))
  have hV : 0 ≤ V := g.integral_nonneg (fun _ => zero_le_one)
  let M : ℝ := (V+L)^(1/2:ℝ)
  have hMn : 0 ≤ M := Real.rpow_nonneg (add_nonneg hV hL) _
  refine ⟨B*M,mul_nonneg hB hMn,fun φ hp hm hρ => ?_⟩
  have h2 : g.powerMoment φ 2 ≤ M := by
    have hI : g.powerIntegral φ 2 = V + g.integral (fun x => φ.value x^2) := by
      simp only [powerIntegral, div_self (by norm_num : (2:ℝ) ≠ 0), Real.rpow_one]
      exact g.integral_add continuous_const (φ.continuous.pow 2)
    change (g.powerIntegral φ 2)^(1/2:ℝ) ≤ (V+L)^(1/2:ℝ)
    apply Real.rpow_le_rpow (g.powerIntegral_nonneg φ 2) _ (by norm_num)
    rw [hI]
    have hh := hL2 φ hp hm hρ
    linarith
  let w : X → ℝ := fun x => Real.sqrt (1+φ.value x^2)
  have hw : Continuous w := (continuous_const.add (φ.continuous.pow 2)).sqrt
  have hwn (x : X) : 0 ≤ w x := Real.sqrt_nonneg _
  let p : ℕ → ℝ := fun n => 2*ν^n
  have hp0 (n : ℕ) : 0 < p n := mul_pos (by norm_num) (pow_pos (lt_trans zero_lt_one hν) n)
  have hpt : Tendsto p atTop atTop := (tendsto_pow_atTop_atTop_of_one_lt hν).const_mul_atTop (by norm_num)
  have hwp (n : ℕ) : (fun x => w x^(p n)) = (fun x => (1+φ.value x^2)^((p n)/2)) := by
    funext x
    dsimp only [w]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 1+φ.value x^2)]
    congr 1; ring
  have hi (n : ℕ) : Integrable (fun x => w x ^ p n) g.volumeMeasure := by
    rw [hwp]
    exact (powerIntegrand_continuous φ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmom (n : ℕ) : ∫ x, w x^p n ∂g.volumeMeasure ≤ (B*M)^p n := by
    rw [hwp, g.integral_volumeMeasure (powerIntegrand_continuous φ _)]
    have hh : g.powerMoment φ (p n) ≤ B*M :=
      (hM φ hp hρ n).trans (mul_le_mul_of_nonneg_left h2 hB)
    have hpow := Real.rpow_le_rpow (g.powerMoment_nonneg φ (p n)) hh (hp0 n).le
    dsimp only [powerMoment] at hpow
    rw [← Real.rpow_mul (g.powerIntegral_nonneg φ (p n)), one_div_mul_cancel (ne_of_gt (hp0 n)), Real.rpow_one] at hpow
    exact hpow
  have hpoint := continuous_le_of_moments hw hwn p hp0 hpt (mul_nonneg hB hMn) hi hmom
  intro x
  calc
    |φ.value x| = Real.sqrt (φ.value x^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ w x := Real.sqrt_le_sqrt (by linarith)
    _ ≤ _ := hpoint x

 
theorem volumePath_C0_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ), g.integral φ.value = 0 →
      ∀ (t b : ℝ), t ∈ Icc 0 1 →
        (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g h).value x+b) →
          ∀ x, |φ.value x| ≤ C := by
  let M := ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖
  let D := 1+Real.exp (2*M)
  obtain ⟨C,hC,hbound⟩ := g.mongeAmpere_C0_bound hd D (by dsimp [D]; positivity)
  refine ⟨C,hC,fun φ hp hm t b ht he => hbound φ hp hm (fun x => ?_)⟩
  have hh := g.volumePath_density_bounds h ht hp he x
  have hpρ : 0 ≤ (g.potentialDensity φ).value x := (Real.exp_pos _).le.trans hh.1
  calc
    |1-(g.potentialDensity φ).value x| ≤ |(1:ℝ)|+|(g.potentialDensity φ).value x| := abs_sub _ _
    _ = 1+(g.potentialDensity φ).value x := by rw [abs_one, abs_of_nonneg hpρ]
    _ ≤ _ := by dsimp [D,M]; linarith [hh.2]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
