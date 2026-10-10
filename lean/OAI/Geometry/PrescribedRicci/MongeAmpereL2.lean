import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerPoincare
import OAI.Geometry.PrescribedRicci.KahlerVolumeVariation
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy
import OAI.Geometry.PrescribedPotential.VolumeDeterminantBounds

namespace OAI

/-! Monge Ampere L2. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

theorem mongeAmpere_L2_bound (g : KaehlerMetric A) (hd : 0 < d)
    (D : ℝ) (hD : 0 ≤ D) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : SmoothRealFunction A, g.PositivePotential φ → g.integral φ.value = 0 →
      (∀ x, |1 - (g.potentialDensity φ).value x| ≤ D) →
      g.integral (fun x => φ.value x ^ 2) ≤ C := by
  obtain ⟨P,hP,hpoincare⟩ := g.poincare
  let c : ℝ := (1/2) ^ d
  have hc : 0 < c := pow_pos (by norm_num) _
  let V := g.integral (fun _ => 1)
  have hV : 0 ≤ V := g.integral_nonneg (fun _ => zero_le_one)
  refine ⟨(P*D)^2 * V / c^2, div_nonneg (mul_nonneg (sq_nonneg _) hV) (sq_nonneg _), ?_⟩
  intro φ hp hmean hρ
  let Iφ := g.integral (fun x => φ.value x ^ 2)
  let Eφ := g.integral (g.energy φ φ).value
  let Lφ := g.integral (fun x => |φ.value x|)
  have hI : 0 ≤ Iφ := g.integral_nonneg (fun _ => sq_nonneg _)
  have hL : 0 ≤ Lφ := g.integral_nonneg (fun _ => abs_nonneg _)
  have hpi : Iφ ≤ P * Eφ := hpoincare φ hmean
  have hma : c * Eφ ≤ D * Lφ := g.mongeAmpere_energy_density_bound φ hp hd D hρ
  have hcs : Lφ ^ 2 ≤ Iφ * V := by
    have hh := g.integral_cauchySchwarz φ.continuous.abs (continuous_const (y := (1 : ℝ)))
    simpa only [one_pow, mul_one, sq_abs] using hh
  have hfirst : c * Iφ ≤ (P*D) * Lφ := by
    calc
      c * Iφ ≤ c * (P * Eφ) := mul_le_mul_of_nonneg_left hpi hc.le
      _ = P * (c * Eφ) := by ring
      _ ≤ P * (D * Lφ) := mul_le_mul_of_nonneg_left hma hP.le
      _ = _ := by ring
  have hs : (c*Iφ)^2 ≤ ((P*D)*Lφ)^2 :=
    (sq_le_sq₀ (mul_nonneg hc.le hI) (mul_nonneg (mul_nonneg hP.le hD) hL)).2 hfirst
  have hprod : (c^2 * Iφ) * Iφ ≤ ((P*D)^2 * V) * Iφ := by
    calc
      (c^2 * Iφ) * Iφ = (c*Iφ)^2 := by ring
      _ ≤ ((P*D)*Lφ)^2 := hs
      _ = (P*D)^2 * Lφ^2 := by ring
      _ ≤ (P*D)^2 * (Iφ*V) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = _ := by ring
  change Iφ ≤ (P*D)^2 * V / c^2
  by_cases hz : Iφ = 0
  · rw [hz]; exact div_nonneg (mul_nonneg (sq_nonneg _) hV) (sq_nonneg _)
  · apply (le_div_iff₀ (sq_pos_of_pos hc)).2
    have hh := (mul_le_mul_iff_left₀ (lt_of_le_of_ne hI (Ne.symm hz))).1 hprod
    simpa only [mul_comm] using hh

omit [T2Space X] in
lemma volumePath_density_bounds (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (ht : t ∈ Icc 0 1)
    (hp : g.PositivePotential φ)
    (he : ∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g h).value x+b)
    (x : X) :
    let M := ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖;
    Real.exp (-2*M) ≤ (g.potentialDensity φ).value x ∧
      (g.potentialDensity φ).value x ≤ Real.exp (2*M) := by
  obtain ⟨i,hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have hh := volumePath_det_ratio_bounds g h ht hp he i hz
  have hdens := g.density_mul_volume φ i hz
  rw [(A.chart i).left_inv hi] at hdens
  have hv := g.volumeCoefficient_pos i hz
  change 0 < (g.matrix i (A.chart i x)).det.re at hv
  have heq : (g.potentialDensity φ).value x =
      (g.matrix i (A.chart i x) + φ.hessian i (A.chart i x)).det.re /
        (g.matrix i (A.chart i x)).det.re := (eq_div_iff (ne_of_gt hv)).2 hdens
  rw [heq]
  exact hh

 

theorem volumePath_L2_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (hd : 0 < d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t b : ℝ) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ), t ∈ Icc 0 1 →
      g.integral φ.value = 0 →
      (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g h).value x+b) →
      g.integral (fun x => φ.value x ^ 2) ≤ C := by
  let M := ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖
  obtain ⟨C,hC,hbound⟩ := g.mongeAmpere_L2_bound hd (1 + Real.exp (2*M)) (by positivity)
  refine ⟨C,hC,fun t b φ hp ht hmean he => hbound φ hp hmean ?_⟩
  intro x
  obtain ⟨hlo,hup⟩ := g.volumePath_density_bounds h ht hp he x
  change Real.exp (-2*M) ≤ _ at hlo
  change _ ≤ Real.exp (2*M) at hup
  have hρ : 0 ≤ (g.potentialDensity φ).value x := (Real.exp_pos _).le.trans hlo
  apply abs_le.mpr
  constructor <;> linarith [Real.exp_pos (2*M)]

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
