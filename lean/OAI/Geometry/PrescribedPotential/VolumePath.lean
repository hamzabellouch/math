import Mathlib
import OAI.Geometry.PrescribedPotential.SourceTarget

namespace OAI

/-! Volume Path. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma volumeCoefficient_pos (g : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) : 0 < g.volumeCoefficient i z :=
  (Complex.pos_iff.mp (g.positive i z hz).det_pos).1

lemma volumeCoefficient_smooth (g : KaehlerMetric A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (g.volumeCoefficient i) (A.chart i).target := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  apply contDiffOn_const.mul
  apply contDiffOn_prod
  intro j _
  exact contDiffOn_pi.mp (contDiffOn_pi.mp (g.smooth i) (σ j)) j

lemma volumeCoefficient_compatibility (g : KaehlerMetric A) (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    g.volumeCoefficient i (A.chart i x) = ‖A.jacobian i j x‖^2 *
      g.volumeCoefficient j (A.chart j x) := by
  unfold volumeCoefficient
  rw [g.compatibility i j x hi hj, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  change ((starRingEnd ℂ) (A.jacobian i j x) *
    (g.matrix j (A.chart j x)).det * A.jacobian i j x).re = _
  have he : (starRingEnd ℂ) (A.jacobian i j x) *
      (g.matrix j (A.chart j x)).det * A.jacobian i j x =
      ((‖A.jacobian i j x‖^2 : ℝ) : ℂ) * (g.matrix j (A.chart j x)).det := by
    rw [show (starRingEnd ℂ) (A.jacobian i j x) *
      (g.matrix j (A.chart j x)).det * A.jacobian i j x =
      (A.jacobian i j x * (starRingEnd ℂ) (A.jacobian i j x)) *
      (g.matrix j (A.chart j x)).det by ring, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma logVolume_compatibility (g : KaehlerMetric A) (i j : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    Real.log (g.volumeCoefficient i (A.chart i x)) =
      Real.log (‖A.jacobian i j x‖^2) + Real.log (g.volumeCoefficient j (A.chart j x)) := by
  rw [g.volumeCoefficient_compatibility i j hi hj]
  apply Real.log_mul
  · have hpos := g.volumeCoefficient_pos i ((A.chart i).mapsTo hi)
    rw [g.volumeCoefficient_compatibility i j hi hj] at hpos
    exact left_ne_zero_of_mul (ne_of_gt hpos)
  · exact ne_of_gt (g.volumeCoefficient_pos j ((A.chart j).mapsTo hj))

 
def logRatioValue (g₀ g : KaehlerMetric A) (x : X) : ℝ :=
  let i := (A.covers x).choose;
  Real.log (g.volumeCoefficient i (A.chart i x)) -
    Real.log (g₀.volumeCoefficient i (A.chart i x))

lemma logRatioValue_local (g₀ g : KaehlerMetric A) (i : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) :
    g₀.logRatioValue g x = Real.log (g.volumeCoefficient i (A.chart i x)) -
      Real.log (g₀.volumeCoefficient i (A.chart i x)) := by
  dsimp only [logRatioValue]
  rw [g.logVolume_compatibility _ i (A.covers x).choose_spec hi,
    g₀.logVolume_compatibility _ i (A.covers x).choose_spec hi]
  ring

def logRatio (g₀ g : KaehlerMetric A) : SmoothRealFunction A where
  value := g₀.logRatioValue g
  smooth i := by
    have hg := (g.volumeCoefficient_smooth i).log
      (fun z hz => ne_of_gt (g.volumeCoefficient_pos i hz))
    have h₀ := (g₀.volumeCoefficient_smooth i).log
      (fun z hz => ne_of_gt (g₀.volumeCoefficient_pos i hz))
    apply (hg.sub h₀).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [g₀.logRatioValue_local g i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]

lemma logRatio_local (g₀ g : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g₀.logRatio g).localExpression i z =
      Real.log (g.volumeCoefficient i z) - Real.log (g₀.volumeCoefficient i z) := by
  change g₀.logRatioValue g ((A.chart i).symm z) = _
  rw [g₀.logRatioValue_local g i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]

end KaehlerMetric

 

def prescribedForcingValue (g₀ : KaehlerMetric A)
    (h : SemipositiveAnticanonicalMetric A) (x : X) : ℝ :=
  let i := (A.covers x).choose;
  -h.weight i (A.chart i x) - Real.log (g₀.volumeCoefficient i (A.chart i x))

lemma prescribedForcingValue_local (g₀ : KaehlerMetric A)
    (h : SemipositiveAnticanonicalMetric A) (i : Fin A.count) {x : X}
    (hi : x ∈ (A.chart i).source) :
    prescribedForcingValue g₀ h x =
      -h.weight i (A.chart i x) - Real.log (g₀.volumeCoefficient i (A.chart i x)) := by
  dsimp only [prescribedForcingValue]
  have hw := h.compatibility (A.covers x).choose i x (A.covers x).choose_spec hi
  rw [g₀.logVolume_compatibility _ i (A.covers x).choose_spec hi]
  linarith

def prescribedForcing (g₀ : KaehlerMetric A)
    (h : SemipositiveAnticanonicalMetric A) : SmoothRealFunction A where
  value := prescribedForcingValue g₀ h
  smooth i := by
    apply ((h.smooth i).neg.sub ((g₀.volumeCoefficient_smooth i).log
      (fun z hz => ne_of_gt (g₀.volumeCoefficient_pos i hz)))).congr
    intro z hz
    dsimp only [Function.comp_apply]
    rw [prescribedForcingValue_local g₀ h i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]

lemma prescribedForcing_local (g₀ : KaehlerMetric A)
    (h : SemipositiveAnticanonicalMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (prescribedForcing g₀ h).localExpression i z =
      -h.weight i z - Real.log (g₀.volumeCoefficient i z) := by
  change prescribedForcingValue g₀ h ((A.chart i).symm z) = _
  rw [prescribedForcingValue_local g₀ h i ((A.chart i).mapsTo_symm hz), (A.chart i).right_inv hz]

 

def SolvesVolumePath (g₀ : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (t : ℝ) (φ : SmoothRealFunction A) (b : ℝ) : Prop :=
  ∃ hp : g₀.PositivePotential φ, ∀ x,
    (g₀.logRatio (g₀.deform φ hp)).value x = t * (prescribedForcing g₀ h).value x + b

lemma volumePath_zero (g₀ : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    SolvesVolumePath g₀ h 0 (SmoothRealFunction.constant 0) 0 := by
  have hp : g₀.PositivePotential (SmoothRealFunction.constant 0) := by
    intro i z hz
    rw [SmoothRealFunction.hessian_constant, add_zero]
    exact g₀.positive i z hz
  refine ⟨hp, fun x => ?_⟩
  obtain ⟨i,hi⟩ := A.covers x
  change g₀.logRatioValue (g₀.deform _ hp) x = _
  rw [g₀.logRatioValue_local _ i hi]
  simp [KaehlerMetric.volumeCoefficient, KaehlerMetric.deform,
    SmoothRealFunction.hessian_constant]

 

lemma volumePath_one (P : A.ProjectiveEmbedding) (h : SemipositiveAnticanonicalMetric A)
    (φ : SmoothRealFunction A) (b : ℝ)
    (hsol : SolvesVolumePath (projectiveBackground P) h 1 φ b) :
    HasPrescribedVolumePotential P h := by
  obtain ⟨hp, heq⟩ := hsol
  refine ⟨φ, Real.exp b, Real.exp_pos b, hp, fun i z hz => ?_⟩
  have hev := heq ((A.chart i).symm z)
  change ((projectiveBackground P).logRatio ((projectiveBackground P).deform φ hp)).localExpression i z =
    1 * (prescribedForcing (projectiveBackground P) h).localExpression i z + b at hev
  rw [KaehlerMetric.logRatio_local _ _ i hz, prescribedForcing_local _ _ i hz, one_mul] at hev
  have hv : Real.log (((projectiveBackground P).deform φ hp).volumeCoefficient i z) = b - h.weight i z := by
    linarith
  have he := congrArg Real.exp hv
  rw [Real.exp_log (((projectiveBackground P).deform φ hp).volumeCoefficient_pos i hz),
    sub_eq_add_neg, Real.exp_add] at he
  exact he

end Anticanonical.SourceSmooth

end
end

end OAI
