import OAI.Probability.InvariantIsing.Fields.FieldFiniteLocal
import OAI.Probability.InvariantIsing.Fields.FieldFiniteMeasurable

namespace OAI

/-! Differentiation of the actual finite-height Gaussian transform and
its tilted observables. The local envelope is derived from the family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma affine_average_hasFDerivAt (hI : IsOpen I)
    (A : FieldCovariate n → ℝ → ℝ)
    (DA : FieldCovariate n → ℝ → FieldCovariate n →L[ℝ] ℝ)
    (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {CA CE : ℝ} (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hA : ∀ q, Measurable (A q))
    (hDA : ∀ q, AEStronglyMeasurable (DA q) (gaussianReal 0 1))
    (hAb : ∀ q, q.1 ∈ I → ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hEb : ∀ q, q.1 ∈ I → ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dA : ∀ q, q.1 ∈ I → ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q => ∫ u, A q u ∂F.affineLaw a v ζ q)
      ((∫ u, DA p u + (ζ * A p u) • F.affineDifferential a v p u ∂F.affineLaw a v ζ p) -
        (∫ u, A p u ∂F.affineLaw a v ζ p) •
          (∫ u, ζ • F.affineDifferential a v p u ∂F.affineLaw a v ζ p)) p := by
  obtain ⟨S, C, L, CD, hS, hpS, hSI, hCD, hExp, hD⟩ :=
    F.local_envelope hI a v ζ hR hhi hc hp
  apply field_finite_gaussianPair_hasFDerivAt (F.affineShift a v) A
    (F.affineDifferential a v) DA hS hpS ζ C L CA CD CE hCA hCD hCE
    (fun q => F.mU.comp (by dsimp only [shiftPoint]; fun_prop)) hA
    (F.measurable_affineDifferential a v p).aestronglyMeasurable (hDA p) hExp
    (fun q hq => hAb q (hSI q hq)) hD (fun q hq => hEb q (hSI q hq))
  · intro q hq u
    exact field_finite_affine_shift_hasFDerivAt F.derivative a v u
      (hSI q hq) (hlo q.1 (hSI q hq))
  · exact fun q hq => dA q (hSI q hq)

def value (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : ℝ :=
  gaussianTransform (fieldFiniteVariance a v p.1) ζ (fun y => F.U (p.1, y)) p.2

lemma value_hasFDerivAt (hI : IsOpen I) (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {V R : ℝ} (hR : 0 ≤ R)
    (hlo : ∀ t ∈ I, 0 < fieldFiniteVariance a v t)
    (hhi : ∀ t ∈ I, fieldFiniteVariance a v t ≤ V)
    (hc : ∀ t ∈ I, ∀ i, |fieldFiniteSlope a v t i| ≤ R)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    HasFDerivAt (F.value a v ζ)
      (∫ u, F.affineDifferential a v p u ∂F.affineLaw a v ζ p) p := by
  obtain ⟨S, C, L, CD, hS, _hpS, hSI, hCD, hExp, hD⟩ :=
    F.local_envelope hI a v ζ hR hhi hc hp
  let B : ℝ → ℝ := fun u => CD * (1 + |u|)
  let E : ℝ → ℝ := fun u => Real.exp (C + L * |u|)
  have hBg : HasLinearGrowth B := by
    refine ⟨CD, CD, hCD, hCD, fun u => ?_⟩
    dsimp only [B]
    rw [abs_of_nonneg (by positivity), Real.norm_eq_abs]
    exact le_of_eq (by ring)
  have hBi : Integrable B (gaussianReal 0 1) :=
    field_gaussian_linear_integrable 1 0 (by fun_prop) hBg
  have hEBi : Integrable (fun u => E u * B u) (gaussianReal 0 1) := by
    apply ((field_gaussian_quadratic_envelope_integrable C L).const_mul CD).mono' (by fun_prop)
    apply ae_of_all
    intro u
    change |Real.exp (C + L * |u|) * (CD * (1 + |u|))| ≤
      CD * (Real.exp (C + L * |u|) * (1 + |u|) ^ 2)
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = CD * Real.exp (C + L * |u|) * (1 + |u|) := by ring
      _ ≤ CD * Real.exp (C + L * |u|) * (1 + |u|) ^ 2 :=
        mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) (by positivity)
      _ = _ := by ring
  have hm : Measurable (F.affineShift a v p) := F.mU.comp (by dsimp only [shiftPoint]; fun_prop)
  have hg : HasLinearGrowth (F.affineShift a v p) :=
    (F.growth p.1 hp).add_left p.2 |>.scale_argument (Real.sqrt (fieldFiniteVariance a v p.1))
  exact field_finite_average_hasFDerivAt_of_envelope (gaussianReal 0 1)
    (F.affineShift a v) (F.affineDifferential a v) hS
    (fun q => F.mU.comp (by dsimp only [shiftPoint]; fun_prop))
    (F.measurable_affineDifferential a v p).aestronglyMeasurable
    (field_gaussian_linear_integrable 1 0 hm hg) ζ
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1) hm hg ζ)
    B E hBi hEBi hD hExp (fun q hq u =>
      field_finite_affine_shift_hasFDerivAt F.derivative a v u
        (hSI q hq) (hlo q.1 (hSI q hq)))

end FieldFiniteFamily
end InvariantIsing

end

end OAI
