import Mathlib
import OAI.Geometry.PrescribedPotential.NormalizedPoisson
import OAI.Geometry.PrescribedPotential.PotentialDensity
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Positive Potential Linearization. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma potentialDensity_quotient (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (i : Fin A.count) {x : X} (hi : x ∈ (A.chart i).source) :
    (g.potentialDensity φ).value x =
      (g.matrix i (A.chart i x) + φ.hessian i (A.chart i x)).det.re /
        g.volumeCoefficient i (A.chart i x) := by
  have hz := (A.chart i).mapsTo hi
  have hN := hermitian_det_im ((g.positive i _ hz).isHermitian.add (φ.hessian_hermitian i hz))
  have hB := hermitian_det_im (g.positive i _ hz).isHermitian
  have heN : ((g.matrix i (A.chart i x) + φ.hessian i (A.chart i x)).det.re : ℂ) =
      (g.matrix i (A.chart i x) + φ.hessian i (A.chart i x)).det :=
    Complex.ext rfl hN.symm
  have heB : ((g.matrix i (A.chart i x)).det.re : ℂ) = (g.matrix i (A.chart i x)).det :=
    Complex.ext rfl hB.symm
  change g.potentialDensityValue φ x = _
  rw [g.potentialDensityValue_local φ i hi,volumePolynomial,← heN,← heB,← Complex.ofReal_div]
  rfl

lemma potentialDensity_pos (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (x : X) : 0 < (g.potentialDensity φ).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  rw [g.potentialDensity_quotient φ i hi]
  exact div_pos (Complex.pos_iff.mp (hp i _ ((A.chart i).mapsTo hi)).det_pos).1
    (g.volumeCoefficient_pos i ((A.chart i).mapsTo hi))

 

lemma potentialLogDensity_directional (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (x : X) :
    HasDerivAt (fun t : ℝ => Real.log
      ((g.potentialDensity (φ.addFunction (ψ.realSMul t))).value x))
      (((g.deform φ hp).laplacian ψ).value x) 0 := by
  obtain ⟨i,hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  let H := g.matrix i (A.chart i x) + φ.hessian i (A.chart i x)
  let K := ψ.hessian i (A.chart i x)
  let b := g.volumeCoefficient i (A.chart i x)
  have hH : H.PosDef := hp i _ hz
  have hb : 0 < b := g.volumeCoefficient_pos i hz
  have hdet : 0 < H.det.re := (Complex.pos_iff.mp hH.det_pos).1
  have him : H.det.im = 0 := hermitian_det_im hH.isHermitian
  have hn := (MongeAmpere.hasDerivAt_det_add_smul H K
    (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos))).real_of_complex
  have hn' : HasDerivAt (fun t : ℝ => (H + (t : ℂ) • K).det.re)
      (H.det.re * (H⁻¹ * K).trace.re) 0 := by
    simpa only [Complex.mul_re,him,zero_mul,sub_zero] using hn
  have he : (fun t : ℝ => (g.potentialDensity (φ.addFunction (ψ.realSMul t))).value x) =
      (fun t : ℝ => (H + (t : ℂ) • K).det.re / b) := by
    funext t
    rw [g.potentialDensity_quotient _ i hi,SmoothRealFunction.hessian_addFunction _ _ i hz,
      SmoothRealFunction.hessian_realSMul]
    simp only [H,K,b,add_assoc]
  rw [show ((g.deform φ hp).laplacian ψ).value x = (H⁻¹ * K).trace.re from
    (g.deform φ hp).laplacianValue_local ψ i hi]
  change HasDerivAt (Real.log ∘ (fun t : ℝ =>
    (g.potentialDensity (φ.addFunction (ψ.realSMul t))).value x)) _ 0
  rw [he]
  have hd := (hn'.div_const b).log (show (H + ((0 : ℝ) : ℂ) • K).det.re / b ≠ 0 from by
    simpa using ne_of_gt (div_pos hdet hb))
  have hc : H.det.re * (H⁻¹ * K).trace.re / b / ((H + ((0 : ℝ) : ℂ) • K).det.re / b) =
      (H⁻¹ * K).trace.re := by
    simp only [Complex.ofReal_zero,zero_smul,add_zero]
    field_simp
  rw [hc] at hd
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => rfl))

end KaehlerMetric

 

theorem positivePotential_linearized_solvable [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (g : KaehlerMetric A) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    (x₀ : X) (f : SmoothRealFunction A) :
    ∃ (ψ : SmoothRealFunction A) (a : ℝ), ψ.value x₀ = 0 ∧
      ∀ x, HasDerivAt (fun t : ℝ =>
        Real.log ((g.potentialDensity (φ.addFunction (ψ.realSMul t))).value x) + t*a)
        (f.value x) 0 := by
  obtain ⟨ψ,a,hn,he⟩ := normalizedPoisson d X A (g.deform φ hp) x₀ f
  refine ⟨ψ,a,hn,fun x => ?_⟩
  obtain ⟨i,hi⟩ := A.covers x
  have h := (g.potentialLogDensity_directional φ ψ hp x).add ((hasDerivAt_id (0 : ℝ)).mul_const a)
  have hr : ((g.deform φ hp).laplacian ψ).value x + a = f.value x := by
    change (g.deform φ hp).laplacianValue ψ x + a = _
    rw [(g.deform φ hp).laplacianValue_local ψ i hi]
    simpa only [SmoothRealFunction.localExpression,Function.comp_apply,(A.chart i).left_inv hi]
      using he i (A.chart i x) ((A.chart i).mapsTo hi)
  rw [one_mul,hr] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => rfl))

end Anticanonical.SourceSmooth

end
end

end OAI
