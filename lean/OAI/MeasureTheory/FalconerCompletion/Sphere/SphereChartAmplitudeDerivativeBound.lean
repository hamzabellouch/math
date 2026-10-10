import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.CompactContDiffOnDerivativeBound2
import OAI.MeasureTheory.FalconerCompletion.Fourier.DerivativeIntegralBoundOfSupport
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAreaAeNorm

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff SchwartzMap RealInnerProductSpace Topology
variable {n : ℕ}

lemma sphereChartAmplitudeND_derivative_bound (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 2)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ) (A : ℝ),
      ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0) →
      (∀ j ≤ m, ∀ w, ‖w‖ = 1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ u : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ j (sphereChartAmplitudeND b) u‖ ≤ D*A^j := by
  obtain ⟨D,hD,hbound⟩ := compact_chart_derivative_bound (f := sphereChartND)
    (w := fun u : EuclideanSpace ℝ (Fin n) => (sphereChartWeightND u:ℂ))
    isOpen_ball (isCompact_closedBall 0 r) (closedBall_subset_ball hr2)
    (sphereChartND_contDiffOn.of_le le_top)
    (Complex.ofRealCLM.contDiff.comp_contDiffOn sphereChartWeightND_contDiffOn) m C hC
  refine ⟨D,hD,?_⟩
  intro b A hb hA hsupp hderiv
  apply hbound b A hb hA (sphereChartAmplitudeND_tsupport hr hsupp)
  intro j hj w hw
  obtain ⟨u,hu,rfl⟩ := hw
  exact hderiv j hj _ (sphereChartND_norm ((show ‖u‖ ≤ r by simpa using hu).trans hr2.le))

theorem sphere_stationaryND_uniform (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 2)
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℂ)
      (A Λ : ℝ) (hb : ContDiff ℝ ∞ b)
      (hsupp : ∀ w, ‖w‖ = 1 → (WithLp.ofLp w).2 ≤ 1-r^2/2 → b w = 0),
      1 ≤ A → 0 < Λ →
      (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖ = 1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ‖(∫ w, Complex.exp (Complex.I * Λ *
        (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w ∂sphereAreaND n) -
        Complex.exp (Complex.I * Λ) *
          (fresnelCoefficientND (EuclideanSpace ℝ (Fin n)) (Λ/2) *
            quadraticExpansionND (sphereChartSchwartzND b r hr hr2 hb hsupp) J (Λ/2))‖ ≤
        D * Λ^(-(n:ℝ)/2-(J+1:ℕ)) * A^(2*(J+1)+n+3) := by
  obtain ⟨C',hC',hamp⟩ := sphereChartAmplitudeND_derivative_bound (n := n) r hr hr2
    (2*(J+1)+n+3) C hC
  obtain ⟨D',hD',hquad⟩ := quadratic_stationaryND_uniform
    (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) (isCompact_closedBall 0 r) C' hC' J
  refine ⟨D'*2^((n:ℝ)/2+(J+1:ℕ)), by positivity, ?_⟩
  intro b A Λ hb hsupp hA hΛ hderiv
  rw [integral_sphereAreaND_eq_quadratic hr hr2 hb.continuous.stronglyMeasurable hsupp,
    ← mul_sub, norm_mul, norm_exp_I_mul_real, one_mul]
  have hφsupp : tsupport (sphereChartSchwartzND b r hr hr2 hb hsupp :
      EuclideanSpace ℝ (Fin n) → ℂ) ⊆ closedBall 0 r :=
    sphereChartAmplitudeND_tsupport hr hsupp
  have hh := hquad (sphereChartSchwartzND b r hr hr2 hb hsupp) A (Λ/2)
    hφsupp hA (by positivity) (by
      change ∀ j ≤ 2*(J+1)+Module.finrank ℝ (EuclideanSpace ℝ (Fin n))+3,
        ∀ u : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ j (sphereChartAmplitudeND b) u‖ ≤ C'*A^j
      simpa using hamp b A hb hA hsupp hderiv)
  have he : (Λ/2)^(-((n:ℝ)/2)-(J+1:ℕ)) =
      2^((n:ℝ)/2+(J+1:ℕ)) * Λ^(-((n:ℝ)/2)-(J+1:ℕ)) := by
    rw [Real.div_rpow hΛ.le (by norm_num)]
    have hp : -((n:ℝ)/2)-(J+1:ℕ) = -((n:ℝ)/2+(J+1:ℕ)) := by ring
    rw [hp, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
  rw [he] at hh
  simpa [sphereChartSchwartzND, mul_assoc, neg_div] using hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ENNReal Pointwise RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def canonicalSphereMeasureND (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : Measure V :=
  Measure.map Subtype.val (volume : Measure V).toSphere

lemma canonicalSphereMeasureND_apply {s : Set V} (hs : MeasurableSet s) :
    canonicalSphereMeasureND V s = (Module.finrank ℝ V : ℝ≥0∞) *
      volume (Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ s)) := by
  rw [canonicalSphereMeasureND, Measure.map_apply measurable_subtype_coe hs,
    Measure.toSphere_apply' volume (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp

lemma canonicalSphereMeasureND_linearIsometry (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving e (canonicalSphereMeasureND V) (canonicalSphereMeasureND V) := by
  refine ⟨e.continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    canonicalSphereMeasureND_apply (e.continuous.measurable hs),
    canonicalSphereMeasureND_apply hs]
  have hset : Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Ioo (0:ℝ) 1 • (sphere (0:V) 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,w,⟨hw,hsw⟩,rfl⟩
      exact ⟨r,hr,e w,⟨by simpa using hw,hsw⟩,by simp⟩
    · rintro ⟨r,hr,w,⟨hw,hsw⟩,hwx⟩
      refine ⟨r,hr,e.symm w,⟨by simpa using hw,by simpa using hsw⟩,?_⟩
      apply e.injective
      simpa using hwx
  rw [hset, e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

lemma integral_canonicalSphereMeasureND_isometry (e : V ≃ₗᵢ[ℝ] V) (f : V → ℂ) :
    (∫ w, f (e w) ∂canonicalSphereMeasureND V) = ∫ w, f w ∂canonicalSphereMeasureND V :=
  (canonicalSphereMeasureND_linearIsometry e).integral_comp e.toHomeomorph.measurableEmbedding f

lemma integral_canonicalSphereMeasureND_neg (f : V → ℂ) :
    (∫ w, f (-w) ∂canonicalSphereMeasureND V) = ∫ w, f w ∂canonicalSphereMeasureND V :=
  integral_canonicalSphereMeasureND_isometry (LinearIsometryEquiv.neg ℝ) f

lemma integrable_canonicalSphereMeasureND {f : V → ℂ} (hf : Continuous f) :
    Integrable f (canonicalSphereMeasureND V) := by
  rw [canonicalSphereMeasureND,
    integrable_map_measure hf.stronglyMeasurable.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable]
  exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_iteratedFDeriv_antipodal_conj {b : V → ℂ} (hb : ContDiff ℝ ∞ b)
    (j : ℕ) (w : V) :
    ‖iteratedFDeriv ℝ j (fun v => star (b (-v))) w‖ ≤
      ‖iteratedFDeriv ℝ j b (-w)‖ := by
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤:ℕ∞) : WithTop ℕ∞) := by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)
  have h := Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.norm_iteratedFDeriv_comp_left (x := w)
    (hb.comp contDiff_neg).contDiffAt hj
  have he : iteratedFDeriv ℝ j (fun v => b (-v)) w =
      (-1:ℝ)^j • iteratedFDeriv ℝ j b (-w) := by
    simpa using congrFun (iteratedFDeriv_comp_const_smul (-1:ℝ) (hb.of_le hj)) w
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, Function.comp_def, Complex.conjLIE_apply, starRingEnd_apply,
    LinearIsometryEquiv.norm_toContinuousLinearMap, one_mul, he,
    norm_smul, norm_pow, norm_neg, norm_one, one_pow] using h

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def sphereNorthCutoffND (w : WithLp 2 (V × ℝ)) : ℂ :=
  Real.smoothTransition ((WithLp.ofLp w).2 + 1/2)

lemma sphereNorthCutoffND_contDiff :
    ContDiff ℝ ∞ (sphereNorthCutoffND : WithLp 2 (V × ℝ) → ℂ) := by
  have h : ContDiff ℝ ∞ (fun w : WithLp 2 (V × ℝ) => (WithLp.ofLp w).2) :=
    contDiff_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).contDiff
  exact Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp (h.add contDiff_const))

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma sphereNorthCutoffND_zero {w : WithLp 2 (V × ℝ)}
    (hw : (WithLp.ofLp w).2 ≤ -(1/2:ℝ)) : sphereNorthCutoffND w = 0 := by
  unfold sphereNorthCutoffND
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), Complex.ofReal_zero]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma sphereNorthCutoffND_one {w : WithLp 2 (V × ℝ)}
    (hw : (1/2:ℝ) ≤ (WithLp.ofLp w).2) : sphereNorthCutoffND w = 1 := by
  unfold sphereNorthCutoffND
  rw [Real.smoothTransition.one_of_one_le (by linarith), Complex.ofReal_one]

noncomputable def sphereNorthPartND (b : WithLp 2 (V × ℝ) → ℂ) (w : WithLp 2 (V × ℝ)) : ℂ :=
  sphereNorthCutoffND w * b w

noncomputable def sphereReflectedSouthPartND
    (b : WithLp 2 (V × ℝ) → ℂ) (w : WithLp 2 (V × ℝ)) : ℂ :=
  star ((1-sphereNorthCutoffND (-w))*b (-w))

lemma sphereNorthPartND_contDiff {b : WithLp 2 (V × ℝ) → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (sphereNorthPartND b) := sphereNorthCutoffND_contDiff.mul hb

lemma sphereReflectedSouthPartND_contDiff {b : WithLp 2 (V × ℝ) → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (sphereReflectedSouthPartND b) := by
  change ContDiff ℝ ∞ (fun w => star ((1-sphereNorthCutoffND (-w))*b (-w)))
  simpa only [Complex.star_def, Function.comp_def, Complex.conjCLE_apply] using
    Complex.conjCLE.contDiff.comp
      ((contDiff_const.sub (sphereNorthCutoffND_contDiff.comp contDiff_neg)).mul
        (hb.comp contDiff_neg))

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma sphereNorthPartND_support {b : WithLp 2 (V × ℝ) → ℂ} {w : WithLp 2 (V × ℝ)}
    (hw : (WithLp.ofLp w).2 ≤ 1-(Real.sqrt 3)^2/2) : sphereNorthPartND b w = 0 := by
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  rw [sphereNorthPartND, sphereNorthCutoffND_zero (by rw [h3] at hw; linarith), zero_mul]

omit [InnerProductSpace ℝ V] in
lemma sphereReflectedSouthPartND_support {b : WithLp 2 (V × ℝ) → ℂ} {w : WithLp 2 (V × ℝ)}
    (hw : (WithLp.ofLp w).2 ≤ 1-(Real.sqrt 3)^2/2) : sphereReflectedSouthPartND b w = 0 := by
  have h3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : (1/2:ℝ) ≤ (WithLp.ofLp (-w)).2 := by
    change (1/2:ℝ) ≤ -(WithLp.ofLp w).2
    rw [h3] at hw
    linarith
  rw [sphereReflectedSouthPartND,sphereNorthCutoffND_one hn,sub_self,zero_mul,star_zero]

lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def sphereOscillationND (Λ : ℝ) (b : WithLp 2 (V × ℝ) → ℂ) : ℂ :=
  ∫ w, Complex.exp (Complex.I * Λ *
    (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ)) * b w
    ∂canonicalSphereMeasureND (WithLp 2 (V × ℝ))

lemma sphereOscillationND_split (Λ : ℝ) {b : WithLp 2 (V × ℝ) → ℂ}
    (hb : Continuous b) :
    sphereOscillationND Λ b = sphereOscillationND Λ (sphereNorthPartND b) +
      star (sphereOscillationND Λ (sphereReflectedSouthPartND b)) := by
  let E := WithLp 2 (V × ℝ)
  let phase : E → ℂ := fun w => Complex.exp (Complex.I * Λ *
    (inner ℝ w (WithLp.toLp 2 (0,(1:ℝ))) : ℂ))
  have hphase : Continuous phase := by dsimp [phase]; fun_prop
  have he (w : E) : star (phase (-w)) = phase w := by
    dsimp [phase]
    simp only [inner_neg_left, Complex.ofReal_neg,
      ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    ring
  have hanti : star (sphereOscillationND Λ (sphereReflectedSouthPartND b)) =
      ∫ w, phase w * ((1-sphereNorthCutoffND w)*b w)
        ∂canonicalSphereMeasureND E := by
    unfold sphereOscillationND
    rw [show (star : ℂ → ℂ) = (starRingEnd ℂ) from rfl, ← integral_conj]
    rw [← integral_canonicalSphereMeasureND_neg]
    apply integral_congr_ae
    filter_upwards [] with w
    change star (phase (-w)*star ((1-sphereNorthCutoffND (-(-w)))*b (-(-w)))) = _
    rw [star_mul,star_star,neg_neg,he]
    ring
  rw [hanti]
  change (∫ w, phase w*b w ∂canonicalSphereMeasureND E) =
    (∫ w, phase w*(sphereNorthCutoffND w*b w) ∂canonicalSphereMeasureND E) + _
  have hN : Integrable (fun w => phase w*(sphereNorthCutoffND w*b w))
      (canonicalSphereMeasureND E) :=
    integrable_canonicalSphereMeasureND (hphase.mul (sphereNorthCutoffND_contDiff.continuous.mul hb))
  have hS : Integrable (fun w => phase w*((1-sphereNorthCutoffND w)*b w))
      (canonicalSphereMeasureND E) :=
    integrable_canonicalSphereMeasureND
      (hphase.mul (((continuous_const : Continuous (fun _ : E => (1:ℂ))).sub
        sphereNorthCutoffND_contDiff.continuous).mul hb))
  rw [← integral_add hN hS]
  apply integral_congr_ae
  filter_upwards [] with w
  ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
