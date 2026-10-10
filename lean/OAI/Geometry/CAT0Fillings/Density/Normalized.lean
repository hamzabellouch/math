import Mathlib
import OAI.Geometry.CAT0Fillings.Tangent.Quadratic
import OAI.Geometry.CAT0Fillings.Density.Chart
import OAI.Geometry.CAT0Fillings.Density.NearEuclidean

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

lemma normalized_piece (C : IntegerChart X k) (hC : IsMetricCurrent C.action)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    {s : Set (Euc k)} (hs : MeasurableSet s) (hss : s ⊆ C.domain) (hs0 : volume s ≠ 0)
    (hθ : ∀ᵐ z ∂volume.restrict s, 1 ≤ |(C.multiplicity z : ℝ)|)
    (p : Seminorm ℝ (Euc k)) (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hnear : ∀ y ∈ s, ∀ z ∈ s,
      (1-ε)*p (y-z) ≤ dist (C.paramExtended y) (C.paramExtended z) ∧
      dist (C.paramExtended y) (C.paramExtended z) ≤ (1+ε)*p (y-z)) :
    ∃ (t : Set (Euc k)) (f : Euc k → X), MeasurableSet t ∧ volume t ≠ 0 ∧ Measurable f ∧
      (∀ y ∈ t, ∀ z ∈ t, dist (f y) (f z) ≤ (1+ε)*dist y z) ∧
      Measure.map f (volume.restrict t) ≤ ENNReal.ofReal ((1-ε)⁻¹^k) • μ := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix p b
  let J := Real.sqrt Q.det
  have hQ : Q.PosDef := polarizationMatrix_posDef b p hp hpara
  have hJ : 0 < J := Real.sqrt_pos.mpr hQ.det_pos
  obtain ⟨e,he,hdet⟩ := exists_hilbert_norm_equiv p hp hpara
  let K : ℝ≥0 := ⟨(1-ε)⁻¹, inv_nonneg.mpr (sub_pos.mpr hε1).le⟩
  let ℓ : Fin k → Euc k →L[ℝ] ℝ := fun i => matrixRowFunctional (CFC.sqrt Q) i
  have hrow : ∀ i y (hy : y ∈ s) z (hz : z ∈ s),
      |ℓ i y-ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hss hy⟩) (C.param ⟨z,hss hz⟩) := by
    intro i y hy z hz
    rw [←map_sub]
    apply (abs_matrixRow_sqrt_le Q hQ.posSemidef i (y-z)).trans
    have hh := (hnear y hy z hz).1
    simp only [paramExtended,dite_eq_left (hss hy),dite_eq_left (hss hz)] at hh
    change Real.sqrt ((WithLp.ofLp (y-z)) ⬝ᵥ Q *ᵥ WithLp.ofLp (y-z)) ≤ _
    rw [show Q = polarizationMatrix p b from rfl,sqrt_polarization_quadratic p hp hpara,WithLp.toLp_ofLp]
    change p (y-z) ≤ (1-ε)⁻¹*_
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    simpa only [mul_comm] using hh
  have hm : (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)) = CFC.sqrt Q := by
    ext i j
    simp only [ℓ,Matrix.of_apply,matrixRowFunctional_single]
  have hdetQ : |(CFC.sqrt Q).det| = J := by
    rw [show (CFC.sqrt Q).det = Real.sqrt Q.det by simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hpiece : densityPush (volume.restrict s) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| * J) ≤ ((K^k) • μ).restrict (C.paramExtended '' s) := by
    simpa only [hm,hdetQ] using C.linear_piece_mass_le hC hμ hs hss ℓ K hrow
  have hconst : ENNReal.ofReal J • Measure.map C.paramExtended (volume.restrict s) ≤ (K^k) • μ := by
    calc
      _ = densityPush (volume.restrict s) C.paramExtended (fun _ => J) := by
        rw [densityPush,withDensity_const,Measure.map_smul _ C.measurable_paramExtended.aemeasurable]
      _ ≤ densityPush (volume.restrict s) C.paramExtended (fun z => |(C.multiplicity z : ℝ)| * J) := by
        apply densityPush_mono_ae C.measurable_paramExtended
        filter_upwards [hθ] with z hz
        exact (le_mul_of_one_le_left hJ.le hz)
      _ ≤ _ := hpiece.trans Measure.restrict_le_self
  refine ⟨e '' s,C.paramExtended ∘ e.symm,
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs,?_,
    C.measurable_paramExtended.comp e.symm.continuous.measurable,?_,?_⟩
  · have hh := Measure.addHaar_image_linearMap volume e.toLinearEquiv.toLinearMap s
    change volume (e '' s) = _ at hh
    rw [hh,hdet]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hJ) hs0
  · rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩
    simp only [Function.comp_apply,e.symm_apply_apply]
    apply ((hnear y hy z hz).2).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith only [hε])
    simp only [dist_eq_norm,←map_sub,he,le_refl]
  · rw [normalized_linear_image_push volume e hs C.measurable_paramExtended,hdet]
    convert hconst using 1
    change (ENNReal.ofReal ((K:ℝ)^k) • μ) = ((K^k) • μ)
    simp only [ENNReal.ofReal_pow K.coe_nonneg,ENNReal.ofReal_coe_nnreal]
    rfl
end IntegerChart

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma exists_almost_euclidean_density (hX : IsCAT0 X) (hM : 0 < mass T)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ o : X, ∀ v : ℝ, 1+ε < v → ∀ d : ℝ, d < Real.pi →
      ∀ᶠ r in 𝓝[>] (0:ℝ), d*(r/v)^2 ≤ (1-ε)⁻¹^2 *
        (MassMeasure.currentMassMeasure hT).real (Metric.ball o r) := by
  obtain ⟨i,s,p,hs,hss,hs0,hθ,hp,hpara,hnear⟩ := q.exists_positive_near_hilbert_piece hX hM hε
  obtain ⟨t,f,ht,ht0,hf,hLip,hdom⟩ := (q.chart i).normalized_piece (q.current i)
    (q.chart_controls_total i) hs hss hs0 hθ p hp hpara hε hε1 hnear
  exact exists_lipschitz_chart_density ht ht0 hf (sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr hε1)))
    (by linarith) hLip hdom
end ChartGeometry
end CAT0Fillings
end

end OAI
