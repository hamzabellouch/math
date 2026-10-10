import Mathlib
import OAI.Analysis.AffineBernstein.ActualProjectiveInverse
import OAI.Analysis.AffineBernstein.ProjectiveNormalized

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open intervalIntegral

section ActualHemisphereInverse
open Filter
open scoped Topology
variable {S F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Exact hemisphere/flat-chart transport of the actual affine inverse metric
area, with the true Haar sphere measure and the true support conormal. No
surface-Jacobian, curvature, or inverse-metric law is assumed. -/
theorem affineEpigraph_hemisphere_inverseArea_lintegral {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × WithLp 2 (F × ℝ)) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : WithLp 2 (F × ℝ)) ∈
      interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ (WithLp 2 (F × ℝ)))
    (hlast : bE (Sum.inr ()) = WithLp.toLp 2 (0,(1:ℝ))) (v : ι → ℝ) :
    let H := fun q : S × WithLp 2 (F × ℝ) =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    (∫⁻ e : Metric.sphere (0:WithLp 2 (F × ℝ)) 1,
      if 0 < (WithLp.ofLp (e:WithLp 2 (F × ℝ))).2 then
        ENNReal.ofReal ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
          Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) *
          (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v v))
      else 0 ∂volume.toSphere) =
      ∫⁻ x : F, ENNReal.ofReal (tubeAreaDensity
        (tubeBaseMatrix H (s,WithLp.toLp 2 (x,(1:ℝ))) bS)
        (tubeRadiusMatrix H (s,WithLp.toLp 2 (x,(1:ℝ))) bE) δ *
        (‖supportConormal H (s,WithLp.toLp 2 (x,(1:ℝ)))‖ *
          inverseMatrixPair (tubeBaseMatrix H (s,WithLp.toLp 2 (x,(1:ℝ))) bS) v v)) := by
  let E := WithLp 2 (F × ℝ)
  let H := fun q : S × E =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let g : E → ℝ≥0∞ := fun e => ENNReal.ofReal
    ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
      Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) *
      (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v v))
  have hg : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    apply measurable_of_continuousOn_compl_singleton (0:E)
    intro e he
    have he0 : e ≠ 0 := by simpa using he
    have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he0).1
    have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he0 bS bE
    exact ((continuousAt_sphericalInverseArea hj bS bE δ hpos.1.det_pos hpos.2.1 v v).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hcard : Fintype.card κ = Module.finrank ℝ F := by
    have hc := (Module.finrank_eq_card_basis bE.toBasis).symm
    have hd : Module.finrank ℝ E = Module.finrank ℝ F + 1 := by
      change Module.finrank ℝ (WithLp 2 (F × ℝ)) = _
      rw [(WithLp.linearEquiv 2 ℝ (F × ℝ)).finrank_eq,Module.finrank_prod,Module.finrank_self]
    simp only [Fintype.card_sum,Fintype.card_unit] at hc
    change Fintype.card κ + 1 = Module.finrank ℝ E at hc
    omega
  change (∫⁻ e : Metric.sphere (0:E) 1,
    if 0 < (WithLp.ofLp (e:E)).2 then g e else 0 ∂volume.toSphere) = _
  rw [projective_hemisphere_normalized_lintegral g hg]
  apply lintegral_congr
  intro x
  let p : E := WithLp.toLp 2 (x,(1:ℝ))
  let c : ℝ := ‖p‖
  let e : E := c⁻¹ • p
  have hc : 0 < c := projective_norm_pos x
  have he : ‖e‖ = 1 := by
    simp only [e,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    exact inv_mul_cancel₀ hc.ne'
  have hce : c • e = p := by simp [e,smul_smul,hc.ne']
  have hf : inner ℝ (c • e) (bE (Sum.inr ())) = 1 := by
    rw [hce,hlast]
    change inner ℝ x (0:F) + inner ℝ (1:ℝ) 1 = 1
    simp
  have hh := affineEpigraph_projective_inverseArea_density hΩ hcv hu hp a L hD hK hzero
    hs he bS bE hc hf v v
  change tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ *
    (‖supportConormal H (s,c • e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,c • e) bS) v v) =
    Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
      ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) *
        (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v v)) at hh
  rw [hce] at hh
  have hexp : Real.rpow c (-((Fintype.card κ:ℝ)+1)) = c⁻¹^(Module.finrank ℝ F+1) := by
    simp only [Real.rpow_eq_pow]
    rw [show -((Fintype.card κ:ℝ)+1) = -((Fintype.card κ+1:ℕ):ℝ) by norm_num,
      Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow,hcard]
  change ENNReal.ofReal (c⁻¹^(Module.finrank ℝ F+1)) * g e = _
  rw [hh,hexp,ENNReal.ofReal_mul (by positivity)]

end ActualHemisphereInverse

open scoped Pointwise

end AffineBernstein

end

end OAI
