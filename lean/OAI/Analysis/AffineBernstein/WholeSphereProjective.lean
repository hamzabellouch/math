import Mathlib
import OAI.Analysis.AffineBernstein.ActualProjectiveInverse
import OAI.Analysis.AffineBernstein.ProjectiveNormalized
import OAI.Analysis.AffineBernstein.ProductEquator

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

section WholeSphereProjective
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/- Exact two-chart projective integration on the actual sphere. -/
theorem sphere_two_projective_lintegral (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ e : Metric.sphere (0:E) 1, g e ∂volume.toSphere) =
    (∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (f (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ))))) +
    (∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
      (Module.finrank ℝ F+1)) *
      g (-f (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ))))) := by
  rw [← (linearIsometrySphere_measurePreserving f).lintegral_comp_emb
    (linearIsometrySphereHomeomorph f).measurableEmbedding]
  simp only [linearIsometrySphereHomeomorph_coe]
  rw [product_sphere_lintegral_split (fun e => g (f e)) (hg.comp f.continuous.measurable),
    product_sphere_negative_lintegral (fun e => g (f e)),
    projective_hemisphere_normalized_lintegral (fun e => g (f e)) (hg.comp f.continuous.measurable),
    projective_hemisphere_normalized_lintegral (fun e => g (f (-e))) (by fun_prop)]
  simp only [map_neg]

end WholeSphereProjective

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- A true affine inverse-energy density in any isometric projective chart;
the spherical angular basis can be chosen independently of the planar one. -/
theorem affineEpigraph_projective_isometry_inverseArea_density {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) (bS : Module.Basis ι ℝ S)
    (bE bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E)
    (hlast : bE (Sum.inr ()) = f (WithLp.toLp 2 (0,(1:ℝ)))) (v : ι → ℝ) (x : F) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    let p := f (WithLp.toLp 2 (x,(1:ℝ)))
    let e := f (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ • WithLp.toLp 2 (x,(1:ℝ)))
    ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,p) bS) (tubeRadiusMatrix H (s,p) bE) δ *
      (‖supportConormal H (s,p)‖ * inverseMatrixPair (tubeBaseMatrix H (s,p) bS) v v)) =
      ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^ (Module.finrank ℝ F+1)) *
      ENNReal.ofReal ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ)) *
        (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v v)) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
  let p₀ := WithLp.toLp 2 (x,(1:ℝ))
  let c := ‖p₀‖
  let p := f p₀
  let e := f (c⁻¹ • p₀)
  have hc : 0 < c := projective_norm_pos x
  have he : ‖e‖ = 1 := by
    simp only [e,f.norm_map,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    exact inv_mul_cancel₀ hc.ne'
  have hce : c • e = p := by simp [e,p,map_smul,smul_smul,hc.ne']
  have hf : inner ℝ (c • e) (bE (Sum.inr ())) = 1 := by
    rw [hce,hlast]
    change inner ℝ (f p₀) (f (WithLp.toLp 2 (0,(1:ℝ)))) = 1
    rw [f.inner_map_map]
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
  rw [hce, tubeAngularDensity_basis_independent H (s,e) bRef bE] at hh
  have hcard : Fintype.card κ = Module.finrank ℝ F := by
    have hc := (Module.finrank_eq_card_basis bE.toBasis).symm
    have hd : Module.finrank ℝ E = Module.finrank ℝ F + 1 := by
      rw [← f.toLinearEquiv.finrank_eq,(WithLp.linearEquiv 2 ℝ (F × ℝ)).finrank_eq,
        Module.finrank_prod,Module.finrank_self]
    simp only [Fintype.card_sum,Fintype.card_unit] at hc
    change Fintype.card κ + 1 = Module.finrank ℝ E at hc
    omega
  have hexp : Real.rpow c (-((Fintype.card κ:ℝ)+1)) = c⁻¹^(Module.finrank ℝ F+1) := by
    simp only [Real.rpow_eq_pow]
    rw [show -((Fintype.card κ:ℝ)+1) = -((Fintype.card κ+1:ℕ):ℝ) by norm_num,
      Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow,hcard]
  dsimp only
  change ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,p) bS)
    (tubeRadiusMatrix H (s,p) bE) δ * _) = _
  rw [hh,hexp,ENNReal.ofReal_mul (by positivity)]

end AffineBernstein
end

end OAI
