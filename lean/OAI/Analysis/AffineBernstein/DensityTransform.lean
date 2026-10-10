import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeWeights
import OAI.Analysis.AffineBernstein.TubeLinearTransform

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter
open scoped Topology

section DensityTransform
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeMeasureCoefficient_congruence (n : ℕ) (h B Q d e t : ℝ) (ht : 0 < t) :
    tubeMeasureCoefficient n h (d^2*B) (e^2/t^2*Q) =
      (|d| *|e|/t)*tubeMeasureCoefficient n h B Q := by
  unfold tubeMeasureCoefficient
  have heq : d^2*B*(e^2/t^2*Q) = (d*e/t)^2*(B*Q) := by ring
  rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_div,abs_mul,abs_of_pos ht]
  ring

omit [CompleteSpace E] in
lemma tubeMeasureDensity_linear_comp {n : ℕ} (B : S →L[ℝ] S) (A : E ≃L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (bS : Module.Basis ι ℝ S) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (he : ‖q.2‖ = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) (B q.1,A q.2) (0,v) (0,A q.2) = 0) :
    tubeMeasureDensity n (fun z => H (B z.1,A z.2)) bS b q =
      (|B.toLinearMap.det| *|A.toLinearMap.det|/‖A q.2‖)*
        tubeMeasureDensity n H bS b (B q.1,A q.2) := by
  have he0 : q.2 ≠ 0 := by intro hz; simp [hz] at he
  have ha0 : 0 < ‖A q.2‖ := norm_pos_iff.mpr (fun hz => he0 (A.injective (by simpa using hz)))
  have hb : (tubeBaseMatrix (fun z => H (B z.1,A z.2)) q bS).det =
      B.toLinearMap.det^2*(tubeBaseMatrix H (B q.1,A q.2) bS).det := by
    have hm : tubeBaseMatrix (fun z => H (B z.1,A z.2)) q bS =
      (LinearMap.toMatrix bS bS B.toLinearMap)ᵀ*tubeBaseMatrix H (B q.1,A q.2) bS*
        LinearMap.toMatrix bS bS B.toLinearMap :=
      tubeBaseMatrix_linear_comp B A.toContinuousLinearMap hH bS
    rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,LinearMap.det_toMatrix]
    ring
  unfold tubeMeasureDensity
  rw [hb,tubeAngularDensity_linear_comp B A hH b he hr]
  exact tubeMeasureCoefficient_congruence _ _ _ _ _ _ _ ha0

lemma tubeMeasureCoefficient_homogeneous {k m : ℕ} {h B Q c : ℝ}
    (hh : 0 < h) (_hB : 0 < B) (_hQ : 0 < Q) (hc : 0 < c) :
    tubeMeasureCoefficient (k+m) (c*h) (c^k*B) ((c⁻¹)^m*Q) =
      (c⁻¹)^m*tubeMeasureCoefficient (k+m) h B Q := by
  unfold tubeMeasureCoefficient
  rw [Real.mul_rpow hc.le hh.le]
  have hprod : c^k*B*((c⁻¹)^m*Q) = (c^k*(c⁻¹)^m)*(B*Q) := by ring
  rw [hprod,← Real.rpow_natCast c k,← Real.rpow_natCast c⁻¹ m,
    Real.inv_rpow hc.le,← Real.rpow_neg hc.le,
    ← Real.rpow_add hc,Real.sqrt_mul (Real.rpow_nonneg hc.le _),Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hc.le]
  have he : -(↑(k+m):ℝ)/2+((k:ℝ)-(m:ℝ))*(1/2) = -(m:ℝ) := by push_cast; ring_nf
  have hp : c^(-(↑(k+m):ℝ)/2)*c^(((k:ℝ)-(m:ℝ))*(1/2)) = (c⁻¹)^m := by
    rw [← Real.rpow_add hc,he,Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow]
  calc
    _ = (c^(-(↑(k+m):ℝ)/2)*c^(((k:ℝ)-(m:ℝ))*(1/2)))*
        (h^(-(↑(k+m):ℝ)/2)*Real.sqrt (B*Q)) := by ring_nf
    _ = _ := by rw [hp,Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow]

lemma homogeneous_tubeMeasureDensity_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (bS : Module.Basis ι ℝ S) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hh : 0 < homogeneousSupport (K s) e)
    (hB : 0 < (tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bS).det)
    (hQ : 0 < tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b) :
    tubeMeasureDensity (Fintype.card ι+Fintype.card κ)
      (fun q : S × E => homogeneousSupport (K q.1) q.2) bS b (s,c • e) =
    (c⁻¹)^Fintype.card κ*tubeMeasureDensity (Fintype.card ι+Fintype.card κ)
      (fun q : S × E => homogeneousSupport (K q.1) q.2) bS b (s,e) := by
  unfold tubeMeasureDensity
  dsimp only
  rw [homogeneousSupport_smul (hK s hs) (hne s hs) e hc,
    homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.det_smul,homogeneous_tubeAngularDensity_scale hD hs hK hne hc hH hHc]
  exact tubeMeasureCoefficient_homogeneous hh hB hQ hc
end DensityTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Exact coordinate formula for the true inverse-block logarithmic norm. -/

end AffineBernstein
end

end OAI
