import Mathlib
import OAI.Analysis.AffineBernstein.NewtonBasis

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma projective_area_exponents (k l : ℕ) {c b q : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    Real.rpow (c^k*b) (1/((k:ℝ)+l+2)) *
      Real.rpow (Real.rpow c (-((l:ℝ)+2))*q) (1-1/((k:ℝ)+l+2)) =
        Real.rpow c (-((l:ℝ)+1)) *
          (Real.rpow b (1/((k:ℝ)+l+2))*Real.rpow q (1-1/((k:ℝ)+l+2))) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hc.le _) hb,
    Real.mul_rpow (Real.rpow_nonneg hc.le _) hq,← Real.rpow_natCast c k,
    ← Real.rpow_mul hc.le,← Real.rpow_mul hc.le]
  rw [show (c^((k:ℝ)*(1/((k:ℝ)+l+2)))*b^(1/((k:ℝ)+l+2))) *
      (c^((-((l:ℝ)+2))*(1-1/((k:ℝ)+l+2)))*q^(1-1/((k:ℝ)+l+2))) =
      (c^((k:ℝ)*(1/((k:ℝ)+l+2))) * c^((-((l:ℝ)+2))*(1-1/((k:ℝ)+l+2)))) *
        (b^(1/((k:ℝ)+l+2))*q^(1-1/((k:ℝ)+l+2))) by ring]
  rw [← Real.rpow_add hc]
  congr 2
  have hd : (k:ℝ)+l+2 ≠ 0 := by positivity
  field_simp
  ring

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Exact projective-normal normalization of the affine area density. The
factor is c^(-m), where m is the transverse dimension, including m=1.
This is the density factor needed to pass from flat to spherical charts. -/
lemma homogeneous_projective_area_density {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c) (he : ‖e‖ = 1)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hflat : inner ℝ (c • e) (bE (Sum.inr ())) = 1)
    (hrad : ∀ v : E, fderiv ℝ (fderiv ℝ
      (fun q : S × E => homogeneousSupport (K q.1) q.2)) (s,c • e) (0,v) (0,c • e) = 0)
    (hB : 0 ≤ (tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bS).det)
    (hQ : 0 ≤ tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bE) :
    let H := fun q : S × E => homogeneousSupport (K q.1) q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ =
      Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
        (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
          Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) := by
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have hn : inner ℝ (c • e) (c • e) = c^2 := by
    rw [real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,he]
    ring
  have hq := tubeAngularDensity_flat hHc bE hflat hrad
  rw [homogeneous_tubeAngularDensity_scale hD hs hK hne hc hH hHc,hn] at hq
  change (c⁻¹)^Fintype.card κ * tubeAngularDensity H (s,e) bE =
    (tubeRadiusMatrix H (s,c • e) bE).det * c^2 at hq
  have hr : (tubeRadiusMatrix H (s,c • e) bE).det =
      Real.rpow c (-((Fintype.card κ:ℝ)+2)) * tubeAngularDensity H (s,e) bE := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hc.le,Real.rpow_add hc,Real.rpow_natCast,Real.rpow_two]
    rw [inv_pow] at hq
    apply (mul_left_injective₀ (show c^Fintype.card κ*c^2 ≠ 0 by positivity))
    field_simp [hc.ne'] at hq ⊢
    nlinarith [hq]
  change tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) _ = _
  rw [tubeAreaDensity,homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.det_smul,hr]
  exact projective_area_exponents _ _ hc hB hQ

end AffineBernstein
end

end OAI
