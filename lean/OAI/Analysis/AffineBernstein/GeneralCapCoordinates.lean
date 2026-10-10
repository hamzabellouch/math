import Mathlib
import OAI.Analysis.AffineBernstein.CapCovariance
import OAI.Analysis.AffineBernstein.SupportCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GeneralCapCoordinates

/- A fixed genuine invertible coordinate map with the prescribed height
functional. The product max norm is retained; no artificial inner-product
instance is introduced on these coordinates. -/
lemma exists_height_coordinates {n : ℕ}
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hne : ell ≠ 0) :
    ∃ A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ), ∀ z, (A z).2 = ell z := by
  obtain ⟨w,hw⟩ := real_functional_surjective ell hne 1
  let T := splitFunctionalEquiv ell w hw
  have hd := T.toLinearEquiv.finrank_eq
  have hk : Module.finrank ℝ ell.ker = Module.finrank ℝ (Space n) := by
    change Module.finrank ℝ (Space n × ℝ) = Module.finrank ℝ (ℝ × ell.ker) at hd
    simp only [Module.finrank_prod,Module.finrank_self] at hd
    omega
  let Q : ell.ker ≃L[ℝ] Space n := (LinearEquiv.ofFinrankEq ell.ker (Space n) hk).toContinuousLinearEquiv
  let A := (T.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr Q)).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ (Space n))
  exact ⟨A,fun _ => rfl⟩

/- The affine-area cap for an arbitrary linear height, in the original
literal graph chart. -/
def affineImageLinearCapArea {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (b : ℝ) : ℝ :=
  Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
    ∫ x in {x | x ∈ Ω ∧ ell (L (x,u x)+v) < b}, affineAreaDensity u x

lemma affineImageCapArea_height_coordinates {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hA : ∀ z, (A z).2 = ell z) (b : ℝ) :
    affineImageCapArea Ω u (L.trans A) (A v) b =
      Real.rpow |A.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        affineImageLinearCapArea Ω u L v ell b := by
  have hd : (L.trans A).toContinuousLinearMap.det =
      A.toContinuousLinearMap.det*L.toContinuousLinearMap.det := by
    change LinearMap.det (A.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap) = _
    rw [LinearMap.det_comp]
    rfl
  have hz (x : Space n) : ((L.trans A) (x,u x)+A v).2 = ell (L (x,u x)+v) := by
    rw [ContinuousLinearEquiv.trans_apply,← map_add,hA]
  simp only [affineImageCapArea,affineImageLinearCapArea,hd,hz,abs_mul, Real.rpow_eq_pow]
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _),mul_assoc]

lemma image_height_cap {n : ℕ} (A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hA : ∀ z, (A z).2 = ell z)
    (C : Set (Space n × ℝ)) (b : ℝ) :
    (A '' C) ∩ {z | z.2 ≤ b} = A '' (C ∩ {z | ell z ≤ b}) := by
  ext z
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hb⟩
    exact ⟨y,⟨hy,by change (A y).2 ≤ b at hb; change ell y ≤ b; rwa [hA] at hb⟩,rfl⟩
  · rintro ⟨y,⟨hy,hb⟩,rfl⟩
    exact ⟨mem_image_of_mem A hy,by change (A y).2 ≤ b; rw [hA]; exact hb⟩

end GeneralCapCoordinates

open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- For distance functions, pointwise convergence is automatically locally
uniform, by the common unit Lipschitz constant and a finite compact cover. -/
/- Fixed changes of coordinates preserve local set convergence. A proper
homeomorphism suffices: compact preimages supply the lower distance bound and
actual approximating points supply the upper bound. In particular this applies
to every fixed invertible affine change of coordinates. -/

end AffineBernstein
end

end OAI
