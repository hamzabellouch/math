import OAI.MathematicalPhysics.Transonic.Phase.PhysicalFlux

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff

lemma GlobalProfile.w0_pos (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) : 0<P.w0 t X :=
  Real.rpow_pos_of_pos (P.s0_timelike ht X) _

lemma GlobalProfile.w0_formula (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    P.w0 t X=t^(-P.beta/3)*P.M0 (radius X/t)^((1:ℝ)/6) := by
  rw [GlobalProfile.w0,P.s0_minkowskiSquare ht X,
    Real.mul_rpow (sq_nonneg _) (P.M0_pos _).le]
  have he : ((t^(-P.beta))^2)^((1:ℝ)/6)=t^(-P.beta/3) := by
    rw [← Real.rpow_two (t^(-P.beta)),← Real.rpow_mul ht.le,← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [he]

lemma GlobalProfile.radialA_pos (P : GlobalProfile) {z : ℝ} (hz : 0≤z) :
    0<P.radialA z := by
  rw [← Real.sq_sqrt hz,P.radialA_sq]
  exact P.A_pos _

lemma GlobalProfile.radial_positive_powers_smooth (P : GlobalProfile) (c : ℝ) :
    ContDiffOn ℝ ∞ (fun z => P.radialH z^c) (Ici 0) ∧
    ContDiffOn ℝ ∞ (fun z => P.radialA z^c) (Ici 0) ∧
    ContDiffOn ℝ ∞ (fun z => P.radialM z^c) (Ici 0) := by
  have hH (z : ℝ) (hz : z∈Ici (0:ℝ)) : 0<P.radialH z := by
    rw [← Real.sq_sqrt hz,← P.H_radial]
    exact P.H_pos _
  exact ⟨P.radialH_smooth.rpow_const_of_ne (fun z hz => ne_of_gt (hH z hz)),
    P.radialA_smooth.rpow_const_of_ne (fun z hz => ne_of_gt (P.radialA_pos hz)),
    P.radialM_smooth.rpow_const_of_ne (fun z hz => ne_of_gt (P.radialM_pos hz))⟩

lemma GlobalProfile.w0_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ (fun z : ℝ×PhysicalSpace => P.w0 z.1 z.2) {z | 0<z.1} := by
  have hr : ContDiff ℝ ∞ (fun z : ℝ×PhysicalSpace => radiusSq z.2) :=
    radiusSq_smooth.comp contDiff_snd
  have harg : ContDiffOn ℝ ∞ (fun z : ℝ×PhysicalSpace => radiusSq z.2/z.1^2) {z | 0<z.1} :=
    hr.contDiffOn.div (contDiff_fst.pow 2).contDiffOn (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hM := (P.radial_positive_powers_smooth ((1:ℝ)/6)).2.2.comp harg
    (fun z _ => div_nonneg (radiusSq_nonneg z.2) (sq_nonneg z.1))
  have hp : ContDiffOn ℝ ∞ (fun z : ℝ×PhysicalSpace => z.1^(-P.beta/3)) {z | 0<z.1} :=
    contDiff_fst.contDiffOn.rpow_const_of_ne (fun z hz => ne_of_gt hz)
  apply (hp.mul hM).congr
  intro z hz
  rw [P.w0_formula hz,← P.radialM_sq,div_pow,radius_sq]
  rfl

end SepticProfile

end
end

end OAI
