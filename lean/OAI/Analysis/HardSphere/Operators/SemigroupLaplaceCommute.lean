import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledEigenvector

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Nontrivial F]
local instance : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _
local instance : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F

omit [Nontrivial F] in
lemma semigroupLaplace_commute (K : ℝ → F→L[ℂ] F)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : F) {t : ℝ} (ht : 0 ≤ t) :
    K t (semigroupLaplace K f)=semigroupLaplace K (K t f) := by
  rw [semigroupLaplace,← (K t).integral_comp_comm (laplaceIntegrand_integrable K hc hnorm f 0)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only [laplaceIntegrand]
  have hs0 : 0 ≤ s := le_of_lt hs
  rw [max_eq_right hs0,(K t).map_smul_of_tower]
  congr 1
  have he : (K t).comp (K s)=(K s).comp (K t) := by
    rw [← hadd t s ht hs0,← hadd s t hs0 ht,add_comm]
  exact congrArg (fun T : F→L[ℂ] F ↦ T f) he

lemma semigroup_eq_regularHeat_range_square (K : ℝ → F→L[ℂ] F)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (R : F→L[ℂ] F) (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (hR : ∀ f, semigroupLaplace K f=R f) (f : F) {t : ℝ} (ht : 0 ≤ t) :
    K t (R (R f))=regularHeat R t (R (R f)) := by
  have hcomm (s : ℝ) (hs : 0 ≤ s) (g : F) : K s (R g)=R (K s g) := by
    simpa only [hR] using semigroupLaplace_commute K hadd hc hnorm g hs
  let w : ℝ → F := fun s ↦ K s (R (R f))-regularHeat R s (R (R f))
  let v : ℝ → F := fun s ↦ K s (R f)-regularHeat R s (R f)
  have hwR (s : ℝ) (hs : 0 ≤ s) : w s=R (v s) := by
    dsimp only [w,v]
    rw [map_sub,← hcomm s hs]
    have he := (regularHeat_commute R s).eq
    have he' := congrArg (fun T : F→L[ℂ] F ↦ T (R f)) he
    change regularHeat R s (R (R f))=R (regularHeat R s (R f)) at he'
    rw [he']
  have hw0 : w 0=0 := by
    have hz := semigroupLaplace_project K hadd hc hnorm (R f)
    rw [hR] at hz
    simp only [w,hz,regularHeat_zero,one_apply_eq_self,sub_self]
  have hcw : ContinuousOn w (Ici 0) := by
    have hk : ContinuousOn (fun s : ℝ ↦ K s (R (R f))) (Ici 0) :=
      (hc (R (R f))).continuousOn.congr (fun s hs ↦ by
        change K s (R (R f))=K (max 0 s) (R (R f))
        rw [max_eq_right (show 0 ≤ s from hs)])
    exact hk.sub (regularHeat_range_continuousOn hRp hRn (R f))
  have hdw (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt w (w s-v s) (Ici s) s := by
    have hk := (semigroupLaplace_hasDerivWithinAt K hadd hc hnorm (R f) hs).mono
      (Ici_subset_Ici.mpr hs)
    simp only [hR] at hk
    have hh := hk.sub (regularHeat_range_hasDerivWithinAt hRp hRn f hs)
    convert hh using 1
    dsimp only [w,v]
    rw [map_sub]
    abel
  let z : ℝ → F := fun s ↦ Real.exp (-s) • w s
  have hcz : ContinuousOn z (Ici 0) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.smul hcw
  have hdz (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt z (-Real.exp (-s) • v s) (Ici s) s := by
    have hh := (((hasDerivAt_id s).neg.exp).hasDerivWithinAt).smul (hdw s hs)
    simp only [Pi.neg_apply,id_eq] at hh
    convert hh using 1
    module
  have hnonpos (s : ℝ) (hs : 0 ≤ s) : inner ℝ (z s) (-Real.exp (-s) • v s)≤0 := by
    have he : z s=R (Real.exp (-s) • v s) := by
      dsimp only [z]
      rw [hwR s hs,map_smul_of_tower]
    rw [he,neg_smul,inner_neg_right]
    apply neg_nonpos.mpr
    exact hRp.re_inner_nonneg_left (Real.exp (-s) • v s)
  have hbound := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s : ℝ ↦ ‖z s‖^2) (f' := fun s ↦ 2*inner ℝ (z s) (-Real.exp (-s) • v s))
    (B := fun _ ↦ (0:ℝ)) (B' := fun _ ↦ (0:ℝ))
    ((continuous_norm.comp_continuousOn hcz).pow 2 |>.mono (Icc_subset_Ici_self : Icc (0:ℝ) t ⊆ Ici 0))
    (fun s hs ↦ (hdz s hs.1).norm_sq)
    (by simp [z,hw0]) continuousOn_const (fun s _ ↦ hasDerivWithinAt_const s _ _)
    (fun s hs ↦ mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hnonpos s hs.1))
    (x := t) ⟨ht,le_refl _⟩
  have hz : z t=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (z t)])
  have hw : w t=0 := by
    change Real.exp (-t) • w t=0 at hz
    exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt (Real.exp_pos _))
  exact sub_eq_zero.mp hw

omit [Nontrivial F] in
lemma semigroupLaplace_kernel (K : ℝ → F→L[ℂ] F)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖) (f : F)
    (he : semigroupLaplace K f=0) {t : ℝ} (ht : 0 ≤ t) : K t f=0 := by
  have hh := semigroupLaplace_difference_tendsto K hadd hc hnorm f
  simp only [he,map_zero,sub_self,smul_zero,sub_zero] at hh
  have hz : K 0 f=0 := (tendsto_nhds_unique tendsto_const_nhds hh).symm
  have hp := congrArg (fun T : F→L[ℂ] F ↦ T f) (hadd t 0 ht (le_refl 0))
  simpa only [add_zero,comp_apply,hz,map_zero] using hp

lemma semigroup_eq_heat (K : ℝ → F→L[ℂ] F)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → K (s+t)=(K s).comp (K t))
    (hc : ∀ f, Continuous (fun t : ℝ ↦ K (max 0 t) f))
    (hnorm : ∀ t, 0 ≤ t → ∀ f, ‖K t f‖≤‖f‖)
    (hKs : ∀ t, IsSelfAdjoint (K t))
    (R : F→L[ℂ] F) (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    (hR : ∀ f, semigroupLaplace K f=R f) {t : ℝ} (ht : 0<t) :
    K t=cfc (p := IsSelfAdjoint) (heatScalar t) R := by
  let H := cfc (p := IsSelfAdjoint) (heatScalar t) R
  let D := K t-H
  have hDs : ∀ f g, inner ℂ (D f) g=inner ℂ f (D g) :=
    isSelfAdjoint_iff_isSymmetric.mp ((hKs t).sub (show IsSelfAdjoint H from IsSelfAdjoint.cfc))
  have hDRR (f : F) : D (R (R f))=0 := by
    change K t (R (R f))-H (R (R f))=0
    apply sub_eq_zero.mpr
    simpa only [regularHeat_pos R ht] using semigroup_eq_regularHeat_range_square K hadd hc hnorm R hRp hRn hR f ht.le
  have hker (f : F) (hf : R f=0) : D f=0 := by
    have hK : K t f=0 := semigroupLaplace_kernel K hadd hc hnorm f ((hR f).trans hf) ht.le
    have hH : H f=0 := by
      dsimp only [H]
      rw [cfc_eigen_apply R hRp.isSelfAdjoint (heatScalar t) (heatScalar_smooth t).continuous
        0 ((heatScalar_smooth t).differentiable (by norm_num)).differentiableAt f (by simpa using hf),
        heatScalar_zero,zero_smul]
    simp only [D,sub_apply,hK,hH,sub_self]
  ext f
  suffices hDf : D f=0 by exact sub_eq_zero.mp hDf
  have hRD : R (D f)=0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      inner ℂ (R (D f)) (R (D f))=inner ℂ (D f) (R (R (D f))) := hRp.inner_left_eq_inner_right _ _
      _ = inner ℂ f (D (R (R (D f)))) := hDs _ _
      _ = 0 := by rw [hDRR,inner_zero_right]
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [hDs,hker (D f) hRD,inner_zero_right]

end
end HardSphere

end
end
end
end
end
end

end OAI
