import OAI.Analysis.LienardCycles.Characteristic

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates ArchSymmetries

lemma base_translation (z k t : ℝ) {r : ℝ} (hr : 0 < r) :
    baseAtWidth profile (((z,k),t),r) = t+baseAtWidth profile (((z+k*t,k),0),r) := by
  have hh := base_affine profile profile_contDiff model_local_flow
    (p := (z+k*t,k)) (q := (z,k)) (t := 0) (H := t)
    (C := z*t+k/2*t^2) hr (show 0 < (1:ℝ) by norm_num)
    (by intro x; dsimp [profile]; ring)
  simpa using hh

lemma J_reparam {z k r : ℝ} (hr : 0 < r) (hk : k ≠ 0) :
    J ((z,k),r)=k*baseAtWidth profile (((0,k),z/k),r) := by
  have hh := base_translation 0 k (z/k) hr
  simp only [zero_add,mul_div_cancel₀ _ hk] at hh
  rw [hh]
  dsimp [J,base]
  field_simp

lemma Jz_pos {z k r : ℝ} (hr : 0 < r) : 0 < Jz ((z,k),r) := by
  by_cases hk : k = 0
  · subst k
    have he : (fun s => J ((s,0),r))=id := by ext s; simp [J]
    have hh := (Jz_hasDerivAt (z := z) (k := 0) hr).unique (he ▸ hasDerivAt_id z)
    rw [hh]; norm_num
  · have hb : DifferentiableAt ℝ (fun t => baseAtWidth profile (((0,k),t),r)) (z/k) :=
      ((WidthCoordinates.base_analytic profile profile_contDiff model_local_flow hr).comp (z/k)
        ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
    have hc := (hb.hasDerivAt.comp z ((hasDerivAt_id z).div_const k)).const_mul k
    have he : (fun s => J ((s,k),r))=(fun s => k*baseAtWidth profile (((0,k),s/k),r)) :=
      funext (fun s => J_reparam hr hk)
    have hh := (Jz_hasDerivAt (z := z) (k := k) hr).unique (he ▸ hc)
    have hp := base_peak_deriv_pos profile profile_contDiff model_local_flow
      (p := (0,k)) (t := z/k) hr
    rw [hh]
    convert hp using 1
    field_simp

lemma Az_formula {z k r : ℝ} (hr : 0 < r) :
    Az ((z,k),r) = P ((J ((z,k),r),k),r)*Jz ((z,k),r)/r := by
  have hc := ((P_hasDerivAt (d := J ((z,k),r)) (k := k) hr).comp z
    (Jz_hasDerivAt (z := z) (k := k) hr)).div_const r
  exact (Az_hasDerivAt hr).unique hc

lemma Ak_formula {z k r : ℝ} (hr : 0 < r) :
    Ak ((z,k),r) = (P ((J ((z,k),r),k),r)*Jk ((z,k),r)+Q ((J ((z,k),r),k),r))/r := by
  have hc := ((H_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    (f := fun s => ((J ((z,s),r),s),r)) k
    (((Jk_hasDerivAt (z := z) (k := k) hr).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have hh := (Ak_hasDerivAt (z := z) (k := k) hr).unique (hc.div_const r)
  rw [fderiv_model] at hh
  simpa [P,Q,mul_comm] using hh

lemma Dz_formula {z k r : ℝ} (hr : 0 < r) :
    Dz ((z,k),r) = R ((J ((z,k),r),k),r)*Jz ((z,k),r) := by
  have hc := (Hr_d_hasDerivAt (d := J ((z,k),r)) (k := k) hr).comp z
    (Jz_hasDerivAt (z := z) (k := k) hr)
  exact (Dz_hasDerivAt hr).unique hc

lemma Dk_formula {z k r : ℝ} (hr : 0 < r) :
    Dk ((z,k),r) = R ((J ((z,k),r),k),r)*Jk ((z,k),r)+S ((J ((z,k),r),k),r) := by
  have hc := ((Hr_analytic (d := J ((z,k),r)) (k := k) hr).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    (f := fun s => ((J ((z,s),r),s),r)) k
    (((Jk_hasDerivAt (z := z) (k := k) hr).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have hh := (Dk_hasDerivAt (z := z) (k := k) hr).unique hc
  rw [fderiv_model] at hh
  have hR : direction ((1,0),0) Hr ((J ((z,k),r),k),r)=R ((J ((z,k),r),k),r) :=
    direction_comm (H_analytic hr) _ _
  have hS : direction ((0,1),0) Hr ((J ((z,k),r),k),r)=S ((J ((z,k),r),k),r) :=
    direction_comm (H_analytic hr) _ _
  simpa [hR,hS,mul_comm] using hh

lemma Az_pos {z k r : ℝ} (hr : 0 < r) : 0 < Az ((z,k),r) := by
  rw [Az_formula hr]
  exact div_pos (mul_pos (QuadraticVariation.P_pos hr) (Jz_pos hr)) hr

end QuinticLienard.ReferenceCharacteristic

end OAI
