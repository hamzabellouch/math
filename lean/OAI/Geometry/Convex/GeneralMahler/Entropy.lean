import OAI.Geometry.Convex.GeneralMahler.GainFinal
import OAI.Geometry.Convex.GeneralMahler.EntScalar

namespace OAI
/-! Entropy bound (10), in normalized trace notation. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ} [NeZero m]

def etL (B:Mat m) : Mat m →L[ℝ]ℝ :=
  trL.comp (ContinuousLinearMap.mul ℝ (Mat m) B)
omit [NeZero m] in
lemma etL_apply (B A:Mat m) : etL B A=trN (B*A) := by simp [etL]

omit [NeZero m] in
lemma int_etw (B:Mat m) {A:Rn m→Mat m} (h:Integrable A (normal m)) :
    Integrable (fun x=>trN (B*A x)) (normal m) := by
  simp_rw [← etL_apply]
  exact (etL B).integrable_comp h

omit [NeZero m] in
lemma etw_add {A:Rn m→Mat m} (h:Integrable A (normal m)) (B C:Mat m) :
    etw (B+C) A=etw B A + etw C A := by
  unfold etw et; simp_rw [add_mul,trN_add]
  exact integral_add (int_etw _ h) (int_etw _ h)

namespace ProjField
variable (q:ProjField m)
lemma h_weighted {f:ℝ→ℝ} (hf:TestF f) :
    etw q.covMat (q.Hmat f) = ∫ x,q.dm x*f x := by
  let l := etL q.covMat
  have hp := hf.der.poly
  have hm := q.H_mixed hp
  have hi := mixed_integrable (ν:=normal m) (μ:=volume) hm q.H_sm.aestronglyMeasurable
  have he (x:Rn m) : trN (q.covMat*q.Hmat f x) = ∫ z,l (q.kerH f z x) := by
    rw [← etL_apply,l.integral_comp_comm (q.H_left_int hp _)]
    rfl
  have hy (z:ℝ) : (∫ x,l (q.kerH f z x) ∂normal m)=- (q.hDel z*deriv f z) := by
    let P := q.Pmat z
    have iP : Integrable P (normal m) := meanJac_integrable ..
    have ie : (∫ x,P x ∂normal m)=meanJac q.C q.root (q.shift z) := rfl
    have hP : Integrable (fun x=> p z • (1:Mat m)- P x) (normal m) :=
      (integrable_const _).sub iP
    rw [l.integral_comp_comm (show Integrable (q.kerH f z) (normal m) from hP.smul (deriv f z))]
    change l (∫ x,deriv f z • (p z • (1:Mat m)-P x) ∂normal m)=_
    rw [integral_smul,integral_sub (integrable_const _) iP,ie]
    simp only [integral_const, probReal_univ, one_smul,_root_.map_smul,smul_eq_mul,
      _root_.map_sub,l, etL_apply,mul_one,hDel,avH,s0]
    ring
  rw [q.hd_test hf]; unfold etw et; simp_rw [he]
  rw [integral_integral_swap]
  · simp_rw [hy]; rw [integral_neg]
  have hh : Integrable (fun u:ℝ×Rn m=>l (q.kerH f u.1 u.2)) (volume.prod (normal m)) :=
    l.integrable_comp hi
  exact hh.swap

omit [NeZero m] in
lemma logD_cov : logD q.covMat=2*logD q.S := by
  unfold covMat logD
  rw [det_mul,Real.log_mul q.pos.det_pos.ne' q.pos.det_pos.ne']
  ring

/-- entropy bound Eq10. Replacing τ log by logD is a notation choice;
see trN_logD_eq. -/
theorem entropy10 {T:Mat m} (he:1+T=q.covMat) :
    logD q.covMat - trN T + etw T (q.Hmat v) - q.delt d + eNt q.edge/8 ≤
      Real.log (chi q.C q.V*chi q.D q.U)/m := by
  have hp := q.pos.det_pos
  have HH : q.V ∈ interior ((posDual q.C):Set (Rn m)) := q.V_in
  have hc := chi_pos (C:=q.C) ⟨q.U,q.U_in⟩ q.V_in
  have hq : q.U ∈ interior ((posDual q.D):Set (Rn m)) := by
    rw [show posDual q.D=q.C from ProperCone.innerDual_innerDual _]; exact q.U_in
  have hd := chi_pos (C:=q.D) ⟨q.V,q.V_in⟩ hq
  have hX := q.primalMap.entropy q.V HH hp.ne'
  have hv : (-q.S).det≠0 := by rw [det_neg]; positivity
  have hY := q.dualMap.entropy q.U hq hv
  rw [q.X_cost] at hX; rw [q.Y_cost] at hY
  change -logN0+1/2+logD q.S+eGain q.edge-m/(m:ℝ) ≤ _ at hX
  change -logN0+1/2+logD (-q.S)+eGain q.edge.ref-q.cBy*m/(m:ℝ) ≤ _ at hY
  change _ ≤ Real.log (chi q.C q.V)/m at hX
  change _ ≤ Real.log (chi q.D q.U)/m at hY
  have hg := q.gain_eq11; rw [LC_average] at hg
  rw [q.cBy_eq,q.logD_cov,Real.log_mul hc.ne' hd.ne',add_div]
  have hm := m_pos (m:=m)
  rw [div_self hm.ne'] at hX
  have heq : logD (-q.S)=logD q.S := by
    rw [logD,det_neg,Real.log_mul (by positivity) hp.ne',Real.log_pow]
    simp [logD]
  rw [heq,mul_div_cancel_right₀ _ hm.ne'] at hY
  have hu := q.h_weighted v_test
  rw [← he,etw_add (q.H_integrable v_test.der.poly)] at hu
  have ht : q.s0=1+trN T := by rw [s0,← he,trN_add,trN_one]
  rw [show etw 1 (q.Hmat v)= _ from (show etw 1 (q.Hmat v)=et (q.Hmat v) by simp [etw])] at hu
  linarith

end ProjField
end GeneralMahler

end

end OAI
