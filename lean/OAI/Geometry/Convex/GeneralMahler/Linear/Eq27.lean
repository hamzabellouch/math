import OAI.Geometry.Convex.GeneralMahler.Linear.Comm
import OAI.Geometry.Convex.GeneralMahler.Linear.Gauss
import OAI.Geometry.Convex.GeneralMahler.Linear.Nu

namespace OAI
/-! §06 final commutator comparison. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open LPt Profile HMode Segment Layers
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def cmbf (x:ℝ) := Kp x+tc*Cp x
lemma cmb_test : TestF cmbf := testK.add ((TestF.const _).mul testC)
lemma expcmb : q.expL cmbf=q.expL Kp+tc•q.expL Cp := by
  let f:=tc
  have he (x:Rn m):
      q.FL.eval cmbf x=q.FL.eval Kp x+tc•q.FL.eval Cp x := by
    have h (g:ℝ→ℝ) (hg:TestF g) :
        q.FL.eval (fun x=>Kp x+g x) x=q.FL.eval Kp x+q.FL.eval g x :=
      cfc_add (q.Lmat x) _ _ testK.cont.continuousOn hg.cont.continuousOn
    unfold cmbf; rw [h (fun x=>tc*Cp x) ((TestF.const _).mul testC),q.FL.eval_scale testC]
  have hi (f:ℝ→ℝ) : q.expL f=∫ x,q.FL.eval f x ∂normal m := rfl
  rw [hi,hi,hi]; simp_rw [he]
  rw [integral_add (q.FL.eval_reg testK).ig (show Integrable (fun x=>tc • q.FL.eval Cp x) (normal m) from Integrable.smul tc (q.FL.eval_reg testC).ig),integral_smul]

lemma eiganti (i:Fin m) (f:ℝ→ℝ) (x:Rn m):
    hsN (cmu (q.FL.eval f x) (q.M i))=q.nupt i x (fun u=>anti u f^2) := by
  let A :=q.FL.eval f x
  let U:=q.FL.Fr x
  have h : U.loc A = diagonal (fun i=>f (q.FL.ev x i)) := q.FL.evfrm x f
  have he : U.eig A=fun i=>f (q.FL.ev x i) := by unfold Frm.eig; rw [h,Matrix.diag_diagonal]
  have hh : U.Dgn A := by unfold Frm.Dgn; rw [h,he]
  rw [cmu_eig A _ U hh,he]
  unfold nupt npt; congr 1; ext j; apply Finset.sum_congr rfl
  intro k _
  dsimp only [anti,U]; ring

lemma eq27elem (T:Mat m) (he:updEq (q.expL Cp) (q.expL Kp) T=0)
    (ht:T∈specBox m tmin tmax)
    (hH: scalar m mstar ≤ updGap (q.expL Cp) T) (i:Fin m):
    (80/100)*hsN (cmu (q.M i) T) ≤ (∫ x,q.nupt i x sgamma ∂normal m) := by
  have hx := Comm_bound (q.expL_sym testC.cont testC.poly) ht he hH (q.M i)
  rw [← q.expcmb] at hx
  let f := fun u:Plane=> anti u cmbf^2
  let g := fun u:Plane=> anti u Cp^2
  have h (x:Rn m) :
      q.nupt i x sgamma = (80/100/mstar^2)*((125/100)*q.nupt i x f+
        5*Profile.tr^2*q.nupt i x g) := by
    unfold nupt
    have he : sgamma=fun u=>(80/100/mstar^2)*((125/100)*f u+5*Profile.tr^2*g u) := by
      ext; unfold sgamma f g cmbf anti; ring
    rw [he,n_s,n_add,n_s,n_s]
  have hi:= q.comm_expect (q.M i) cmb_test
  have hj:= q.comm_expect (q.M i) testC
  simp_rw [q.eiganti] at hi hj
  change hsN _ ≤ ∫ x,q.nupt i x f ∂normal m at hi
  change hsN _ ≤ ∫ x,q.nupt i x g ∂normal m at hj
  simp_rw [h,integral_const_mul]
  have hfi := (q.nu_i (Wsq (Wa cmb_test)) i).const_mul (125/100)
  have hgi := (q.nu_i (Wsq (Wa testC)) i).const_mul (5*Profile.tr^2)
  rw [integral_add (show Integrable (fun x=>125/100*q.nupt i x f) (normal m) from hfi)
    (show Integrable (fun x=> (5*Profile.tr^2)*q.nupt i x g) (normal m) from hgi),
    integral_const_mul,integral_const_mul]
  unfold mstar Profile.tr at *; norm_num at *; linarith

lemma eq27 (T:Mat m) (he:updEq (q.expL Cp) (q.expL Kp) T=0)
    (ht:T∈specBox m tmin tmax)
    (hH: scalar m mstar ≤ updGap (q.expL Cp) T) :
    (80/100)*Hcomm q.Lmat T ≤ q.nu sgamma := by
  rw [q.Comm_L,Finset.mul_sum]; unfold nu
  exact Finset.sum_le_sum (fun i _=> q.eq27elem T he ht hH i)
end ProjField
end GeneralMahler

end

end OAI
