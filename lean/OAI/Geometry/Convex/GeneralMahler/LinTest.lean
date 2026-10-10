import OAI.Geometry.Convex.GeneralMahler.FormLin

namespace OAI
/-! Test/functional linearities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
namespace Profile
variable {f g:ℝ→ℝ}
lemma sq_test (hf:TestF f) : TestF (fun x=>f x^2) := by
  simpa only [pow_two] using hf.mul hf
lemma drv_sub (hf:TestF f) (hg:TestF g) :
    deriv (fun x=>f x-g x)=fun x=>deriv f x-deriv g x := by
  ext x; exact ((hf.diff x).hasDerivAt.fun_sub (hg.diff x).hasDerivAt).deriv
lemma prim_sub (hf:TestF f) (hg:TestF g) :
    prim (fun x=>f x-g x)=fun x=>prim f x-prim g x := by
  ext x; unfold prim; rw [intervalIntegral.integral_sub]; exact hf.cont.intervalIntegrable ..; exact hg.cont.intervalIntegrable ..
lemma pl_sub (hf:TestF f) (hg:TestF g) :
    pl (fun x=>f x-g x)=fun x=>pl f x-pl g x := by
  unfold pl; rw [prim_sub hf hg,ga_sub (p_test hf) (p_test hg)]; ext; ring
lemma N_sub (hf:TestF f) (hg:TestF g) :
    N (fun x=>f x-g x)=fun x=>N f x-N g x := by
  unfold N; rw [drv_sub hf hg,drv_sub hf.der hg.der]; ext; ring
lemma ps_sub (hf:TestF f) (hg:TestF g) :
    ps (fun x=>f x-g x)=fun x=>ps f x-ps g x := by
  unfold ps
  have hh := pl_test hf
  have hi := pl_test hg
  rw [pl_sub hf hg,N_sub hh hi,← prim_sub ((N_test hh).sub hh) ((N_test hi).sub hi)]
  congr 1; ext; ring
end Profile
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
lemma delt_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    q.delt (fun x=>f x-g x)=q.delt f-q.delt g := by
  rw [q.delta_eq (hf.sub hg),q.delta_eq hf,q.delta_eq hg]
  have h : shiftD (fun x=>f x-g x)=fun x=>shiftD f x-shiftD g x := by
    unfold shiftD; rw [drv_sub hf hg]; ext; ring
  have hi (f:ℝ→ℝ) (hf:TestF f) : TestF (shiftD f) := ((((TestF.const _).mul
    TestF.id).mul hf).sub hf.der)
  rw [h]
  simp_rw [mul_sub]
  rw [integral_sub (q.pb_m.int_test hf) (q.pb_m.int_test hg),
    integral_sub (q.rk_m.int_test (hi f hf)) (q.rk_m.int_test (hi g hg))]
  ring
omit [NeZero m] in
lemma ct_sym (u:Plane) : q.ct u.swap=q.ct u := by unfold ct; simp [min_comm,max_comm]
omit [NeZero m] in
lemma Cts {f g:ℝ→ℝ} : q.Ct f g=q.Ct g f := by
  unfold Ct
  let l := fun u:Plane=> q.ct u*(deriv g u.1*deriv f u.2)
  rw [show (∫ u,l u)=(∫ u:Plane,l u.swap) from (integral_prod_swap _).symm]
  congr 1; ext u; unfold l; rw [q.ct_sym,mul_comm (deriv f u.1)]; rfl
end ProjField
end GeneralMahler

end

end OAI
