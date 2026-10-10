import OAI.Geometry.Convex.GeneralMahler.Threshold

namespace OAI
/-! Divided difference evaluated on two possibly different frames. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers Profile
variable {m:ℕ}

-- averages on segment
def along (u:Plane) (t:ℝ) := (1-t)*u.1+t*u.2
def bav (f:ℝ→ℝ) (u:Plane) := ∫ t in (0:ℝ)..1,f (along u t)
lemma bav_con {f:ℝ→ℝ} (hf:Continuous f) : Continuous (bav f) := by
  have hm : Continuous fun p:Plane × ℝ=> f (along p.1 p.2) := by unfold along; fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hm 0 1
lemma bav_same (f:ℝ→ℝ) (x:ℝ) : bav f (x,x)=f x := by
  have he (t) : along (x,x) t=x := by unfold along; ring
  unfold bav; simp_rw [he]; simp
lemma delta_eq {f} (hf:TestF f) (x y:ℝ) :
    f x-f y=bav (deriv f) (x,y)*(x-y) := by
  have he (t:ℝ) : HasDerivAt (fun t=>along (x,y) t) (y-x) t := by
    convert ((((hasDerivAt_const t 1).sub (hasDerivAt_id' t)).mul_const x).fun_add
      ((hasDerivAt_id' t).mul_const y)) using 1
    all_goals first | rfl | ring
  have hd (t:ℝ) : HasDerivAt (fun t=> f (along (x,y) t)) (deriv f (along (x,y) t)*(y-x)) t :=
    ((hf.diff _).hasDerivAt).comp t (he t)
  have hc : Continuous (fun t:ℝ=> deriv f (along (x,y) t)*(y-x)) :=
    ((hf.der.cont.comp (by unfold along; fun_prop)).mul continuous_const)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hd t)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const,show along (x,y) 1=y from by unfold along; ring,
    show along (x,y) 0=x from by unfold along; ring] at hh
  unfold bav; linarith

lemma bav_bound {f} (hf:PolyBound f) : PolyBound (bav f) := by
  obtain ⟨C,n,hc,h⟩ := hf
  refine ⟨C,n,hc,fun u=>?_⟩
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t=>f (along u t))
    (C:=C*(1+‖u‖)^n) (a:=0) (b:=1) ?_
  · unfold bav; convert he using 1; first | rfl | simp
  intro z hz
  have ha : 0≤z ∧ z≤1 := by rw [uIoc_of_le zero_le_one] at hz; exact ⟨le_of_lt hz.1,hz.2⟩
  apply (h _).trans
  have hb : ‖along u z‖≤‖u‖ := by
    change |(1-z)*u.1+z*u.2| ≤ max |u.1| |u.2|
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg ha.1,abs_of_nonneg (by linarith)]
    calc
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left |u.1| |u.2|) (sub_nonneg.mpr ha.2))
        (mul_le_mul_of_nonneg_left (le_max_right |u.1| |u.2|) ha.1)
      _ = _ := by ring
  gcongr

namespace Frm
variable (u v w:Frm m)
def showM (A:Mat m) := star u.val*A*v.val
def hideM (A:Mat m) := u.val*A*star v.val
lemma reveal (A:Mat m) : u.showM v (u.hideM v A)=A := by
  unfold showM hideM
  simp only [mul_assoc]; rw [v.m₁,mul_one,← mul_assoc,u.m₁,one_mul]
lemma combine (C:Mat m) (v w:Frm m) :
    u.showM w C=(u.showM v C)*(v.showM w 1) := by
  unfold showM; simp only [mul_one,mul_assoc]
  rw [show v.val*(star v.val*w.val)=w.val from by rw [← mul_assoc,v.m₂,one_mul] ]

def secDiag (A B:Mat m) (g:Plane→ℝ) (C:Mat m) : Mat m :=
  Matrix.of (fun i j=> g (u.eig A i,v.eig B j)*u.showM v C i j)
def sec (A B:Mat m) (g:Plane→ℝ) (C:Mat m) :=
  u.hideM v (u.secDiag v A B g C)
lemma sec_eq (A B C:Mat m) (g:Plane→ℝ) (i j) :
    u.showM v (u.sec v A B g C) i j = g (u.eig A i,v.eig B j)*u.showM v C i j := by
  rw [sec,reveal]; rfl

lemma sec_add (A B:Mat m) (g:Plane→ℝ) (C D:Mat m) :
    u.sec v A B g (C+D)=u.sec v A B g C+u.sec v A B g D := by
  have he : u.secDiag v A B g (C+D) = u.secDiag v A B g C+u.secDiag v A B g D := by
    ext i j; simp [secDiag,showM,mul_add,add_mul]
  unfold sec; rw [he]; simp only [hideM,mul_add,add_mul]
lemma sec_smul (A B:Mat m) (g:Plane→ℝ) (a:ℝ) (C:Mat m) :
    u.sec v A B g (a•C)=a•u.sec v A B g C := by
  unfold sec
  have he : u.secDiag v A B g (a•C)=a•u.secDiag v A B g C := by
    ext i j; simp [secDiag,showM,mul_left_comm]
  rw [he]
  simp only [hideM,smul_mul_assoc,mul_smul_comm]

lemma Aentry (A:Mat m) (h:u.Dgn A) (i j) :
    u.showM v A i j= u.eig A i * u.showM v 1 i j := by
  unfold showM; rw [mul_one,u.fix_mul_cross v A,show u.loc A=_ from h,Matrix.diagonal_mul]
lemma Bentry (A:Mat m) (h:v.Dgn A) (i j) :
    u.showM v A i j=u.showM v 1 i j*v.eig A j := by
  unfold showM; rw [mul_one,u.fix_mul_cross' v A,show v.loc A=_ from h,Matrix.mul_diagonal]
lemma Aeval (A:Mat m) (h:A.IsHermitian) (hh:u.Dgn A) (f:ℝ→ℝ) (i j):
    u.showM v (cfc f A) i j=f (u.eig A i)*u.showM v 1 i j := by
  unfold showM; rw [mul_one,u.fix_mul_cross v,u.loc_cfc h hh f,Matrix.diagonal_mul]
lemma Beval (A:Mat m) (h:A.IsHermitian) (hh:v.Dgn A) (f:ℝ→ℝ) (i j):
    u.showM v (cfc f A) i j=u.showM v 1 i j*f (v.eig A j) := by
  unfold showM; rw [mul_one,u.fix_mul_cross' v,v.loc_cfc h hh f,Matrix.mul_diagonal]
lemma show_sub (A B:Mat m) : u.showM v (A-B)=u.showM v A-u.showM v B := by
  simp only [showM,mul_sub,sub_mul]

lemma exact_sec {A B:Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian)
    (hu:u.Dgn A) (hv:v.Dgn B) {f:ℝ→ℝ} (hf:TestF f) :
    cfc f A-cfc f B=u.sec v A B (bav (deriv f)) (A-B) := by
  apply u.cross_cancel v
  change u.showM v _ = u.showM v _
  ext i j
  rw [sec_eq,u.show_sub,u.show_sub]; simp only [Matrix.sub_apply]
  rw [u.Aentry v A hu,u.Bentry v B hv,u.Aeval v A ha hu,u.Beval v B hb hv]
  have hh := delta_eq hf (u.eig A i) (v.eig B j)
  linear_combination u.showM v 1 i j*hh

-- Right frame independence for all test kernels on entries
lemma sec_ind (A B C:Mat m) (g:Plane→ℝ) (hv:v.Dgn B) (hw:w.Dgn B) :
    u.sec v A B g C=u.sec w A B g C := by
  apply u.cross_cancel w
  change u.showM w _= u.showM w _
  ext i j
  rw [sec_eq,combine u (u.sec v A B g C) v w, combine u C v w]
  simp_rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [sec_eq]
  by_cases h : v.showM w 1 k j=0
  · rw [h]; ring
  have he : v.eig B k=w.eig B j := by
    have he := (v.Aentry w B hv k j).symm.trans (v.Bentry w B hw k j)
    exact mul_right_cancel₀ h (he.trans (mul_comm ..))
  rw [he]; ring
end Frm
end GeneralMahler

end

end OAI
